#!/usr/bin/env python3
"""Read-only Lean MCP transport probe; native agent access is tested separately.

The JSON-line reader stays alive until both tool responses arrive. This avoids
tearing down an async client task group while a long Lean request is pending.
No source/build/cache copies are created and no proof is edited.
"""
import argparse
import hashlib
import json
from pathlib import Path
import queue
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[1]


def content_data(result):
    if result.get('isError'):
        raise RuntimeError('MCP tool error: ' + json.dumps(result, ensure_ascii=False))
    structured = result.get('structuredContent')
    if structured is not None:
        return structured
    texts = [item['text'] for item in result.get('content', [])
             if item.get('type') == 'text']
    if len(texts) == 1:
        try:
            return json.loads(texts[0])
        except ValueError:
            pass
    return {'text': '\n'.join(texts)}


class StdioClient:
    def __init__(self, command, stderr, timeout, cwd=ROOT):
        self.process = subprocess.Popen(command, cwd=cwd, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=stderr,
                                        text=True, bufsize=1, start_new_session=True)
        self.timeout = timeout
        self.messages = queue.Queue()
        self.serial = 0
        self.reader = threading.Thread(target=self._read, daemon=True)
        self.reader.start()

    def _read(self):
        try:
            for line in self.process.stdout:
                self.messages.put(json.loads(line))
        except Exception as exc:
            self.messages.put(exc)
        finally:
            self.messages.put(EOFError('MCP server closed stdout'))

    def send(self, method, params, request_id=None):
        message = {'jsonrpc': '2.0', 'method': method, 'params': params}
        if request_id is not None:
            message['id'] = request_id
        self.process.stdin.write(json.dumps(message) + '\n')
        self.process.stdin.flush()

    def request(self, method, params):
        self.serial += 1
        request_id = self.serial
        self.send(method, params, request_id)
        deadline = time.monotonic() + self.timeout
        while True:
            try:
                message = self.messages.get(timeout=max(0, deadline - time.monotonic()))
            except queue.Empty as exc:
                raise TimeoutError(f'MCP {method} exceeded {self.timeout}s') from exc
            if isinstance(message, Exception):
                raise message
            if message.get('id') != request_id or 'method' in message:
                continue
            if 'error' in message:
                raise RuntimeError('MCP protocol error: ' + json.dumps(message['error']))
            return message['result']

    def close(self):
        # First let the server consume EOF and close its LSP processes itself.
        if self.process.stdin:
            self.process.stdin.close()
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            import os
            os.killpg(self.process.pid, signal.SIGTERM)
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
        self.reader.join(timeout=2)
        self.process.stdout.close()


def check(file_path, line, column=1, timeout=180, log_path=None):
    target = Path(file_path).resolve(strict=True)
    if target.suffix != '.lean' or line < 1 or column < 1:
        raise ValueError('Expected a Lean file and positive 1-based line/column')
    if ROOT not in target.parents:
        raise ValueError('Use the actual repository or its prepared worker file')
    before = hashlib.sha256(target.read_bytes()).hexdigest()
    report = {'ok': False, 'native_agent_access': False, 'error_kind': 'infrastructure',
              'file_path': str(target), 'file_sha256': before, 'line': line,
              'column': column, 'project_root': str(ROOT),
              'transport': 'stdio', 'cache_copied': False}
    if log_path is None:
        with tempfile.NamedTemporaryFile(prefix='kip126-mcp-', suffix='.log', delete=False) as log:
            log_path = log.name
    log_path = Path(log_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    report['stderr_log'] = str(log_path)
    started = time.monotonic()
    deadline = started + timeout
    with log_path.open('w') as stderr:
        client = StdioClient([sys.executable, str(ROOT / 'scripts/kip126_lean_mcp.py')],
                             stderr, timeout)
        try:
            init = client.request('initialize', {'protocolVersion': '2025-03-26',
                                  'capabilities': {}, 'clientInfo': {
                                      'name': 'kip126-mcp-check', 'version': '1'}})
            client.send('notifications/initialized', {})
            definitions = client.request('tools/list', {})['tools']
            names = {tool['name'] for tool in definitions}
            required = {'lean_goal', 'lean_diagnostic_messages'}
            if not required <= names:
                raise RuntimeError('Required tools not advertised: ' + str(required - names))
            report['server'] = init['serverInfo']
            report['tools'] = sorted(required)
            report['polls'] = {}
            for key, name, extra in [('goal', 'lean_goal', {'line': line, 'column': column}),
                                     ('diagnostics', 'lean_diagnostic_messages', {})]:
                for attempt in range(3):
                    remaining = deadline - time.monotonic()
                    if remaining < 2:
                        raise TimeoutError('MCP readiness deadline exceeded')
                    client.timeout = remaining
                    response = client.request('tools/call', {'name': name, 'arguments': {
                        'file_path': str(target), **extra, 'timeout_s': min(60, remaining - 1)}})
                    data = content_data(response)
                    report[key] = data.get('result', data)
                    report['polls'][key] = attempt + 1
                    if (report[key].get('status') != 'still_elaborating' and
                            not report[key].get('partial')):
                        break
            if before != hashlib.sha256(target.read_bytes()).hexdigest():
                raise RuntimeError('File changed during MCP probe; retry current source')
            if report['goal'].get('status') == 'still_elaborating' or report['diagnostics'].get('partial'):
                raise TimeoutError('Lean is still elaborating; rerun/poll before proving')
            if not any(report['goal'].get(key) for key in ('goals', 'goals_before', 'goals_after')):
                raise RuntimeError('No concrete goal at requested position; choose a current tactic position')
            # Existing candidate proof errors remain visible in diagnostics; they
            # do not mean the MCP transport or goal query failed.
            report.update(ok=True, error_kind=None)
        except Exception as exc:
            report['error'] = f'{type(exc).__name__}: {exc}'
        finally:
            client.close()
    report['elapsed_seconds'] = round(time.monotonic() - started, 3)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--file', required=True)
    parser.add_argument('--line', required=True, type=int)
    parser.add_argument('--column', type=int, default=1)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.timeout < 1 or args.timeout > 600:
        parser.error('--timeout must be between 1 and 600 seconds')
    try:
        report = check(args.file, args.line, args.column, args.timeout,
                       args.output.with_suffix('.stderr.log') if args.output else None)
    except Exception as exc:
        report = {'ok': False, 'error_kind': 'infrastructure',
                  'error': f'{type(exc).__name__}: {exc}'}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(report, ensure_ascii=False))
    return 0 if report['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
