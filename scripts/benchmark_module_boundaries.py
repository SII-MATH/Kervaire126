#!/usr/bin/env python3
"""Compile six real mutations at the M08 and M16 module handoffs.

Run after ``lake build KIP126 checkdecls``. Every experiment starts from the
same successful warm build, changes one real producer declaration, and keeps
the consumer source untouched. A private opaque identity theorem changes an
actual proof expression; an optional True binder changes an actual public
type while keeping the existing applications compilable. These are temporary
experiments, never proposed changes to the mathematical interface.

Both source bytes and the project's complete .lake/build tree are
restored after every experiment, including failures. Dependencies are not
cleaned or changed. The JSON report records Lean expression hashes, artifact
SHA-256 hashes/timestamps, Lake Built/Replayed actions, elapsed build time,
and exact patches. This checks reuse, not proof completion or a percentage
speedup relative to the old layout.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import difflib
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import tempfile
import time

from module_boundaries import header_tokens, tokens


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "KIP126.Main.Solution.Route.Section7"
KINDS = ("public-proof", "internal-proof", "public-statement")
WRAPPER_NAME = "moduleBoundaryExperimentTransport"
WRAPPER = (
    f"\nprivate theorem {WRAPPER_NAME} {{P : Prop}} (h : P) : P := by\n"
    "  exact h\n"
)
ARTIFACT_SUFFIXES = ("olean", "olean.server", "olean.private", "ir", "ilean", "trace")
ACTION_RE = re.compile(
    r"^[^\[\n]*\[\d+(?:/\d+)?\]\s+(Built|Replayed|Fetched|Unpacked)\s+([^\s(]+)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Declaration:
    module: str
    name: str
    private: bool = False

    @property
    def source(self) -> Path:
        return Path(*self.module.split(".")).with_suffix(".lean")

    @property
    def short_name(self) -> str:
        return self.name.rsplit(".", 1)[-1]


@dataclass(frozen=True)
class Boundary:
    name: str
    provider: Declaration
    implementation: Declaration
    consumer: str


BOUNDARIES = (
    Boundary(
        "M08",
        Declaration(f"{PREFIX}.ThetaMassey", f"{PREFIX}.h5_square_times_entire_770_zero"),
        Declaration(f"{PREFIX}.ThetaMassey", f"{PREFIX}.theta_b_massey_from_inputs", True),
        f"{PREFIX}.ThetaToda",
    ),
    Boundary(
        "M16",
        Declaration(f"{PREFIX}.WeakY", f"{PREFIX}.weak_y_exists"),
        Declaration(f"{PREFIX}.WeakRepresentative", f"{PREFIX}.main_weak_high_representative", True),
        f"{PREFIX}.NuTarget",
    ),
)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def artifact_state(root: Path, modules: list[str]) -> dict:
    state = {}
    for module in modules:
        stem = root / ".lake/build/lib/lean" / Path(*module.split("."))
        files = {}
        for suffix in ARTIFACT_SUFFIXES:
            path = Path(f"{stem}.{suffix}")
            if not path.is_file():
                raise RuntimeError(f"Missing warm-build artifact: {path}")
            stat = path.stat()
            files[suffix] = {"sha256": sha256(path), "mtimeNs": stat.st_mtime_ns,
                             "sizeBytes": stat.st_size}
            if suffix == "trace":
                saved = json.loads(path.read_text())
                files[suffix]["lakeDepHash"] = saved.get("depHash")
                files[suffix]["lakeInputs"] = saved.get("inputs")
        state[module] = files
    return state


def offset(text: str, token) -> int:
    return sum(len(line) for line in text.splitlines(keepends=True)[:token.line - 1]) + token.column


def theorem_tokens(text: str, declaration: Declaration):
    """Locate the selected real theorem, ignoring comments and string contents."""
    ts = tokens(text)
    starts = [i for i in range(len(ts) - 1)
              if ts[i].value == "theorem" and ts[i + 1].value in
              (declaration.short_name, declaration.name)]
    if len(starts) != 1:
        raise RuntimeError(f"Expected one theorem {declaration.short_name}; found {len(starts)}")
    start = starts[0]
    depth = 0
    colon = None
    for i in range(start + 2, len(ts) - 1):
        value = ts[i].value
        if value in ("(", "[", "{"):
            depth += 1
        elif value in (")", "]", "}"):
            depth -= 1
        elif depth == 0 and value == ":" and colon is None:
            colon = ts[i]
        # The selected private Massey theorem has `let ... := ...` in its type.
        # Its declaration assignment is the top-level `:= by`, not those lets.
        elif depth == 0 and value == ":=" and ts[i + 1].value == "by":
            if colon is None:
                raise RuntimeError(f"Missing result type for {declaration.name}")
            return colon, ts[i + 1]
    raise RuntimeError(f"Cannot locate a tactic proof for {declaration.name}")


def mutate(text: str, declaration: Declaration, kind: str) -> str:
    colon, proof_by = theorem_tokens(text, declaration)
    if kind == "public-statement":
        at = offset(text, colon)
        return text[:at] + "(_moduleBoundaryProbe : True := True.intro) " + text[at:]
    if WRAPPER_NAME in text:
        raise RuntimeError("Temporary proof wrapper already exists in producer source")
    at = offset(text, proof_by) + len("by")
    if text[at:at + 1] != "\n":
        raise RuntimeError(f"Expected a multiline tactic proof for {declaration.name}")
    changed = text[:at] + f"\n  refine _root_.{WRAPPER_NAME} ?_" + text[at:]
    header = header_tokens(changed)
    if not header:
        raise RuntimeError("Expected a Lean module/import header")
    end = changed.find("\n", offset(changed, header[-1]))
    if end < 0:
        raise RuntimeError("Incomplete module header")
    return changed[:end + 1] + WRAPPER + changed[end + 1:]


def run_command(command: list[str], root: Path, env: dict, log: Path,
                timeout: int) -> dict:
    started = time.monotonic()
    timed_out = False
    with log.open("w") as output:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            returncode = process.wait(timeout=timeout)
        except BaseException as exc:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            if not isinstance(exc, subprocess.TimeoutExpired):
                raise
            returncode = process.returncode
            timed_out = True
    log_text = log.read_text(errors="replace")
    actions: dict[str, list[str]] = {}
    for action, module in ACTION_RE.findall(log_text):
        actions.setdefault(action.lower(), []).append(module)
    return {"command": command, "returnCode": returncode, "timedOut": timed_out,
            "elapsedSeconds": round(time.monotonic() - started, 3),
            "actualBuilt": sorted(set(actions.get("built", []))),
            "actions": actions, "log": log.name}


def expression_state(root: Path, env: dict, declarations: list[Declaration],
                     output: Path, tag: str, timeout: int) -> dict:
    imports = sorted({decl.module for decl in declarations})
    lines = ["module", "import Lean"] + [f"import all {module}" for module in imports]
    lines += ["", "run_cmd do", "  let env := (← Lean.getEnv).setExporting false"]
    for declaration in declarations:
        name = f"`{declaration.name}"
        if declaration.private:
            name = f"Lean.mkPrivateNameCore `{declaration.module} {name}"
        lines += [
            f"  let name := {name}",
            "  let some info := env.find? name | throwError \"Missing declaration {name}\"",
            "  let some value := info.value? (allowOpaque := true) | throwError \"No proof body for {name}\"",
            "  let entry := Lean.Json.mkObj [",
            f'    ("key", Lean.toJson "{declaration.name}"),',
            '    ("resolvedName", Lean.toJson name.toString),',
            '    ("typeHash", Lean.toJson (toString (hash info.type))),',
            '    ("valueHash", Lean.toJson (toString (hash value)))]',
            '  Lean.logInfo m!"MODULE_BOUNDARY_EXPR {entry.compress}"',
        ]
    probe = output / f"{tag}.probe.lean"
    probe.write_text("\n".join(lines) + "\n")
    log = output / f"{tag}.probe.log"
    result = run_command(["lake", "env", "lean", str(probe)], root, env, log, timeout)
    if result["returnCode"] or result["timedOut"]:
        raise RuntimeError(f"Compiled-expression probe failed; see {log.name}")
    found = {}
    for line in log.read_text().splitlines():
        if "MODULE_BOUNDARY_EXPR " in line:
            item = json.loads(line.split("MODULE_BOUNDARY_EXPR ", 1)[1])
            found[item.pop("key")] = item
    if len(found) != len(declarations):
        raise RuntimeError(f"Expected {len(declarations)} expression records, found {len(found)}")
    return found


def check_case(boundary: Boundary, kind: str, declaration: Declaration,
               before: dict, after: dict, expr_before: dict, expr_after: dict,
               build: dict) -> list[str]:
    errors = []

    def require(ok: bool, message: str) -> None:
        if not ok:
            errors.append(message)

    built = set(build["actualBuilt"])
    require(build["returnCode"] == 0 and not build["timedOut"], "Mutated build did not succeed")
    require(declaration.module in built, "Changed source module was not actually compiled")
    old_expr, new_expr = expr_before[declaration.name], expr_after[declaration.name]
    provider = boundary.provider.module
    consumer = boundary.consumer
    public_changed = (before[provider]["olean"]["sha256"] != after[provider]["olean"]["sha256"])
    if kind == "public-statement":
        require(old_expr["typeHash"] != new_expr["typeHash"], "Public declaration type did not change")
        require(public_changed, "Changed public statement did not change provider .olean")
        require(consumer in built, "Consumer did not recompile after a public statement change")
        require(before[consumer]["trace"] != after[consumer]["trace"], "Consumer trace did not change")
    else:
        require(old_expr["typeHash"] == new_expr["typeHash"], "Proof mutation changed declaration type")
        require(old_expr["valueHash"] != new_expr["valueHash"], "Actual compiled proof expression did not change")
        require(before[declaration.module]["olean.private"]["sha256"] !=
                after[declaration.module]["olean.private"]["sha256"], "Private artifact did not change")
        require(not public_changed, "Hidden proof change leaked into provider .olean")
        require(consumer not in built, "Consumer recompiled after a hidden proof change")
        require(before[consumer] == after[consumer], "Reused consumer artifacts or timestamps changed")
        if kind == "internal-proof" and declaration.module != provider:
            require(provider in built, "Public handoff producer did not consume the private implementation change")
    return errors


def run_suite(root: Path, output: Path, boundaries=BOUNDARIES, timeout: int = 1200) -> dict:
    root, output = root.resolve(), output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    # Disable artifact-cache restoration, not Lake's dependency checking. Never use --old.
    env.update({"LAKE_ARTIFACT_CACHE": "false", "LAKE_NO_CACHE": "true"})
    targets = sorted({boundary.consumer for boundary in boundaries})
    declarations = list(dict.fromkeys(
        decl for boundary in boundaries for decl in (boundary.provider, boundary.implementation)))
    modules = sorted({*targets, *(decl.module for decl in declarations)})
    source_paths = sorted({decl.source for decl in declarations})
    source_original = {p: (root / p).read_bytes() for p in source_paths}
    consumer_sources = {m: sha256(root / Path(*m.split(".")).with_suffix(".lean")) for m in targets}
    command = ["lake", "--no-ansi", "--no-cache", "-v", "build", *targets]
    report = {"schemaVersion": 1, "boundaries": [asdict(b) for b in boundaries],
              "interpretation": "Incremental reuse after real proof/type mutations; no proof-completion or old/new speedup claim.",
              "environment": {"platform": platform.platform(), "cpuCount": os.cpu_count(),
                              "leanNumThreads": env.get("LEAN_NUM_THREADS"),
                              "artifactCache": False, "externalCacheDownloads": False},
              "cases": [], "passed": False, "sourcesRestored": False, "artifactsRestored": False}

    def write_report() -> None:
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def restore_sources() -> None:
        for relative, content in source_original.items():
            path = root / relative
            if path.read_bytes() != content:
                path.write_bytes(content)

    try:
        for label, cmd in (("leanVersion", ["lean", "--version"]),
                           ("lakeVersion", ["lake", "--version"]),
                           ("commit", ["git", "rev-parse", "HEAD"])):
            result = subprocess.run(cmd, cwd=root, env=env, text=True, capture_output=True, timeout=60)
            report["environment"][label] = result.stdout.strip()
        report["warmBuild"] = run_command(command, root, env, output / "warm-build.log", timeout)
        if report["warmBuild"]["returnCode"] or report["warmBuild"]["timedOut"]:
            raise RuntimeError("Warm build failed; no source was mutated")
        baseline = artifact_state(root, modules)
        report["baselineArtifacts"] = baseline
        report["baselineExpressions"] = expression_state(root, env, declarations, output, "baseline", timeout)
        report["noopBuild"] = run_command(command, root, env, output / "noop-build.log", timeout)
        if (report["noopBuild"]["returnCode"] or report["noopBuild"]["actualBuilt"]
                or artifact_state(root, modules) != baseline):
            raise RuntimeError("No-op warm build was not stable")
        build_dir = root / ".lake/build"
        if build_dir.is_symlink():
            raise RuntimeError("Refusing to snapshot/replace a symlinked project build directory")
        with tempfile.TemporaryDirectory(prefix="module-boundary-snapshot-", dir=root / ".lake") as temporary:
            backup = Path(temporary) / "build"
            shutil.copytree(build_dir, backup, symlinks=True)

            def restore_artifacts() -> None:
                shutil.rmtree(build_dir)
                shutil.copytree(backup, build_dir, symlinks=True)

            try:
                for boundary in boundaries:
                    for kind in KINDS:
                        tag = f"{boundary.name}-{kind}"
                        print(f"Running {tag}", flush=True)
                        declaration = boundary.implementation if kind == "internal-proof" else boundary.provider
                        source_path = root / declaration.source
                        original = source_original[declaration.source].decode()
                        case = {"id": tag, "kind": kind, "declaration": asdict(declaration), "passed": False}
                        report["cases"].append(case)
                        try:
                            changed = mutate(original, declaration, kind)
                            case["sourceBeforeSha256"] = hashlib.sha256(original.encode()).hexdigest()
                            case["sourceAfterSha256"] = hashlib.sha256(changed.encode()).hexdigest()
                            (output / f"{tag}.patch").write_text("".join(difflib.unified_diff(
                                original.splitlines(keepends=True), changed.splitlines(keepends=True),
                                fromfile=str(declaration.source), tofile=str(declaration.source))))
                            source_path.write_text(changed)
                            case["build"] = run_command(command, root, env, output / f"{tag}.build.log", timeout)
                            if case["build"]["returnCode"] or case["build"]["timedOut"]:
                                raise RuntimeError("Mutated build failed; see build log")
                            case["artifacts"] = artifact_state(root, modules)
                            case["expressions"] = expression_state(root, env, declarations, output, tag, timeout)
                            case["errors"] = check_case(boundary, kind, declaration, baseline, case["artifacts"],
                                report["baselineExpressions"], case["expressions"], case["build"])
                            unchanged = all(sha256(root / Path(*m.split(".")).with_suffix(".lean")) == value
                                            for m, value in consumer_sources.items())
                            if not unchanged:
                                case["errors"].append("Consumer source changed during the experiment")
                            case["passed"] = not case["errors"]
                        except Exception as exc:
                            case["errors"] = [str(exc)]
                        finally:
                            restore_sources()
                            restore_artifacts()
                            case["baselineRestored"] = artifact_state(root, modules) == baseline
                            if not case["baselineRestored"]:
                                raise RuntimeError("Artifact snapshot restoration failed")
                            write_report()
                        print(f"{tag}: {'PASS' if case['passed'] else 'FAIL'}", flush=True)
            finally:
                restore_sources()
                restore_artifacts()
                report["artifactsRestored"] = artifact_state(root, modules) == baseline
        report["restoredNoopBuild"] = run_command(command, root, env, output / "restored-noop-build.log", timeout)
        report["restoredNoopArtifacts"] = artifact_state(root, modules)
        restored_noop_ok = (report["restoredNoopBuild"]["returnCode"] == 0
                            and not report["restoredNoopBuild"]["actualBuilt"]
                            and report["restoredNoopArtifacts"] == baseline)
        report["passed"] = (len(report["cases"]) == len(boundaries) * len(KINDS)
                            and all(case["passed"] for case in report["cases"])
                            and report["artifactsRestored"] and restored_noop_ok)
    except Exception as exc:
        report["error"] = str(exc)
    finally:
        restore_sources()
        report["sourcesRestored"] = all((root / p).read_bytes() == content
                                        for p, content in source_original.items())
        report["passed"] = report["passed"] and report["sourcesRestored"]
        write_report()
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "metrics/module-boundary-benchmark")
    parser.add_argument("--command-timeout-seconds", type=int, default=1200)
    args = parser.parse_args()
    # GitHub runner cancellation may send TERM. Unwind the snapshot/source
    # finally blocks, and terminate the active Lean process group first.
    def cancelled(_signum, _frame):
        raise KeyboardInterrupt("Module boundary experiments cancelled")
    signal.signal(signal.SIGTERM, cancelled)
    report = run_suite(ROOT, args.output, timeout=args.command_timeout_seconds)
    print(f"Module boundary experiments: {'PASS' if report['passed'] else 'FAIL'}")
    print(f"Report: {args.output / 'report.json'}")
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
