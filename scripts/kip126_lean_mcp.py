#!/usr/bin/env python3
"""Start the pinned Lean MCP with project-local, writable uv caches."""
import os
from pathlib import Path

root = Path(__file__).resolve().parents[1]
cache = root / 'Prover-all/.cache'
os.environ.setdefault('UV_CACHE_DIR', str(cache / 'uv'))
os.environ.setdefault('UV_TOOL_DIR', str(cache / 'tools'))
# Lightweight workers have source files only. Their language server must use
# the original project's toolchain and imports, not infer a separate Lake root.
os.environ['LEAN_PROJECT_PATH'] = str(root)
os.chdir(root)
os.execvp('uvx', ['uvx', '--from', 'lean-lsp-mcp==0.31.0', 'lean-lsp-mcp'])
