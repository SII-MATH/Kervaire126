"""Deterministic public Lean module syntax for generated certificate sources.

Only the module header, import visibility and section visibility are changed.
Callers hash and compare the resulting complete bytes; raw inputs and generated
mathematical declarations are never normalized for acceptance.
"""
from functools import wraps
from pathlib import Path
import re


def lean_module(source):
    """Retain existing module sources, or expose a legacy generated module."""
    binary = isinstance(source, bytes)
    text = source.decode("utf-8") if binary else source
    if re.match(r"^module\b", text):
        return source
    lines = text.strip().splitlines()
    imports = [i for i, line in enumerate(lines) if line.startswith("import ")]
    for i in imports:
        if not lines[i].startswith("import all "):
            lines[i] = "public " + lines[i]
    at = imports[-1] + 1 if imports else 0
    lines[at:at] = ["", "@[expose] public section", ""]
    text = "module\n\n" + "\n".join(lines).strip() + "\n"
    return text.encode("utf-8") if binary else text


def module_output(render):
    """Adapt a Lean renderer, including renderers returning mixed output maps."""
    @wraps(render)
    def wrapped(*args, **kwargs):
        output = render(*args, **kwargs)
        if isinstance(output, dict):
            return {path: lean_module(data) if str(path).endswith(".lean") else data
                    for path, data in output.items()}
        return lean_module(output)
    return wrapped
