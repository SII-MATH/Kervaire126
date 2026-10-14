#!/usr/bin/env python3
"""Translate supported DB equations to actual fixed-sphere Lean statements.

This bounded backend selects already proved producer rules. Its explicit
literature and LinE2Presentation arguments remain unconstructed inputs. It
neither proves the secondary d2 algorithm nor certifies the complete database.
Unsupported equations produce no Lean output.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import sqlite3
import sys
import time

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output

# Share the canonical manifest/LFS verification used by the algebra prototype.
_spec = importlib.util.spec_from_file_location(
    "replay_local_algebra", Path(__file__).with_name("replay-lowstem.py"))
_inputs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_inputs)

# Mathematical equations, not database ids, select the independently proved
# producer. These are the only currently certified coordinate patterns.
BACKENDS = {
    (5, 14, 2, (0,), ()): "row5432",
    (1, 16, 2, (0,), (0,)): "row5434",
}


def indices(code):
    if code == "":
        return ()
    values = tuple(int(i) for i in code.split(","))
    if any(i < 0 for i in values) or tuple(sorted(set(values))) != values:
        raise ValueError("noncanonical coordinate vector")
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--row", type=int, default=5434)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    path, _, digest = _inputs.pinned("proofs.db")
    with sqlite3.connect(f"file:{path}?mode=ro", uri=True) as connection:
        connection.row_factory = sqlite3.Row
        found = connection.execute("select * from log where id=?", (args.row,)).fetchone()
        if found is None:
            raise ValueError("missing database record")
        row = dict(found)
    if row["depth"] != 0 or row["name"] != "S0" or row["reason"] != "d2":
        raise ValueError("not a supported closed forward sphere seed")
    if row["stem"] != row["t"] - row["s"]:
        raise ValueError("inconsistent stem and internal degree")
    equation = (row["s"], row["t"], row["r"], indices(row["x"]), indices(row["dx"]))
    backend = BACKENDS.get(equation)
    if backend is None:
        raise ValueError("no proved actual-sphere backend for this equation")
    def vector(values):
        return "[" + ", ".join(map(str, values)) + "]"
    literal = (f'⟨{row["id"]}, "d2", {row["s"]}, {row["t"]}, {row["r"]}, '
               f'{vector(equation[3])}, {vector(equation[4])}⟩')
    lean = f'''import KIP126.Interface.Solution.LinProgram.Differentials.VanishingD2
import KIP126.Interface.Solution.LinProgram.AdamsOneLine.H4

-- Generated actual-object statement. Explicit literature/presentation inputs
-- and the fixed Def model's existing foundational proof debt are retained.
namespace Replay{row["id"]}

def rawRow : KIP126.Computation.LinProofs.DifferentialRow := {literal}

set_option maxHeartbeats 2000000 in
theorem replay (literature : KIP126.Challenge2.LiteratureInterface)
    (P : KIP126.Classical.Adams.LinE2Presentation) :
    KIP126.Challenge2.DifferentialStatement P rawRow := by
  exact KIP126.Interface.Solution.LinProgram.{backend} literature P

#print axioms replay

end Replay{row["id"]}
'''
    report = {
        "status": "actual-object-proof-source-generated",
        "lean_checked": False,
        "db_derivation_replayed": False,
        "route": "literature_one_line" if backend == "row5434" else "literature_vanishing_line",
        "row": row,
        "proofs_db_sha256": digest,
        "backend": f"KIP126.Interface.Solution.LinProgram.{backend}",
        "explicit_inputs": ["LiteratureInterface", "LinE2Presentation"],
        "limitations": [
            "The fixed Def model still inherits its existing sorryAx",
            "This instantiates a proved producer, not the original secondary d2 derivation",
            "No other database equation is certified by this backend",
        ],
        "generation_s": time.perf_counter() - started,
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "GeneratedReplay.lean").write_text(lean_module(lean))
    (args.output_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"backend": backend, "generation_s": report["generation_s"],
                      "lean_checked": False}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, sqlite3.Error) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        raise SystemExit(2)
