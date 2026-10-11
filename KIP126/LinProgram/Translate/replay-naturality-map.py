#!/usr/bin/env python3
"""Extract two fixed Ceta__S0 word certificates and render their Lean inputs.

The input tables are authenticated with the existing manifest/LFS loader.
This checks coordinate transcription and formal generator substitution only.
It neither reconstructs a historical premise edge nor proves a differential,
quotient descent, resolution exactness, or an actual spectrum-map comparison.
"""
import argparse
import importlib.util
import json
from pathlib import Path

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / "KIP126/LinProgram"
DEFAULT_OUTPUT = LIN / "Generated/Naturality"
STEM = "Row245131Map"
INPUTS = ("proofs.db", "S0_AdamsSS_t261.db", "Ceta_AdamsSS_t200.db",
          "map_AdamsSS_Ceta_to_S0_t200.db", "ss.json")


def load_native():
    spec = importlib.util.spec_from_file_location(
        "lin_native_contract", LIN / "Translate/native-contract.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def basis_record(row):
    return {"id": row["id"], "s": row["s"], "t": row["t"],
            "local_index": row["local_index"], "code": row["mon"]}


def rebuild():
    native = load_native()
    lowstem = native.load_lowstem()
    manifest = json.loads((LIN / "Raw/manifest.json").read_text())
    native.validate_ceta_archive_origin(manifest)
    paths, identities = {}, []
    for name in INPUTS:
        path, data, digest = lowstem.pinned(name)
        paths[name] = path
        identities.append({"path": "KIP126/LinProgram/Raw/" + name,
                           "size": len(data), "sha256": digest})
        if name == "ss.json":
            config = json.loads(data)
    with native.connect(paths["proofs.db"]) as logs, \
            native.connect(paths["S0_AdamsSS_t261.db"]) as sphere, \
            native.connect(paths["Ceta_AdamsSS_t200.db"]) as ceta, \
            native.connect(paths["map_AdamsSS_Ceta_to_S0_t200.db"]) as maps:
        source = native.raw_row(logs, 245130)
        target = native.raw_row(logs, 245131)
        mappings = [m for m in config["maps"] if m["name"] == target["info"]]
        native.require(len(mappings) == 1, "missing or ambiguous native map")
        mapping = mappings[0]
        sliced = native.native_ceta_map_slice(
            ceta, maps, sphere, source, target, mapping, lowstem)

    images = {row["id"]: row["map"] for row in sliced["generator_images"]}
    certificates = []
    for side in ("source", "target"):
        part = sliced["degree_slices"][side]
        # This initial format certifies a single native module word. Reject
        # unsupported inputs rather than dropping terms or inventing zeros.
        native.require(len(part["source_basis"]) == len(part["target_basis"]) == 1,
                       "this replay requires singleton recorded degree slices")
        native.require(part["source_log_coordinates"] == part["mapped_coordinates"] == [0],
                       "this replay requires the selected singleton coordinates")
        a, b = part["source_basis"][0], part["target_basis"][0]
        generator = int(a["mon"].split(",")[-1])
        certificates.append({"source": basis_record(a), "target": basis_record(b),
                             "generator_id": generator, "image_code": images[generator],
                             "witness": []})
    return {
        "schema_version": 1,
        "kind": "fixed-native-module-word-map-certificate",
        "scope": "Two word evaluations in the unchanged sphere data quotient; not a certified quotient map or actual Adams differential.",
        "canonical_registry": "docs/external-inputs.json",
        "inputs": identities,
        "source_candidate_log": source,
        "target_log": target,
        "historical_premise_edge_certified": False,
        "native_map": mapping,
        "native_slice": sliced,
        "certificates": certificates,
        "remaining_obligations": [
            "Certify all 76569 original Ceta relations under the full 887-generator native graph before asserting its quotient descent.",
            "Identify the fixed native Ceta and sphere representatives with actual E2 classes on the same model and presentation.",
            "Construct and certify the native resolution map lifting the contravariant cohomology map of the actual top-cell projection.",
            "Prove the native-to-actual comparisons commute with that map, including the two suspension identifications.",
            "Prove the actual source differential from (2,19)[0] to (5,21)[0]; neither the D tag nor the final staircase is its proof.",
            "Retain the existing unfinished fixed-model foundations; no total computation delivery is used as input.",
        ],
        "actual_certification": False,
    }


def validate_certificate(candidate, expected):
    # Authenticate the complete native claim, not only its computed output.
    # This prevents a different true word equality from silently changing
    # the selected goal or its declared proof boundary.
    if candidate != expected:
        raise ValueError("certificate differs from reconstruction of pinned inputs")


def render_json(bundle):
    return json.dumps(bundle, ensure_ascii=False, indent=2) + "\n"


@module_output
def render_lean(bundle):
    def basis(row):
        return "⟨" + ", ".join(str(row[k]) for k in ("id", "s", "t", "local_index")) + ", " + json.dumps(row["code"]) + "⟩"

    lines = [
        "import KIP126.LinProgram.Certificates.Naturality.MapCertificate",
        "",
        "/-! Generated from authenticated v126.3.cw49 tables by",
        "Translate/replay-naturality-map.py. These are certificate inputs, not proofs.",
        "Raw IDs identify table rows; localIndex identifies the recorded degree slice.",
        "Source basis transcription is checked by the exporter, not a basis theorem. -/",
        "namespace KIP126.LinModule.RawData.Naturality245131",
        "open KIP126.LinModule.NaturalityMapCertificate",
        "",
    ]
    for name, cert in zip(("sourceCertificate", "targetCertificate"), bundle["certificates"]):
        if cert["witness"]:
            raise ValueError("this direct-word replay expects an empty relation witness")
        lines.extend([
            f"def {name} : Certificate where",
            f"  source := {basis(cert['source'])}",
            f"  target := {basis(cert['target'])}",
            f"  generatorId := {cert['generator_id']}",
            f"  imageCode := {json.dumps(cert['image_code'])}",
            "  witness := []",
            "",
        ])
    lines.append("end KIP126.LinModule.RawData.Naturality245131")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--certificate", type=Path,
                        help="validate a supplied JSON certificate against pinned inputs before Lean translation")
    parser.add_argument("--check", action="store_true", help="check both committed outputs without changing files")
    args = parser.parse_args()
    expected = rebuild()
    bundle = json.loads(args.certificate.read_text()) if args.certificate else expected
    validate_certificate(bundle, expected)
    outputs = {STEM + ".json": render_json(bundle), STEM + ".lean": render_lean(bundle)}
    if args.check:
        for name, contents in outputs.items():
            if (args.output_dir / name).read_text() != contents:
                raise ValueError(f"generated file differs from pinned reconstruction: {name}")
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for name, contents in outputs.items():
            (args.output_dir / name).write_text(contents)
    print("Two native map certificate inputs " + ("checked" if args.check else "generated") +
          "; Lean verification is separate; actual certification remains false.")


if __name__ == "__main__":
    main()
