#!/usr/bin/env python3
"""Check the external provenance manifest and its mathematical interface coverage.

This validates metadata, field coverage, local artifacts and declared review
status. It cannot verify that a cited source proves the mathematical statement.
After `lake build KIP126`, use --lean-check FILE and `lake env lean FILE`
to check the actual declarations, defining modules, and structure fields.
"""
from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path

try:
    from .check_source_inventory import strip_unescaped_percent_comments, validate_inventory
except ImportError:
    from check_source_inventory import strip_unescaped_percent_comments, validate_inventory


ROUTE_STATUSES = {
    "source-result": {"external-statement-unproved"},
    "model-comparison": {"comparison-obligation"},
    "internal-application": {"internal-application-obligation"},
    "internal-adapter": {"implemented-adapter", "proof-placeholder"},
}
FIELD_STATUSES = {
    "literature": "external-statement-unproved",
    "computation": "certification-obligation",
    "internal-application": "internal-application-obligation",
}
REQUIRED_STRUCTURES = {
    "KIP126.Challenge2.LiteratureResults",
    "KIP126.Challenge2.ComputationResults",
}
COMPUTATION_RESULTS = "KIP126.Challenge2.ComputationResults"
COMPUTATION_BINDINGS = "KIP126.Challenge2.ComputationBindings"
COMPUTATION_MODULE = "KIP126/Interface/Challenge/Computation/Delivery.lean"
CERTIFICATION_MODULE = "KIP126/LinProgram/Interpretation/Route/Certification.lean"
PRESENTATION_MODULE = "KIP126/Interface/Challenge/Computation/Presentation.lean"


def computation_structure_contracts():
    """The selected computation tree, including data fields excluded as claims."""
    return {
        COMPUTATION_RESULTS: (COMPUTATION_MODULE, {
            "sphereBasis", "sphereMultiplicative", "sphereStaircase", "sphereSquare",
            "sphereTable_sound", "route", "route_presentation",
        }),
        COMPUTATION_BINDINGS: (COMPUTATION_MODULE, {
            "presentation", "routeRealization", "tmfCoordinates", "tmfMultiplicative",
            "tmf_v2Sixteen", "tmf_betaGFour",
        }),
        "KIP126.Challenge2.SphereBasisInterface": (COMPUTATION_MODULE, {"coordinates", "csv_values"}),
        "KIP126.Challenge2.SphereStaircaseInterface": (COMPUTATION_MODULE, {"rows_sound"}),
        "KIP126.Challenge2.SphereSquareInterface": (COMPUTATION_MODULE, {
            "nonzero", "exhaustive", "standard_class",
        }),
        "KIP126.Computation.Route.CertifiedRealization": (CERTIFICATION_MODULE, {
            "basis", "csv", "products", "labels", "results", "bottom", "top",
        }),
        "KIP126.Computation.Route.LabelsCorrect": (CERTIFICATION_MODULE, {
            "h0", "h1", "h2", "h4", "h5", "h6", "h0_square", "h5_square",
            "h6_square", "x_126_8_4", "x_126_8", "x_124_8", "x_109_12",
            "g", "delta_h_1_mul_g",
        }),
        "KIP126.Classical.Adams.LinE2Presentation": (PRESENTATION_MODULE, {
            "comparison", "product", "comparison_mul",
        }),
    }


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module_name(root, value):
    path = Path(value)
    require(not path.is_absolute() and ".." not in path.parts, f"unsafe module: {value}")
    require(path.suffix == ".lean" and (root / path).is_file(), f"missing module: {value}")
    require((root / path).resolve().is_relative_to(root.resolve()), f"module escapes checkout: {value}")
    return path.with_suffix("").as_posix().replace("/", ".")


def declaration_name(name):
    require(isinstance(name, str) and re.fullmatch(r"KIP126(?:\.[^\s`(),;\[\]{}\"]+)+", name),
            f"invalid declaration name: {name!r}")


def without_comments(text):
    """Remove nested Lean block/line comments without joining source lines."""
    result, index, depth, string = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                index += 2
                continue
            result.append("\n" if char == "\n" else " ")
        elif string:
            result.append(char)
            if char == "\\" and index + 1 < len(text):
                index += 1
                result.append(text[index])
            elif char == '"':
                string = False
        elif pair == "/-":
            depth = 1
            index += 2
            continue
        elif pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
            continue
        else:
            string = char == '"'
            result.append(char)
        index += 1
    require(depth == 0, "unclosed Lean comment")
    return "".join(result)


def structure_fields(text, name):
    """Fast source check; --lean-check also checks kernel environment metadata."""
    clean = without_comments(text)
    short = name.rsplit(".", 1)[-1]
    matches = list(re.finditer(r"^structure " + re.escape(short) + r"\b", clean, re.M))
    require(len(matches) == 1, f"expected one structure declaration for {name}, found {len(matches)}")
    remaining = clean[matches[0].end():]
    header = re.search(r"\bwhere[ \t]*\n", remaining)
    require(header is not None, f"missing structure body for {name}")
    body = remaining[header.end():]
    boundary = re.search(r"^\S", body, re.M)
    if boundary:
        body = body[:boundary.start()]
    fields = re.findall(r"^  ([^\s:(){}]+)(?=\s*(?:[:({]))", body, re.M)
    require(len(fields) == len(set(fields)) and fields, f"invalid fields for {name}")
    return set(fields)


def computation_statements(root):
    """Expand only the selected certificate wrappers, never arbitrary data."""
    actual = {}
    for name, (module, expected) in computation_structure_contracts().items():
        actual[name] = structure_fields((root / module).read_text(), name)
        require(actual[name] == expected, f"computation structure field drift: {name}")

    def projection(owner, field, module):
        return {"declaration": owner + "." + field, "module": module}

    wrappers = {
        "sphereBasis": "KIP126.Challenge2.SphereBasisInterface",
        "sphereStaircase": "KIP126.Challenge2.SphereStaircaseInterface",
        "sphereSquare": "KIP126.Challenge2.SphereSquareInterface",
    }
    results = {}
    for field in sorted(actual[COMPUTATION_RESULTS]):
        if field in wrappers:
            owner = wrappers[field]
            fields = actual[owner] - ({"coordinates"} if field == "sphereBasis" else set())
            results[field] = {
                leaf: projection(owner, leaf, COMPUTATION_MODULE) for leaf in sorted(fields)
            }
        elif field == "route":
            owner = "KIP126.Computation.Route.CertifiedRealization"
            label_owner = "KIP126.Computation.Route.LabelsCorrect"
            results[field] = {
                leaf: projection(owner, leaf, CERTIFICATION_MODULE)
                for leaf in sorted(actual[owner] - {"labels"})
            }
            results[field].update({
                "labels." + leaf: projection(label_owner, leaf, CERTIFICATION_MODULE)
                for leaf in sorted(actual[label_owner])
            })
        else:
            results[field] = {"": projection(COMPUTATION_RESULTS, field, COMPUTATION_MODULE)}
    bindings = {
        "presentation.comparison_mul": projection(
            "KIP126.Classical.Adams.LinE2Presentation", "comparison_mul", PRESENTATION_MODULE),
        **{
            field: projection(COMPUTATION_BINDINGS, field, COMPUTATION_MODULE)
            for field in ("tmfMultiplicative", "tmf_v2Sixteen", "tmf_betaGFour")
        },
    }
    require(sum(len(leaves) for leaves in results.values()) == 29,
            "computation statement count drift")
    return results, bindings


def validate_computation_coverage(root, document, labels, nodes, used_labels, reference):
    """Bind each computation conclusion and comparison to its actual projection."""
    expected, expected_bindings = computation_statements(root)
    item = next(c for c in document["interface_coverage"] if c["structure"] == COMPUTATION_RESULTS)
    leaves = {row["declaration"] for rows in expected.values() for row in rows.values()}
    leaves.update(row["declaration"] for row in expected_bindings.values())
    used_labels = set(used_labels)
    used_nodes = {id(nodes[label]) for label in used_labels}
    declarations = {
        (name, module_name(root, module))
        for name, (module, _) in computation_structure_contracts().items()
    }

    def node_link(row, specification, parent, where, binding=False):
        require(isinstance(row, dict), f"invalid computation statement: {where}")
        declaration_name(row.get("declaration"))
        require(row["declaration"] == specification["declaration"],
                f"wrong computation leaf declaration: {where}")
        require(row.get("module") == specification["module"],
                f"wrong computation leaf module: {where}")
        owner = module_name(root, row["module"])
        canonical = row.get("blueprint_labels")
        require(isinstance(canonical, list) and len(canonical) == 1,
                f"expected one individual computation Blueprint node: {where}")
        label = canonical[0]
        require(label in labels, f"unknown computation Blueprint label: {where}")
        require(label in nodes, f"computation coverage is not a mathematical node: {label}")
        require(label not in used_labels and id(nodes[label]) not in used_nodes,
                f"Blueprint computation node reused: {label}")
        used_labels.add(label)
        used_nodes.add(id(nodes[label]))
        links = nodes[label]
        require(parent in links, f"missing direct Blueprint computation parent link: {where}")
        require(row["declaration"] in links,
                f"missing direct Blueprint computation leaf link: {where}")
        root_name = COMPUTATION_BINDINGS if binding else COMPUTATION_RESULTS
        require({name for name in links if name.startswith(root_name + ".")} == {parent},
                f"wrong Blueprint computation root link: {where}")
        if binding:
            require(not any(name.startswith(COMPUTATION_RESULTS + ".") for name in links),
                    f"wrong Blueprint computation root link: {where}")
        require(links & leaves == {row["declaration"]},
                f"Blueprint node combines computation leaves: {label}")
        declarations.add((row["declaration"], owner))
        return label

    for field, specification in expected.items():
        row = item["fields"][field]
        statements = row.get("statements")
        require(isinstance(statements, dict), f"missing computation statements: {field}")
        require(set(statements) == set(specification),
                f"computation statement coverage drift: {field}")
        union = []
        for relative, leaf in statements.items():
            require(isinstance(leaf, dict) and set(leaf) == {
                "declaration", "module", "blueprint_labels",
            }, f"unexpected computation statement metadata: {field}.{relative}")
            label = node_link(leaf, specification[relative],
                              COMPUTATION_RESULTS + "." + field, field + "." + relative)
            if label not in union:
                union.append(label)
        require(row["blueprint_labels"] == union,
                f"computation parent Blueprint label union drift: {field}")

    bindings = document.get("computation_binding_statements")
    require(isinstance(bindings, dict) and set(bindings) == set(expected_bindings),
            "computation binding statement coverage drift")
    for relative, row in bindings.items():
        require(isinstance(row, dict) and set(row) == {
            "declaration", "module", "blueprint_labels", "sources", "locator", "proof_status",
        }, f"unexpected computation binding metadata: {relative}")
        reference(row, relative)
        allowed_sources = {"lwx_machine"}
        if relative in {"tmf_v2Sixteen", "tmf_betaGFour"}:
            allowed_sources.add("br21")
        require(set(row["sources"]) <= allowed_sources,
                f"wrong computation binding source: {relative}")
        require(row["proof_status"] == "comparison-obligation",
                f"computation binding role/status mismatch: {relative}")
        parent = COMPUTATION_BINDINGS + "." + relative.split(".")[0]
        node_link(row, expected_bindings[relative], parent, relative, binding=True)
    return declarations


def blueprint_text(root):
    """Expand the active, validated Blueprint source without executing TeX."""
    directory = (root / "blueprint/src").resolve()
    visited, active = set(), []
    environments = r"theorem|proposition|lemma|corollary|definition"
    input_pattern = re.compile(r"\\input\b\s*\{([^}]+)\}")

    def source_text(path):
        text = strip_unescaped_percent_comments(path.read_text())
        require(not re.search(
            r"\\(?:verb|lstinline|mintinline)\b|"
            r"\\begin\s*\{(?:verbatim\*?|comment|lstlisting|minted)\}", text),
            f"unsupported Blueprint verbatim construct: {path}")

        # external_results.tex has a node-free fallback preamble for its
        # standalone editor build. No mathematical coverage can depend on it.
        def standalone_preamble(match):
            body = match[1]
            require(not re.search(
                r"\\(?:label|input|include)\b|\\lean\s*\{|"
                r"\\begin\s*\{(?:" + environments + r")\}|\\if[A-Za-z@]*\b", body),
                f"unsupported Blueprint conditional coverage: {path}")
            return "\n" * match[0].count("\n")

        text = re.sub(r"\\ifdefined\s*\\chapter\b(.*?)\\fi\b",
                      standalone_preamble, text, flags=re.S)
        require(not re.search(r"\\(?:if[A-Za-z@]*|else|fi)\b", text),
                f"unsupported Blueprint conditional: {path}")
        require(not re.search(r"\\include\b", text),
                f"unsupported Blueprint include; use braced input: {path}")
        require(len(re.findall(r"\\input\b", text)) == len(input_pattern.findall(text)),
                f"unsupported Blueprint input; use braced input: {path}")
        return text

    def expand(path):
        path = path.resolve()
        require(path.is_relative_to(directory), f"Blueprint input escapes source tree: {path}")
        require(path.is_file(), f"missing Blueprint input: {path}")
        require(path not in active, f"cyclic Blueprint input: {path}")
        require(path not in visited, f"repeated Blueprint input: {path}")
        visited.add(path)
        active.append(path)
        try:
            text = source_text(path)

            def input_text(match):
                name = match[1]
                relative = Path(name)
                require(not relative.is_absolute() and ".." not in relative.parts,
                        f"unsafe Blueprint input: {name}")
                if not relative.suffix:
                    relative = relative.with_suffix(".tex")
                return "\n" + expand(directory / relative) + "\n"

            return input_pattern.sub(input_text, text)
        finally:
            active.pop()

    return expand(directory / "content.tex")


def blueprint_nodes(root):
    """Read active Blueprint inputs and their mathematical declaration links."""
    text = blueprint_text(root)
    environments = r"theorem|proposition|lemma|corollary|definition"
    labels, nodes, stack = set(), {}, []
    tokens = re.compile(
        r"\\(?:(begin|end)\s*\{(" + environments + r")\}|"
        r"label\s*\{([^}]+)\}|lean\s*\{([^}]+)\})")
    for match in tokens.finditer(text):
        command, environment, label, declarations = match.groups()
        if command == "begin":
            stack.append({"environment": environment, "labels": [], "declarations": set()})
        elif command == "end":
            require(stack and stack[-1]["environment"] == environment,
                    f"unbalanced Blueprint mathematical environment: {environment}")
            node = stack.pop()
            for alias in node["labels"]:
                nodes[alias] = node["declarations"]
        elif label is not None:
            require(label not in labels, f"duplicate active Blueprint label: {label}")
            labels.add(label)
            if stack:
                stack[-1]["labels"].append(label)
        elif stack:
            stack[-1]["declarations"].update(
                name.strip() for name in declarations.split(",") if name.strip())
    require(not stack, "unclosed Blueprint mathematical environment")
    return labels, nodes


def validate_document(root, document):
    require(document["schema_version"] == 3, "unsupported external manifest schema")
    sources = {s["id"]: s for s in document["sources"]}
    require(len(sources) == len(document["sources"]), "duplicate source ID")
    artifacts = {a["path"] for s in sources.values() for a in s["artifacts"]}
    for source in sources.values():
        require(set(source.get("members", [])) <= sources.keys(), f"unknown source-group member: {source['id']}")
        require(set(source.get("route_review", {}).get("artifact_paths", [])) <= artifacts,
                f"unregistered review artifact: {source['id']}")

    def reference(row, where):
        require(row.get("sources") and set(row["sources"]) <= sources.keys(), f"unknown/missing source: {where}")
        require(isinstance(row.get("locator"), str) and row["locator"].strip(), f"missing locator: {where}")

    route = document["route"]
    claims = route["claims"]
    data = (root / "KIP126/Interface/Challenge/Challenge2.lean").read_text()
    require(structure_fields(data, "KIP126.Challenge2") == {"literature", "computation"},
            "Challenge2 root field drift")
    for path, name in (
        ("KIP126/Interface/Challenge/Literature/Delivery.lean", "KIP126.Challenge2.LiteratureInterface"),
        ("KIP126/Interface/Challenge/Computation/Delivery.lean", "KIP126.Challenge2.ComputationInterface"),
    ):
        require(structure_fields((root / path).read_text(), name) == {"bindings", "results"},
                f"delivery field drift: {name}")
    consumer_fields = structure_fields(
        (root / "KIP126/Interface/Solution/Literature/Applications.lean").read_text(),
        "KIP126.Literature.Route.Inputs")
    require({c["input_field"] for c in claims} == consumer_fields, "route consumer field coverage drift")
    paper_labels = set(re.findall(r"\\label\{([^}]+)\}", strip_unescaped_percent_comments(
        (root / "MainPaper/main.tex").read_text())))
    for claim in claims:
        reference(claim, claim["id"])
        require("aim_paper" not in claim["sources"], "MainPaper consumption is not a proof of an external result")
        require(claim["kind"] and claim["lwx_consumers"], f"missing consumer locator: {claim['id']}")
        require(set(claim["lwx_consumers"]) <= paper_labels, f"unknown paper label: {claim['id']}")
    entries = sum((route[k] for k in ("claims", "model_bindings", "delivery_packages",
                  "internal_adapters", "source_producers")), [])
    require(len({e["id"] for e in entries}) == len(entries), "duplicate route audit ID")
    declarations = set()
    for entry in entries:
        require(entry["proof_status"] in ROUTE_STATUSES.get(entry["role"], set()), f"role/status mismatch: {entry['id']}")
        if "sources" in entry:
            require(set(entry["sources"]) <= sources.keys(), f"unknown source: {entry['id']}")
        module = module_name(root, entry["module"])
        require(entry["declarations"], f"empty declaration group: {entry['id']}")
        modules = entry.get("declaration_modules", {})
        require(set(modules) <= set(entry["declarations"]), f"unknown declaration owner: {entry['id']}")
        for name in entry["declarations"]:
            declaration_name(name)
            owner = module_name(root, modules[name]) if name in modules else module
            declarations.add((name, owner))
    require(all(e["role"] == "model-comparison" for e in route["model_bindings"]), "model role drift")
    require(all(e["role"] == "internal-adapter" for e in route["internal_adapters"]), "adapter role drift")
    for evidence in route["csv_evidence"]:
        source = sources[evidence["source"]]
        require(evidence["path"] in {a["path"] for a in source["artifacts"]}, "unregistered CSV artifact")
        with (root / evidence["path"]).open(newline="") as handle:
            selected = [{"line": line, "row": row} for line, row in enumerate(csv.DictReader(handle), 2)
                        if all(row[key] == value for key, value in evidence["selector"].items())]
        require(selected == evidence["expected"], f"primary CSV evidence changed: {evidence['id']}")
    blueprint_labels, nodes = blueprint_nodes(root)
    literature_nodes = set()
    coverage = document["interface_coverage"]
    require({c["structure"] for c in coverage} == REQUIRED_STRUCTURES, "interface coverage structure set drift")
    require(len(coverage) == len(REQUIRED_STRUCTURES), "duplicate interface coverage structure")
    for item in coverage:
        name = item["structure"]
        expected_role = {
            "KIP126.Challenge2.ComputationResults": "computation",
        }.get(name, "literature")
        require(item["role"] == expected_role, f"structure role mismatch: {name}")
        declaration_name(name)
        module = module_name(root, item["module"])
        actual = structure_fields((root / item["module"]).read_text(), name)
        require(set(item["fields"]) == actual,
                f"field coverage drift: {name}: missing={actual-set(item['fields'])}, extra={set(item['fields'])-actual}")
        declarations.add((name, module))
        for field, row in item["fields"].items():
            reference(row, f"{name}.{field}")
            require(row["proof_status"] == FIELD_STATUSES[item["role"]], f"field role/status mismatch: {name}.{field}")
            require(set(row["blueprint_labels"]) <= blueprint_labels, f"unknown Blueprint label: {name}.{field}")
            if item["role"] == "literature":
                require(len(row["blueprint_labels"]) == 1,
                        f"expected one individual Blueprint node: {name}.{field}")
                label = row["blueprint_labels"][0]
                require(label not in literature_nodes, f"Blueprint literature node reused: {label}")
                literature_nodes.add(label)
                require(label in nodes, f"Blueprint coverage is not a mathematical node: {label}")
                require(name + "." + field in nodes[label],
                        f"missing direct Blueprint field link: {name}.{field} at {label}")
                field_links = {n for n in nodes[label] if n.startswith(name + ".")}
                require(field_links == {name + "." + field},
                        f"Blueprint node combines literature fields: {label}")
            declarations.add((name + "." + field, module))
    declarations.update(validate_computation_coverage(
        root, document, blueprint_labels, nodes, literature_nodes, reference))
    for row in document["declaration_sources"]:
        reference(row, row["declaration"])
        require(row["status"] == "statement-or-data-only", f"invalid declaration review status: {row['declaration']}")
        declaration_name(row["declaration"])
        declarations.add((row["declaration"], module_name(root, row["module"])))
    return declarations


def lean_check(document, declarations):
    modules = sorted({module for _, module in declarations})
    pairs = ",\n    ".join(f"(`{name}, `{module})" for name, module in sorted(declarations))
    checks = "".join(f"import {module}\n" for module in modules)
    checks += "import Lean.Elab.Command\nimport Lean.Meta.Basic\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n"
    checks += f"  for (n, expected) in [{pairs}] do\n"
    checks += '    unless env.contains n do throwError "missing provenance declaration: {n}"\n'
    checks += '    let some idx := env.getModuleIdxFor? n | throwError "no defining module: {n}"\n'
    checks += '    unless env.header.moduleNames[idx.toNat]! == expected do\n'
    checks += '      throwError "wrong provenance module for {n}: expected {expected}, got {env.header.moduleNames[idx.toNat]!}"\n'
    for item in document["interface_coverage"]:
        expected = ", ".join("`" + field for field in sorted(item["fields"]))
        checks += f"  let actual := getStructureFields env `{item['structure']}\n"
        checks += f"  let expected : Array Name := #[{expected}]\n"
        checks += '  unless actual.size == expected.size && actual.all (expected.contains ·) do\n'
        checks += f'    throwError "structure field coverage drift: {item["structure"]}: {{actual}}"\n'
        if item["role"] == "literature":
            checks += f"  for field in getStructureFields env `{item['structure']} do\n"
            checks += f"    let name := `{item['structure']} ++ field\n"
            checks += '    let some info := env.find? name | throwError "missing literature field: {name}"\n'
            checks += '    unless ← liftTermElabM (Lean.Meta.isProp info.type) do\n'
            checks += '      throwError "literature results field is data rather than a proposition: {name}"\n'
    for name, (_, fields) in computation_structure_contracts().items():
        expected = ", ".join("`" + field for field in sorted(fields))
        checks += f"  let actual := getStructureFields env `{name}\n"
        checks += f"  let expected : Array Name := #[{expected}]\n"
        checks += '  unless actual.size == expected.size && actual.all (expected.contains ·) do\n'
        checks += f'    throwError "computation structure field drift: {name}: {{actual}}"\n'
    wrapper_types = (
        (COMPUTATION_RESULTS + ".sphereBasis", "KIP126.Challenge2.SphereBasisInterface"),
        (COMPUTATION_RESULTS + ".sphereStaircase", "KIP126.Challenge2.SphereStaircaseInterface"),
        (COMPUTATION_RESULTS + ".sphereSquare", "KIP126.Challenge2.SphereSquareInterface"),
        (COMPUTATION_RESULTS + ".route", "KIP126.Computation.Route.CertifiedRealization"),
        ("KIP126.Computation.Route.CertifiedRealization.labels", "KIP126.Computation.Route.LabelsCorrect"),
        (COMPUTATION_BINDINGS + ".presentation", "KIP126.Classical.Adams.LinE2Presentation"),
    )
    pairs = ", ".join(f"(`{projection}, `{target})" for projection, target in wrapper_types)
    checks += f"  for (name, expected) in [{pairs}] do\n"
    checks += '    let some info := env.find? name | throwError "missing computation wrapper: {name}"\n'
    checks += '    unless ← liftTermElabM (Lean.Meta.forallTelescopeReducing info.type fun _ type =>\n'
    checks += '      pure (type.getAppFn.constName? == some expected)) do\n'
    checks += '      throwError "wrong computation wrapper type: {name}, expected {expected}"\n'
    computation = next(c for c in document["interface_coverage"] if c["structure"] == COMPUTATION_RESULTS)
    leaves = [leaf["declaration"] for row in computation["fields"].values()
              for leaf in row["statements"].values()]
    leaves.extend(row["declaration"] for row in document["computation_binding_statements"].values())
    expected = ", ".join("`" + name for name in leaves)
    checks += f"  for name in #[{expected}] do\n"
    checks += '    let some info := env.find? name | throwError "missing computation leaf: {name}"\n'
    checks += '    unless ← liftTermElabM (Lean.Meta.isProp info.type) do\n'
    checks += '      throwError "computation statement is data rather than a proposition: {name}"\n'
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-check", type=Path, help="emit declaration/module/field checks for lake env lean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    errors = validate_inventory(root)
    require(not errors, "\n".join(errors))
    document = json.loads((root / "docs/external-inputs.json").read_text())
    declarations = validate_document(root, document)
    if args.lean_check:
        args.lean_check.write_text(lean_check(document, declarations))
    fields = sum(len(c["fields"]) for c in document["interface_coverage"])
    computation = next(c for c in document["interface_coverage"] if c["role"] == "computation")
    statements = sum(len(row["statements"]) for row in computation["fields"].values())
    print(f"External inputs: {len(document['sources'])} sources, {fields} interface fields, "
          f"{statements} computation statements, {len(document['computation_binding_statements'])} computation comparisons, "
          f"{len(document['route']['claims'])} route audit groups, {len(declarations)} declaration/module pairs.")
    print("Sources, artifacts, locators, field coverage and declared statuses checked; mathematical truth and source fidelity remain review obligations.")


if __name__ == "__main__":
    main()
