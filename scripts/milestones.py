#!/usr/bin/env python3
"""Validate milestone metadata and derive a scheduling view, never proof status.

Full-file hashes conservatively detect changes since a recorded human review.
They do not compare elaborated Lean types, authenticate reviewers, or certify
proofs. Ordinary validation allows stale reviews and unfinished proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit

try:
    from .check_external_inputs import blueprint_nodes, declaration_name
except ImportError:
    from check_external_inputs import blueprint_nodes, declaration_name


CATALOG = "docs/milestones.json"
MANIFEST = "docs/external-inputs.json"
COMMON_FILES = ("lean-toolchain", "lake-manifest.json", "PROJECT_BOUNDARY.md", MANIFEST)
LANES = {"foundations", "tools", "literature", "computation", "prop78", "prop79", "integration"}
ENTRY_FIELDS = {
    "id", "title", "lane", "goal", "lean_declarations", "blueprint_labels",
    "dependencies", "definition_files", "source_refs", "write_scope", "owner",
    "statement_status", "proof_status", "review", "proof_evidence",
    "review_blockers", "acceptance", "notes",
}
REVIEW_FIELDS = {"commit", "record", "reviewers", "source_hashes", "dependency_reviews", "contract_hash"}
EVIDENCE_FIELDS = {"commit", "record", "checks", "axioms"}
CONTRACT_FIELDS = ("id", "goal", "lean_declarations", "blueprint_labels", "dependencies",
                   "definition_files", "source_refs", "acceptance")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, expected, context):
    require(isinstance(value, dict), f"{context}: expected an object")
    require(set(value) == expected,
            f"{context}: missing fields {sorted(expected - set(value))}; "
            f"unknown fields {sorted(set(value) - expected)}")


def nonempty(value, context):
    require(isinstance(value, str) and bool(value.strip()), f"{context}: expected a nonempty string")


def strings(value, context, *, allow_empty=True, allow_empty_strings=False):
    require(isinstance(value, list), f"{context}: expected a list")
    require(allow_empty or bool(value), f"{context}: must not be empty")
    for item in value:
        if allow_empty_strings:
            require(isinstance(item, str), f"{context}: expected strings")
        else:
            nonempty(item, context)
    require(len(value) == len(set(value)), f"{context}: duplicate entries")


def hex_string(value, length, context):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{" + str(length) + "}", value),
            f"{context}: expected {length} lowercase hexadecimal characters")


def relative_path(value, *, directory_allowed=False):
    """Validate a path spelling without opening a possibly historical file."""
    nonempty(value, "path")
    require("\\" not in value and "\0" not in value, f"unsafe path: {value!r}")
    relative = PurePosixPath(value)
    require(not relative.is_absolute() and ".." not in relative.parts and "." not in value.split("/"),
            f"unsafe path: {value}")
    normalized = relative.as_posix()
    require(value == normalized or (directory_allowed and value == normalized + "/"),
            f"noncanonical path: {value}")
    return normalized


def checked_path(root, value, *, directory_allowed=False):
    path = root / relative_path(value, directory_allowed=directory_allowed)
    require(path.resolve().is_relative_to(root.resolve()), f"path escapes checkout: {value}")
    require(path.is_file() or (directory_allowed and path.is_dir()), f"missing path: {value}")
    require(not value.endswith("/") or path.is_dir(), f"directory prefix names a file: {value}")
    return path


def record_reference(root, value, context, *, pull_request=False):
    nonempty(value, context)
    if "://" not in value:
        checked_path(root, value)
        return
    url = urlsplit(value)
    require(url.scheme == "https" and bool(url.hostname) and not url.username and not url.password,
            f"{context}: expected an HTTPS URL without credentials")
    if pull_request:
        require(re.search(r"/(?:pull|pulls)/[1-9][0-9]*(?:/|$)", url.path),
                f"{context}: expected a pull-request URL or an existing local record")


def resolve_pointer(document, pointer):
    require(isinstance(pointer, str), f"invalid JSON Pointer: {pointer!r}")
    if pointer == "":
        return document
    require(pointer.startswith("/") and not re.search(r"~(?![01])", pointer),
            f"invalid JSON Pointer: {pointer!r}")
    value = document
    for token in pointer[1:].split("/"):
        key = token.replace("~1", "/").replace("~0", "~")
        if isinstance(value, dict):
            require(key in value, f"unresolved source reference: {pointer}")
            value = value[key]
        elif isinstance(value, list):
            require(re.fullmatch(r"0|[1-9][0-9]*", key) and int(key) < len(value),
                    f"unresolved source reference: {pointer}")
            value = value[int(key)]
        else:
            raise ValueError(f"unresolved source reference: {pointer}")
    return value


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=_unique_object)


def watched_files(milestone):
    return sorted(set(COMMON_FILES) | set(milestone["definition_files"]) |
                  {item["path"] for item in milestone["lean_declarations"]})


def source_hashes(root, milestone, cache=None):
    cache = {} if cache is None else cache
    result = {}
    for name in watched_files(milestone):
        if name not in cache:
            digest = hashlib.sha256()
            with checked_path(root, name).open("rb") as source:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    digest.update(chunk)
            cache[name] = digest.hexdigest()
        result[name] = cache[name]
    return result


def review_fingerprint(review):
    """SHA-256 of compact, key-sorted, UTF-8 JSON; missing reviews have no digest."""
    if review is None:
        return None
    encoded = json.dumps(review, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def contract_fingerprint(milestone):
    """Bind the selected review target without hashing its mutable review/state."""
    return review_fingerprint({key: milestone[key] for key in CONTRACT_FIELDS})


def validate_catalog(root, document, active_labels=None):
    """Validate structure and references; stale review content is not an error."""
    root = Path(root).resolve()
    fields(document, {"schema", "baseline_commit", "milestones"}, "milestone catalog")
    require(type(document["schema"]) is int and document["schema"] == 1, "unsupported milestone schema")
    hex_string(document["baseline_commit"], 40, "baseline_commit")
    require(isinstance(document["milestones"], list) and bool(document["milestones"]),
            "milestones: expected a nonempty list")
    if active_labels is None:
        _, nodes = blueprint_nodes(root)
        active_labels = set(nodes)
    else:
        active_labels = set(active_labels)
    manifest = read_json(checked_path(root, MANIFEST))
    for name in COMMON_FILES:
        checked_path(root, name)
    entries = {}
    for item in document["milestones"]:
        fields(item, ENTRY_FIELDS, "milestone")
        mid = item["id"]
        require(isinstance(mid, str) and re.fullmatch(r"M[0-9]{2,}", mid), f"invalid milestone id: {mid!r}")
        require(mid not in entries, f"duplicate milestone id: {mid}")
        entries[mid] = item
        for key in ("title", "goal"):
            nonempty(item[key], f"{mid}.{key}")
        require(isinstance(item["lane"], str) and item["lane"] in LANES, f"{mid}: invalid lane")
        require(item["owner"] is None or isinstance(item["owner"], str), f"{mid}: invalid owner")
        if item["owner"] is not None:
            nonempty(item["owner"], f"{mid}.owner")
        require(isinstance(item["statement_status"], str) and
                item["statement_status"] in {"draft", "frozen", "reopened"}, f"{mid}: invalid statement_status")
        require(isinstance(item["proof_status"], str) and
                item["proof_status"] in {"open", "conditional", "closed"}, f"{mid}: invalid proof_status")
        for key in ("blueprint_labels", "dependencies", "definition_files", "source_refs", "write_scope",
                    "review_blockers", "acceptance", "notes"):
            strings(item[key], f"{mid}.{key}",
                    allow_empty=key not in {"blueprint_labels", "write_scope", "acceptance"},
                    allow_empty_strings=key == "source_refs")
        require(set(item["blueprint_labels"]) <= active_labels,
                f"{mid}: unknown active Blueprint labels: {sorted(set(item['blueprint_labels']) - active_labels)}")
        for pointer in item["source_refs"]:
            resolve_pointer(manifest, pointer)
        require(isinstance(item["lean_declarations"], list) and bool(item["lean_declarations"]),
                f"{mid}: lean_declarations must be a nonempty list")
        names = set()
        for declaration in item["lean_declarations"]:
            fields(declaration, {"name", "path"}, f"{mid}.lean_declarations")
            declaration_name(declaration["name"])
            require(declaration["name"] not in names, f"{mid}: duplicate Lean declaration")
            names.add(declaration["name"])
            path = checked_path(root, declaration["path"])
            require(path.suffix == ".lean", f"{mid}: declaration path must name a Lean file")
        for name in item["definition_files"]:
            checked_path(root, name)
        for name in item["write_scope"]:
            checked_path(root, name, directory_allowed=True)
        review = item["review"]
        require(item["statement_status"] != "frozen" or review is not None,
                f"{mid}: frozen statement requires a review record")
        if review is not None:
            fields(review, REVIEW_FIELDS, f"{mid}.review")
            hex_string(review["commit"], 40, f"{mid}.review.commit")
            hex_string(review["contract_hash"], 64, f"{mid}.review.contract_hash")
            record_reference(root, review["record"], f"{mid}.review.record", pull_request=True)
            strings(review["reviewers"], f"{mid}.review.reviewers", allow_empty=False)
            same_contract = review["contract_hash"] == contract_fingerprint(item)
            for key, expected in (("source_hashes", set(watched_files(item))),
                                  ("dependency_reviews", set(item["dependencies"]))):
                require(isinstance(review[key], dict), f"{mid}.review.{key}: expected an object")
                if same_contract:
                    require(set(review[key]) == expected,
                            f"{mid}.review.{key}: expected exactly {sorted(expected)}")
                elif key == "source_hashes":
                    require(set(COMMON_FILES) <= set(review[key]),
                            f"{mid}.review.source_hashes: missing common environment files")
                # An old review remains a valid historical record when the
                # contract changes. Its former paths/dependencies need not
                # still exist; current declarations and dependencies above do.
                for name, digest in review[key].items():
                    if key == "source_hashes":
                        relative_path(name)
                    else:
                        require(re.fullmatch(r"M[0-9]{2,}", name),
                                f"{mid}.review.dependency_reviews: invalid milestone id: {name}")
                    hex_string(digest, 64, f"{mid}.review.{key}.{name}")
        evidence = item["proof_evidence"]
        require(item["proof_status"] != "closed" or evidence is not None,
                f"{mid}: closed proof requires proof_evidence")
        if evidence is not None:
            fields(evidence, EVIDENCE_FIELDS, f"{mid}.proof_evidence")
            hex_string(evidence["commit"], 40, f"{mid}.proof_evidence.commit")
            record_reference(root, evidence["record"], f"{mid}.proof_evidence.record")
            strings(evidence["checks"], f"{mid}.proof_evidence.checks", allow_empty=False)
            strings(evidence["axioms"], f"{mid}.proof_evidence.axioms")
    for mid, item in entries.items():
        require(set(item["dependencies"]) <= set(entries),
                f"{mid}: unknown milestone dependencies: {sorted(set(item['dependencies']) - set(entries))}")
    active, done = set(), set()

    def visit(mid):
        require(mid not in active, f"milestone dependency cycle at {mid}")
        if mid in done:
            return
        active.add(mid)
        for dependency in entries[mid]["dependencies"]:
            visit(dependency)
        active.remove(mid)
        done.add(mid)

    for mid in sorted(entries):
        visit(mid)
    return document


def load_catalog(root, active_labels=None):
    root = Path(root).resolve()
    return validate_catalog(root, read_json(checked_path(root, CATALOG)), active_labels)


def snapshot_changes(current, recorded):
    return {
        "added": sorted(set(current) - set(recorded)),
        "removed": sorted(set(recorded) - set(current)),
        "modified": sorted(key for key in set(current) & set(recorded)
                           if current.get(key) != recorded.get(key)),
    }


def make_schedule(root, document=None, active_labels=None):
    root = Path(root).resolve()
    document = load_catalog(root, active_labels) if document is None else validate_catalog(root, document, active_labels)
    entries = {item["id"]: item for item in document["milestones"]}
    rows, hash_cache = {}, {}
    for mid, item in sorted(entries.items()):
        review = item["review"]
        blockers = []
        warnings = []
        if item["statement_status"] != "frozen":
            blockers.append(f"statement_status:{item['statement_status']}")
        blockers.extend(f"review_blocker:{reason}" for reason in item["review_blockers"])
        changed_sources, changed_reviews, changed_contract = [], [], False
        source_changes, dependency_changes = snapshot_changes({}, {}), snapshot_changes({}, {})
        if review is None:
            blockers.append("review_missing")
        else:
            current = source_hashes(root, item, hash_cache)
            source_changes = snapshot_changes(current, review["source_hashes"])
            current_dependencies = {dep: review_fingerprint(entries[dep]["review"])
                                    for dep in item["dependencies"]}
            dependency_changes = snapshot_changes(current_dependencies, review["dependency_reviews"])
            changed_sources = sorted(name for names in source_changes.values() for name in names)
            changed_reviews = sorted(dep for deps in dependency_changes.values() for dep in deps)
            changed_contract = contract_fingerprint(item) != review["contract_hash"]
            if changed_contract:
                blockers.append("contract_changed")
            for kind, reason in (("added", "added"), ("removed", "removed"), ("modified", "changed")):
                blockers.extend(f"source_{reason}:{name}" for name in source_changes[kind])
                blockers.extend(f"dependency_review_{reason}:{dep}" for dep in dependency_changes[kind])
        if item["proof_status"] == "conditional" and item["proof_evidence"] is None:
            warnings.append("conditional proof has no recorded evidence")
        if item["proof_evidence"] is not None:
            warnings.append("proof evidence records a commit; its coverage of the current result needs review")
        rows[mid] = {
            "id": mid, "title": item["title"], "lane": item["lane"], "owner": item["owner"],
            "statement_status": item["statement_status"], "proof_status_recorded": item["proof_status"],
            "closed_by_record": item["proof_status"] == "closed",
            "proof_evidence": item["proof_evidence"],
            "lean_declarations": item["lean_declarations"], "blueprint_labels": item["blueprint_labels"],
            "dependencies": sorted(item["dependencies"]), "write_scope": item["write_scope"],
            "changed_sources": changed_sources, "changed_dependency_reviews": changed_reviews,
            "source_changes": source_changes, "dependency_review_changes": dependency_changes,
            "changed_contract": changed_contract,
            "own_interface_current": not blockers, "blockers": blockers, "warnings": warnings,
        }

    def evaluate(mid):
        row = rows[mid]
        if "interface_current" in row:
            return row["interface_current"]
        failed = [dep for dep in row["dependencies"] if not evaluate(dep)]
        row["blocking_dependencies"] = failed
        row["blockers"].extend(f"dependency_not_current:{dep}" for dep in failed)
        row["interface_current"] = row["own_interface_current"] and not failed
        row["ready_against_frozen_interfaces"] = row["interface_current"] and not row["closed_by_record"]
        return row["interface_current"]

    for mid in rows:
        evaluate(mid)
    return {
        "schema": 1, "baseline_commit": document["baseline_commit"],
        "meaning": "Scheduling metadata only: frozen/current interfaces do not establish proof completion.",
        "fingerprint_scope": "Conservative whole-file hashes, including proof bodies; not elaborated Lean type comparison.",
        "evidence_scope": "Human review and proof records are recorded, not authenticated or kernel-verified here.",
        "queue_scope": "The implementation queue excludes closed_by_record entries even when their interfaces are current.",
        "ready_against_frozen_interfaces": [mid for mid, row in rows.items() if row["ready_against_frozen_interfaces"]],
        "blocked": [mid for mid, row in rows.items() if not row["interface_current"]],
        "closed_by_record": [mid for mid, row in rows.items() if row["closed_by_record"]],
        "milestones": list(rows.values()),
    }


def schedule_markdown(report):
    lines = ["## Milestone scheduling", "", report["meaning"], report["fingerprint_scope"],
             report["evidence_scope"], report["queue_scope"], "",
             "A closed_by_record entry may also be blocked; a record never overrides stale interfaces.", "",
             "| Milestone | Lane | Statement | Proof record | Interface current | Scheduling |",
             "| --- | --- | --- | --- | --- | --- |"]
    for row in report["milestones"]:
        if not row["interface_current"]:
            scheduling = "; ".join(row["blockers"])
        elif row["closed_by_record"]:
            scheduling = "closed_by_record; verify evidence coverage before relying on closure"
        else:
            scheduling = "ready against frozen interfaces"
        values = [row["id"] + " — " + row["title"], row["lane"], row["statement_status"],
                  "closed_by_record" if row["closed_by_record"] else row["proof_status_recorded"],
                  "yes" if row["interface_current"] else "no", scheduling]
        lines.append("| " + " | ".join(str(value).replace("|", "\\|").replace("\n", " ") for value in values) + " |")
    return "\n".join(lines) + "\n"


def snapshot(root, document, mid):
    entries = {item["id"]: item for item in document["milestones"]}
    require(mid in entries, f"unknown milestone: {mid}")
    item = entries[mid]
    try:
        result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True, check=False)
        commit = result.stdout.strip() if result.returncode == 0 else None
    except OSError:
        commit = None
    dependencies = {dep: review_fingerprint(entries[dep]["review"]) for dep in sorted(item["dependencies"])}
    return {
        "milestone": mid, "candidate_commit": commit, "contract_hash": contract_fingerprint(item),
        "source_hashes": source_hashes(root, item),
        "dependency_reviews": dependencies,
        "unreviewed_dependencies": [dep for dep, digest in dependencies.items() if digest is None],
        "notice": "Candidate metadata only; no review, approval, or status is assigned. "
                  "candidate_commit names Git HEAD, while hashes describe the current working tree, "
                  "including any uncommitted edits; confirm the reviewed commit before recording them.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true", help="validate metadata without requiring reviewed or completed proofs")
    action.add_argument("--snapshot", metavar="ID", help="print candidate review fingerprints without recording approval")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        document = load_catalog(root)
        if args.snapshot:
            print(json.dumps(snapshot(root, document, args.snapshot), indent=2, ensure_ascii=False))
        else:
            report = make_schedule(root, document)
            print(json.dumps({"milestones": len(report["milestones"]),
                              "ready_against_frozen_interfaces": len(report["ready_against_frozen_interfaces"]),
                              "blocked": len(report["blocked"]),
                              "closed_by_record": len(report["closed_by_record"]),
                              "validation": "metadata only; not proof acceptance"}, sort_keys=True))
    except (OSError, ValueError) as error:
        print(f"milestones: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
