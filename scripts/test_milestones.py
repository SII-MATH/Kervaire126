"""Milestone metadata must never turn stale interfaces or scheduling into proofs."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.blueprint_frontier import make_report
from scripts.milestones import (
    CATALOG, contract_fingerprint, load_catalog, make_schedule, read_json, resolve_pointer,
    review_fingerprint, schedule_markdown, snapshot, source_hashes, validate_catalog,
)


SCRIPT = Path(__file__).with_name("milestones.py")


class MilestoneTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        files = {
            "lean-toolchain": "leanprover/lean4:v4.32.2\n",
            "lake-manifest.json": '{"packages": []}\n',
            "PROJECT_BOUNDARY.md": "Development compilation is not proof acceptance.\n",
            "docs/external-inputs.json": json.dumps({"sources": [{"id": "source", "a/b~c": 1}]}),
            "KIP126/Shared.lean": "namespace KIP126\ndef Shared : Prop := True\nend KIP126\n",
        }
        for number in range(1, 4):
            files[f"KIP126/P{number}.lean"] = (
                f"namespace KIP126\ntheorem p{number} : True := by trivial\nend KIP126\n")
        files["blueprint/src/content.tex"] = "\n".join(
            rf"\begin{{theorem}}\label{{thm:p{number}}}\lean{{KIP126.p{number}}}"
            + (rf"\uses{{thm:p{number - 1}}}" if number > 1 else "")
            + r"\notready\end{theorem}" for number in range(1, 4))
        for name, text in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def milestone(self, number, dependencies=None):
        return {
            "id": f"M{number:02}", "title": f"Result {number}", "lane": "tools",
            "goal": "Prove the reviewed result.",
            "lean_declarations": [{"name": f"KIP126.p{number}", "path": f"KIP126/P{number}.lean"}],
            "blueprint_labels": [f"thm:p{number}"], "dependencies": dependencies or [],
            "definition_files": ["KIP126/Shared.lean"], "source_refs": ["/sources/0"],
            "write_scope": [f"KIP126/P{number}.lean"], "owner": None,
            "statement_status": "draft", "proof_status": "open", "review": None,
            "proof_evidence": None, "review_blockers": [],
            "acceptance": ["Review the elaborated type and audit the chosen proof roots."], "notes": [],
        }

    def catalog(self, count=2):
        return {"schema": 1, "baseline_commit": "a" * 40,
                "milestones": [self.milestone(i, [f"M{i - 1:02}"] if i > 1 else [])
                               for i in range(1, count + 1)]}

    def install(self, document):
        (self.root / CATALOG).write_text(json.dumps(document, indent=2) + "\n")

    def freeze(self, document, mid=None):
        entries = {entry["id"]: entry for entry in document["milestones"]}
        for item in document["milestones"]:
            if mid is not None and mid != item["id"]:
                continue
            item["statement_status"] = "frozen"
            item["review"] = {
                "commit": "b" * 40, "record": "https://github.com/SII-MATH/Kervaire126/pull/1",
                "contract_hash": contract_fingerprint(item),
                "reviewers": ["数学审查者"], "source_hashes": source_hashes(self.root, item),
                "dependency_reviews": {dep: review_fingerprint(entries[dep]["review"]) or "0" * 64
                                       for dep in item["dependencies"]},
            }
        return document

    def rows(self, document):
        return {row["id"]: row for row in make_schedule(self.root, document)["milestones"]}

    def evidence(self):
        return {"commit": "c" * 40, "record": "https://github.com/SII-MATH/Kervaire126/actions/runs/1",
                "checks": ["Scoped compiled-environment audit"], "axioms": ["propext", "Quot.sound"]}

    def test_drafts_validate_without_approval_or_proof_debt_gate(self):
        document = self.catalog()
        self.install(document)
        report = make_schedule(self.root)
        self.assertEqual(report["ready_against_frozen_interfaces"], [])
        self.assertEqual(report["blocked"], ["M01", "M02"])
        self.assertEqual(report["closed_by_record"], [])
        self.assertIn("statement_status:draft", report["milestones"][0]["blockers"])
        run = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root), "--check"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)

    def test_frozen_dependencies_allow_parallel_work_without_marking_blueprint_complete(self):
        original = make_report(self.root)
        document = self.freeze(self.catalog())
        self.install(document)
        report = make_report(self.root)
        for key, value in original.items():
            self.assertEqual(report[key], value)
        self.assertEqual(report["schema"], 1)
        self.assertEqual(report["completed_by_blueprint_markers"], 0)
        self.assertEqual(report["milestone_scheduling"]["ready_against_frozen_interfaces"], ["M01", "M02"])
        self.assertEqual(report["milestone_scheduling"]["closed_by_record"], [])
        self.assertIn("thm:p2", [row["label"] for row in report["groups"]["blocked"]])

    def test_proof_body_edit_stales_self_and_transitive_consumers_but_check_passes(self):
        document = self.freeze(self.catalog(3))
        with (self.root / "KIP126/P1.lean").open("a") as target:
            target.write("-- Proof-only change also invalidates the conservative fingerprint.\n")
        rows = self.rows(document)
        self.assertEqual(rows["M01"]["changed_sources"], ["KIP126/P1.lean"])
        self.assertEqual(rows["M02"]["changed_sources"], [])
        self.assertEqual(rows["M03"]["blocking_dependencies"], ["M02"])
        self.assertFalse(any(row["interface_current"] for row in rows.values()))
        self.install(document)
        run = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root), "--check"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)["blocked"], 3)

    def test_shared_definition_and_common_environment_changes_invalidate_review(self):
        for path in ("KIP126/Shared.lean", "lean-toolchain", "PROJECT_BOUNDARY.md", "docs/external-inputs.json"):
            with self.subTest(path=path):
                document = self.freeze(self.catalog())
                file = self.root / path
                original = file.read_text()
                file.write_text(original + "\n")
                rows = self.rows(document)
                self.assertTrue(all(path in row["changed_sources"] for row in rows.values()))
                file.write_text(original)

    def test_changed_upstream_review_requires_consumer_review_refresh(self):
        document = self.freeze(self.catalog())
        document["milestones"][0]["review"]["record"] = "https://github.com/SII-MATH/Kervaire126/pull/2"
        rows = self.rows(document)
        self.assertTrue(rows["M01"]["interface_current"])
        self.assertEqual(rows["M02"]["changed_dependency_reviews"], ["M01"])
        self.assertFalse(rows["M02"]["interface_current"])
        document["milestones"][1]["review"]["dependency_reviews"]["M01"] = review_fingerprint(
            document["milestones"][0]["review"])
        self.assertTrue(self.rows(document)["M02"]["interface_current"])

    def test_reopened_ancestor_and_unresolved_review_blockers_stop_readiness(self):
        document = self.freeze(self.catalog())
        document["milestones"][0]["statement_status"] = "reopened"
        self.assertFalse(self.rows(document)["M02"]["interface_current"])
        document["milestones"][0]["statement_status"] = "frozen"
        document["milestones"][0]["review_blockers"] = ["Check the hidden typeclass hypothesis."]
        rows = self.rows(document)
        self.assertFalse(rows["M01"]["interface_current"])
        self.assertFalse(rows["M02"]["interface_current"])

    def test_frozen_statement_requires_well_formed_review(self):
        document = self.catalog(1)
        item = document["milestones"][0]
        item["statement_status"] = "frozen"
        with self.assertRaisesRegex(ValueError, "requires a review"):
            validate_catalog(self.root, document)
        self.freeze(document)
        for field, replacement in (("reviewers", []), ("source_hashes", {}), ("dependency_reviews", {"M02": "0" * 64})):
            with self.subTest(field=field):
                changed = deepcopy(document)
                changed["milestones"][0]["review"][field] = replacement
                with self.assertRaises(ValueError):
                    validate_catalog(self.root, changed)

    def test_review_must_watch_exact_declarations_definitions_and_common_files(self):
        document = self.freeze(self.catalog(1))
        hashes = document["milestones"][0]["review"]["source_hashes"]
        self.assertEqual(set(hashes), {"KIP126/P1.lean", "KIP126/Shared.lean", "lean-toolchain",
                                      "lake-manifest.json", "PROJECT_BOUNDARY.md", "docs/external-inputs.json"})
        hashes["unwatched.txt"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source_hashes"):
            validate_catalog(self.root, document)

    def test_historical_review_survives_moved_declaration_and_changed_definition_scope(self):
        document = self.freeze(self.catalog(1))
        item = document["milestones"][0]
        old_review = deepcopy(item["review"])
        (self.root / "KIP126/P1.lean").rename(self.root / "KIP126/Moved.lean")
        (self.root / "KIP126/Shared.lean").unlink()
        (self.root / "KIP126/NewDefinition.lean").write_text("-- New defining scope.\n")
        item["lean_declarations"][0]["path"] = "KIP126/Moved.lean"
        item["write_scope"] = ["KIP126/Moved.lean"]
        item["definition_files"] = ["KIP126/NewDefinition.lean"]
        row = self.rows(document)["M01"]
        self.assertTrue(row["changed_contract"])
        self.assertFalse(row["interface_current"])
        self.assertEqual(row["source_changes"], {
            "added": ["KIP126/Moved.lean", "KIP126/NewDefinition.lean"],
            "removed": ["KIP126/P1.lean", "KIP126/Shared.lean"], "modified": [],
        })
        self.install(document)
        run = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root), "--check"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(load_catalog(self.root)["milestones"][0]["review"], old_review)

    def test_historical_review_survives_added_and_removed_dependencies(self):
        document = self.freeze(self.catalog(3))
        item = document["milestones"][2]
        old_review = deepcopy(item["review"])
        item["dependencies"] = ["M01"]
        # The old dependency has also left the current catalog entirely.
        document["milestones"] = [document["milestones"][0], item]
        row = self.rows(document)["M03"]
        self.assertTrue(row["changed_contract"])
        self.assertFalse(row["interface_current"])
        self.assertEqual(row["dependency_review_changes"], {
            "added": ["M01"], "removed": ["M02"], "modified": [],
        })
        self.install(document)
        run = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root), "--check"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(load_catalog(self.root)["milestones"][1]["review"], old_review)

    def test_historical_review_still_requires_safe_well_formed_snapshot_keys(self):
        changes = (
            lambda review: review["source_hashes"].update({"../outside.lean": "0" * 64}),
            lambda review: review["source_hashes"].pop("lean-toolchain"),
            lambda review: review["dependency_reviews"].update({"not-an-id": "0" * 64}),
            lambda review: review["source_hashes"].update({"deleted.lean": "not-a-hash"}),
        )
        for change in changes:
            document = self.freeze(self.catalog(1))
            document["milestones"][0]["goal"] = "A changed contract."
            change(document["milestones"][0]["review"])
            with self.assertRaises(ValueError):
                validate_catalog(self.root, document)

    def test_closed_record_needs_evidence_and_cannot_override_stale_interfaces(self):
        document = self.freeze(self.catalog(1))
        item = document["milestones"][0]
        item["proof_status"] = "closed"
        with self.assertRaisesRegex(ValueError, "requires proof_evidence"):
            validate_catalog(self.root, document)
        item["proof_evidence"] = self.evidence()
        current = make_schedule(self.root, document)
        self.assertTrue(current["milestones"][0]["interface_current"])
        self.assertFalse(current["milestones"][0]["ready_against_frozen_interfaces"])
        self.assertEqual(current["ready_against_frozen_interfaces"], [])
        (self.root / "KIP126/P1.lean").write_text("-- changed result\n")
        report = make_schedule(self.root, document)
        self.assertEqual(report["closed_by_record"], ["M01"])
        self.assertEqual(report["blocked"], ["M01"])
        self.assertEqual(report["ready_against_frozen_interfaces"], [])
        self.assertTrue(report["milestones"][0]["warnings"])
        self.assertIn("closed_by_record", schedule_markdown(report))

    def test_target_metadata_changes_stale_review_but_administrative_progress_does_not(self):
        changes = (
            lambda item: item["lean_declarations"][0].update(name="KIP126.otherTarget"),
            lambda item: item.update(goal="A different mathematical result."),
            lambda item: item.update(source_refs=["/sources/0/a~1b~0c"]),
            lambda item: item.update(acceptance=["A different acceptance condition."]),
        )
        for change in changes:
            document = self.freeze(self.catalog(1))
            change(document["milestones"][0])
            row = self.rows(document)["M01"]
            self.assertTrue(row["changed_contract"])
            self.assertFalse(row["interface_current"])
            self.assertEqual(row["changed_sources"], [])
            self.assertIn("contract_changed", row["blockers"])
        document = self.freeze(self.catalog(1))
        item = document["milestones"][0]
        item.update(owner="Worker A", proof_status="conditional", notes=["Proof construction is underway."])
        row = self.rows(document)["M01"]
        self.assertFalse(row["changed_contract"])
        self.assertTrue(row["interface_current"])

    def test_conditional_without_evidence_is_valid_and_disclosed(self):
        document = self.catalog(1)
        document["milestones"][0]["proof_status"] = "conditional"
        row = self.rows(document)["M01"]
        self.assertIn("conditional proof has no recorded evidence", row["warnings"])
        self.assertFalse(row["closed_by_record"])

    def test_unknown_dependencies_and_disconnected_cycles_fail(self):
        for dependencies, error in [(["M99"], "unknown milestone dependencies"), (["M01"], "cycle")]:
            document = self.catalog(1)
            document["milestones"][0]["dependencies"] = dependencies
            with self.subTest(dependencies=dependencies), self.assertRaisesRegex(ValueError, error):
                validate_catalog(self.root, document)
        document = self.catalog(3)
        document["milestones"][1]["dependencies"] = ["M03"]
        with self.assertRaisesRegex(ValueError, "cycle"):
            validate_catalog(self.root, document)

    def test_duplicate_ids_unknown_fields_and_invalid_schema_fail(self):
        document = self.catalog()
        document["milestones"][1]["id"] = "M01"
        with self.assertRaisesRegex(ValueError, "duplicate milestone"):
            validate_catalog(self.root, document)
        for change in (lambda d: d.update(schema=True),
                       lambda d: d["milestones"][0].update(auto_approved=True),
                       lambda d: d["milestones"][0].update(owner="")):
            document = self.catalog(1)
            change(document)
            with self.assertRaises(ValueError):
                validate_catalog(self.root, document)

    def test_paths_must_exist_and_stay_in_checkout_including_symlinks(self):
        for path in ("../outside.lean", "/tmp/outside.lean", "KIP126/missing.lean", "KIP126/./P1.lean"):
            document = self.catalog(1)
            document["milestones"][0]["definition_files"] = [path]
            with self.subTest(path=path), self.assertRaises(ValueError):
                validate_catalog(self.root, document)
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / "outside.lean"
            target.write_text("-- Outside the checkout.\n")
            (self.root / "KIP126/Escape.lean").symlink_to(target)
            document = self.catalog(1)
            document["milestones"][0]["definition_files"] = ["KIP126/Escape.lean"]
            with self.assertRaisesRegex(ValueError, "escapes checkout"):
                validate_catalog(self.root, document)

    def test_directory_write_scope_is_valid_but_file_prefix_is_not(self):
        document = self.catalog(1)
        document["milestones"][0]["write_scope"] = ["KIP126/"]
        validate_catalog(self.root, document)
        document["milestones"][0]["write_scope"] = ["KIP126/P1.lean/"]
        with self.assertRaisesRegex(ValueError, "directory prefix"):
            validate_catalog(self.root, document)

    def test_active_labels_and_source_pointers_are_checked_without_claiming_symbol_elaboration(self):
        document = self.catalog(1)
        item = document["milestones"][0]
        item["blueprint_labels"] = ["thm:inactive"]
        with self.assertRaisesRegex(ValueError, "active Blueprint"):
            validate_catalog(self.root, document)
        item["blueprint_labels"] = ["thm:p2"]  # A related label need not name exactly this declaration.
        validate_catalog(self.root, document)
        for pointer in ("/sources/9", "/sources/01", "/sources/0/missing", "/bad~2escape", "sources/0"):
            item["source_refs"] = [pointer]
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                validate_catalog(self.root, document)
        item["source_refs"] = ["/sources/0/a~1b~0c"]
        validate_catalog(self.root, document)
        self.assertEqual(resolve_pointer({"a/b~c": [7]}, "/a~1b~0c/0"), 7)

    def test_review_fingerprint_is_canonical_utf8_json(self):
        review = {"z": "审查", "a": {"two": 2, "one": 1}}
        expected = hashlib.sha256(json.dumps(review, sort_keys=True, separators=(",", ":"),
                                             ensure_ascii=False).encode("utf-8")).hexdigest()
        self.assertEqual(review_fingerprint(review), expected)
        self.assertEqual(review_fingerprint({"a": {"one": 1, "two": 2}, "z": "审查"}), expected)
        self.assertIsNone(review_fingerprint(None))

    def test_snapshot_is_read_only_and_missing_dependency_review_is_explicit(self):
        document = self.catalog()
        self.install(document)
        before = (self.root / CATALOG).read_bytes()
        result = snapshot(self.root, load_catalog(self.root), "M02")
        self.assertIsNone(result["dependency_reviews"]["M01"])
        self.assertEqual(result["unreviewed_dependencies"], ["M01"])
        self.assertEqual((self.root / CATALOG).read_bytes(), before)
        self.assertEqual(document["milestones"][1]["statement_status"], "draft")
        self.assertEqual(document["milestones"][1]["review"], None)
        with self.assertRaisesRegex(ValueError, "unknown milestone"):
            snapshot(self.root, document, "M99")

    def test_report_is_deterministic_and_does_not_mutate_catalog(self):
        document = self.freeze(self.catalog())
        original = deepcopy(document)
        self.assertEqual(make_schedule(self.root, document), make_schedule(self.root, document))
        self.assertEqual(document, original)

    def test_duplicate_json_keys_are_not_silently_overwritten(self):
        file = self.root / CATALOG
        file.write_text('{"schema": 1, "schema": 2}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            read_json(file)


if __name__ == "__main__":
    unittest.main()
