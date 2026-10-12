"""Regression mutations for public handoffs, import modes, and audit isolation."""

import json
import unittest

from scripts.module_boundaries import (
    ROOT, header_tokens, module_from_path, module_parts, parse_source,
    source_inventory, tokens, validate,
)


def minimal_registry():
    owners = ["steenrod", "spectral", "adams", "literature", "computation", "rules", "main"]
    return {
        "schema_version": 1,
        "owners": [{"id": name} for name in owners],
        "ownership": [{"path": "KIP126/Def/", "owner": "adams"},
                      {"path": "KIP126/Main/", "owner": "main"}],
        "milestones": [{"id": f"M{i:02}", "contracts": ["M16.weak_y"] if i == 16 else []}
                       for i in range(1, 21)],
        "contracts": [{"id": "M16.weak_y", "owner": "main", "milestone": "M16",
                       "nlfl_entry_ids": ["I-example"]}],
        "deliveries": [], "private_imports": [],
    }


def fixture_sources(files):
    return {s.module: s for path, text in files.items() for s in [parse_source(text, path)]}


def fixture_delivery():
    return {
        "id": "joint_y", "contract": "M16.weak_y", "nlfl_entry_ids": ["I-example"],
        "provider": "KIP126/Main/WeakY.lean",
        "declarations": [{"name": "KIP126.Main.weak_y_exists", "kind": "theorem"}],
        "consumers": ["KIP126/Main/NuTarget.lean"],
        "private_implementation": ["KIP126.Main.WeakHelper"],
        "mathematical_review": {"status": "pending"},
        "public_boundary": {"status": "implemented_in_source"},
        "build_isolation": {"status": "not_measured"},
        "public_environment": ["One shared witness and the original Q9 predicates"],
        "unfolding_policy": {"description": "The proof body remains hidden."},
    }


class ImportLexerTests(unittest.TestCase):
    def test_modes_multiple_imports_and_quoted_components(self):
        source = parse_source('''module
public meta import all KIP126.Def.A
public meta import all KIP126.Def.«A B»
import «KIP126.Other».«Name.with.dots»
meta import KIP126.Def.B
public import KIP126.Def.C
''', "KIP126/Checks/Test.lean")
        self.assertEqual([(i.target, i.mode) for i in source.imports], [
            ("KIP126.Def.A", "public meta import all"),
            ("KIP126.Def.«A B»", "public meta import all"),
            ("«KIP126.Other».«Name.with.dots»", "import"),
            ("KIP126.Def.B", "meta import"),
            ("KIP126.Def.C", "public import"),
        ])
        self.assertEqual(module_parts("KIP126.Def.«A.B C»"), ["KIP126", "Def", "A.B C"])
        self.assertEqual(module_from_path("KIP126/Def/A.B C.lean"), "KIP126.Def.«A.B C»")

    def test_nested_comments_and_strings_cannot_invent_imports(self):
        text = '''module
/- outer
  /- inner -/
  import all KIP126.Main.Fake
-/
public /- comment /- nested -/ -/ import KIP126.Def.Real -- trailing
def example := "import all KIP126.Main.Fake\\nopen private z from KIP126.Main.Fake"
def quoted := "escaped \\" quote" -- an opaque escaped string
'''.replace('\\\\" quote', '\\" quote')
        source = parse_source(text, "KIP126/Checks/Test.lean")
        self.assertEqual([(i.target, i.public) for i in source.imports], [("KIP126.Def.Real", True)])
        self.assertEqual(source.private_opens, [])

    def test_multiline_import_modifiers_and_private_open(self):
        source = parse_source('''module
public
import KIP126.Def.A
meta
import all KIP126.Def.B
public /- outer
 /- nested -/ -/ import KIP126.Def.Hidden
open /- comment -/ private first second
  from KIP126.Def.Hidden
''', "KIP126/Main/Consumer.lean")
        self.assertEqual([i.target for i in source.imports], ["KIP126.Def.A", "KIP126.Def.B", "KIP126.Def.Hidden"])
        self.assertEqual([i.mode for i in source.imports], ["public import", "meta import all", "public import"])
        self.assertEqual(source.private_opens, [("KIP126.Def.Hidden", 8)])

    def test_non_provider_fast_path_retains_crossline_modes_and_private_open(self):
        text = '''module
public
meta /- a\n b -/ import all KIP126.Def.Hidden
open /- nested /- comment -/ -/ private thing from KIP126.Def.Hidden
'''
        full = parse_source(text, "KIP126/Main/Consumer.lean")
        fast = parse_source(text, "KIP126/Main/Consumer.lean", declarations=False)
        self.assertEqual(fast.imports, full.imports)
        self.assertEqual(fast.imports[0].mode, "public meta import all")
        self.assertEqual(fast.private_opens, full.private_opens)
        self.assertEqual(len(fast.private_opens), 1)

    def test_header_fast_path_stops_before_generated_data(self):
        text = 'module\npublic import KIP126.Def.A\n@[expose] public section\ndef data := [1, 2, 3]\n'
        self.assertEqual([t.value for t in header_tokens(text)], ["module", "public", "import", "KIP126.Def.A"])
        full = parse_source(text, "KIP126/Main/Data.lean")
        fast = parse_source(text, "KIP126/Main/Data.lean", declarations=False)
        self.assertEqual(full.imports, fast.imports)

    def test_unclosed_comment_does_not_silently_hide_a_boundary(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            tokens("module\n/- hidden import all KIP126.Def.A")

    def test_redundant_quoting_cannot_hide_the_project_root(self):
        source = parse_source('module\nimport all «KIP126».Def.«Hidden»', "KIP126/Main/Consumer.lean")
        self.assertEqual(source.imports[0].target, "KIP126.Def.Hidden")

    def test_private_section_restores_the_enclosing_visibility(self):
        source = parse_source('''module
public section
namespace KIP126.Main
private section
theorem hidden : True := by trivial
end
theorem visible : True := by trivial
end KIP126.Main
''', "KIP126/Main/Provider.lean")
        self.assertEqual(source.declarations["KIP126.Main.hidden"]["visibility"], "private")
        self.assertEqual(source.declarations["KIP126.Main.visible"]["visibility"], "public")

    def test_declaration_modifiers_and_attributes_cross_lines(self):
        source = parse_source('''module
public section
namespace KIP126.Main
private
theorem hidden : True := by trivial
@[no_expose]
noncomputable
def operation : Nat := 0
end KIP126.Main
''', "KIP126/Main/Provider.lean")
        self.assertEqual(source.declarations["KIP126.Main.hidden"]["visibility"], "private")
        self.assertTrue(source.declarations["KIP126.Main.operation"]["no_expose"])


class BoundaryMutationTests(unittest.TestCase):
    def make_sources(self, consumer="import KIP126.Main.WeakY", provider_import="import all KIP126.Main.WeakHelper", visibility="public"):
        return fixture_sources({
            "KIP126/Main/WeakHelper.lean": "module\nprivate theorem construction : True := by trivial\n",
            "KIP126/Main/WeakY.lean": f"module\n{provider_import}\n{visibility} section\nnamespace KIP126.Main\ntheorem weak_y_exists : True := by trivial\nend KIP126.Main\n",
            "KIP126/Main/NuTarget.lean": f"module\n{consumer}\n",
        })

    def make_registry(self):
        registry = minimal_registry()
        registry["deliveries"] = [fixture_delivery()]
        registry["private_imports"] = [{"consumer": "KIP126.Main.WeakY", "provider": "KIP126.Main.WeakHelper",
                                        "classification": "component_internal", "reason": "The producer constructs its own joint witness."}]
        return registry

    def test_ordinary_handoff_stops_proof_implementation_visibility(self):
        self.assertEqual(validate(self.make_registry(), self.make_sources())["errors"], [])

    def test_import_all_of_public_provider_is_a_boundary_regression(self):
        result = validate(self.make_registry(), self.make_sources("import all KIP126.Main.WeakY"))
        self.assertTrue(any("consumer opens delivery implementation" in e for e in result["errors"]))

    def test_public_bridge_cannot_reexport_a_private_helper(self):
        sources = self.make_sources("import KIP126.Main.WeakY\nimport KIP126.Main.Bridge")
        bridge = parse_source("module\npublic import KIP126.Main.WeakHelper", "KIP126/Main/Bridge.lean")
        sources[bridge.module] = bridge
        result = validate(self.make_registry(), sources)
        self.assertTrue(any("NuTarget -> KIP126.Main.Bridge -> KIP126.Main.WeakHelper" in e for e in result["errors"]))

    def test_an_aggregator_cannot_publicly_reexport_proof_support(self):
        sources = fixture_sources({
            "KIP126/Main/Support.lean": "module",
            "KIP126/Main/Aggregator.lean": "module\npublic import KIP126.Main.Support",
        })
        registry = minimal_registry()
        registry["implementation_only_modules"] = ["KIP126.Main.Support"]
        self.assertTrue(any("implementation-only module is publicly reexported" in e for e in validate(registry, sources)["errors"]))
        sources["KIP126.Main.Aggregator"] = parse_source("module\nimport KIP126.Main.Support", "KIP126/Main/Aggregator.lean")
        self.assertEqual(validate(registry, sources)["errors"], [])

    def test_production_cannot_reach_checks_through_a_bridge(self):
        sources = fixture_sources({
            "KIP126/Main/Consumer.lean": "module\nimport KIP126.Main.Bridge",
            "KIP126/Main/Bridge.lean": "module\nimport KIP126.Checks.Internals",
            "KIP126/Checks/Internals.lean": "module",
        })
        result = validate(minimal_registry(), sources)
        self.assertTrue(any("Consumer -> KIP126.Main.Bridge -> KIP126.Checks.Internals" in e for e in result["errors"]))

    def test_library_root_exception_cannot_be_used_as_an_audit_backdoor(self):
        sources = fixture_sources({
            "KIP126.lean": "module\npublic import KIP126.Checks.Internals",
            "KIP126/Checks/Internals.lean": "module",
        })
        self.assertEqual(validate(minimal_registry(), sources)["errors"], [])
        consumer = parse_source("module\nimport KIP126", "KIP126/Main/Consumer.lean")
        sources[consumer.module] = consumer
        result = validate(minimal_registry(), sources)
        self.assertTrue(any("Consumer -> KIP126 -> KIP126.Checks.Internals" in e for e in result["errors"]))

    def test_checks_root_is_also_an_audit_module(self):
        sources = fixture_sources({
            "KIP126/Checks.lean": "module",
            "KIP126/Main/Consumer.lean": "module\nimport KIP126.Checks",
        })
        self.assertTrue(any("production import closure reaches Checks" in e for e in validate(minimal_registry(), sources)["errors"]))

    def test_losing_a_definitions_no_expose_is_rejected(self):
        registry = self.make_registry()
        registry["deliveries"][0]["declarations"] = [{"name": "KIP126.Main.operation", "kind": "def", "require_no_expose": True}]
        sources = self.make_sources()
        path = "KIP126/Main/WeakY.lean"
        for attribute, expected in [("@[no_expose] ", False), ("", True)]:
            sources["KIP126.Main.WeakY"] = parse_source(
                f"module\npublic section\nnamespace KIP126.Main\n{attribute}noncomputable def operation : Nat := 0\nend KIP126.Main", path)
            result = validate(registry, sources)
            self.assertEqual(any("lost its explicit no_expose" in e for e in result["errors"]), expected)

    def test_new_cross_owner_private_import_needs_individual_registration(self):
        sources = fixture_sources({
            "KIP126/Main/Consumer.lean": "module\nimport all KIP126.Def.Hidden",
            "KIP126/Def/Hidden.lean": "module",
        })
        registry = minimal_registry()
        self.assertTrue(any("unregistered cross-owner private import" in e for e in validate(registry, sources)["errors"]))
        registry["private_imports"] = [{"consumer": "KIP126.Main.Consumer", "provider": "KIP126.Def.Hidden",
                                        "classification": "existing_debt", "reason": "A named retained debt pending an operation theorem."}]
        self.assertEqual(validate(registry, sources)["errors"], [])
        registry["private_imports"][0]["reason"] = ""
        self.assertTrue(validate(registry, sources)["errors"])

    def test_making_an_export_private_is_rejected(self):
        result = validate(self.make_registry(), self.make_sources(visibility="private"))
        self.assertTrue(any("delivery declaration remains private" in e for e in result["errors"]))

    def test_missing_nlfl_mapping_or_independent_status_is_rejected(self):
        registry = self.make_registry()
        registry["deliveries"][0]["nlfl_entry_ids"] = ["invented-id"]
        del registry["deliveries"][0]["build_isolation"]
        # A broken schema must return a failed check, not accidentally accept
        # the public implementation as evidence of mathematical review.
        result = validate(registry, self.make_sources())
        self.assertTrue(any("NL-FL" in e for e in result["errors"]))
        self.assertTrue(any("build_isolation" in e for e in result["errors"]))

    def test_existing_nlfl_id_from_another_contract_is_rejected(self):
        registry = self.make_registry()
        registry["contracts"].append({"id": "M03.other", "milestone": "M03", "owner": "spectral", "nlfl_entry_ids": ["I-another-contract"]})
        registry["milestones"][2]["contracts"] = ["M03.other"]
        registry["deliveries"][0]["nlfl_entry_ids"] = ["I-another-contract"]
        self.assertTrue(any("belonging to its contract" in e for e in validate(registry, self.make_sources())["errors"]))

    def test_duplicate_registry_ids_and_milestone_assignments_are_rejected(self):
        for collection in ("owners", "contracts", "deliveries"):
            registry = self.make_registry()
            registry[collection].append(dict(registry[collection][0]))
            self.assertTrue(validate(registry, self.make_sources())["errors"], collection)
        registry = self.make_registry()
        registry["milestones"][15]["contracts"].append("M16.weak_y")
        self.assertTrue(any("exactly once" in e for e in validate(registry, self.make_sources())["errors"]))


class RepositoryBoundaryTests(unittest.TestCase):
    def test_registered_public_handoffs_and_private_imports(self):
        registry = json.loads((ROOT / "docs/module-boundaries.json").read_text())
        sources = source_inventory(ROOT, {d["provider"] for d in registry["deliveries"]})
        result = validate(registry, sources)
        self.assertEqual(result["errors"], [], "\n".join(result["errors"]))


if __name__ == "__main__":
    unittest.main()
