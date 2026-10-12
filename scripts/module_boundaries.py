#!/usr/bin/env python3
"""Audit Lean import modes and the registered mathematical delivery boundaries.

This is a source/import audit, not a Lean parser, elaborated-type comparison,
proof audit, or build benchmark. Lean compilation remains the authority for
whether a public declaration and its complete type are usable by a consumer.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = Path("docs/module-boundaries.json")
DECLARATIONS = {"theorem", "lemma", "def", "abbrev", "opaque", "structure", "inductive", "class"}
COMMANDS = DECLARATIONS | {
    "module", "prelude", "namespace", "section", "end", "open", "export",
    "import", "public", "private", "meta", "noncomputable", "variable",
    "universe", "set_option", "attribute", "instance", "syntax", "macro",
    "elab", "initialize", "example", "local", "scoped", "notation",
    "unsafe", "partial", "protected", "mutual",
}


@dataclass(frozen=True)
class Token:
    value: str
    line: int
    column: int
    kind: str = "code"


@dataclass(frozen=True)
class Import:
    target: str
    public: bool
    meta: bool
    all: bool
    line: int

    @property
    def mode(self) -> str:
        return " ".join(x for x in (
            "public" if self.public else "", "meta" if self.meta else "",
            "import", "all" if self.all else "") if x)


@dataclass
class Source:
    path: str
    module: str
    has_module: bool
    imports: list[Import]
    private_opens: list[tuple[str, int]]
    declarations: dict[str, dict]


def iter_tokens(text: str):
    """Keep source positions; skip nested comments and opaque string contents.

    Quoted identifier segments are kept intact, including embedded dots and
    spaces. A string remains an opaque token so text across it is never joined
    into a fictitious import or command.
    """
    i, line, column, n = 0, 1, 0, len(text)

    def advance(end: int) -> None:
        nonlocal i, line, column
        chunk = text[i:end]
        count = chunk.count("\n")
        if count:
            line += count
            column = len(chunk.rsplit("\n", 1)[-1])
        else:
            column += len(chunk)
        i = end

    while i < n:
        if text[i].isspace():
            advance(i + 1)
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            advance(n if end < 0 else end)
            continue
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise ValueError(f"unterminated Lean block comment at line {line}")
            advance(j)
            continue
        start, start_line, start_column = i, line, column
        if text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            else:
                raise ValueError(f"unterminated Lean string at line {line}")
            yield Token(text[i:j], line, column, "string")
            advance(j)
            continue
        # Character literals cannot contain a newline. Apostrophes inside
        # identifiers are consumed in the identifier branch below.
        if text[i] == "'":
            match = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:])
            if match:
                j = i + len(match.group())
                yield Token(text[i:j], line, column, "string")
                advance(j)
                continue
        if text.startswith((":=", "=>", "->"), i):
            yield Token(text[i:i + 2], line, column)
            advance(i + 2)
            continue
        if text[i] in "(){}[],:;=@#":
            yield Token(text[i], line, column)
            advance(i + 1)
            continue
        j = i
        while j < n:
            if text[j] == "«":
                end = text.find("»", j + 1)
                if end < 0:
                    raise ValueError(f"unterminated quoted identifier at line {start_line}")
                j = end + 1
                continue
            if (text[j].isspace() or text[j] in '(){}[],:;=@#"'
                    or text.startswith(("--", "/-", ":=", "=>", "->"), j)):
                break
            j += 1
        if j == start:
            j += 1
        yield Token(text[start:j], start_line, start_column)
        advance(j)


def tokens(text: str) -> list[Token]:
    return list(iter_tokens(text))


def header_tokens(text: str) -> list[Token]:
    """Read Lean's token-based header; modifiers may cross lines/comments.

    Lean 4.32 permits one module identifier per import command. Multiple
    import commands can be separated by arbitrary whitespace.
    """
    result, stream = [], iter(iter_tokens(text))
    token = next(stream, None)
    while token:
        if token.value in ("module", "prelude"):
            result.append(token)
            token = next(stream, None)
            continue
        command = []
        while token and token.value in ("public", "meta"):
            command.append(token)
            token = next(stream, None)
        if token is None or token.value != "import":
            break
        command.append(token)
        token = next(stream, None)
        if token and token.value == "all":
            command.append(token)
            token = next(stream, None)
        if token is None or not is_module_name(token):
            raise ValueError(f"unsupported or empty Lean import at line {command[0].line}")
        command.append(token)
        result.extend(command)
        token = next(stream, None)
    return result


def module_parts(name: str) -> list[str]:
    """Parse dots outside «quoted segments»; reject path traversal components."""
    parts, part, quoted = [], "", False
    for character in name:
        if character == "«":
            if quoted or part:
                raise ValueError(f"invalid module identifier: {name}")
            quoted = True
        elif character == "»":
            if not quoted:
                raise ValueError(f"invalid module identifier: {name}")
            quoted = False
        elif character == "." and not quoted:
            parts.append(part)
            part = ""
        else:
            part += character
    parts.append(part)
    if quoted or any(not p or p in (".", "..") or "/" in p or "\\" in p for p in parts):
        raise ValueError(f"invalid module identifier: {name}")
    return parts


def is_module_name(token: Token) -> bool:
    if token.kind != "code" or token.value in COMMANDS or token.value == "all":
        return False
    try:
        parts = module_parts(token.value)
    except ValueError:
        return False
    # Lean identifiers are Unicode; quoted segments also permit spaces/dots.
    return all(p and (p[0].isalpha() or p[0] == "_" or "«" in token.value) for p in parts)


def module_from_path(path: str) -> str:
    parts = list(Path(path).with_suffix("").parts)
    return ".".join(p if re.fullmatch(r"[^\W\d]\w*", p, re.UNICODE) else f"«{p}»" for p in parts)


def canonical_module(name: str) -> str:
    # «KIP126».Def.X and KIP126.Def.X name the same module. Retain quotes
    # only when they carry a space, an embedded dot, or another special char.
    return ".".join(p if re.fullmatch(r"[^\W\d]\w*", p, re.UNICODE) else f"«{p}»"
                    for p in module_parts(name))


def private_open_targets(stream) -> list[tuple[str, int]]:
    """Recognize open /- nested comments -/ private ... from M lexically."""
    result, state, line = [], 0, 0
    for token in stream:
        if token.kind != "code":
            state = 0
            continue
        if state == 1 and token.value == "private":
            state = 2
        elif state == 2 and token.value == "from":
            state = 3
        elif state == 3:
            if is_module_name(token):
                result.append((canonical_module(token.value), line))
            state = 0
        elif token.value == "open":
            state, line = 1, token.line
        elif state == 1 or token.value in COMMANDS:
            state = 0
    return result


def may_have_private_open(text: str) -> bool:
    """Cheap, conservative prefilter, with lexical lookahead through comments.

    A raw occurrence inside a string/comment can cause a full scan, but cannot
    hide a real command. Only two tokens are inspected at each occurrence, so
    generated files containing many private proofs do not need a full scan.
    """
    for match in re.finditer(r"\bopen\b", text):
        stream = iter(iter_tokens(text[match.start():]))
        try:
            first, second = next(stream, None), next(stream, None)
        except ValueError:
            return True
        if first and second and first.value == "open" and second.value == "private":
            return True
    return False


def declaration_modifiers(ts: list[Token], index: int) -> list[str]:
    """Read adjacent attributes/modifiers across newlines, not a whole line."""
    result, j = [], index - 1
    modifiers = {"public", "private", "protected", "noncomputable", "unsafe", "partial"}
    while j >= 0:
        if ts[j].value in modifiers:
            result.append(ts[j].value)
            j -= 1
        elif ts[j].value == "]":
            end, depth = j, 1
            j -= 1
            while j >= 0 and depth:
                depth += (ts[j].value == "]") - (ts[j].value == "[")
                j -= 1
            if depth or j < 0 or ts[j].value != "@":
                break
            result.extend(t.value for t in ts[j:end + 1])
            j -= 1
        else:
            break
    return result


def parse_source(text: str, path: str, *, declarations: bool = True) -> Source:
    header = header_tokens(text)
    imports: list[Import] = []
    i = 0
    while i < len(header):
        if header[i].value in ("module", "prelude"):
            i += 1
            continue
        public, meta = False, False
        while header[i].value in ("public", "meta"):
            public |= header[i].value == "public"
            meta |= header[i].value == "meta"
            i += 1
        lineno = header[i].line
        i += 1  # import
        import_all = header[i].value == "all"
        i += int(import_all)
        imports.append(Import(canonical_module(header[i].value), public, meta, import_all, lineno))
        i += 1
    ts = tokens(text) if declarations else []
    private_opens = private_open_targets(ts if declarations else iter_tokens(text)) if may_have_private_open(text) else []
    declaration_table: dict[str, dict] = {}
    # Track only namespace/section commands. This deliberately does not claim
    # to reconstruct all elaboration context or infer field/instance exports.
    scopes: list[tuple[str, str, bool]] = []
    namespace, public_section = "", False
    for i, token in enumerate(ts):
        value = token.value
        if token.kind != "code":
            continue
        previous = ts[i - 1].value if i else ""
        following = ts[i + 1] if i + 1 < len(ts) else None
        if value == "namespace" and following:
            scopes.append(("namespace", namespace, public_section))
            namespace = f"{namespace}.{following.value}".strip(".")
        elif value == "section":
            scopes.append(("section", namespace, public_section))
            public_section = False if previous == "private" else public_section or previous == "public"
        elif value == "end" and scopes:
            _, namespace, public_section = scopes.pop()
        elif value in DECLARATIONS and following and is_module_name(following):
            raw = following.value
            name = raw[len("_root_."):] if raw.startswith("_root_.") else f"{namespace}.{raw}".strip(".")
            # Visibility modifiers apply directly to the declaration, possibly
            # with noncomputable/unsafe/partial between modifier and kind.
            preceding = declaration_modifiers(ts, i)
            visibility = "private" if "private" in preceding else "public" if "public" in preceding or public_section else "private"
            declaration_table[name] = {"kind": value, "visibility": visibility, "line": token.line,
                                  "no_expose": "no_expose" in preceding}
    return Source(path, module_from_path(path), any(t.value == "module" for t in header), imports, private_opens, declaration_table)


def source_inventory(root: Path, declaration_paths: set[str] | None = None) -> dict[str, Source]:
    paths = [root / "KIP126.lean", *sorted((root / "KIP126").rglob("*.lean"))]
    return {source.module: source for path in paths if path.is_file()
            for relative in [path.relative_to(root).as_posix()]
            for source in [parse_source(path.read_text(), relative,
                                        declarations=declaration_paths is None or relative in declaration_paths)]}


def owner_for(path: str, registry: dict) -> str | None:
    matches = [rule for rule in registry["ownership"]
               if path == rule["path"] or (rule["path"].endswith("/") and path.startswith(rule["path"]))]
    return max(matches, key=lambda r: len(r["path"]))["owner"] if matches else None


def reachable(graph: dict[str, list[str]], start: str) -> dict[str, str | None]:
    parents: dict[str, str | None] = {start: None}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for target in graph.get(current, []):
            if target not in parents:
                parents[target] = current
                queue.append(target)
    return parents


def path_to(parents: dict[str, str | None], target: str) -> str:
    chain = [target]
    while parents[chain[-1]] is not None:
        chain.append(parents[chain[-1]])
    return " -> ".join(reversed(chain))


def validate(registry: dict, sources: dict[str, Source]) -> dict:
    errors, warnings = [], []
    owners = {row["id"] for row in registry.get("owners", [])}
    expected_owners = {"steenrod", "spectral", "adams", "literature", "computation", "rules", "main"}
    if owners != expected_owners or len(registry.get("owners", [])) != len(owners):
        errors.append("the registry must retain the seven named maintenance owners")
    if registry.get("schema_version") != 1:
        errors.append("unsupported module-boundaries schema_version")
    milestones = registry.get("milestones", [])
    if {m["id"] for m in milestones} != {f"M{i:02}" for i in range(1, 21)} or len(milestones) != 20:
        errors.append("the registry must retain M01 through M20 exactly once")
    contracts = {c["id"]: c for c in registry.get("contracts", [])}
    if len(contracts) != len(registry.get("contracts", [])):
        errors.append("contract IDs must be unique")
    delivery_ids = [d["id"] for d in registry.get("deliveries", [])]
    if len(delivery_ids) != len(set(delivery_ids)):
        errors.append("delivery IDs must be unique")
    entry_ids = set()
    for cid, contract in contracts.items():
        if contract["owner"] not in owners or contract["milestone"] != cid.split(".")[0]:
            errors.append(f"invalid contract owner/milestone: {cid}")
        entry_ids.update(contract.get("nlfl_entry_ids", []))
    assigned = []
    for milestone in milestones:
        for cid in milestone.get("contracts", []):
            assigned.append(cid)
            if cid not in contracts or contracts[cid]["milestone"] != milestone["id"]:
                errors.append(f"unknown or misassigned contract in milestone {milestone['id']}: {cid}")
    if Counter(assigned) != Counter({cid: 1 for cid in contracts}):
        errors.append("each contract must occur exactly once in its milestone")

    allowed = {}
    for exception in registry.get("private_imports", []):
        key = (exception["consumer"], exception["provider"])
        if key in allowed:
            errors.append(f"duplicate private-import registration: {key}")
        if not exception.get("reason", "").strip() or exception.get("classification") not in ("component_internal", "existing_debt", "audit"):
            errors.append(f"private import needs a classification and reason: {key}")
        allowed[key] = exception
    graph, reverse = {}, defaultdict(list)
    private_edges, observed = [], set()
    implementation_only = set(registry.get("implementation_only_modules", []))
    for module in implementation_only - sources.keys():
        errors.append(f"missing implementation-only module: {module}")
    for name, source in sources.items():
        graph[name] = []
        for edge in source.imports:
            if not (edge.target == "KIP126" or edge.target.startswith("KIP126.")):
                continue
            if edge.target not in sources:
                errors.append(f"missing project import {source.path}:{edge.line}: {edge.target}")
                continue
            graph[name].append(edge.target)
            reverse[edge.target].append({"module": name, "mode": edge.mode, "line": edge.line})
            if edge.public and edge.target in implementation_only:
                errors.append(f"implementation-only module is publicly reexported: {source.path}:{edge.line}: {edge.target}")
            if edge.all:
                key = (name, edge.target)
                observed.add(key)
                provider = sources[edge.target]
                consumer_owner, provider_owner = owner_for(source.path, registry), owner_for(provider.path, registry)
                private_edges.append({"consumer": name, "provider": edge.target,
                                      "consumer_owner": consumer_owner, "provider_owner": provider_owner,
                                      "mode": edge.mode, "line": edge.line,
                                      "registration": allowed.get(key)})
                if key not in allowed:
                    crossing = "cross-owner " if consumer_owner != provider_owner else ""
                    errors.append(f"unregistered {crossing}private import {source.path}:{edge.line}: {edge.mode} {edge.target}")
        for target, line in source.private_opens:
            if (target == "KIP126" or target.startswith("KIP126.")) and (name, target) not in observed:
                errors.append(f"open private without registered import all at {source.path}:{line}: {target}")
    for key in allowed.keys() - observed:
        warnings.append(f"retired private-import registration can be removed: {key[0]} -> {key[1]}")

    # A production module cannot borrow a Checks module, even through an
    # innocently named bridge. Use reverse reachability once for all checks.
    def is_checks(name: str) -> bool:
        return name == "KIP126.Checks" or name.startswith("KIP126.Checks.")

    parents: dict[str, str | None] = {name: None for name in sources if is_checks(name)}
    queue = deque(parents)
    while queue:
        current = queue.popleft()
        for importer in reverse.get(current, []):
            name = importer["module"]
            if name not in parents:
                parents[name] = current
                queue.append(name)
    for name in parents:
        # KIP126.lean is the existing full-library/audit root. A production
        # module importing that root is still caught by the same traversal.
        if name != "KIP126" and not is_checks(name):
            errors.append("production import closure reaches Checks: " + " -> ".join(reversed(path_to(parents, name).split(" -> "))))

    deliveries = []
    for delivery in registry.get("deliveries", []):
        did = delivery["id"]
        if delivery.get("contract") not in contracts:
            errors.append(f"unknown delivery contract: {did}")
        own_entry_ids = set(contracts.get(delivery.get("contract"), {}).get("nlfl_entry_ids", []))
        if not delivery.get("nlfl_entry_ids") or any(e not in own_entry_ids for e in delivery.get("nlfl_entry_ids", [])):
            errors.append(f"delivery needs NL-FL entry IDs belonging to its contract: {did}")
        for status in ("mathematical_review", "public_boundary", "build_isolation"):
            if not delivery.get(status, {}).get("status"):
                errors.append(f"missing independent {status} status: {did}")
        if not delivery.get("unfolding_policy", {}).get("description") or not delivery.get("public_environment"):
            errors.append(f"delivery needs unfolding policy and public environment: {did}")
        provider_name = module_from_path(delivery["provider"])
        provider = sources.get(provider_name)
        if provider is None:
            errors.append(f"missing delivery provider: {did}: {delivery['provider']}")
            continue
        if not provider.has_module:
            errors.append(f"public delivery must use module: {did}: {delivery['provider']}")
        for declaration in delivery["declarations"]:
            actual = provider.declarations.get(declaration["name"])
            if actual is None:
                errors.append(f"public delivery declaration not found: {did}: {declaration['name']}")
            elif actual["visibility"] != "public":
                errors.append(f"delivery declaration remains private: {did}: {declaration['name']}")
            elif actual["kind"] != declaration["kind"]:
                errors.append(f"delivery declaration kind changed: {did}: {declaration['name']}")
            elif declaration.get("require_no_expose") and not actual["no_expose"]:
                errors.append(f"hidden definition lost its explicit no_expose policy: {did}: {declaration['name']}")
        for consumer_path in delivery.get("consumers", []):
            consumer_name = module_from_path(consumer_path)
            consumer = sources.get(consumer_name)
            if consumer is None:
                errors.append(f"missing registered consumer: {did}: {consumer_path}")
                continue
            edges = [e for e in consumer.imports if e.target == provider_name]
            if not edges:
                errors.append(f"consumer does not directly import delivery: {did}: {consumer_path}")
            if any(e.all for e in edges) or any(p == provider_name for p, _ in consumer.private_opens):
                errors.append(f"consumer opens delivery implementation: {did}: {consumer_path}")
            # Only public reexports propagate a module's imported environment.
            # An ordinary import of a legitimate provider is the intended
            # boundary; its proof-only imports are not counted as leakage.
            public_graph = {n: [e.target for e in s.imports if e.public and e.target in sources]
                            for n, s in sources.items()}
            public_graph[consumer_name] = [e.target for e in consumer.imports if e.target in sources]
            paths = reachable(public_graph, consumer_name)
            for forbidden in delivery.get("private_implementation", []):
                if forbidden in paths:
                    errors.append(f"consumer can reach private implementation through imports: {did}: {path_to(paths, forbidden)}")
        deliveries.append({"id": did, "provider": provider_name,
                           "registered_consumers": delivery.get("consumers", []),
                           "observed_direct_importers": reverse.get(provider_name, []),
                           "mathematical_review": delivery.get("mathematical_review", {}).get("status"),
                           "public_boundary": delivery.get("public_boundary", {}).get("status"),
                           "build_isolation": delivery.get("build_isolation", {}).get("status")})

    all_edges = [{"consumer": name, **asdict(edge), "mode": edge.mode}
                 for name, source in sources.items() for edge in source.imports]
    return {
        "schema_version": 1, "scope": "source import modes and registered handoffs; not kernel dependencies or compilation evidence",
        "summary": {"source_files": len(sources), "module_files": sum(s.has_module for s in sources.values()),
                    "imports": len(all_edges), "import_modes": dict(sorted(Counter(e["mode"] for e in all_edges).items())),
                    "project_private_imports": len(private_edges),
                    "maintenance_owners": len(owners), "milestones": len(milestones), "contracts": len(contracts),
                    "linked_nlfl_entries": len(entry_ids), "public_deliveries": len(deliveries)},
        "errors": sorted(set(errors)), "warnings": sorted(set(warnings)),
        "deliveries": deliveries, "private_imports": private_edges, "imports": all_edges,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--registry", type=Path, default=REGISTRY)
    parser.add_argument("--check", action="store_true", help="check the registered source boundaries (the default)")
    parser.add_argument("--report", type=Path, help="write the full mode-preserving import inventory as JSON")
    args = parser.parse_args(argv)
    registry_path = args.registry if args.registry.is_absolute() else args.root / args.registry
    try:
        registry = json.loads(registry_path.read_text())
        result = validate(registry, source_inventory(args.root, {d["provider"] for d in registry.get("deliveries", [])}))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"module-boundaries: {error}", file=sys.stderr)
        return 1
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print("module-boundaries: " + json.dumps(result["summary"], ensure_ascii=False, sort_keys=True))
    for warning in result["warnings"]:
        print("warning: " + warning)
    for error in result["errors"]:
        print("error: " + error, file=sys.stderr)
    return bool(result["errors"])


if __name__ == "__main__":
    raise SystemExit(main())
