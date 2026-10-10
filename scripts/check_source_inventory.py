#!/usr/bin/env python3
"""Validate the KIP126 source inventory.

The inventory is deliberately checked outside Lean: source acquisition state,
filesystem paths, and cryptographic hashes are properties of the checkout, not
mathematical propositions.  The checker has no third-party dependencies and is
safe to run from any working directory::

    python3 scripts/check_source_inventory.py

Use ``--root`` when checking a copied checkout and ``--inventory`` when
checking a fixture or an alternate inventory.  A non-zero exit status means
that the inventory cannot currently be trusted as a complete, aligned ledger.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping


SCHEMA_VERSION = 3
HASH_CHUNK_SIZE = 1024 * 1024
EXPECTED_ARTIFACT_KINDS_BY_NAME: dict[str, set[str]] = {
    "main.tex": {"tex"},
    "112.tex": {"tex"},
    "main.bib": {"bibliography"},
    "main.bbl": {"bibliography"},
    "citation.bib": {"citation"},
    "source-status.json": {"status"},
    "openalex.json": {"metadata"},
    "semantic-scholar.json": {"metadata"},
    "paper.pdf": {"pdf"},
    "paper.txt": {"text"},
    "arxiv-source": {"source_archive"},
    "zenodo-record.json": {"machine_metadata"},
    "lin-program-page.html": {"machine_artifact"},
    "lin-plot.html": {"machine_artifact"},
}

ACQUISITION_STATES: dict[str, set[str]] = {
    "open_pdf": {"downloaded", "unavailable", "missing"},
    "plain_text": {"extracted", "unavailable", "missing"},
    "arxiv_source": {"downloaded", "unavailable", "missing"},
    "openalex_metadata": {"downloaded", "unavailable", "missing"},
    "semantic_scholar_metadata": {"downloaded", "unavailable", "missing"},
}


def strip_unescaped_percent_comments(text: str) -> str:
    """Remove TeX/BibTeX comments while preserving line boundaries."""

    code_lines: list[str] = []
    for line in text.splitlines():
        end = len(line)
        for index, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                end = index
                break
        code_lines.append(line[:end])
    return "\n".join(code_lines)


ID_RE = re.compile(r"^[a-z][a-z0-9_]*$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
LINE_SEPARATORS = {0x85, 0x2028, 0x2029}
ALLOWED_KINDS = {"paper", "literature", "machine", "source_group"}
ALLOWED_ARTIFACT_KINDS = {
    "citation",
    "bibliography",
    "status",
    "metadata",
    "machine_metadata",
    "machine_artifact",
    "source_archive",
    "pdf",
    "text",
    "tex",
}
ALLOWED_STATUS_CLASSES = {
    "source_of_record",
    "full_text",
    "metadata_only",
    "partial",
}

EXPECTED_KINDS = {
    "aim_paper": "paper",
    "lwx_machine": "machine",
}

REQUIRED_SOURCE_FIELDS = {
    "id",
    "directory",
    "kind",
    "citation_keys",
    "title",
    "year",
    "canonical_url",
    "role",
    "status_file",
    "status_class",
    "availability",
    "artifacts",
}
REQUIRED_ARTIFACT_FIELDS = {"path", "kind", "required", "sha256"}
AVAILABILITY_FIELDS = {"metadata", "pdf", "text", "source"}


def _sha256_file(path: Path) -> str:
    """Hash a file incrementally so large artifacts do not fill memory."""

    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(HASH_CHUNK_SIZE), b""):
            digest.update(chunk)
    return digest.hexdigest()


class InventoryValidator:
    """Collect validation errors without raising on the first malformed row."""

    def __init__(
        self,
        root: Path,
        inventory_path: Path,
    ):
        self.root = root.resolve()
        self.inventory_path = inventory_path.resolve()
        self.errors: list[str] = []
        self.source_count = 0
        self.artifact_count = 0
        self.artifact_paths: dict[str, str] = {}

    def error(self, where: str, message: str) -> None:
        self.errors.append(f"{where}: {message}")

    def validate(self) -> list[str]:
        document = self._load_inventory()
        if document is None:
            return self.errors
        if not isinstance(document, Mapping):
            self.error("inventory", "top level must be a JSON object")
            return self.errors

        self._check_top_level(document)
        sources = document.get("sources")
        if not isinstance(sources, list):
            self.error("inventory.sources", "must be a non-empty array")
            return self.errors
        if not sources:
            self.error("inventory.sources", "must not be empty")
            return self.errors

        self._check_source_layout(sources)
        self.source_count = len(sources)
        ids: set[str] = set()
        directories: set[str] = set()
        citation_keys: dict[str, str] = {}
        for index, raw_source in enumerate(sources):
            where = f"sources[{index}]"
            if not isinstance(raw_source, Mapping):
                self.error(where, "must be a JSON object")
                continue
            source = dict(raw_source)
            self._check_unknown_empty_fields(source, where, REQUIRED_SOURCE_FIELDS)
            source_id = self._string(source, "id", where)
            directory = source.get("directory")
            if directory is not None and (not isinstance(directory, str) or not directory.strip()):
                self.error(f"{where}.directory", "must be null or a non-empty path")
                directory = None
            if source_id is not None:
                if not ID_RE.fullmatch(source_id):
                    self.error(f"{where}.id", "must use canonical snake_case")
                if source_id in ids:
                    self.error(f"{where}.id", f"duplicate source id {source_id!r}")
                ids.add(source_id)
            if directory is not None:
                if directory in directories:
                    self.error(f"{where}.directory", f"duplicate directory {directory!r}")
                directories.add(directory)
            self._check_source(source, where, source_id, directory, citation_keys)

        return self.errors

    def _load_inventory(self) -> Any | None:
        try:
            with self.inventory_path.open("r", encoding="utf-8") as stream:
                return json.load(stream)
        except FileNotFoundError:
            self.error("inventory", f"file not found: {self.inventory_path}")
        except UnicodeError as exc:
            self.error("inventory", f"cannot decode file: {exc}")
        except json.JSONDecodeError as exc:
            self.error("inventory", f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}")
        except ValueError as exc:
            self.error("inventory", f"invalid JSON value: {exc}")
        except OSError as exc:
            self.error("inventory", f"cannot read file: {exc}")
        return None

    def _check_top_level(self, document: Mapping[str, Any]) -> None:
        version = document.get("schema_version")
        # In Python, `True == 1` and `1.0 == 1`; neither is a valid schema
        # version.  Require the JSON integer type explicitly.
        if isinstance(version, bool) or not isinstance(version, int) or version != SCHEMA_VERSION:
            self.error("inventory.schema_version", f"expected {SCHEMA_VERSION}, got {version!r}")
        project = document.get("project")
        if not isinstance(project, str) or not project.strip():
            self.error("inventory.project", "must be a non-empty string")
        elif project != "KIP126":
            self.error("inventory.project", f"expected 'KIP126', got {project!r}")

    def _check_source_layout(self, sources: list[Any]) -> None:
        """Ensure every retained source-status file has a catalogue slot."""
        status_dirs = {
            path.parent.relative_to(self.root).as_posix()
            for path in self.root.glob("Source/*/source-status.json")
        }
        expected_dirs = {s["directory"] for s in sources if isinstance(s, Mapping)
                         and isinstance(s.get("directory"), str) and s.get("status_file")}
        missing_dirs = sorted(expected_dirs - status_dirs)
        unexpected_dirs = sorted(status_dirs - expected_dirs)
        if missing_dirs:
            self.error("Source", "missing expected source-status.json: " + ", ".join(missing_dirs))
        if unexpected_dirs:
            self.error("Source", "source-status.json has no inventory entry: " + ", ".join(unexpected_dirs))

    def _check_source(
        self,
        source: Mapping[str, Any],
        where: str,
        source_id: str | None,
        directory: str | None,
        citation_keys: dict[str, str],
    ) -> None:
        if source_id is None:
            return
        directory_path = self._safe_path(directory, f"{where}.directory") if directory else None
        if directory_path is not None and not directory_path.is_dir():
            self.error(f"{where}.directory", f"directory does not exist: {directory}")

        kind = self._string(source, "kind", where)
        if kind is not None and kind not in ALLOWED_KINDS:
            self.error(f"{where}.kind", f"unknown kind {kind!r}")
        expected_kind = EXPECTED_KINDS.get(source_id)
        if expected_kind is not None and kind != expected_kind:
            self.error(f"{where}.kind", f"expected {expected_kind!r} for {source_id!r}")
        status_class = self._string(source, "status_class", where)
        if status_class is not None and status_class not in ALLOWED_STATUS_CLASSES:
            self.error(f"{where}.status_class", f"unknown status class {status_class!r}")
        self._check_scalar_metadata(source, where)

        keys = source.get("citation_keys")
        if not isinstance(keys, list) or (source.get("status_file") and not keys):
            self.error(f"{where}.citation_keys", "must be an array, non-empty for acquisition records")
            keys = []
        local_keys: set[str] = set()
        for key_index, key in enumerate(keys):
            key_where = f"{where}.citation_keys[{key_index}]"
            if not isinstance(key, str) or not key.strip():
                self.error(key_where, "must be a non-empty string")
                continue
            if key in local_keys:
                self.error(key_where, f"duplicate citation key {key!r} in source")
            local_keys.add(key)
            previous = citation_keys.get(key)
            if previous is not None and previous != source_id:
                self.error(key_where, f"citation key {key!r} is also assigned to {previous!r}")
            citation_keys[key] = source_id

        status_file_value = source.get("status_file")
        is_project_source = source_id == "aim_paper"
        status: Mapping[str, Any] | None = None
        if is_project_source:
            if status_file_value is not None:
                self.error(f"{where}.status_file", "aim_paper must not claim a source-status.json")
            self._check_citation_file(self.root / "MainPaper/main.bib", where, keys)
        elif status_file_value is not None:
            expected_status = f"{directory}/source-status.json"
            if not isinstance(status_file_value, str) or not status_file_value.strip():
                self.error(f"{where}.status_file", "must name source-status.json")
            elif status_file_value != expected_status:
                self.error(f"{where}.status_file", f"expected {expected_status!r}")
            status_path = self._safe_path(status_file_value, f"{where}.status_file")
            if status_path is not None:
                status = self._check_status_file(status_path, source, where, keys)

        if source.get("bibliography_file"):
            bibliography = self._safe_path(source["bibliography_file"], f"{where}.bibliography_file")
            if bibliography:
                self._check_citation_file(bibliography, where, keys)
        self._check_availability(source, where, source_id, directory)
        self._check_artifacts(source, where, is_project_source, status)

    def _check_scalar_metadata(self, source: Mapping[str, Any], where: str) -> None:
        title = source.get("title")
        if not isinstance(title, str) or not title.strip():
            self.error(f"{where}.title", "must be a non-empty string")
        year = source.get("year")
        if year is None and source.get("kind") == "source_group":
            pass
        elif isinstance(year, bool) or not isinstance(year, int) or not (1800 <= year <= 2100):
            self.error(f"{where}.year", "must be an integer year between 1800 and 2100")
        for field in ("canonical_url", "role"):
            value = source.get(field)
            if not isinstance(value, str) or not value.strip():
                self.error(f"{where}.{field}", "must be a non-empty string")
        if "doi" in source:
            doi = source["doi"]
            if not isinstance(doi, str) or not doi.strip():
                self.error(f"{where}.doi", "must be a non-empty string when supplied")

    def _check_status_file(
        self,
        status_path: Path,
        source: Mapping[str, Any],
        where: str,
        citation_keys: Iterable[Any],
    ) -> Mapping[str, Any] | None:
        if not status_path.is_file():
            self.error(f"{where}.status_file", f"file does not exist: {status_path.relative_to(self.root)}")
            return None
        try:
            with status_path.open("r", encoding="utf-8") as stream:
                status = json.load(stream)
        except (OSError, UnicodeError) as exc:
            self.error(f"{where}.status_file", f"cannot read status file: {exc}")
            return None
        except json.JSONDecodeError as exc:
            self.error(f"{where}.status_file", f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}")
            return None
        if not isinstance(status, Mapping):
            self.error(f"{where}.status_file", "status file must contain an object")
            return None
        for field, allowed in ACQUISITION_STATES.items():
            if field not in status:
                continue
            value = status[field]
            if not isinstance(value, str):
                self.error(f"{where}.status_file.{field}", "must be a status string")
            elif value not in allowed and not value.startswith("failed"):
                self.error(
                    f"{where}.status_file.{field}",
                    f"unknown status {value!r}; expected one of {sorted(allowed)!r} or failed...",
                )
        bib_key = status.get("bib_key")
        if not isinstance(bib_key, str) or not bib_key.strip():
            self.error(f"{where}.status_file.bib_key", "must be a non-empty string")
        elif bib_key not in citation_keys:
            self.error(f"{where}.status_file.bib_key", f"{bib_key!r} is absent from citation_keys")
        grouped = status.get("grouped_bib_keys", [])
        if not isinstance(grouped, list):
            self.error(f"{where}.status_file.grouped_bib_keys", "must be an array when supplied")
        else:
            seen: set[str] = set()
            for i, key in enumerate(grouped):
                item_where = f"{where}.status_file.grouped_bib_keys[{i}]"
                if not isinstance(key, str) or not key.strip():
                    self.error(item_where, "must be a non-empty string")
                    continue
                if key in seen:
                    self.error(item_where, f"duplicate grouped citation key {key!r}")
                seen.add(key)
                if key not in citation_keys:
                    self.error(item_where, f"{key!r} is absent from citation_keys")
        status_doi = status.get("doi")
        inventory_doi = source.get("doi")
        if status_doi is not None:
            if not isinstance(status_doi, str) or not status_doi.strip():
                self.error(f"{where}.status_file.doi", "must be a non-empty string when supplied")
            elif not isinstance(inventory_doi, str) or not inventory_doi.strip():
                self.error(f"{where}.doi", "inventory must copy the DOI from source-status.json")
            elif self._normalise_doi(status_doi) != self._normalise_doi(inventory_doi):
                self.error(
                    f"{where}.doi",
                    f"does not match source-status.json ({inventory_doi!r} vs {status_doi!r})",
                )
        self._check_citation_file(status_path.parent / "citation.bib", where, citation_keys)
        # A downloaded/extracted claim must have its corresponding local file.
        directory = status_path.parent
        claims = {
            "open_pdf": ("downloaded", directory / "paper.pdf"),
            "plain_text": ("extracted", directory / "paper.txt"),
            "arxiv_source": ("downloaded", directory / "arxiv-source"),
            "openalex_metadata": ("downloaded", directory / "openalex.json"),
            "semantic_scholar_metadata": ("downloaded", directory / "semantic-scholar.json"),
        }
        for key, (expected, artifact) in claims.items():
            if status.get(key) == expected and not artifact.exists():
                self.error(
                    f"{where}.status_file.{key}",
                    f"claims {expected!r} but {artifact.relative_to(self.root)} is missing",
                )
            if (
                status.get(key, "")
                and isinstance(status.get(key), str)
                and (
                    status[key].startswith("failed")
                    or status[key] in {"unavailable", "missing"}
                )
                and artifact.exists()
            ):
                self.error(
                    f"{where}.status_file.{key}",
                    f"claims {status[key]!r} but {artifact.relative_to(self.root)} exists",
                )
        return status

    def _check_citation_file(self, citation_path: Path, where: str, citation_keys: Iterable[Any]) -> None:
        if not citation_path.is_file():
            self.error(f"{where}.citation", f"file does not exist: {citation_path.relative_to(self.root)}")
            return
        try:
            citation_text = citation_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            self.error(f"{where}.citation", f"cannot read citation file: {exc}")
            return
        citation_text = strip_unescaped_percent_comments(citation_text)
        for key in citation_keys:
            # BibTeX permits both ``@article{Key,`` and ``@article {Key,``
            # (and arbitrary whitespace).
            pattern = rf"@[^{{]+\{{\s*{re.escape(str(key))}\s*[,}}]"
            if re.search(pattern, citation_text) is None:
                self.error(f"{where}.citation", f"citation key {key!r} is not present in citation file")

    def _check_availability(self, source: Mapping[str, Any], where: str, source_id: str, directory: str) -> None:
        availability = source.get("availability")
        if not isinstance(availability, Mapping):
            self.error(f"{where}.availability", "must be an object")
            return
        missing_fields = AVAILABILITY_FIELDS - set(availability)
        extra_fields = set(availability) - AVAILABILITY_FIELDS
        for field in sorted(missing_fields):
            self.error(f"{where}.availability", f"missing field {field!r}")
        for field in sorted(extra_fields):
            self.error(f"{where}.availability.{field}", "unknown field")
        for field in AVAILABILITY_FIELDS:
            if field in availability and not isinstance(availability[field], bool):
                self.error(f"{where}.availability.{field}", "must be boolean")

        if source_id == "aim_paper":
            expected = {
                "metadata": (self.root / "MainPaper/main.bib").is_file(),
                "pdf": (self.root / "MainPaper/2412.10879.pdf").is_file(),
                "text": (self.root / "MainPaper/main.tex").is_file(),
                "source": (self.root / "MainPaper/main.tex").is_file(),
            }
        elif source.get("status_file"):
            status_path = self.root / directory / "source-status.json"
            try:
                status = json.loads(status_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, json.JSONDecodeError):
                return
            if not isinstance(status, Mapping):
                # `_check_status_file` reports the same malformed status file;
                # this guard prevents the availability pass from calling `.get`
                # on a list, string, or scalar.
                self.error(f"{where}.status_file", "status file must contain an object")
                return
            expected = {
                "metadata": status.get("openalex_metadata") == "downloaded"
                or status.get("semantic_scholar_metadata") == "downloaded",
                "pdf": status.get("open_pdf") == "downloaded",
                "text": status.get("plain_text") == "extracted",
                "source": status.get("arxiv_source") == "downloaded",
            }
        else:
            artifacts = source.get("artifacts", [])
            kinds = {a.get("kind") for a in artifacts if isinstance(a, Mapping)} if isinstance(artifacts, list) else set()
            expected = {"metadata": "metadata" in kinds, "pdf": "pdf" in kinds,
                        "text": bool(kinds & {"text", "tex"}), "source": "source_archive" in kinds}
        expected_class = self._status_class_for(source_id, expected)
        declared_class = source.get("status_class")
        if declared_class != expected_class:
            self.error(
                f"{where}.status_class",
                f"does not agree with local availability (expected {expected_class!r})",
            )
        for field, value in expected.items():
            if field in availability and availability[field] != value:
                self.error(f"{where}.availability.{field}", f"does not agree with source status (expected {value})")

    @staticmethod
    def _status_class_for(source_id: str, availability: Mapping[str, bool]) -> str:
        if source_id == "aim_paper":
            return "source_of_record"
        if availability.get("pdf") and availability.get("text"):
            return "full_text"
        if (
            availability.get("metadata")
            and not availability.get("pdf")
            and not availability.get("text")
            and not availability.get("source")
        ):
            return "metadata_only"
        return "partial"

    def _check_artifacts(
        self,
        source: Mapping[str, Any],
        where: str,
        is_project_source: bool,
        status: Mapping[str, Any] | None,
    ) -> None:
        artifacts = source.get("artifacts")
        if not isinstance(artifacts, list) or (source.get("status_file") and not artifacts):
            self.error(f"{where}.artifacts", "must be an array, non-empty for acquisition records")
            return
        seen: set[str] = set()
        for index, raw_artifact in enumerate(artifacts):
            artifact_where = f"{where}.artifacts[{index}]"
            if not isinstance(raw_artifact, Mapping):
                self.error(artifact_where, "must be a JSON object")
                continue
            artifact = dict(raw_artifact)
            self._check_unknown_empty_fields(artifact, artifact_where, REQUIRED_ARTIFACT_FIELDS)
            artifact_kind = artifact.get("kind")
            if not isinstance(artifact_kind, str) or artifact_kind not in ALLOWED_ARTIFACT_KINDS:
                self.error(f"{artifact_where}.kind", f"unknown artifact kind {artifact_kind!r}")
            path_value = artifact.get("path")
            if not isinstance(path_value, str) or not path_value.strip():
                self.error(f"{artifact_where}.path", "must be a non-empty string")
                continue
            expected_kinds = EXPECTED_ARTIFACT_KINDS_BY_NAME.get(PurePosixPath(path_value).name)
            if expected_kinds is not None and artifact_kind not in expected_kinds:
                self.error(
                    f"{artifact_where}.kind",
                    f"path {path_value!r} requires kind in {sorted(expected_kinds)!r}",
                )
            if path_value in seen:
                self.error(f"{artifact_where}.path", f"duplicate artifact path {path_value!r}")
            seen.add(path_value)
            directory = str(source.get("directory", "")).rstrip("/")
            if directory and not path_value.startswith(directory + "/"):
                self.error(
                    f"{artifact_where}.path",
                    f"artifact must be inside source directory {directory!r}",
                )
            previous_source = self.artifact_paths.get(path_value)
            if previous_source is not None and previous_source != where:
                self.error(
                    f"{artifact_where}.path",
                    f"artifact path is already assigned to {previous_source}",
                )
            self.artifact_paths[path_value] = where
            path = self._safe_path(path_value, f"{artifact_where}.path")
            if path is None:
                continue
            if directory:
                try:
                    resolved_directory = (self.root / Path(*PurePosixPath(directory).parts)).resolve()
                except (OSError, RuntimeError, UnicodeError) as exc:
                    self.error(f"{artifact_where}.path", f"cannot resolve source directory: {exc}")
                    continue
                try:
                    path.relative_to(resolved_directory)
                except ValueError:
                    self.error(
                        f"{artifact_where}.path",
                        f"artifact resolves outside source directory {directory!r}",
                    )
            required = artifact.get("required")
            if not isinstance(required, bool):
                self.error(f"{artifact_where}.required", "must be boolean")
            sha256 = artifact.get("sha256")
            valid_hash = isinstance(sha256, str) and SHA256_RE.fullmatch(sha256) is not None
            if not valid_hash:
                self.error(f"{artifact_where}.sha256", "must be a lowercase SHA-256 digest")
            try:
                exists = path.exists()
                is_file = path.is_file() if exists else False
            except (OSError, UnicodeError) as exc:
                self.error(f"{artifact_where}.path", f"cannot inspect artifact: {exc}")
                self.artifact_count += 1
                continue
            if not exists:
                if required is True:
                    self.error(f"{artifact_where}.path", f"required artifact does not exist: {path_value}")
                # An optional artifact may be absent in a lean checkout.  Its
                # digest is still checked whenever the file is present.
                self.artifact_count += 1
                continue
            if not is_file:
                self.error(
                    f"{artifact_where}.path",
                    f"artifact must be a regular file: {path_value}",
                )
                self.artifact_count += 1
                continue
            if valid_hash:
                try:
                    digest = _sha256_file(path)
                except (OSError, UnicodeError) as exc:
                    self.error(f"{artifact_where}.sha256", f"cannot hash artifact: {exc}")
                    self.artifact_count += 1
                    continue
                if digest != sha256:
                    self.error(
                        f"{artifact_where}.sha256",
                        f"hash mismatch for {path_value} (expected {sha256}, got {digest})",
                    )
            self.artifact_count += 1

        artifact_by_path = {
            a.get("path"): a for a in artifacts
            if isinstance(a, Mapping) and isinstance(a.get("path"), str)
        }
        if is_project_source:
            # The checked-in target paper is the source of record.  These four
            # files are the minimum auditable project-source inputs.
            required_project_paths = (
                "MainPaper/main.tex",
                "MainPaper/112.tex",
                "MainPaper/main.bib",
                "MainPaper/2412.10879.pdf",
            )
            for required_name in required_project_paths:
                row = artifact_by_path.get(required_name)
                if row is None:
                    self.error(
                        f"{where}.artifacts",
                        f"missing required source-of-record artifact {required_name!r}",
                    )
                elif row.get("required") is not True:
                    self.error(
                        f"{where}.artifacts",
                        f"source-of-record artifact {required_name!r} must have required=true",
                    )
        elif source.get("status_file"):
            # Every acquisition row must expose both its citation and status file
            # as explicit required artefacts.  This prevents a valid-looking
            # row from hiding the authoritative acquisition record.
            paths = set(artifact_by_path)
            directory = source.get("directory")
            for required_name in (f"{directory}/citation.bib", f"{directory}/source-status.json"):
                if required_name not in paths:
                    self.error(f"{where}.artifacts", f"missing required catalogue artifact {required_name!r}")
                elif artifact_by_path[required_name].get("required") is not True:
                    self.error(
                        f"{where}.artifacts",
                        f"catalogue artifact {required_name!r} must have required=true",
                    )
            if isinstance(status, Mapping):
                claims = {
                    "open_pdf": ("downloaded", f"{directory}/paper.pdf"),
                    "plain_text": ("extracted", f"{directory}/paper.txt"),
                    "arxiv_source": ("downloaded", f"{directory}/arxiv-source"),
                    "openalex_metadata": ("downloaded", f"{directory}/openalex.json"),
                    "semantic_scholar_metadata": ("downloaded", f"{directory}/semantic-scholar.json"),
                }
                for key, (expected, required_path) in claims.items():
                    if status.get(key) == expected and required_path not in paths:
                        self.error(
                            f"{where}.artifacts",
                            f"{key}={expected!r} requires artifact {required_path!r}",
                        )
                    elif status.get(key) == expected:
                        claimed_artifact = artifact_by_path.get(required_path)
                        if isinstance(claimed_artifact, Mapping) and claimed_artifact.get("required") is not True:
                            self.error(
                                f"{where}.artifacts",
                                f"status-claimed artifact {required_path!r} must have required=true",
                            )

    def _check_unknown_empty_fields(
        self, value: Mapping[str, Any], where: str, required_fields: set[str]
    ) -> None:
        # Unknown keys are allowed for forward-compatible notes, but an empty
        # value in a declared field is almost always an accidental stub.
        for field in required_fields:
            if field not in value:
                self.error(where, f"missing field {field!r}")
        for field, item in value.items():
            if field in {"doi", "status_file"} and item is None:
                continue
            if isinstance(item, str) and not item.strip():
                self.error(f"{where}.{field}", "must not be empty")

    def _string(self, value: Mapping[str, Any], field: str, where: str) -> str | None:
        item = value.get(field)
        if not isinstance(item, str) or not item.strip():
            self.error(f"{where}.{field}", "must be a non-empty string")
            return None
        return item

    def _safe_path(self, value: Any, where: str) -> Path | None:
        if not isinstance(value, str) or not value.strip():
            self.error(where, "must be a non-empty relative path")
            return None
        raw_components = value.split("/")
        if any(component in {"", ".", ".."} for component in raw_components):
            self.error(
                where,
                "must be a safe relative path without empty, '.' or '..' components",
            )
            return None
        if any(ord(char) < 32 or ord(char) == 127 for char in value):
            self.error(where, "must not contain ASCII control characters")
            return None
        if any(ord(char) in LINE_SEPARATORS for char in value):
            self.error(where, "must not contain non-ASCII line separators")
            return None
        candidate = PurePosixPath(value)
        if candidate.is_absolute() or "\\" in value:
            self.error(where, "must be a relative path without backslashes")
            return None
        try:
            path = (self.root / Path(*candidate.parts)).resolve()
        except (OSError, RuntimeError, UnicodeError) as exc:
            self.error(where, f"cannot resolve path: {exc}")
            return None
        try:
            path.relative_to(self.root)
        except ValueError:
            self.error(where, "resolves outside repository root")
            return None
        return path

    @staticmethod
    def _normalise_doi(value: Any) -> str:
        if not isinstance(value, str):
            return ""
        value = value.strip()
        value = re.sub(r"^https?://(?:dx\.)?doi\.org/", "", value, flags=re.IGNORECASE)
        return value.rstrip("/").lower()


def validate_inventory(
    root: Path,
    inventory_path: Path | None = None,
) -> list[str]:
    """Return validation errors for callers that want a library API."""

    root = root.resolve()
    if inventory_path is None:
        inventory_path = root / "docs/external-inputs.json"
    return InventoryValidator(root, inventory_path).validate()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=None, help="repository root (default: parent of this script)")
    parser.add_argument(
        "--inventory",
        type=Path,
        default=None,
        help="inventory JSON path (default: docs/external-inputs.json)",
    )
    args = parser.parse_args(argv)

    script_root = Path(__file__).resolve().parents[1]
    root = (args.root or script_root).resolve()
    inventory = args.inventory
    if inventory is None:
        inventory = root / "docs/external-inputs.json"
    elif not inventory.is_absolute():
        inventory = root / inventory

    validator = InventoryValidator(root, inventory)
    errors = validator.validate()
    if errors:
        print(f"source inventory: {len(errors)} error(s)", file=sys.stderr)
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"source inventory: OK ({validator.source_count} sources, {validator.artifact_count} artifacts)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
