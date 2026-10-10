#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

required_version="$(sed -n 's/^leanblueprint==//p' requirements-blueprint.txt)"
installed_version="$(python3 -c 'from importlib.metadata import version; print(version("leanblueprint"))')"
if [[ "$installed_version" != "$required_version" ]]; then
  echo "Expected leanblueprint $required_version, found ${installed_version:-unknown}." >&2
  echo "Install the pinned renderer with: python3 -m pip install --user -r requirements-blueprint.txt" >&2
  exit 1
fi

manifest=blueprint/lean_decls

leanblueprint web

if [[ ! -s "$manifest" ]]; then
  echo "$manifest was not generated or is empty." >&2
  exit 1
fi

lake exe checkdecls "$manifest"
