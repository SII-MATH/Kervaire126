#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PYTHONDONTWRITEBYTECODE=1

python3 scripts/check_source_inventory.py
python3 scripts/check_external_inputs.py
python3 -m unittest \
  scripts.test_stage_boundary_layout \
  scripts.test_external_inputs \
  scripts.test_check_source_inventory \
  scripts.test_blueprint_frontier
python3 scripts/test-import-lin-selected.py
python3 KIP126/LinProgram/Translate/import-proofs.py --self-test
python3 scripts/blueprint_frontier.py --output-dir metrics/frontier
