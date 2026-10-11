#!/usr/bin/env bash
# Compile the original FullInput afresh, then all supplemental augmentation goals.
set -euo pipefail
if [ "$#" -ne 3 ]; then
  printf '%s\n' 'Usage: bash check-augmentation.sh ROOT FULL_INPUT_DIR AUGMENTATION_DIR' >&2
  exit 2
fi
secondary_root=$(cd -- "$1" && pwd -P)
secondary_core=$(cd -- "$2" && pwd -P)
secondary_aug=$(cd -- "$3" && pwd -P)
secondary_package="$secondary_root/KIP126/LinProgram/Translate/secondary-seed5487-certificates"
cd -- "$secondary_root"
python3 -B "$secondary_package/augmentation.py" --root "$secondary_root" \
  --full-input-dir "$secondary_core" --output-dir "$secondary_aug" --check
lake build +KIP126.LinProgram.Certificates.Secondary.Augmentation:olean
secondary_verify=$(mktemp -d "$secondary_aug/kernel-check.XXXXXX")
lake env bash -s -- "$secondary_verify" "$secondary_core" "$secondary_aug" <<'LEAN'
set -euo pipefail
secondary_verify=$1
secondary_core=$2
secondary_aug=$3
mkdir -p "$secondary_verify/lib/lean" "$secondary_verify/logs"
export LEAN_PATH="$secondary_verify/lib/lean:$LEAN_PATH"
secondary_module='KIP126/LinProgram/Certificates/Secondary/Seed5487/FullInput'
mkdir -p "$(dirname "$secondary_verify/lib/lean/$secondary_module.olean")"
lean --root="$secondary_core/src" -o "$secondary_verify/lib/lean/$secondary_module.olean" \
  "$secondary_core/src/$secondary_module.lean" > "$secondary_verify/logs/FullInput.log" 2>&1
for secondary_part in Data Proofs Checks; do
  secondary_module="KIP126/LinProgram/Certificates/Secondary/Seed5487/Augmentation/$secondary_part"
  mkdir -p "$(dirname "$secondary_verify/lib/lean/$secondary_module.olean")"
  lean --root="$secondary_aug/src" -o "$secondary_verify/lib/lean/$secondary_module.olean" \
    "$secondary_aug/src/$secondary_module.lean" > "$secondary_verify/logs/$secondary_part.log" 2>&1
done
LEAN
python3 -B "$secondary_package/augmentation.py" --root "$secondary_root" \
  --full-input-dir "$secondary_core" --output-dir "$secondary_aug" --check
printf 'Augmentation kernel checks passed; fresh artifacts and logs: %s\n' "$secondary_verify"
