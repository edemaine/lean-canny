#!/usr/bin/env bash
# Build every library target and run all standalone Lean audits.
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

lake build LeanCanny LeanCannyAlternatives LeanCannyConnectivity \
  LeanCannyCountingHierarchy RealCountingHierarchy --wfail --iofail --fail-fast

checks=(scripts/Check*.lean)
for ((i = 0; i < ${#checks[@]}; i++)); do
  printf '\n[%d/%d] %s\n' "$((i + 1))" "${#checks[@]}" "${checks[i]}"
  lake env lean -DwarningAsError=true "${checks[i]}"
done
printf '\nAll %d audits passed.\n' "${#checks[@]}"
