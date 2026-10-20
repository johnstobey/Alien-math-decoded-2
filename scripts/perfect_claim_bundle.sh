#!/usr/bin/env bash
# Builds an audit archive; does not submit or certify an institutional prize claim.
set -euo pipefail
proof_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$proof_root/scripts/export_proof_bundle.py" --translation "$@"
