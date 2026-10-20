#!/usr/bin/env bash
set -euo pipefail
proof_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$proof_root/scripts/export_proof_bundle.py" "$@"
