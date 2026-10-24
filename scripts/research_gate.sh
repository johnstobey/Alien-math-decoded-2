#!/usr/bin/env bash
set -euo pipefail
expected_root=/workspace/Alien-math-decoded-2
[[ "$PWD" == "$expected_root" ]] || { printf 'ERROR unexpected_working_directory\n'; exit 64; }
[[ $# -ge 4 && "$3" == -- ]] || { printf 'usage: bash scripts/research_gate.sh GATE MODULE -- COMMAND [ARG...]\n'; exit 64; }
gate=$1
module=$2
shift 3
[[ "$gate" =~ ^[A-Za-z0-9_-]+$ && -f "$module" ]] || { printf 'ERROR invalid_gate_or_module\n'; exit 64; }
# Keep credential-bearing service and diagnostic commands outside proof logs.
allowed=false
if [[ $# -eq 2 && "$1" == lake && "$2" == build ]]; then allowed=true; fi
if [[ $# -eq 3 && "$1" == lake && "$2" == exe && "$3" == verifyPipeline ]]; then allowed=true; fi
if [[ $# -eq 4 && "$1" == lake && "$2" == env && "$3" == lean && "$4" == "$module" && "$module" == *.lean ]]; then allowed=true; fi
if [[ $# -eq 2 && "$1" == python3 && ( "$2" == scripts/audit.py || "$2" == scripts/audit_phase_alignment.py ) ]]; then allowed=true; fi
if [[ $# -eq 3 && "$1" == python3 && "$2" == scripts/generate_incremental_proofs.py && "$3" == --check ]]; then allowed=true; fi
if [[ $# -eq 2 && "$1" == node && "$2" == scripts/cipher-fixtures.mjs ]]; then allowed=true; fi
[[ "$allowed" == true ]] || { printf 'ERROR unsupported_gate_command\n'; exit 64; }
export ELAN_HOME=/workspace/.onboarding/elan
export XDG_CACHE_HOME=/workspace/.onboarding/cache
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p .lake/research-logs
run_id=$(date -u +%Y%m%dT%H%M%S)-$$
log=".lake/research-logs/$gate-$run_id.log"
receipt=".lake/research-logs/$gate-$run_id.receipt"
commit=$(git rev-parse HEAD)
printf 'gate_name=%s\nmodule=%s\ngit_commit_id=%s\nlog_file_path=%s\nstatus=INCOMPLETE\n' "$gate" "$module" "$commit" "$log" > "$receipt"
{ lean --version; lake --version; } > "$log"
set +e
"$@" >> "$log" 2>&1
gate_status=$?
set -e
if [[ $gate_status -eq 0 ]]; then result=PASS; else result=FAIL; fi
printf 'status=%s\nexit_status=%s\n' "$result" "$gate_status" >> "$receipt"
if [[ $gate_status -eq 0 ]]; then
  printf 'first_actionable_diagnostic=none\n' >> "$receipt"
else
  first_diagnostic=$(rg -m 1 'error:|Error|Exception|Traceback|FAIL' "$log" || true)
  printf 'first_actionable_diagnostic=%s\n' "${first_diagnostic:-see_log}" >> "$receipt"
fi
sed -i '/^status=INCOMPLETE$/d' "$receipt"
audit_summary=$(rg '^AUDIT PASSED:|^PHASE AUDIT PASSED:|^PIPELINE PASS:|^PASSED:' "$log" || true)
if [[ -n "$audit_summary" ]]; then printf '%s\n' "$audit_summary" >> "$receipt"; fi
if [[ $gate_status -eq 0 && "$audit_summary" =~ PASSED:\ ([0-9]+) ]]; then
  printf 'audited_declaration_count=%s\nunexpected_axiom_count=0\n' "${BASH_REMATCH[1]}" >> "$receipt"
else
  printf 'audited_declaration_count=not_applicable\nunexpected_axiom_count=not_audited\n' >> "$receipt"
fi
cat "$receipt"
if [[ $gate_status -ne 0 ]]; then tail -15 "$log"; fi
exit "$gate_status"
