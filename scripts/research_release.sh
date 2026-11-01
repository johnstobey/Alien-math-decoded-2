#!/usr/bin/env bash
set -euo pipefail
[[ "$PWD" == /workspace/Alien-math-decoded-2 ]] || exit 64
[[ $(git branch --show-current) == research/dual-ring-invariant-program ]] || exit 65
[[ -z $(git status --porcelain) ]] || { printf 'ERROR uncommitted_changes\n'; exit 65; }
git_commit=$(git rev-parse HEAD)
[[ -f .lake/research-logs/release-approved-commit ]] || { printf 'ERROR missing_release_gate_receipt\n'; exit 65; }
[[ $(cat .lake/research-logs/release-approved-commit) == "$git_commit" ]] || { printf 'ERROR stale_release_gate_receipt\n'; exit 65; }
git push -u origin HEAD:refs/heads/research/dual-ring-invariant-program
