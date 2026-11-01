#!/usr/bin/env bash
set -euo pipefail
[[ "$PWD" == /workspace/Alien-math-decoded-2 ]] || exit 64
git branch --show-current
git rev-parse HEAD
git status --short
cat verification/research/current_state.md
