#!/usr/bin/env python3
"""Inventory theorem statements and ask Lean for proof terms and transitive axioms."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
modules = [root / 'IndependentDuodenary.lean', *sorted((root / 'IndependentDuodenary').rglob('*.lean'))]
names = []
for path in modules:
    text = path.read_text()
    if re.search(r'\b(sorry|admit|native_decide|axiom)\b', text):
        sys.exit(f'Forbidden proof placeholder, native evaluator, or axiom in {path.name}')
    names.extend(re.findall(r'^(?:theorem|lemma)\s+(\w+)', text, re.MULTILINE))
if not names:
    sys.exit('No theorems found')
commands = ['import IndependentDuodenary', 'import Lean.Util.FoldConsts', 'set_option pp.proofs true']
for name in names:
    commands += [f'#print IndependentDuodenary.{name}', f'#print axioms IndependentDuodenary.{name}']
    commands += [f'run_cmd do\n  let env ← Lean.getEnv\n  let some ci := env.find? ``IndependentDuodenary.{name} | throwError \"Missing theorem\"\n  Lean.logInfo m!\"DIRECT DEPENDENCIES {name}: {{ci.getUsedConstantsAsSet.toList}}\"']
file = root / '.lake' / 'ProofAudit.lean'
file.write_text('\n'.join(commands) + '\n')
result = subprocess.run(['lake', 'env', 'lean', str(file)], cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    sys.exit(result.returncode)
axiom_results = re.findall(
    r"'IndependentDuodenary\.(\w+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
    result.stdout,
)
if len(axiom_results) != len(names) or {n for n, _ in axiom_results} != set(names):
    sys.exit('Incomplete axiom audit')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axiom_text in axiom_results:
    used = set(re.findall(r'[\w.]+', axiom_text))
    if not used <= allowed:
        sys.exit(f'Unexpected axioms in {name}: {used - allowed}')
print(f'AUDIT PASSED: {len(names)} theorem declarations; only standard Lean axioms permitted.')
