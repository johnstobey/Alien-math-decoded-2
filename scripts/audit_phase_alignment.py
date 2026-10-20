#!/usr/bin/env python3
"""Check the independent phase experiment and its transitive foundational usage."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
source = (root / 'examples/PhaseAlignmentBridge.lean').read_text()
if re.search(r'\b(sorry|admit|native_decide|axiom)\b', source):
    raise SystemExit('Forbidden proof construct in phase experiment')
names = re.findall(r'^theorem\s+(\w+)', source, re.M)
assert names and len(set(names)) == len(names)
prefix = 'IndependentDuodenary.PhaseAlignmentInvestigation.'
commands = [source, 'set_option pp.proofs true']
for name in names:
    commands += ['#print ' + prefix + name, '#print axioms ' + prefix + name]
path = root / '.lake/PhaseAlignmentAudit.lean'
path.parent.mkdir(exist_ok=True)
path.write_text('\n'.join(commands) + '\n')
result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    raise SystemExit(result.returncode)
entries = re.findall(
    r"'IndependentDuodenary\.PhaseAlignmentInvestigation\.(\w+)' "
    r"(?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", result.stdout)
assert len(entries) == len(names) and {name for name, _ in entries} == set(names)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, used in entries:
    assert set(re.findall(r'[\w.]+', used)) <= allowed, name
print(f'PHASE AUDIT PASSED: {len(names)} experimental theorem declarations; only standard Lean axioms permitted.')
