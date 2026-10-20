#!/usr/bin/env python3
"""Generate a source-domain inventory; never infer an external conjecture bridge."""
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
entries = []
for path in sorted((root / 'IndependentDuodenary').glob('*.lean')):
    source = path.read_text()
    for match in re.finditer(r'^(?:theorem|lemma)\s+(\w+)', source, re.M):
        entries.append({'name': 'IndependentDuodenary.' + match[1],
                        'module': path.stem, 'source': str(path.relative_to(root)),
                        'line': source[:match.start()].count('\n') + 1,
                        'external_prize_implication_established': False})
result = {'schema_version': 1, 'count': len(entries),
          'audit_evidence': 'verification/axioms-and-proofs.txt', 'theorems': entries}
(root / 'packaging/theorem_alignment.json').write_text(json.dumps(result, indent=2) + '\n')
print(f'CATALOG: {len(entries)} declarations')
