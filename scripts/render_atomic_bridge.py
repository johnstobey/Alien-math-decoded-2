#!/usr/bin/env python3
"""Render and validate the explicit bridge obligation graph without assuming its goals."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
data = json.loads((root / 'packaging/atomic_bridge_obligations.json').read_text())
atoms = {a['id']: a for g in data['groups'] for a in g['atoms']}
assert len(atoms) == sum(len(g['atoms']) for g in data['groups'])
assert all(d in atoms for a in atoms.values() for d in a['requires'])
visited, active = set(), set()

def visit(identifier):
    if identifier in visited:
        return
    assert identifier not in active, 'Cyclic proof-obligation dependencies'
    active.add(identifier)
    for dep in atoms[identifier]['requires']:
        visit(dep)
    active.remove(identifier)
    visited.add(identifier)

for identifier in atoms:
    visit(identifier)
proved = [a for a in atoms.values() if a['status'] in ('proved_in_Lean_example', 'proved_in_library', 'defined_in_library')]
assert all(a['status'] in ('open', 'proved_in_Lean_example', 'proved_in_library', 'defined_in_library') for a in atoms.values())
assert all(a['evidence'] and (root / a['evidence']).is_file() for a in proved)
lines = [data['specification'].rstrip(), '',
         f"**Register totals:** {len(atoms)} atoms; {len(proved)} completed obligations; "
         f"{len(atoms)-len(proved)} open obligations. These totals are not library theorem counts.", '']
for group in data['groups']:
    lines += [f"## Item {group['item']}: {group['title']}", '']
    for atom in group['atoms']:
        lines += [f"### {atom['id']} — {atom['title']}", '', atom['acceptance_criterion'], '',
                  f"Status: **{atom['status']}**.", '',
                  'Prerequisites: ' + (', '.join(atom['requires']) or 'none') + '.', '']
        if atom.get('declarations'):
            lines += ['Declarations: ' + ', '.join('`' + n + '`' for n in atom['declarations']) + '.', '']
        if atom['evidence']:
            lines += [f"Evidence: `{atom['evidence']}`.", '']
(root / 'verification/ATOMIC_BRIDGE_SPECIFICATION.md').write_text('\n'.join(lines))
print(f'ATOMIC GRAPH PASS: {len(atoms)} nodes, no cycles; {len(proved)} completed obligations')
