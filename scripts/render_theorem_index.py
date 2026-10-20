#!/usr/bin/env python3
"""Render complete theorem headers in this repository's Lean source format."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
audit = (root / 'verification/axioms-and-proofs.txt').read_text()
match = re.search(r'AUDIT PASSED: (\d+) theorem declarations', audit)
assert match, 'Missing successful library audit'
count = int(match[1])
axioms = dict(re.findall(
    r"'IndependentDuodenary\.(\w+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", audit))
old = (root / 'verification/THEOREMS.md').read_text()
methods = {}
for block in re.split(r'^## `', old, flags=re.M)[1:]:
    name = block.split('`', 1)[0]
    method = re.search(r'^Proof method: (.*)$', block, re.M)
    if method:
        methods[name] = method[1]


def proof_separator(text, start):
    """Skip bracketed named arguments and top-level let binding assignments."""
    closers = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
    stack, pending_lets = [], 0
    i = start
    while i < len(text):
        if text.startswith('/-', i):
            depth, i = 1, i + 2
            while depth:
                assert i < len(text), 'Unclosed comment'
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            continue
        if text.startswith('--', i):
            i = text.index('\n', i)
            continue
        if text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            continue
        if text[i] in closers:
            stack.append(closers[text[i]])
        elif stack and text[i] == stack[-1]:
            stack.pop()
        elif not stack and text.startswith('let', i) and (
                i == 0 or not (text[i-1].isalnum() or text[i-1] == '_')) and (
                i + 3 == len(text) or not (text[i+3].isalnum() or text[i+3] == '_')):
            pending_lets += 1
            i += 3
            continue
        elif not stack and text.startswith(':=', i):
            if pending_lets:
                pending_lets -= 1
                i += 2
                continue
            return i
        i += 1
    raise ValueError('No proof separator found')


entries = []
for path in sorted((root / 'IndependentDuodenary').glob('*.lean')):
    source = path.read_text()
    declarations = list(re.finditer(r'^(?:theorem|lemma)\s+(\w+)', source, re.M))
    for declaration in declarations:
        end = proof_separator(source, declaration.end())
        header = source[declaration.start():end].rstrip()
        assert not re.search(r'\n(?:theorem|lemma|def)\s', header), declaration[1]
        entries.append((declaration[1], path.relative_to(root), header))
assert len(entries) == count and {e[0] for e in entries} == set(axioms)
assert all(name in methods for name, _, _ in entries), 'Missing reviewed proof method'
lines = ['# Theorem-by-theorem audit', '',
         f'All {count} named library declarations in namespace `IndependentDuodenary` compiled and passed the axiom audit. Complete source propositions are reproduced below. Exact elaborated propositions, proof terms and direct dependencies are retained in [axioms-and-proofs.txt](axioms-and-proofs.txt).', '']
for name, path, header in entries:
    lines += [f'## `{name}`', '', f'Source: `{path}`. Compilation: **passed**.', '',
              '```lean', header, '```', '', 'Proof method: ' + methods[name], '',
              f"Axioms: `{axioms[name].strip() or 'none'}`.", '',
              f'Dependencies: see `DIRECT DEPENDENCIES {name}` and the printed proof in the machine-generated audit.', '']
(root / 'verification/THEOREMS.md').write_text('\n'.join(lines))
print(f'THEOREM INDEX PASS: {count} complete source headers')
