#!/usr/bin/env python3
"""Compile the audit monograph and its complete source-derived theorem index."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / '.lake/translation')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    catalog = json.loads((ROOT / 'packaging/theorem_alignment.json').read_text())
    actual = []
    for path in sorted((ROOT / 'IndependentDuodenary').glob('*.lean')):
        actual += [('IndependentDuodenary.' + m[1], path.stem)
                   for m in re.finditer(r'^(?:theorem|lemma)\s+(\w+)', path.read_text(), re.M)]
    expected = [(item['name'], item['module']) for item in catalog['theorems']]
    if actual != expected or catalog['count'] != len(actual):
        raise SystemExit('Translation catalog does not match the current Lean source')
    def escaped(s):
        return s.replace('_', r'\_\allowbreak{}')
    index = ['\\begin{enumerate}\\small']
    for name, module in actual:
        index.append(r'\item \texttt{' + escaped(name.removeprefix('IndependentDuodenary.')) +
                     r'}; module \texttt{' + escaped(module) + '}.')
    index.append('\\end{enumerate}')
    (output / 'theorem-index.tex').write_text('\n'.join(index) + '\n')
    (output / 'theorem-count.tex').write_text(r'\newcommand{\AuditedTheoremCount}{' + str(len(actual)) + '}\n')
    source = ROOT / 'MillenniumPrizeTranslation.tex'
    target = output / source.name
    if source != target:
        shutil.copy2(source, target)
    for pass_number in [1, 2]:
        with (output / f'latex-pass-{pass_number}.log').open('w') as log:
            subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                            '-halt-on-error', source.name], cwd=output,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    log = (output / 'MillenniumPrizeTranslation.log').read_text()
    if 'undefined references' in log or 'Overfull' in log:
        raise SystemExit('Unresolved references or overfull boxes in translation monograph')
    manifest = {'theorem_count': len(actual), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'pdf_sha256': hashlib.sha256((output / 'MillenniumPrizeTranslation.pdf').read_bytes()).hexdigest(),
                'latex_passes': 2, 'prize_conjecture_proved': False,
                'institutional_submission_performed': False}
    (output / 'translation-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest))


if __name__ == '__main__':
    main()
