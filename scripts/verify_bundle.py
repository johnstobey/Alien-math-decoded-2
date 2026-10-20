#!/usr/bin/env python3
"""Verify archive payload hashes before optionally building the defined package."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument('--all', action='store_true', help='verify, build, audit and run the executable guard')
    ap.add_argument('--sources-only', action='store_true', help='omit mutable .lake cache files after rebuilding')
    args = ap.parse_args()
    root = args.root.resolve()
    count = 0
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        rel = Path(name)
        if rel.is_absolute() or '..' in rel.parts:
            raise SystemExit(f'Unsafe manifest path: {name}')
        if args.sources_only and '.lake' in rel.parts:
            continue
        path = root / rel
        if not path.is_file() or digest(path) != expected:
            raise SystemExit(f'Checksum mismatch: {name}')
        count += 1
    print(f'CHECKSUM PASS: {count} files', flush=True)
    if args.all:
        metadata = json.loads((root / 'BUNDLE.json').read_text())
        build = ['lake', '--no-cache', 'build'] if metadata['vendor_dependencies'] else ['lake', 'build']
        for cmd in [build, ['python3', 'scripts/audit.py'], ['lake', 'exe', 'verifyPipeline']]:
            subprocess.run(cmd, cwd=root, check=True)


if __name__ == '__main__':
    main()
