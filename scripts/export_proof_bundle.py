#!/usr/bin/env python3
"""Export verified, pinned audit material without asserting a prize solution."""
import argparse
import gzip
import hashlib
from html.parser import HTMLParser
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def run(cmd, cwd=ROOT):
    return subprocess.check_output(cmd, cwd=cwd, text=True).strip()


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def checked_command(cmd, log, strict=False):
    with log.open('w') as f:
        result = subprocess.run(cmd, cwd=ROOT, text=True, stdout=f, stderr=subprocess.STDOUT)
    if result.returncode or (strict and log.stat().st_size):
        raise SystemExit(f'Verification failed: {cmd}; inspect {log}')
    return {'argv': cmd, 'exit_code': result.returncode, 'log': log.name, 'sha256': digest(log)}


def get_url(url):
    with urllib.request.urlopen(url, timeout=30) as response:
        return response.read().decode()


class JobParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.status = None
        self.steps = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == 'check-steps':
            self.status = a.get('data-job-status')
        if tag == 'check-step':
            self.steps.append({'name': a.get('data-name'), 'conclusion': a.get('data-conclusion')})


def capture_ci(url, commit, dest):
    match = re.fullmatch(r'https://github\.com/([\w.-]+/[\w.-]+)/actions/runs/(\d+)', url)
    if not match:
        raise SystemExit('CI URL must name a public GitHub Actions run')
    repo, run_id = match.groups()
    origin = run(['git', 'remote', 'get-url', 'origin']).removesuffix('.git')
    if origin != 'https://github.com/' + repo:
        raise SystemExit('CI repository does not match origin')
    dest.mkdir(parents=True)
    page = get_url(url)
    (dest / 'run.html').write_text(page)
    if '/commit/' + commit not in page:
        raise SystemExit('CI run page does not link the exported source commit')
    listing = get_url(f'https://github.com/{repo}/actions?query=branch%3Amain+event%3Apush')
    (dest / 'workflow-list.html').write_text(listing)
    data = json.loads(re.search(r'<script type="application/json" data-target="react-app.embeddedData">(.*?)</script>', listing, re.S)[1])
    entry = next((r for r in data['payload']['allWorkflowRunsRoute']['workflowRuns'] if r['id'] == run_id), None)
    if not entry or entry['state'].get('conclusion') != 'WORKFLOW_RUN_CONCLUSION_SUCCESS':
        raise SystemExit('Exact CI run is not listed as successful')
    jobs = sorted(set(re.findall(re.escape(f'/{repo}/actions/runs/{run_id}/job/') + r'\d+', page)))
    if not jobs:
        raise SystemExit('No CI job evidence found')
    result = {'url': url, 'source_commit': commit, 'workflow': entry['state'], 'jobs': [],
              'raw_ci_logs_included': False, 'evidence_kind': 'public run/job HTML and parsed statuses'}
    for index, job in enumerate(jobs):
        text = get_url('https://github.com' + job + '?check_suite_focus=true')
        (dest / f'job-{index}.html').write_text(text)
        parsed = JobParser()
        parsed.feed(text)
        if parsed.status != 'completed' or not parsed.steps or any(s['conclusion'] != 'success' for s in parsed.steps):
            raise SystemExit('CI job evidence is incomplete or unsuccessful')
        result['jobs'].append({'url': 'https://github.com' + job, 'status': parsed.status, 'steps': parsed.steps})
    write_json(dest / 'summary.json', result)
    return result


def vendor(stage, manifest):
    original = stage / 'upstream-configuration'
    original.mkdir()
    for name in ['lakefile.lean', 'lake-manifest.json']:
        shutil.copy2(stage / name, original / name)
    config = 'import Lake\nopen Lake DSL\npackage independent_duodenary where\n  version := v!"0.1.0"\n\n'
    packages = []
    for p in manifest['packages']:
        name = p['name']
        source = ROOT / manifest['packagesDir'] / name
        if run(['git', 'rev-parse', 'HEAD'], source) != p['rev']:
            raise SystemExit(f'Dependency revision mismatch: {name}')
        if run(['git', 'status', '--porcelain', '--untracked-files=no'], source):
            raise SystemExit(f'Modified dependency source: {name}')
        target = stage / 'vendor' / name
        target.mkdir(parents=True)
        data = subprocess.check_output(['git', '-C', str(source), 'archive', p['rev']])
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for member in archive.getmembers():
                rel = Path(member.name)
                if rel.is_absolute() or '..' in rel.parts:
                    raise SystemExit('Unsafe dependency archive path')
            archive.extractall(target, filter='data')
        cache = source / '.lake' / 'build'
        if cache.is_dir():
            shutil.copytree(cache, target / '.lake' / 'build')
        config += f'require «{name}» from "vendor/{name}"\n'
        packages.append({'type': 'path', 'scope': '', 'name': name, 'dir': f'vendor/{name}',
                         'inherited': False, 'configFile': p['configFile'], 'manifestFile': p['manifestFile']})
    config += '\n@[default_target]\nlean_lib IndependentDuodenary\n\n@[default_target]\nlean_exe verifyPipeline where\n  root := `PipelineMain\n'
    (stage / 'lakefile.lean').write_text(config)
    write_json(stage / 'lake-manifest.json', {'version': manifest['version'], 'packagesDir': '.lake/packages',
                                             'packages': packages, 'name': manifest['name'], 'lakeDir': '.lake'})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, default=ROOT / 'dist')
    ap.add_argument('--translation', action='store_true', help='compile and include the LaTeX audit monograph')
    ap.add_argument('--vendor', action='store_true', help='include pinned dependency sources and available build caches')
    ap.add_argument('--ci-url', help='capture successful public CI evidence for exactly HEAD')
    ap.add_argument('--allow-dirty', action='store_true', help='development archives only; recorded in metadata')
    args = ap.parse_args()
    commit = run(['git', 'rev-parse', 'HEAD'])
    dirty = bool(run(['git', 'status', '--porcelain']))
    if dirty and not args.allow_dirty:
        raise SystemExit('Refusing release export from a dirty source tree')
    if dirty and args.ci_url:
        raise SystemExit('Dirty sources cannot be certified by a committed CI run')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='proof-export-') as temp:
        name = f'independent-duodenary-{commit[:12]}' + ('-vendor' if args.vendor else '-source')
        if args.translation:
            name += '-translation'
        stage = Path(temp) / name
        stage.mkdir()
        files = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=ROOT).decode().split('\0')
        for rel in files:
            if rel and (ROOT / rel).is_file():
                dst = stage / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / rel, dst)
        logs = stage / 'export-evidence'
        logs.mkdir()
        records = []
        for cmd, filename, strict in [
            (['lake', 'build'], 'build.log', False),
            (['python3', 'scripts/audit.py'], 'audit.log', False),
            (['lake', 'env', 'lean', 'IndependentDuodenary/MillenniumBridge.lean'], 'new-module.log', True),
            (['lake', 'env', 'lean', 'examples/MillenniumBoundary.lean'], 'boundary.log', True),
            (['lake', 'env', 'lean', 'IndependentDuodenary/SearchBoundary.lean'], 'search-module.log', True),
            (['lake', 'env', 'lean', 'examples/SearchBoundary.lean'], 'search-fixtures.log', True),
            (['lake', 'env', 'lean', 'IndependentDuodenary/ComplexityEncoding.lean'], 'parser-module.log', True),
            (['lake', 'env', 'lean', 'examples/ComplexityParserBoundary.lean'], 'parser-fixtures.log', True),
            (['lake', 'exe', 'verifyPipeline'], 'pipeline.log', False)]:
            records.append(checked_command(cmd, logs / filename, strict))
        if args.translation:
            records.append(checked_command(['python3', 'scripts/build_translation.py', '--output',
                                            str(stage / 'publication')], logs / 'translation.log'))
        if args.translation:
            shutil.copytree(ROOT / '.lake/build', stage / '.lake/build')
        audit = (logs / 'audit.log').read_text()
        match = re.search(r'AUDIT PASSED: (\d+) theorem declarations', audit)
        if not match:
            raise SystemExit('Missing complete theorem audit')
        catalog = json.loads((ROOT / 'packaging/theorem_alignment.json').read_text())
        if catalog['count'] != int(match[1]) or len(catalog['theorems']) != int(match[1]):
            raise SystemExit('Theorem alignment catalog does not match the audited count')
        metadata = {'format': 1, 'source_commit': commit, 'source_dirty': dirty,
                    'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
                    'vendor_dependencies': args.vendor, 'dependency_build_caches_included': args.vendor,
                    'toolchain_included': False, 'translation_included': args.translation,
                    'institutional_submission_performed': False,
                    'project_build_artifacts_included': args.translation, 'theorem_count': int(match[1]),
                    'verification': records, 'prize_alignment': json.loads((ROOT / 'packaging/problem_alignment.json').read_text()),
                    'ci': None}
        write_json(stage / 'DEPENDENCIES.json', json.loads((ROOT / 'lake-manifest.json').read_text()))
        if args.ci_url:
            metadata['ci'] = capture_ci(args.ci_url, commit, logs / 'ci')
        if args.vendor:
            vendor(stage, json.loads((ROOT / 'lake-manifest.json').read_text()))
        write_json(stage / 'BUNDLE.json', metadata)
        (stage / 'BUNDLE_README.md').write_text(
            '# Verified audit bundle\n\n'
            'Requires the pinned Lean/Lake toolchain, Python 3 and a C compiler/linker.\n'
            'This bundle does not certify a Millennium Prize solution.\n\n'
            'Verify and execute from this directory:\n\n'
            '```sh\npython3 scripts/verify_bundle.py --all\n```\n\n'
            'Vendor mode uses local dependency paths and includes build caches.\n'
            'After rebuilding, mutable .lake caches may differ; use --sources-only to recheck immutable files.\n'
            'Original pinned Git configuration, when overridden, is in upstream-configuration/.\n'
            'Raw CI logs are not included; captured CI pages and statuses are identified in BUNDLE.json.\n')
        checksums = []
        for path in sorted(stage.rglob('*')):
            if path.is_file():
                checksums.append(f'{digest(path)}  {path.relative_to(stage).as_posix()}')
        (stage / 'SHA256SUMS').write_text('\n'.join(checksums) + '\n')
        archive_path = output / f'{name}.tar.gz'
        epoch = int(run(['git', 'show', '-s', '--format=%ct', 'HEAD']))
        with archive_path.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0, compresslevel=6) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as archive:
                for path in [stage, *sorted(stage.rglob('*'))]:
                    info = archive.gettarinfo(str(path), arcname=str(Path(name) / path.relative_to(stage)))
                    info.uid = info.gid = 0
                    info.uname = info.gname = ''
                    info.mtime = epoch
                    info.pax_headers = {}
                    if path.is_file():
                        with path.open('rb') as stream:
                            archive.addfile(info, stream)
                    else:
                        archive.addfile(info)
        archive_hash = digest(archive_path)
        archive_path.with_suffix(archive_path.suffix + '.sha256').write_text(f'{archive_hash}  {archive_path.name}\n')
        print(json.dumps({'archive': str(archive_path), 'sha256': archive_hash, 'bytes': archive_path.stat().st_size,
                          'source_commit': commit, 'source_dirty': dirty, 'theorems': int(match[1]),
                          'ci_evidence': bool(args.ci_url), 'vendor_dependencies': args.vendor}))


if __name__ == '__main__':
    main()
