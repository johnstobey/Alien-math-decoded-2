#!/usr/bin/env python3
"""Assemble and verify a scoped intake dossier; never submit an institutional claim."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile

if not __debug__:
    raise SystemExit('Integrity verification requires Python assertions; do not use optimization mode')

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '65e0db131c5ab65cddd0b913b41ddcb588108d97'
REPO = 'https://github.com/johnstobey/Alien-math-decoded-2'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def safe_path(root, name):
    rel = Path(name)
    if rel.is_absolute() or '..' in rel.parts:
        raise ValueError('Unsafe relative artifact path')
    return root / rel


def verify(root, require_ledger=False):
    manifest = json.loads((root / 'claim_manifest.json').read_text())
    assert manifest['schema_version'] == 1
    assert manifest['proof_baseline']['commit'] == BASELINE
    assert manifest['verification']['named_theorems'] == 350
    assert manifest['verification']['harness_checks_passed'] == 13
    assert manifest['claims']['prize_conjecture_proved'] is False
    assert manifest['claims']['institutional_submission_performed'] is False
    assert manifest['claims']['legal_completeness_certified'] is False
    assert manifest['administration']['signature'] is None
    ids, paths = set(), set()
    for a in manifest['artifacts']:
        assert a['id'] not in ids and a['path'] not in paths
        ids.add(a['id']); paths.add(a['path'])
        assert re.fullmatch(r'[0-9a-f]{64}', a['sha256'])
        p = safe_path(root, a['path'])
        assert p.is_file() and p.stat().st_size == a['bytes']
        assert digest(p) == a['sha256'], f'Hash mismatch: {a["path"]}'
    ledger = root / 'DOSSIER_SHA256SUMS'
    if require_ledger and not ledger.is_file():
        raise ValueError('Missing enclosure checksum ledger')
    if ledger.exists():
        listed = set()
        for line in ledger.read_text().splitlines():
            expected, name = line.split('  ', 1)
            assert name not in listed
            listed.add(name)
            assert digest(safe_path(root, name)) == expected, f'Ledger mismatch: {name}'
        assert listed == paths | {'claim_manifest.json'}
    print(f'DOSSIER VERIFIED: {len(ids)} indexed artifacts; SHA-256 checks passed')
    return manifest


def generate(root):
    evidence = json.loads((root / 'dist/claim-release-validation.json').read_text())
    assert evidence['source_commit'] == BASELINE
    assert evidence['ci']['source_commit'] == BASELINE
    assert all(j['status'] == 'completed' and all(s['conclusion'] == 'success' for s in j['steps'])
               for j in evidence['ci']['jobs'])
    assert 'AUDIT PASSED: 350 theorem declarations' in (root / 'verification/axioms-and-proofs.txt').read_text()
    assert 'PIPELINE PASS: 13 checks' in (root / 'dist/claim-vendor-verification.log').read_text()
    artifacts = []
    def add(identifier, relative, role, baseline=False):
        path = root / relative
        actual = digest(path)
        url = None
        if baseline:
            blob = subprocess.check_output(['git', 'show', f'{BASELINE}:{relative}'], cwd=root)
            assert hashlib.sha256(blob).hexdigest() == actual, f'Baseline changed: {relative}'
            url = f'{REPO}/blob/{BASELINE}/{relative}'
        artifacts.append({'id': identifier, 'path': relative, 'role': role, 'bytes': path.stat().st_size,
                          'sha256': actual, 'baseline_git_url': url})
    for a in [
        ('cover_letter','administrative/COVER_LETTER.md','unsigned administrative correspondence',False),
        ('intake_summary','administrative/INTAKE_SUMMARY.md','scope and review instructions',False),
        ('dossier_builder','scripts/build_intake_bundle.py','standard-library enclosure verifier and builder',False),
        ('manifest_schema','packaging/claim_manifest.schema.json','JSON Schema for the authoritative index',False),
        ('monograph_tex','MillenniumPrizeTranslation.tex','translation monograph source',True),
        ('monograph_pdf','dist/MillenniumPrizeTranslation.pdf','compiled translation monograph',False),
        ('theorem_index','verification/THEOREMS.md','exact theorem statements and proof index',True),
        ('theorem_catalog','packaging/theorem_alignment.json','machine-readable declaration map',True),
        ('proof_audit','verification/axioms-and-proofs.txt','proof terms and transitive foundations',True),
        ('build_log','verification/local-build.txt','actual baseline build transcript',True),
        ('extracted_verification','dist/claim-vendor-verification.log','independent extraction build/audit/harness transcript',False),
        ('source_integrity','dist/claim-source-integrity.log','source archive checksum transcript',False),
        ('release_validation','dist/claim-release-validation.json','original release provenance record',False),
        ('bridge','IndependentDuodenary/MillenniumBridge.lean','finite reachability equivalence and unproved complexity definition',True),
        ('lakefile','lakefile.lean','pinned build configuration',True),
        ('toolchain','lean-toolchain','Lean toolchain pin',True),
        ('dependency_lock','lake-manifest.json','locked dependency closure',True),
        ('proof_exporter','scripts/perfect_claim_bundle.sh','proof and monograph archive entry point',True)]:
        add(*a)
    for key in ['source_archive', 'vendor_archive']:
        record = evidence[key]
        relative = 'dist/' + Path(record['archive']).name
        assert digest(root / relative) == record['sha256']
        add(key, relative, 'complete nested proof archive')
        add(key + '_sidecar', relative + '.sha256', 'nested archive SHA-256 sidecar')
    assert digest(root / 'dist/MillenniumPrizeTranslation.pdf') == evidence['monograph']['pdf_sha256']
    manifest = {
        'schema_version': 1,
        'title': 'Finite protocol verification: administrative technical-review dossier',
        'proof_baseline': {'repository': REPO, 'commit': BASELINE, 'theorem_catalog': 'theorem_catalog'},
        'verification': {'named_theorems': 350, 'harness_checks_passed': 13, 'new_Lean_diagnostics': 0,
                         'full_build': 'passed_with_upstream_Mathlib_docPrime_warnings',
                         'ci_url': evidence['ci']['url'], 'ci_evidence_kind': evidence['ci']['evidence_kind'],
                         'ci_commit': BASELINE, 'raw_CI_logs_included': False,
                         'standard_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                         'custom_axioms': False, 'constructive_only': False},
        'claims': {'scope': 'finite algebraic protocol and bounded aligned substitution recovery',
                   'prize_problem': 'P versus NP', 'prize_conjecture_proved': False,
                   'external_complexity_equivalence': 'not_formalized',
                   'CMI_eligibility': 'not_established', 'institutional_submission_performed': False,
                   'legal_completeness_certified': False},
        'administration': {'document_status': 'unsigned technical-review dossier; not a perfected prize claim',
                           'signature': None, 'submitter_legal_identity': None, 'institutional_receipt': None,
                           'DOI': None, 'public_record': 'Git source and metadata publication only',
                           'official_rules_review': evidence['limitations']['official_rules_check']},
        'packaging': {'enclosure_ledger': 'DOSSIER_SHA256SUMS', 'algorithm': 'SHA-256',
                      'manifest_self_hash': 'in enclosure ledger; ledger itself excluded',
                      'archive_digest': 'external .sha256 sidecar',
                      'all_indexed_files_in_administrative_packet': True,
                      'institutional_signature_or_endorsement': False},
        'artifacts': artifacts}
    (root / 'claim_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return verify(root)


def package(root, manifest, output):
    output.mkdir(parents=True, exist_ok=True)
    name = 'institutional-review-dossier-' + BASELINE[:12]
    with tempfile.TemporaryDirectory(prefix='intake-dossier-') as temp:
        stage = Path(temp) / name
        for rel in ['claim_manifest.json', *(a['path'] for a in manifest['artifacts'])]:
            target = stage / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / rel, target)
        paths = sorted(p for p in stage.rglob('*') if p.is_file())
        (stage / 'DOSSIER_SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(stage).as_posix()}\n' for p in paths))
        verify(stage, require_ledger=True)
        archive = output / (name + '.tar.gz')
        epoch = int(subprocess.check_output(['git', 'show', '-s', '--format=%ct', BASELINE], cwd=root))
        with archive.open('wb') as raw, gzip.GzipFile(fileobj=raw, filename='', mode='wb', mtime=0, compresslevel=1) as gz:
            with tarfile.open(fileobj=gz, mode='w') as tar:
                for p in [stage, *sorted(stage.rglob('*'))]:
                    info = tar.gettarinfo(str(p), arcname=str(Path(name) / p.relative_to(stage)))
                    info.uid = info.gid = 0
                    info.uname = info.gname = ''
                    info.mtime = epoch
                    info.pax_headers = {}
                    if p.is_file():
                        with p.open('rb') as stream: tar.addfile(info, stream)
                    else: tar.addfile(info)
        archive.with_suffix('.gz.sha256').write_text(f'{digest(archive)}  {archive.name}\n')
        print(json.dumps({'archive': str(archive), 'sha256': digest(archive), 'bytes': archive.stat().st_size,
                          'proof_baseline': BASELINE, 'institutional_submission_performed': False}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--verify-only', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / 'dist')
    args = parser.parse_args()
    if args.verify_only:
        verify(ROOT, require_ledger=True)
        return
    manifest = generate(ROOT)
    if not args.generate_only:
        package(ROOT, manifest, args.output.resolve())


if __name__ == '__main__':
    main()
