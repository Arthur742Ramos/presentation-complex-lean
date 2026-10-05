#!/usr/bin/env python3
"""Run explicit local verification stages and record exact artifacts and limits.

Default is the lightweight static stage. No downloads or network operations are
performed. Full-source replay, standalone elaboration, axiom audit, exports,
direct kernels, and sandboxed Comparator are separate selectable stages.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_standalone import ROOT, LOCAL_PREFIXES, closure
from derive_verification_metadata import AXIOM_TARGETS, PERMITTED_AXIOMS, derive
from audit_sources import audit

STAGES = ['static', 'source_replay', 'compile', 'axioms', 'exports', 'kernels', 'comparator']


def distribution_binary(prefix: Path, name: str) -> Path:
    return prefix/'bin'/(name + ('.exe' if os.name == 'nt' else ''))


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''): h.update(chunk)
    return h.hexdigest()


def modular_snapshot() -> tuple[dict[str, str], str]:
    paths = [p for folder in LOCAL_PREFIXES for p in sorted((ROOT/folder).rglob('*.lean'))]
    paths += [ROOT/(name+'.lean') for name in LOCAL_PREFIXES if (ROOT/(name+'.lean')).is_file()]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in paths}
    fingerprint = hashlib.sha256(json.dumps(snapshot, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return snapshot, fingerprint


def save(path: Path, result: dict) -> None:
    result['updated_at_utc'] = datetime.now(timezone.utc).isoformat()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')


def package_paths() -> list[str]:
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    folder = ROOT/manifest.get('packagesDir', '.lake/packages')
    result = []
    for package in manifest['packages']:
        source = folder/package['name']
        path = source/'.lake/build/lib/lean'
        if not path.is_dir():
            if package['name'] == 'mathlib': raise ValueError(f'missing pinned Mathlib cache: {path}')
            continue  # A manifest package unused by these imports may have no built Lean library.
        # These are external package caches only, never the sibling project's build tree.
        result.append(str(path.resolve()))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', nargs='+', choices=STAGES, default=['static'])
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--lean-prefix', type=Path)
    parser.add_argument('--memory-mb', type=int, default=6144)
    parser.add_argument('--kernels', nargs='+', choices=['leanchecker', 'leanchecker-paranoid', 'nanoda_bin', 'con-ron', 'lean4lean', 'con-leche'],
                        default=['leanchecker', 'leanchecker-paranoid', 'nanoda_bin', 'con-ron'])
    parser.add_argument('--report', default='reports/local-verification-results.json')
    args = parser.parse_args()
    if args.lean_prefix:
        prefix = args.lean_prefix.resolve()
        lean = args.lean_bin.resolve() if args.lean_bin else distribution_binary(prefix, 'lean')
    elif args.lean_bin or os.environ.get('CELL_LEAN_BIN') or shutil.which('lean'):
        lean = Path(args.lean_bin or os.environ.get('CELL_LEAN_BIN') or shutil.which('lean')).resolve()
        prefix = lean.parent.parent
    else:
        raise SystemExit('Provide --lean-prefix or --lean-bin for the pinned distribution')
    lake_source = prefix/'src/lean/lake/Lake/CLI/Check.lean'
    if not lake_source.is_file():
        raise SystemExit('Pinned Lake.Check source not found; pass --lean-prefix for the exact installed distribution')
    metadata = derive(lake_source)
    for name, content in metadata.items():
        path = ROOT/name
        if not path.is_file() or path.read_text(encoding='utf-8') != content:
            raise SystemExit(f'STALE verification metadata: {name}; run derive_verification_metadata.py')
    hashes = {name.replace('.lean', '_sha256').lower(): digest(ROOT/name) for name in ['Solution.lean', 'Challenge.lean']}
    hashes['generated_package_sha256'] = hashlib.sha256(json.dumps({str(p.relative_to(ROOT)): digest(p) for p in sorted((ROOT/'PresentationPackage').glob('*.lean'))}, sort_keys=True).encode()).hexdigest()
    hashes['export_targets_sha256'] = digest(ROOT/'reports/export-targets.json')
    hashes['solution_export_targets_sha256'] = digest(ROOT/'reports/solution-export-targets.json')
    report_path = ROOT/args.report
    prior = json.loads(report_path.read_text()) if report_path.is_file() else {}
    keep_prior = all(prior.get(key) == value for key, value in hashes.items() if key in prior) and all(prior.get(key) == hashes[key] for key in ['solution_sha256', 'challenge_sha256'])
    result = prior if keep_prior else {
        **hashes,
        'lean_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
        'mathlib_commit': next(p['rev'] for p in json.loads((ROOT/'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib'),
        'stages': {stage: {'status': 'not_run'} for stage in STAGES},
        'official_hosted_full_verification': {'status': 'not_run'},
        'trusted_challenge_render': {'status': 'not_run'},
        'registry_submission': {'status': 'not_submitted'},
        'verification_boundary': 'Direct local stages do not establish sandboxed build provenance or official hosted acceptance. No sandbox bypass is provided.',
    }
    result.update(hashes)
    snapshot, fingerprint = modular_snapshot()
    old_replay = prior.get('stages', {}).get('source_replay', {})
    if not keep_prior and old_replay.get('status') == 'pass' and old_replay.get('modular_source_fingerprint_sha256') == fingerprint:
        result['stages']['source_replay'] = dict(old_replay)
        result['stages']['source_replay']['reuse_basis'] = 'Exact identical modular source fingerprint; changed generated standalone hashes do not alter modular replay inputs'
    result['modular_source_fingerprint_sha256'] = fingerprint
    destination = ROOT/'.toolchain/standalone/lean'
    exports = ROOT/'.toolchain/audits'
    destination.mkdir(parents=True, exist_ok=True); exports.mkdir(parents=True, exist_ok=True)
    base = package_paths()
    env = dict(os.environ)
    env['PATH'] = str(prefix/'bin') + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join([str(destination)] + base)
    env['LEAN_ABORT_ON_PANIC'] = '1'
    result['standalone_search_path'] = [str(destination.relative_to(ROOT))] + [str(Path(p).relative_to((ROOT/'.lake/packages').resolve())) for p in base]
    result['standalone_environment'] = 'Isolated outputs plus pinned external package caches; inherited LEAN_PATH and sibling project oleans excluded'
    save(report_path, result)

    def run(command: list[str], logname: str, stdout_file: Path | None = None, child_env: dict | None = None) -> int:
        log = ROOT/'reports'/logname
        print('RUN ' + ' '.join(command), flush=True)
        with log.open('wb') as logstream:
            if stdout_file:
                with stdout_file.open('wb') as output:
                    proc = subprocess.run(command, cwd=ROOT, env=child_env or env, stdout=output, stderr=logstream)
            else:
                proc = subprocess.run(command, cwd=ROOT, env=child_env or env, stdout=logstream, stderr=subprocess.STDOUT)
        return proc.returncode

    def compile_source(source: Path, output: Path, environment: dict, logname: str) -> int:
        output.parent.mkdir(parents=True, exist_ok=True)
        return run([str(lean), '-j1', f'-M{args.memory_mb}', '-o', str(output), '-i', str(output.with_suffix('.ilean')), str(source)], logname, child_env=environment)

    if any(stage != 'static' for stage in args.stages):
        version = subprocess.run([str(lean), '--version'], cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        expected = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
        parsed_version = re.search(r'\bversion ([^\s,)]+)', version.stdout)
        if version.returncode or parsed_version is None or parsed_version.group(1) != expected:
            raise SystemExit('Selected Lean version does not match the pinned toolchain: ' + version.stdout)
        result['lean_version'] = version.stdout.strip()
        result['lean_binary_sha256'] = digest(lean)

    failed = False
    for stage in args.stages:
        entry = {'status': 'running'}
        result['stages'][stage] = entry; save(report_path, result)
        try:
            if stage in ['axioms', 'exports']:
                if result['stages']['compile']['status'] != 'pass':
                    raise ValueError('No passing standalone compile stage for these source hashes; run compile first')
                compiled = result['stages']['compile'].get('modules', {})
                for name in (['Solution'] if stage == 'axioms' else ['Solution', 'Challenge']):
                    artifact = destination/(name+'.olean')
                    bound = compiled.get(name, {}).get('olean_sha256')
                    if not artifact.is_file() or bound != digest(artifact):
                        raise ValueError(f'{name}.olean is missing, changed, or unbound; rerun compile')
            if stage in ['kernels', 'comparator']:
                if result['stages']['exports']['status'] != 'pass':
                    raise ValueError('No passing export stage for these source hashes; run exports first')
                for name in (['Solution'] if stage == 'kernels' else ['Solution', 'Challenge']):
                    artifact = exports/(name.lower()+'.ndjson')
                    bound = result['stages']['exports']['modules'].get(name, {}).get('sha256')
                    if not artifact.is_file() or bound != digest(artifact):
                        raise ValueError(f'{name} export is missing or changed; rerun exports')
            if stage == 'static':
                record = audit()
                (ROOT/'reports/static-source-audit.json').write_text(json.dumps(record, indent=2)+'\n')
                entry.update(status=record['status'], modular_sources=record['shipped_modular_source_count'],
                             private_visibility_collisions=record['publicized_name_collisions'])
            elif stage == 'source_replay':
                modules = ['.'.join(p.relative_to(ROOT).with_suffix('').parts)
                           for folder in LOCAL_PREFIXES for p in sorted((ROOT/folder).rglob('*.lean'))]
                modules += [name for name in LOCAL_PREFIXES if (ROOT/(name+'.lean')).is_file()]
                order, _ = closure(modules)
                output_root = ROOT/'.toolchain/replayed/lean'
                replay_env = dict(env); replay_env['LEAN_PATH'] = os.pathsep.join([str(output_root)] + base)
                before_snapshot, before_fingerprint = modular_snapshot()
                entry['module_count'] = len(order)
                entry['modular_source_fingerprint_sha256'] = before_fingerprint
                entry['modular_source_sha256'] = before_snapshot
                for name, source in order:
                    output = output_root/(name.replace('.', '/')+'.olean')
                    ret = compile_source(source, output, replay_env, 'replay-'+name.replace('.', '_')+'.log')
                    if ret:
                        entry.update(status='fail', exit_code=ret, failed_module=name); break
                else:
                    after_snapshot, after_fingerprint = modular_snapshot()
                    if before_fingerprint != after_fingerprint:
                        entry.update(status='fail', blocker='Modular source changed during replay; outputs are not a frozen-source verdict')
                    else: entry.update(status='pass', exit_code=0)
            elif stage == 'compile':
                entry['modules'] = {}
                compilation_order, _ = closure(['Solution', 'Challenge'])
                for name, source in compilation_order:
                    ret = compile_source(source, destination/(name.replace('.', '/')+'.olean'), env, 'standalone-'+name.lower()+'.log')
                    artifact = destination/(name.replace('.', '/')+'.olean')
                    entry['modules'][name] = {'status': 'pass' if ret == 0 else 'fail', 'exit_code': ret,
                                             'source_sha256': digest(source),
                                             'olean_sha256': digest(artifact) if ret == 0 and artifact.is_file() else None}
                entry.update(status='pass' if all(m['exit_code'] == 0 for m in entry['modules'].values()) else 'fail')
                entry['challenge_intentional_theorem_holes'] = 2
            elif stage == 'axioms':
                ret = run([str(lean), '-j1', f'-M{args.memory_mb}', 'reports/AuditSolution.lean'], 'standalone-axioms.log')
                log = (ROOT/'reports/standalone-axioms.log').read_text()
                matches = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.S)
                closures = {name: [a.strip() for a in axioms.split(',') if a.strip()] for name, axioms in matches}
                absent = [name for name in AXIOM_TARGETS if name not in closures]
                illegal = {name: [ax for ax in axes if ax not in PERMITTED_AXIOMS] for name, axes in closures.items() if any(ax not in PERMITTED_AXIOMS for ax in axes)}
                entry.update(status='pass' if ret == 0 and not absent and not illegal else 'fail', exit_code=ret,
                             targets_checked=len(closures), axiom_closures=closures, missing_targets=absent, forbidden_axioms=illegal)
            elif stage == 'exports':
                entry['modules'] = {}
                for name, targetfile in [('Challenge', 'export-targets.json'), ('Solution', 'solution-export-targets.json')]:
                    targets = json.loads((ROOT/'reports'/targetfile).read_text())
                    output = exports/(name.lower()+'.ndjson')
                    ret = run([str(distribution_binary(prefix, 'leanexport')), name, '--', *targets], name.lower()+'-export.log', output)
                    entry['modules'][name] = {'status': 'pass' if ret == 0 else 'fail', 'exit_code': ret,
                                             'target_count': len(targets), 'sha256': digest(output)}
                entry['status'] = 'pass' if all(m['exit_code'] == 0 for m in entry['modules'].values()) else 'fail'
            elif stage == 'kernels':
                output = exports/'solution.ndjson'
                if not output.is_file(): raise ValueError('Solution export is missing; run exports first')
                config = {'export_file_path': str(output), 'use_stdin': False, 'permitted_axioms': PERMITTED_AXIOMS,
                          'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
                          'nat_extension': True, 'string_extension': True, 'num_threads': 1, 'print_success_message': True}
                configpath = ROOT/'reports/nanoda-config.json'
                configpath.write_text(json.dumps(config, indent=2)+'\n')
                commands = {'leanchecker': ['--silent', '--from-export', str(output)],
                            'leanchecker-paranoid': ['--silent', '--from-export', str(output)],
                            'nanoda_bin': [str(configpath)], 'con-ron': ['--verified', '--jobs=1', str(output)],
                            'lean4lean': ['--import', str(output)], 'con-leche': [str(output)]}
                entry['checks'] = {}
                for name in args.kernels:
                    binary = distribution_binary(prefix, name)
                    if not binary.is_file():
                        entry['checks'][name] = {'status': 'blocked', 'blocker': 'Checker is absent from pinned distribution'}; continue
                    ret = run([str(binary), *commands[name]], name+'.log')
                    entry['checks'][name] = {'status': 'pass' if ret == 0 else 'fail', 'exit_code': ret,
                                            'binary_sha256': digest(binary)}
                entry.update(status='pass' if all(c['status'] == 'pass' for c in entry['checks'].values()) else 'fail', export_sha256=digest(output))
            elif stage == 'comparator':
                ret = run([str(distribution_binary(prefix, 'lake')), 'comparator', '--config', 'reports/comparator-local.json',
                           '--challenge-from-export', str(exports/'challenge.ndjson'),
                           '--solution-from-export', str(exports/'solution.ndjson')], 'comparator-from-export.log')
                log = (ROOT/'reports/comparator-from-export.log').read_text()
                sandbox_failure = ret != 0 and any(term in log for term in ['NETLINK_ROUTE', 'Operation not permitted', 'needs `bwrap`', 'Creating new namespace failed', 'which needs Linux namespaces'])
                entry.update(status='blocked' if sandbox_failure else 'pass' if ret == 0 else 'fail', exit_code=ret,
                             sandbox_preserved=True, artifact_origin='previous local exports; isolated-build provenance not established')
                if sandbox_failure: entry['blocker'] = log.strip()[-1500:]
        except (OSError, ValueError) as error:
            entry.update(status='blocked', blocker=str(error))
        save(report_path, result)
        print(stage + ': ' + entry['status'], flush=True)
        if entry['status'] != 'pass':
            failed = True
            # Do not treat failed elaboration/exports as input to later checks.
            if stage in ['static', 'source_replay', 'compile', 'exports']: break
    raise SystemExit(1 if failed else 0)


if __name__ == '__main__': main()
