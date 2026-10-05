#!/usr/bin/env python3
"""Compile a renamed Challenge with ONLY external dependency search paths.

No repository or generated-package oleans are available during compilation.
This regression models the user-reported canonical Challenge isolation boundary;
it does not assert the complete hosted intake or Comparator protocol.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import uuid

ROOT = Path(__file__).resolve().parent.parent

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=ROOT/'Challenge.lean')
    parser.add_argument('--lean-bin', default=os.environ.get('CELL_LEAN_BIN') or shutil.which('lean'))
    parser.add_argument('--report', type=Path, default=ROOT/'reports/canonical-challenge.json')
    parser.add_argument('--compare-solution-dir', type=Path, help='After isolated compilation, compare exported declaration types and definition bodies against Solution in this directory')
    parser.add_argument('--expect-missing-package', action='store_true', help='Negative control for the historical import-only Challenge')
    args = parser.parse_args()
    if not args.lean_bin: parser.error('Pass the pinned --lean-bin')
    # Resolve elan's project-selected toolchain before entering the empty cwd.
    # Keep the launcher's basename intact: resolving a symlink to elan can
    # change multicall dispatch. No global/default toolchain is configured.
    launcher = str(Path(args.lean_bin).absolute())
    selected_prefix = subprocess.check_output([launcher, '-j1', '--print-prefix'], cwd=ROOT, text=True).strip()
    executable = 'lean.exe' if os.name == 'nt' else 'lean'
    lean = str((Path(selected_prefix)/'bin'/executable).resolve())
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    package_root = ROOT/manifest.get('packagesDir', '.lake/packages')
    paths = [(package_root/p['name']/'.lake/build/lib/lean').resolve() for p in manifest['packages']]
    omitted = []
    for package, path in zip(manifest['packages'], paths):
        if not path.is_dir():
            if package['name'] != 'Cli':
                raise SystemExit('Missing pinned dependency build: ' + str(path))
            omitted.append({'package': package, 'reason': 'Unused Lake CLI dependency; successful canonical elaboration establishes that no Cli artifact is required'})
    paths = [p for p in paths if p.is_dir()]
    if not paths: raise SystemExit('No pinned dependency build paths found')
    local_modules = ['PresentationComplex', 'FiniteGraphFreeGroup', 'CellAttachment', 'ClassicalSVK', 'Lean4', 'PresentationPackage', 'Challenge', 'Solution']
    for path in paths:
        if any((path/name).exists() or (path/(name+'.olean')).exists() for name in local_modules):
            raise SystemExit(f'Repository module contaminates dependency path: {path}')
    env = dict(os.environ)
    # findSysroot inside the extraction harness must also use the resolved
    # compiler, rather than invoke an elan proxy outside the project.
    env['PATH'] = str(Path(lean).parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    env.pop('LEAN_SRC_PATH', None)
    expected = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
    version = subprocess.check_output([lean, '-j1', '--version'], env=env, text=True).strip()
    if f'version {expected},' not in version: raise SystemExit(f'Wrong pinned compiler: {version}')
    data = args.source.read_bytes()
    # A fresh directory is also the working directory. Neither implicit '.' nor
    # the module name can resolve an existing repository or package artifact.
    with tempfile.TemporaryDirectory(prefix='canonical-challenge-') as folder:
        cwd = Path(folder)
        name = 'CanonicalChallenge_' + uuid.uuid4().hex
        source = cwd/(name+'.lean'); source.write_bytes(data)
        command = [lean, '-j1', '-M6144', '-o', name+'.olean', source.name]
        def run_bounded(command, environment):
            try:
                return subprocess.run(command, cwd=cwd, env=environment, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
            except subprocess.TimeoutExpired as error:
                output = error.stdout or ''
                if isinstance(output, bytes): output = output.decode('utf-8', errors='replace')
                return subprocess.CompletedProcess(command, 124, output + '\nTIMEOUT after 900 seconds\n')
        result = run_bounded(command, env)
        expected_failure = result.returncode != 0 and "unknown module prefix 'PresentationPackage'" in result.stdout
        passed = expected_failure if args.expect_missing_package else result.returncode == 0
        report = {'status': 'pass' if passed else 'fail', 'negative_control': args.expect_missing_package,
                  'source_sha256': hashlib.sha256(data).hexdigest(), 'lean_version': version,
                  'compiler_launcher': launcher, 'resolved_compiler': lean,
                  'lean_binary_sha256': hashlib.sha256(Path(lean).read_bytes()).hexdigest(),
                  'dependency_manifest_sha256': hashlib.sha256((ROOT/'lake-manifest.json').read_bytes()).hexdigest(),
                  'module_name': name, 'command': command, 'exit_code': result.returncode,
                  'lean_path': list(map(str, paths)), 'omitted_manifest_packages': omitted,
                  'repository_builds_excluded': True,
                  'fresh_working_directory': True, 'output': result.stdout,
                  'scope': 'Renamed canonical Challenge elaboration only; not hosted protocol or Comparator acceptance'}
        if result.returncode == 0 and args.compare_solution_dir:
            compare_env = dict(env)
            compare_env['LEAN_PATH'] = os.pathsep.join([folder, str(args.compare_solution_dir.resolve()), *map(str, paths)])
            snapshots = [cwd/'canonical.jsonl', cwd/'solution.jsonl']
            extraction = []
            for module, mode, snapshot in [(name, 'canonical', snapshots[0]), ('Solution', 'solution', snapshots[1])]:
                comparison = run_bounded([lean, '-j1', '-M6144', '--run', str(ROOT/'scripts/CompareCanonical.lean'), module, str(cwd/'names.json'), str(snapshot), mode], compare_env)
                extraction.append({'module': module, 'exit_code': comparison.returncode, 'output': comparison.stdout})
                print(comparison.stdout, end='')
                if comparison.returncode: break
            equal = len(extraction) == 2 and all(e['exit_code'] == 0 for e in extraction)
            mismatches = []
            if equal:
                import itertools
                with snapshots[0].open() as left, snapshots[1].open() as right:
                    for line, (a, b) in enumerate(itertools.zip_longest(left, right), 1):
                        if a != b: mismatches.append(line)
                equal = not mismatches
            report['comparison_solution_artifacts'] = {str(p.relative_to(args.compare_solution_dir)): hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.compare_solution_dir/'Solution.olean', *sorted((args.compare_solution_dir/'PresentationPackage').glob('*.olean'))]}
            report['comparison_solution_sources'] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'Solution.lean', *sorted((ROOT/'PresentationPackage').glob('*.lean'))]}
            report['expression_comparison'] = {'status': 'pass' if equal else 'fail', 'extractions': extraction, 'mismatch_lines': mismatches,
                'snapshots': {p.name: {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in snapshots if p.exists()},
                'scope': 'Byte equality of deterministic alpha-normalized Lean expression DAGs, with only six explicit compiler-private auxiliary names mapped bijectively; public declarations reference no private names; separate processes; not sandboxed Comparator'}
            if not equal:
                report['status'] = 'fail'; passed = False
                evidence = ROOT/'.toolchain/canonical-diagnostics'/name
                evidence.mkdir(parents=True, exist_ok=True)
                for p in [*snapshots, cwd/'names.json']:
                    if p.exists(): shutil.copy2(p, evidence/p.name)
                report['expression_comparison']['diagnostic_directory'] = str(evidence.relative_to(ROOT))
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2)+'\n')
        print(result.stdout, end='')
        print('CANONICAL CHALLENGE ' + report['status'].upper())
        raise SystemExit(0 if passed else 1)

if __name__ == '__main__': main()
