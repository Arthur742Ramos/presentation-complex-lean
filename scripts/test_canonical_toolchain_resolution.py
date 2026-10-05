#!/usr/bin/env python3
"""Light functional regression for project-sensitive Lean launcher resolution.

The fixture launcher models elan with a project pin and no global default.
It delegates to the installed pinned compiler; no user configuration is changed.
The real elan path is exercised separately by the hosted canonical CI step.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', default=os.environ.get('CELL_LEAN_BIN') or shutil.which('lean'))
    args = parser.parse_args()
    if not args.lean_bin: parser.error('Pass the pinned --lean-bin')
    prefix = subprocess.check_output([args.lean_bin, '-j1', '--print-prefix'], cwd=ROOT, text=True).strip()
    executable = 'lean.exe' if os.name == 'nt' else 'lean'
    real = str((Path(prefix)/'bin'/executable).resolve())
    with tempfile.TemporaryDirectory(prefix='canonical-launcher-test-') as folder:
        tmp = Path(folder)
        calls = tmp/'calls.jsonl'
        launcher = tmp/('lean.cmd' if os.name == 'nt' else 'lean')
        fixture = '#!/usr/bin/env python3\n' + (
            'import json, os, pathlib, sys\n' +
            f'root = pathlib.Path({str(ROOT)!r})\n' +
            'if pathlib.Path.cwd() != root:\n' +
            '    print("error: no default toolchain configured", file=sys.stderr)\n' +
            '    sys.exit(1)\n' +
            f'with open({str(calls)!r}, "a") as out: out.write(json.dumps(sys.argv[1:])+"\\n")\n' +
            f'os.execv({real!r}, [{real!r}, *sys.argv[1:]])\n')
        if os.name == 'nt':
            fixture_path = tmp/'launcher.py'
            fixture_path.write_text(fixture, encoding='utf-8', newline='\n')
            launcher.write_text(f'@echo off\n@"{sys.executable}" "{fixture_path}" %*\n',
                                encoding='utf-8', newline='\n')
        else:
            launcher.write_text(fixture, encoding='utf-8', newline='\n')
        launcher.chmod(0o755)
        control = subprocess.run([str(launcher), '--version'], cwd=tmp, text=True, capture_output=True)
        assert control.returncode == 1 and 'no default toolchain' in control.stderr
        source = tmp/'Tiny.lean'
        source.write_text('module\n\npublic import Init\n\n@[expose] public section\nexample : True := trivial\n')
        report = tmp/'result.json'
        subprocess.run([sys.executable, str(ROOT/'scripts/check_canonical_challenge.py'),
                        '--lean-bin', str(launcher), '--source', str(source), '--report', str(report)],
                       cwd=ROOT, check=True)
        result = json.loads(report.read_text())
        assert result['status'] == 'pass' and result['exit_code'] == 0
        assert result['resolved_compiler'] == real
        assert result['lean_binary_sha256'] == hashlib.sha256(Path(real).read_bytes()).hexdigest()
        assert result['fresh_working_directory'] and result['repository_builds_excluded']
        assert [json.loads(line) for line in calls.read_text().splitlines()] == [['-j1', '--print-prefix']]
        receipt = {'status': 'pass', 'scope': 'Synthetic project-sensitive launcher and tiny-module regression; not real elan or full Challenge verification', 'negative_control': {'exit_code': control.returncode, 'stderr': control.stderr}, 'launcher_calls_at_root': [['-j1', '--print-prefix']], 'isolated_compile': result}
        (ROOT/'reports/canonical-launcher-regression.json').write_text(json.dumps(receipt, indent=2)+'\n')
        print('PASS: project-sensitive launcher resolved before isolated tiny-module compilation; no global default needed')

if __name__ == '__main__': main()
