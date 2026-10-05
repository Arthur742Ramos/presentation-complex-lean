#!/usr/bin/env python3
"""Bind an already passing legacy replay to its frozen input source snapshot.

Never creates a passing verdict. Requires recorded source_replay pass, exactly
matching before/after modular sources, and all replay outputs/logs. This lets
standalone regeneration retain applicable modular replay evidence.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_standalone import ROOT
from verify_local import digest, modular_snapshot, save


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-audit', default='reports/static-source-audit.json')
    parser.add_argument('--report', default='reports/local-verification-results.json')
    args = parser.parse_args()
    audit_path = ROOT/args.source_audit
    report_path = ROOT/args.report
    frozen = json.loads(audit_path.read_text())
    result = json.loads(report_path.read_text())
    entry = result.get('stages', {}).get('source_replay', {})
    if entry.get('status') != 'pass' or entry.get('exit_code') != 0:
        raise SystemExit('No already-passing source replay to bind; this command cannot create a verdict')
    snapshot, fingerprint = modular_snapshot()
    if frozen.get('status') != 'pass' or frozen.get('modular_source_sha256') != snapshot:
        raise SystemExit('Current modular sources do not exactly match the frozen static source audit')
    if entry.get('module_count') != len(snapshot):
        raise SystemExit('Recorded replay count does not cover every frozen modular source')
    evidence = {}
    for relative in snapshot:
        module = '.'.join(Path(relative).with_suffix('').parts)
        output = ROOT/'.toolchain/replayed/lean'/Path(relative).with_suffix('.olean')
        log = ROOT/'reports'/('replay-'+module.replace('.', '_')+'.log')
        if not output.is_file() or not log.is_file():
            raise SystemExit(f'Missing recorded replay output or log for {module}')
        evidence[module] = {'olean_sha256': digest(output), 'log_sha256': digest(log)}
    entry['modular_source_fingerprint_sha256'] = fingerprint
    entry['modular_source_sha256'] = snapshot
    entry['replay_output_evidence'] = evidence
    entry['source_binding'] = {
        'status': 'bound existing pass; no new replay verdict created',
        'frozen_static_audit_sha256': digest(audit_path),
        'basis': 'Existing terminal pass and exact current modular hashes match the frozen pre-replay static snapshot; all modular replay outputs/logs exist',
    }
    save(report_path, result)
    print(f'BOUND existing replay pass to {len(snapshot)} exact modular source hashes')


if __name__ == '__main__': main()
