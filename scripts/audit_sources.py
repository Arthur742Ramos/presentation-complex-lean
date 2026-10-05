#!/usr/bin/env python3
"""Read-only static source/hole/visibility audit; this is not a Lean verdict."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_standalone import ROOT, LOCAL_PREFIXES, code_only, closure, generate


def declaration_names(source: str) -> list[tuple[str, bool]]:
    scopes: list[tuple[str, str]] = []
    declared = []
    for line in code_only(source).splitlines():
        start = re.match(r'^\s*(?:(?:noncomputable|public)\s+)?(section|namespace)(?:\s+(\S+))?\s*$', line)
        if start:
            kind, label = start.groups(); scopes.append((kind, label or '')); continue
        end = re.match(r'^\s*end(?:\s+(\S+))?\s*$', line)
        if end:
            label = end.group(1)
            if not scopes: raise ValueError('unmatched source end')
            if label is None or scopes[-1][1] == label:
                scopes.pop(); continue
            names = []
            for n in range(len(scopes)-1, -1, -1):
                if scopes[n][0] != 'namespace': break
                names.insert(0, scopes[n][1])
                if '.'.join(names) == label:
                    del scopes[n:]; break
            else:
                raise ValueError('mismatched named source end')
            continue
        definition = re.match(r'^\s*(?:@\[[^\]]+\]\s*)?((?:(?:private|protected|noncomputable|unsafe|partial|public)\s+)*)'
                              r'(?:def|abbrev|theorem|lemma|opaque|inductive|class|structure)\s+([^\s(:]+)', line)
        if definition:
            modifiers, name = definition.groups()
            namespace = '.'.join(label for kind, label in scopes if kind == 'namespace')
            if name.startswith('_root_.'): full = name[len('_root_.'):]
            elif namespace.startswith('_root_.'): full = namespace[len('_root_.'):] + '.' + name
            else: full = namespace + '.' + name if namespace else name
            declared.append((full, 'private' in modifiers.split()))
    return declared


def audit() -> dict:
    generated = generate()
    stale = [name for name, content in generated.items()
             if not (ROOT/name).is_file() or (ROOT/name).read_text(encoding='utf-8') != content]
    closure_modules, _ = closure(['PresentationComplex.Main'])
    locations: dict[str, list[dict]] = {}
    privacy = []
    for module, path in closure_modules:
        source = path.read_text(encoding='utf-8')
        for name, private in declaration_names(source):
            locations.setdefault(name, []).append({'module': module, 'was_private': private})
            if private: privacy.append({'stable_name': name, 'module': module})
    collisions = [{'name': name, 'declarations': origins} for name, origins in locations.items()
                  if len(origins) > 1 and any(d['was_private'] for d in origins)]
    shipped = [p for prefix in LOCAL_PREFIXES for p in sorted((ROOT/prefix).rglob('*.lean'))]
    shipped += [ROOT/(prefix + '.lean') for prefix in LOCAL_PREFIXES if (ROOT/(prefix + '.lean')).is_file()]
    violations = []
    hashes = {}
    for path in shipped:
        source = path.read_text(encoding='utf-8')
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(source.encode()).hexdigest()
        if re.search(r'\b(?:sorry|admit|axiom)\b', code_only(source)):
            violations.append(str(path.relative_to(ROOT)))
    challenge = code_only(generated['Challenge.lean'])
    solution = code_only(generated['Solution.lean'])
    comparator = json.loads((ROOT/'comparator.json').read_text())
    local_comparator = json.loads((ROOT/'reports/comparator-local.json').read_text())
    targets = ['PresentationComplex.presentation_complex', 'PresentationComplex.every_group_fundamental_group']
    comparator_valid = (comparator == local_comparator and comparator.get('theorem_names') == targets
                        and comparator.get('definition_names') == [])
    result = {
        'status': 'pass' if not (stale or collisions or violations) and comparator_valid else 'fail',
        'comparator_targets_and_configs_match': comparator_valid,
        'scope': 'static audit only; does not assert elaboration, kernel checking, hosted verification, or registry acceptance',
        'stale_generated_files': stale,
        'private_visibility_transform': 'Remove private modifiers only in generated standalones to eliminate module-dependent helper names; no modular source changed.',
        'stable_publicized_helpers': privacy,
        'publicized_name_collisions': collisions,
        'modular_source_admissions_or_axioms': violations,
        'challenge_sorry_count': len(re.findall(r'\bsorry\b', challenge)),
        'solution_sorry_count': len(re.findall(r'\bsorry\b', solution)),
        'shipped_modular_source_count': len(shipped),
        'modular_source_sha256': hashes,
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', default='reports/static-source-audit.json')
    args = parser.parse_args()
    result = audit()
    path = ROOT/args.report
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(f"STATIC {result['status'].upper()}: {result['shipped_modular_source_count']} modular sources; "
          f"{len(result['stable_publicized_helpers'])} stable helpers, {len(result['publicized_name_collisions'])} visibility collisions")
    if result['status'] != 'pass' or result['challenge_sorry_count'] != 2 or result['solution_sorry_count'] != 0:
        raise SystemExit(1)


if __name__ == '__main__': main()
