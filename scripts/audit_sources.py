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
from generate_standalone import ROOT, LOCAL_PREFIXES, code_only, closure, generate, imports


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
             if not (ROOT/name).is_file() or (ROOT/name).read_bytes() != content.encode('utf-8')]
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
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        if re.search(r'\b(?:sorry|admit|axiom)\b', code_only(source)):
            violations.append(str(path.relative_to(ROOT)))
    challenge = code_only(generated['Challenge.lean'])
    solution = code_only(generated['Solution.lean'] + ''.join(content for name, content in generated.items() if name.startswith('PresentationPackage/')))
    comparator = json.loads((ROOT/'comparator.json').read_text())
    local_comparator = json.loads((ROOT/'reports/comparator-local.json').read_text())
    targets = ['PresentationComplex.presentation_complex', 'PresentationComplex.every_group_fundamental_group']
    comparator_valid = (comparator == local_comparator and comparator.get('theorem_names') == targets
                        and comparator.get('definition_names') == [])
    active = shipped + [ROOT/'Challenge.lean', ROOT/'Solution.lean', ROOT/'reports/AuditSolution.lean'] + sorted((ROOT/'scripts').glob('*.lean'))
    headers = [str(p.relative_to(ROOT)) for p in active if not code_only(p.read_text()).lstrip().startswith('module\n')]
    oversized = [str(p.relative_to(ROOT)) for p in active if len(p.read_text().splitlines()) > 10000]
    challenge_closure, _ = closure(['Challenge'])
    forbidden = {'Solution', 'PresentationComplex.Main', 'PresentationComplex.FundamentalGroup',
                 'PresentationComplex.CW', 'PresentationComplex.Hausdorff',
                 'PresentationComplex.EveryGroupPresentation', 'CellAttachment.Main'}
    bad_imports = [n for n, _ in challenge_closure if n in forbidden or n.startswith('PresentationPackage.Proof')]
    construction = code_only(generated['PresentationPackage/Construction.lean'])
    leaked_targets = [n for n in ['presentation_complex', 'every_group_fundamental_group']
                      if re.search(r'\b(?:theorem|def|axiom)\s+' + n + r'\b', construction)]
    extra_generated = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT/'PresentationPackage').glob('*.lean') if p.relative_to(ROOT).as_posix() not in generated)
    local_challenge_imports = [n for n in imports(generated['Challenge.lean'])
                               if n.split('.')[0] in LOCAL_PREFIXES or n in ['Solution', 'Challenge']]
    construction_prefix_matches = generated['Challenge.lean'].startswith(generated['PresentationPackage/Construction.lean'])
    challenge_bytes = len((ROOT/'Challenge.lean').read_bytes())
    challenge_byte_cap_exceeded = challenge_bytes > 102400
    packaging_ok = not (extra_generated or headers or oversized or bad_imports or leaked_targets or local_challenge_imports or challenge_byte_cap_exceeded) and construction_prefix_matches
    result = {
        'unexpected_generated_modules': extra_generated,
        'challenge_repository_import_failures': local_challenge_imports,
        'challenge_utf8_bytes': challenge_bytes,
        'challenge_byte_cap_exceeded': challenge_byte_cap_exceeded,
        'challenge_byte_cap': 102400,
        'challenge_identical_construction_prefix': construction_prefix_matches,
        'packaging_module_header_failures': headers,
        'packaging_line_cap_failures': oversized,
        'packaging_line_cap_basis': 'Conservative user-provided 10,000 lines/file; current official policy not re-read',
        'active_lean_file_line_counts': {str(p.relative_to(ROOT)): len(p.read_text().splitlines()) for p in active},
        'challenge_proof_dependency_failures': bad_imports,
        'construction_headline_leaks': leaked_targets,
        'status': 'pass' if not (stale or collisions or violations) and comparator_valid and packaging_ok else 'fail',
        'comparator_targets_and_configs_match': comparator_valid,
        'scope': 'static audit only; does not assert elaboration, kernel checking, hosted verification, or registry acceptance',
        'stale_generated_files': stale,
        'private_visibility_transform': 'Remove private modifiers only in generated standalones to eliminate module-dependent helper names; generated proof helpers remain stable; original modules use explicit public exports.',
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
