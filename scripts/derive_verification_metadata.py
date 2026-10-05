#!/usr/bin/env python3
"""Derive export/audit metadata from the exact toolchain's Lake.Check source.

This command reads source files only and never executes Lean or another checker.
Use --lean-prefix for the pinned toolchain, or --lake-check-source explicitly.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_standalone import ROOT, code_only

PERMITTED_AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
THEOREM = 'PresentationComplex.presentation_complex'
THEOREMS = [THEOREM, 'PresentationComplex.every_group_fundamental_group']
# Only declarations independently present in both files are comparison targets.
CONSTRUCTION_TARGETS = [
    'PresentationComplex.completeStatement',
    'PresentationComplex.groupRelators', 'PresentationComplex.EveryGroupSpace',
    'PresentationComplex.everyGroupPoint',
    'PresentationComplex.Vertex', 'PresentationComplex.Bouquet',
    'PresentationComplex.base', 'PresentationComplex.edgeLoop',
    'PresentationComplex.signedEdgeLoop', 'PresentationComplex.wordLoop',
    'PresentationComplex.relatorWord', 'PresentationComplex.relatorLoop',
    'PresentationComplex.relatorMap', 'PresentationComplex.Space',
    'PresentationComplex.inclusion', 'PresentationComplex.point',
    'PresentationComplex.relatorNormalClosure',
    'CellAttachment.Disk', 'CellAttachment.Raw', 'CellAttachment.AttachingRel',
    'CellAttachment.Space', 'CellAttachment.quotientMap',
    'CellAttachment.inclusion', 'CellAttachment.inclusionPi1',
]
AXIOM_TARGETS = [
    THEOREM,
    'PresentationComplex.every_group_fundamental_group',
    'PresentationComplex.presentationPi1Equiv',
    'PresentationComplex.presentationPi1Equiv_inclusion',
    'PresentationComplex.presentationPi1Equiv_generator',
    'PresentationComplex.presentationMap_exact',
    'PresentationComplex.bouquetEquiv',
    'PresentationComplex.bouquetEquiv_edgeLoop',
    'PresentationComplex.attachingLoopClass_eq',
    'PresentationComplex.presentationCW',
    'PresentationComplex.presentationCW_generatorCells',
    'PresentationComplex.presentationCW_relatorCells',
    'PresentationComplex.presentationCW_noHigherCells',
    'PresentationComplex.presentation_t2Space',
    'PresentationComplex.everyGroupPi1Equiv',
    'PresentationComplex.everyGroupPi1Equiv_generator',
    'PresentationComplex.everyGroupCW_hasTwoCell',
    'PresentationComplex.groupPresentationEquiv',
    'PresentationComplex.groupPresentationEquiv_generator',
    'CellAttachment.cell_attachment_exact',
    'FiniteGraphFreeGroup.graphCombinatorialToTopologicalEquiv',
]


def unique(names: list[str]) -> list[str]:
    return list(dict.fromkeys(names))


def derive(source_path: Path) -> dict[str, str]:
    source = source_path.read_text(encoding='utf-8')
    clean = code_only(source)
    primitive = re.search(r'^def primitiveTargets\b(.*?)(?=^def builtinTargets\b)', clean, re.M | re.S)
    builtin = re.search(r'^def builtinTargets\b(.*?)(?=^def verifyMatch\b)', clean, re.M | re.S)
    if primitive is None or builtin is None:
        raise ValueError('cannot locate exact Lake.Check primitiveTargets/builtinTargets definitions')
    primitives = re.findall(r'``([A-Za-z_][A-Za-z_0-9.]*)', primitive.group(1))
    if not primitives or len(primitives) != len(set(primitives)):
        raise ValueError('empty or duplicated primitive target list')
    # The conditional Quot addition in the exact source is required, not guessed.
    b = builtin.group(1)
    condition = re.search(r'if\s+\(← getLegalAxioms\)\.contains\s+``Quot.sound\s+then', b)
    array = re.search(r'additional\s*:=\s*additional\s*\+\+\s*#\[(.*?)\]', b, re.S)
    if condition is None or array is None:
        raise ValueError('unrecognized Lake.Check builtin-target logic; review the exact source')
    builtins = re.findall(r'``([A-Za-z_][A-Za-z_0-9.]*)', array.group(1)) if 'Quot.sound' in PERMITTED_AXIOMS else []
    common = unique(builtins + THEOREMS + PERMITTED_AXIOMS + primitives + CONSTRUCTION_TARGETS)
    solution = unique(common + AXIOM_TARGETS)
    comparator = {
        'challenge_module': 'Challenge', 'solution_module': 'Solution',
        'theorem_names': THEOREMS, 'definition_names': [],
        'permitted_axioms': PERMITTED_AXIOMS, 'enable_nanoda': True,
    }
    metadata = {
        'status': 'prepared; no compile, export, comparator, or kernel verdict asserted',
        'primitive_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'primitive_source': 'pinned Lean distribution src/lean/lake/Lake/CLI/Check.lean',
        'primitive_targets': primitives, 'builtin_targets': builtins,
        'comparison_theorems': THEOREMS, 'comparison_definitions': [],
        'construction_export_targets': CONSTRUCTION_TARGETS,
        'axiom_audit_targets': AXIOM_TARGETS, 'permitted_axioms': PERMITTED_AXIOMS,
        'challenge_export_target_count': len(common), 'solution_export_target_count': len(solution),
        'note': 'Every-group and generator compatibility are audited/exported from Solution. The independent Challenge compares its arbitrary-presentation target with all transitive construction bodies. No definition holes are authorized; definition_names is empty.',
    }
    audit = ('module\n\nimport Solution\n\nuniverse u v\n'
             'example : PresentationComplex.completeStatement.{u,v} :=\n'
             '  PresentationComplex.presentation_complex\n\n'
             '#print PresentationComplex.completeStatement\n'
             '#check PresentationComplex.every_group_fundamental_group\n'
             '#check PresentationComplex.everyGroupPi1Equiv_generator\n\n' +
             '\n'.join('#print axioms ' + name for name in AXIOM_TARGETS) + '\n')
    def dump(value): return json.dumps(value, indent=2) + '\n'
    return {
        'reports/comparator-local.json': dump(comparator),
        'reports/export-targets.json': dump(common),
        'reports/solution-export-targets.json': dump(solution),
        'reports/verification-plan.json': dump(metadata),
        'reports/AuditSolution.lean': audit,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    selector = parser.add_mutually_exclusive_group(required=True)
    selector.add_argument('--lean-prefix', type=Path)
    selector.add_argument('--lake-check-source', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = args.lake_check_source or args.lean_prefix / 'src/lean/lake/Lake/CLI/Check.lean'
    outputs = derive(source)
    for name, content in outputs.items():
        path = ROOT / name
        if args.check:
            if not path.is_file() or path.read_text(encoding='utf-8') != content:
                raise SystemExit(f'STALE: {name}; rerun metadata derivation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding='utf-8')
    print(f"{'CHECKED' if args.check else 'PREPARED'} verification metadata from exact Lake.Check source")


if __name__ == '__main__': main()
