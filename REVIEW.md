# Minimal review manifest

**Bounded module repair: source/static checks passed; fresh proof verification pending.**
See [the current verification matrix](reports/CURRENT_VERIFICATION.md). Previous merged-source passes are historical and do not certify these new module boundaries.

## Primary review package

The byte-bound file list is [review-package-manifest.json](reports/review-package-manifest.json).
Read these files first:

1. `Challenge.lean`: shared construction and two explicit theorem holes
2. `Solution.lean`: public-import entrypoint for both targets, without intended
   proof admissions
3. `comparator.json`: exactly both headline theorem names, an empty definition-hole
   list, and the permitted standard logical axioms
4. `formalization.yaml`: scope, source relationships, attribution, and status
5. `LICENSE` and `Lean4/LICENSE.md`: complete Apache-2.0 and MIT license notices
6. `PROVENANCE.md`: exact upstream source commits and the mathematical reference

`README.md`, this manifest, and `SETUP.md` provide the reading and reproduction
instructions. Generated standalones retain source notices and both licenses.
Edit modular sources and regenerate rather than hand-editing the standalones.

## Changes being reviewed

- `completeStatement` now requires the chosen CW structure's actual zero-, one-,
  and two-cell types to be equivalent to a singleton, the generator type, and the
  relator-index type, respectively
- `presentation_complex` and `every_group_fundamental_group` are both independent
  Challenge targets and Comparator theorem targets
- `PresentationComplex/EveryGroupConstruction.lean` supplies shared construction
  definitions without bringing the every-group proof into Challenge
- Both entrypoints publicly import `PresentationPackage.Construction`;
  `Proof1` and `Proof2` preserve proof-source order and never enter Challenge

Challenge has exactly two intended theorem holes and no definition holes.
Solution must solve both against the same construction. The supplemental
`everyGroupPi1Equiv_generator` theorem is audited/exported, but its generator
compatibility equation is not part of the selected every-group headline type.
Source generation alone does not establish exact type/body comparison or kernel
verification.

## Reproduction source retained

The small review interface does not replace its auditable reproduction source:

- `PresentationComplex/` and its root `.lean` module: construction, topology,
  cell structure, fundamental-group comparison, and both headlines
- `FiniteGraphFreeGroup/`, `CellAttachment/`, `ClassicalSVK/`, `Lean4/`, and their
  root `.lean` modules: reused infrastructure, source notices, port documentation,
  and provenance manifest
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`: exact dependency pins
- `scripts/` and `.github/workflows/ci.yml`: generation, replay, audits, ordinary
  builds, and independent verification tooling
- Active files in [reports/README.md](reports/README.md): generated module/hash
  manifests, comparison/export targets, stage results, and the audit harness

The repaired tree contains 84 reproduction Lean sources plus three generated package modules, including five library root
modules, plus two generated entrypoints and an audit harness. Solution's local
proof closure contains 77 modules; Challenge's shared construction closure contains
16. These are packaging counts, not compilation verdicts. Every-source replay
covers the complete retained modular tree, beyond the headline dependency closure.

The upstream `Lean4/directed_van_kampen.lean` and `Lean4/all.lean` umbrella are
intentionally absent. The ordinary-path proof uses the attributed
`Lean4/path_descent_helpers.lean` extraction; see [Lean4/PORTING.md](Lean4/PORTING.md).
Historical upstream manifest entries do not require adding unused modules.

## Historical material

All 33 tracked reports from `4eb147d` are preserved byte-for-byte under
[reports/history/pre-packaging-4eb147d](reports/history/pre-packaging-4eb147d/README.md).
Historical-only artifacts move out of the active directory; script-managed paths
remain available and any logs already changed by a new run are left untouched.
An archived pass, generated metadata, or old active-path result does not verify
new source. Full source and history remain available for independent reproduction;
ignored local caches and build outputs are outside the review interface.

## Bounded module package

Include `PresentationPackage/Construction.lean`, `Proof1.lean`, and `Proof2.lean` with both entrypoints. Construction contains no selected headline proof and imports no proof chunk. Every active Lean source, including the audit harness, has a module header and at most 10,000 lines. This cap is conservatively enforced from the user-provided intake constraint; current official policy has not been independently re-read. Generation partitions only at original module boundaries, retaining scope closure, helper names, notices, and declaration order.

The module port exposes eleven existing helpers required in public signatures or exposed computational bodies; 31 proof-local helpers retain privacy. See `reports/module-visibility-inventory.json` for the complete dependency inventory. All bodies and generated helper names are unchanged.
