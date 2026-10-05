# Minimal review manifest

**Status: UNVERIFIED repair after public checkpoint `4eb147d`.** See the
[current verification matrix](reports/CURRENT_VERIFICATION.md). This guide
organizes review; it does not certify revised proofs or authorize registry intake.

## Primary review package

Read these files first:

1. `Challenge.lean`: shared construction and two explicit theorem holes
2. `Solution.lean`: standalone implementation of both targets, without intended
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
- Both standalones use the same external imports and elaborate the same shared
  construction prefix before their respective targets/proofs

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

The repaired tree contains 84 modular Lean sources, including five library root
modules, plus two generated standalones and an audit harness. Solution's local
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
