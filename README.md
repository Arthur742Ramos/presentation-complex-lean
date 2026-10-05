# Fundamental groups of arbitrary presentation complexes

**Canonical Challenge repair: dependency-only compilation and supplemental type/body comparison passed; official Comparator remains unverified.**
See [the current verification matrix](reports/CURRENT_VERIFICATION.md). Historical proof checks apply to the byte-identical Solution package; the repaired Challenge has separate hash-bound evidence.

## Start here

The small review interface is:

- [Challenge.lean](Challenge.lean): two theorem targets and their inlined, dependency-only
  construction, with exactly two intended theorem holes
- [PresentationPackage/](PresentationPackage/): Solution construction and two bounded proof modules
- [Solution.lean](Solution.lean): the public-import proof entrypoint, with no intended admissions
- [comparator.json](comparator.json): both theorem targets; no definition holes
- [formalization.yaml](formalization.yaml): scope, attribution, and status
- [LICENSE](LICENSE) and [Lean4/LICENSE.md](Lean4/LICENSE.md): Apache-2.0 and MIT notices

[REVIEW.md](REVIEW.md) explains the minimal review manifest and retained
reproduction source. [SETUP.md](SETUP.md) gives the pinned-toolchain checks.

## Mathematical targets

For arbitrary generator type `S`, independently universe-polymorphic relator-index
type `R`, and `r : R → FreeGroup S`,
`PresentationComplex.presentation_complex` states that the actual presentation
space has:

- The weak quotient topology obtained from one vertex, one interval per generator,
  and one closed complex disk per relator index
- An ordinary Mathlib CW structure whose actual cell types are equivalent to a
  singleton in dimension zero, `S` in dimension one, and `R` in dimension two,
  with no higher cells
- Hausdorffness and path connectedness
- Ordinary path-based fundamental group equivalent to
  `FreeGroup S ⧸ Subgroup.normalClosure (Set.range r)`, with the actual bouquet
  inclusion and literal generator-loop equations

`PresentationComplex.every_group_fundamental_group` states that every group is
the fundamental group of its constructed connected Hausdorff CW complex, with
no cells above dimension two and a nonempty two-cell type. The presentation uses
all group elements as generators, multiplication-table relators, and an identity
relator. `everyGroupPi1Equiv_generator` is a supplemental audited/exported theorem;
its generator equation is not part of the selected every-group headline type.

The targets impose no finite/countable restriction, CW input, or assumed generator
identification. Duplicate and identity relators retain indexed disk cells; empty
generators retain a vertex and empty relators give the bouquet.

## Sources and evidence

Lean `4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.
[PROVENANCE.md](PROVENANCE.md) records exact source commits, authors, maintainers,
and the classical mathematical reference. No mathematical or worldwide-priority
novelty is claimed.

All historical reports are preserved under
[reports/history/pre-packaging-4eb147d](reports/history/pre-packaging-4eb147d/README.md).
Their pass records describe their recorded source hashes only. Read
[reports/README.md](reports/README.md) before interpreting active report files.
