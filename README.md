# Fundamental groups of arbitrary presentation complexes

All 83 modular sources and both standalones compile on the pinned toolchain.
The complete standard-only axiom audit and four independent direct kernel
checks pass on the exact exports. Normal serial and aggregate Lake builds also pass.
The sandboxed Comparator is blocked at kernel launch; no
official hosted verdict or registry acceptance is claimed.

For every generator type `S`, independently universe-polymorphic relator-index
type `R`, and family `r : R → FreeGroup S`, this project constructs:

- The actual weak-topology endpoint quotient of one vertex and one interval for
  each generator
- A circle attaching map for every relator, obtained from an actual finite word
  loop with the ordinary path-fundamental-group multiplication convention
- The genuine quotient of that bouquet and the family of closed complex disks
- An ordinary Mathlib CW structure on this exact space, with one zero-cell,
  one one-cell per generator, one two-cell per relator index, and no higher cells
- Hausdorffness and path connectedness of the actual quotient
- An ordinary path-based fundamental-group equivalence with
  `FreeGroup S ⧸ Subgroup.normalClosure (Set.range r)`
- Literal compatibility with the actual bouquet inclusion and each generator
  interval loop

No finite/countable restriction, CW input, assumed generator identification,
custom mathematical axiom, or admitted topological bridge appears in the theorem.
Duplicate and identity relators retain their genuine indexed disk cells.
Empty generators still give a vertex; empty relators give the bouquet.

## Headline theorems

`PresentationComplex.presentation_complex` proves the complete arbitrary
presentation statement, including the actual inclusion and generator equations.

`PresentationComplex.every_group_fundamental_group` realizes any group as the
fundamental group of a connected Hausdorff CW complex with no cells above two
and a nonempty two-cell type. Its CW structure is therefore two-dimensional.
The explicit presentation uses all group elements as generators, multiplication
table relators, and an identity relator. The generator loop indexed by `g`
is labeled exactly `g` by `everyGroupPi1Equiv_generator`.

Named cell-index equivalences preserve every generator and relator index.
Mathlib's CW domains use the maximum norm, so an actual interior/boundary-
respecting homeomorphism connects its square two-cell domain to the complex disk.

## Reproduction and verification boundary

Lean `4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.
See [SETUP.md](SETUP.md) for independent verification gates and status.
Generated `Challenge.lean` has one explicitly intended theorem hole;
`Solution.lean` is the admission-free standalone proof. No definition holes are
permitted in the comparison configuration.

See [PROVENANCE.md](PROVENANCE.md) for exact source commits, licenses, author
credits, and the mathematical reference. No mathematical or worldwide-priority
novelty is claimed.
