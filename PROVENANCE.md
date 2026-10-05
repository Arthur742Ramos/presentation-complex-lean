# Source provenance and current status

First-party authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Responsible maintainers: Arthur Freitas Ramos,
David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
No invented roles or mathematical novelty are claimed.

All 83 modular sources, both standalones, the standard-only transitive axiom
audit, and four direct independent kernels pass on the exact toolchain. Normal
serial and aggregate Lake builds also pass.
The sandboxed Comparator is blocked at
kernel launch; no official hosted or registry verdict is claimed.

The genuine arbitrary graph realization, covering, contraction, and comparison
are adapted from Arthur742Ramos/finite-graph-fundamental-group exact commit
`dd57e3ab8bc5a7042fcc5498e778b008d87ac032`, Apache-2.0. The upstream rank wrapper
is finite, but the graphCombinatorialToTopologicalEquiv proof is arbitrary.
Only that dependency closure is retained here: unrelated finite-rank wrappers
and Consequences are omitted. Narrow Lean4.32→4.35rc2 port changes preserve the
arbitrary theorem; explicit case eliminators and transparency adaptations are
recorded in the files. No finiteness hypothesis is introduced.

The actual complex-disk adjunction, arbitrary-family two-cell kernel theorem,
open cover, and groupoid quotient proof are reused from
Arthur742Ramos/cell-attachment-lean exact commit
`8883b95e8ace951e27c2bc86f95d02397787dd59`, Apache-2.0.
That project's ordinary all-object topological SVK infrastructure is from
Arthur742Ramos/classical-svk-lean exact commit
`874680e16db88b4a41daadf56eafbac79fd2f748`.

Inherited Basold–Bruin–Lawson path subdivision source is from
Dominique-Lawson/Directed-Topology-Lean-4 exact commit
`009529606c66d37ef93b4b81b8587f71ce4d2c56`. Its MIT notices are preserved
in Lean4/LICENSE.md. Original backport author notices in CellAttachment/
CircleGenerator.lean are preserved. First-party source remains Apache-2.0.

The square-to-complex-disk bridge uses Yury Kudryashov's proved convex-body
homeomorphism in Mathlib.Analysis.Convex.GaugeRescale. The ordinary CW class
is Mathlib.Topology.CWComplex.Classical.Basic, credited in its upstream source.
The one-vertex combinatorial/free-group equivalence is constructed via universal
properties, with actual generator-path equations; no free-group or CW oracle.

Mathematical source: Allen Hatcher, Algebraic Topology, Corollary 1.28,
printed page 52, Cornell edition:
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=61 .
The target explicitly permits arbitrary independent-universe presentations.
No worldwide-priority claim is made.

Exact toolchain: Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
