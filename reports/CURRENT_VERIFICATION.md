# Current canonical Challenge repair

The user-reported canonical build excludes repository-generated oleans. The old
Challenge imported `PresentationPackage.Construction`, so its earlier ordinary
package-build pass did not test that boundary. The repair inlines exactly the
same construction source and leaves Solution and all three package modules
byte-for-byte unchanged.

| Gate | Result |
| --- | --- |
| Historical negative control | PASS: renamed old Challenge fails at line 225 with unknown module prefix `PresentationPackage` in the dependency-only environment |
| Renamed canonical Challenge | PASS: fresh unique module and empty working directory, eight pinned dependency build paths plus standard library; no repository/generated-package oleans |
| Supplemental expression comparison | PASS: 550 declaration types and 169 definition bodies, including both headline types; equal serialized bytes |
| Compiler-private auxiliary handling | Exactly nine names mapped bijectively: six equation theorems and three splitter definitions; kinds checked; no other names normalized |
| Public declaration comparison | All 541 public declaration types and 166 definition bodies match without private-name mapping; no public type/body references a private constant or projection |
| Deterministic generation and static audit | PASS: module headers and fewer than 10,000 lines for every active Lean source, including the comparison harness; exactly two Challenge holes |
| Proof source preservation | PASS: Solution, Construction, Proof1, Proof2 unchanged from the reviewed bounded package |
| Normal Lake and fresh audit/export | PASS: Challenge 3,149 jobs; Solution 3,152; aggregate 3,234; all 21 Solution audit targets standard-only; fresh repaired Challenge export |
| Historical Solution replay / axioms / direct kernels | Passes apply to unchanged, hash-bound Solution package only; see the preserved pre-canonical report |
| Official sandboxed Comparator | No new verdict; previously blocked by host NETLINK_ROUTE restriction; no bypass or retry |
| Remote ordinary CI | PENDING publication |
| Hosted canonical acceptance / rendering | NOT RUN for this repair |
| Registry submission | No new submission authorized or performed |

## Evidence and limits

- [Canonical compile and comparison receipt](canonical-challenge.json)
- [Historical failure reproduction](canonical-challenge-negative-control.json)
- [Source preservation](canonical-source-preservation.json)
- [Static audit](static-source-audit.json)
- [Normal builds, audit and export](canonical-normal-lake.json)
- [Historical proof and package evidence](history/pre-canonical-a209b96/README.md)

The supplemental checker extracts one environment per process. It compares exact
bytes of deterministic Lean expression DAGs, ignoring binder names/annotations
and metadata, and rewriting only nine explicitly listed compiler-private names.
It preserves constant names, levels, expressions, let flags, and definition
values otherwise. Both 2,153,939-byte snapshots have SHA-256
`16358cb422a8e8e207eebb09fcfd5841bbc8f7d0559f417030af036eb38519ba`.
This is additional local evidence, not the official sandboxed Comparator.
The first dual-environment attempt was killed by signal 9; its receipt is retained.
The first sequential attempt correctly rejected unmatched module-local private
names; its receipt and diagnostic snapshots were retained before adding the
reviewed explicit mapping.

The manifest's unused `Cli` dependency has no local build directory and is the
only explicitly allowed omission. Its exact pinned manifest entry is recorded.
All other missing dependency builds cause failure. Successful isolated
elaboration establishes that no Cli artifact was required.

## Exact package

- Challenge: 5,913 lines; Construction: 5,877; Proof1: 7,996; Proof2: 4,236; Solution: 229
- Challenge SHA-256: `2690aaf4e12651244f880bf4e5ed6c57d3cf8dd089a97afdad079e88e476a270`
- Lean: `4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- The line cap follows the user-provided constraint; current official policy was not re-read

Both selected theorem statements, all three maintainers, source notices, and
licenses are preserved. No target or hypothesis is weakened. Ordinary CI now
runs the renamed dependency-only regression and supplemental comparison after
its normal build. It performs no registry submission.
