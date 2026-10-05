# Reproduction and E2E gates

Current status: implementation in progress, with individual components checked.
The complete theorem and whole-project verification are not yet available.

## Exact toolchain

Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned in lean-toolchain,
lakefile.toml, and lake-manifest.json. Local env.sh only selects an existing
verified toolchain/cache on the current host and is deliberately not published.
A normal installation should use the pinned Lean toolchain through Lake.

When the complete modules are implemented:
1. Run `lake exe cache get` for official pinned Mathlib compiled dependencies
2. Run `lake build` on the complete package
3. Run `python3 scripts/build_sources.py` to replay every shipped Lean source
   serially, not just the headline theorem's dependency closure
4. Generate Challenge/Solution standalone files reproducibly from frozen source
5. Check exact Challenge/Solution types and standard-only transitive axioms
6. Perform the independent source review and direct exported kernel checks
7. Complete the separately authorized official full hosted verification and
   trusted statement rendering, on the exact frozen public commit

Do not treat one module, a local whole build, a direct kernel pass, or an official
hosted verdict as equivalent to the other stages. Registry intake and acceptance
are separate outcomes, requiring their own exact-source authorization and review.
No registry intake or official hosted verification has been performed for this
project at this checkpoint.

## Publication

The authorized destination is public Arthur742Ramos/presentation-complex-lean,
with arthurpalomar742 invited for Write access. Publish the verified reviewed
source, confirm exact remote commit/public visibility, and verify the Write
invitation. This authorization does not cover credential-scope expansion,
security-setting changes, financial actions, or registry intake.

## Source preservation

Frozen milestone backups include the exact source archive, SHA256 manifest, and
recoverable gitbundle, explicitly labeled with their verification status.

## Provenance

See PROVENANCE.md and reports/statement-review.md. First-party authors are Arthur
Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; Arthur
is sole responsible maintainer. Original reused Apache2/MIT source notices are
preserved. No mathematical or worldwide-priority novelty is claimed.
