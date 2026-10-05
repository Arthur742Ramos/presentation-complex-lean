# Reproduction and E2E gates

Current status: all 83 modular sources, both generated standalones, the full
standard-only axiom audit, and four direct kernel checks pass on the exact pin.
Normal serial and aggregate Lake builds also pass.
The sandboxed Comparator reaches
its kernel stage but is blocked by NETLINK_ROUTE namespace creation. No
security workaround was used. Official hosted verification and registry
intake have not run.

## Exact toolchain

Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned in lean-toolchain,
lakefile.toml, and lake-manifest.json. Local env.sh only selects an existing
verified toolchain/cache on the current host and is deliberately not published.
A normal installation should use the pinned Lean toolchain through Lake.

Separate mandatory gates:
1. Run `lake exe cache get` for official pinned Mathlib compiled dependencies
2. Run `python3 scripts/generate_standalone.py`
3. Run `lake build` on the complete package (on constrained hosts, first run
   `python3 scripts/build_lake_serial.py`, which uses normal Lake builds only)
4. Run `python3 scripts/build_sources.py` to replay every shipped Lean source
   serially, not just the headline theorem's dependency closure
5. Check reproducible Challenge/Solution bytes against frozen modular source
6. Check exact Challenge/Solution types and standard-only transitive axioms
7. Perform the independent source review and direct exported kernel checks
8. Complete the separately authorized official full hosted verification and
   trusted statement rendering, on the exact frozen public commit

Do not treat one module, a local whole build, a direct kernel pass, or an official
hosted verdict as equivalent to the other stages. Registry intake and acceptance
are separate outcomes, requiring their own exact-source authorization and review.
No registry intake or official hosted verification has been performed for this
project at this checkpoint.

## Ordinary CI

The pinned `.github/workflows/ci.yml` performs normal serial and aggregate
Lake builds, every-source replay, reproducible standalone/source checks, and
prints the complete transitive axiom audit. This is ordinary repository CI;
it is not the official hosted Comparator or registry protocol.

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
Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; the
responsible maintainers are Arthur Freitas Ramos, David Barros Hulak, and Ruy
Jose Guerra Barretto de Queiroz. Original reused Apache2/MIT source notices are
preserved. No mathematical or worldwide-priority novelty is claimed.
