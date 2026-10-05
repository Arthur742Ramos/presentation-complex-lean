# Standalone generation and local verification

The generated `Solution.lean` contains the complete local import dependency
closure of `PresentationComplex.Main`, including the arbitrary-presentation
headline, exact bouquet and quotient generator compatibility, the ordinary
Hausdorff CW structure, and the every-group consequence with a genuine 2-cell.
The generated `Challenge.lean` contains the actual construction dependency
closure of `PresentationComplex.Relators` and the exact `completeStatement`
declaration copied from `Main`. It does not import Solution, Main,
FundamentalGroup, CW, Hausdorff, or the proved cell-attachment headline.
Its sole intentional theorem hole is `PresentationComplex.presentation_complex`.

## Mechanical transformations

Imports are resolved in deterministic dependency order and consolidated into
external-only public imports. `module` and `@[expose] public section` commands
are consolidated. Each original module is enclosed in a section; any scope
left open at its original EOF is explicitly closed. Namespace identities,
declaration bodies, source notices, and both full Apache-2.0 and MIT notices
are preserved.

Private visibility modifiers are removed **only in generated files** so that
helpers have stable names in both generated module environments. Otherwise
private helpers such as `loopCircleMap`'s circle chart would receive different
`_private.Challenge` and `_private.Solution` identifiers and prevent exact body
comparison. `reports/static-source-audit.json` records all affected helper
names and checks them against all explicitly declared names in the complete
source closure. This is a static collision check; successful elaboration is
still required.

`definition_names` is deliberately empty in the local Comparator config.
Lake treats that list as permitted definition holes, checking their types
rather than exact bodies. An empty list ensures `completeStatement` and all
of its transitive actual construction bodies remain immutable during
Challenge/Solution comparison. Additional construction constants are exported
for review, without authorizing any definition hole.

## Reproducible commands

On a normal exact-toolchain installation, replace PREFIX with the installed
Lean prefix (`lean --print-prefix`). Commands below do not download tools.

```sh
python3 scripts/generate_standalone.py
python3 scripts/derive_verification_metadata.py --lean-prefix PREFIX
python3 scripts/generate_standalone.py --check
python3 scripts/verify_local.py --lean-prefix PREFIX --stages static
python3 scripts/verify_local.py --lean-prefix PREFIX --stages source_replay
python3 scripts/verify_local.py --lean-prefix PREFIX --stages compile axioms exports kernels comparator
```

`source_replay` recompiles every shipped modular Lean source in an isolated
local output tree, rather than relying on previously compiled local modules.
`compile` separately elaborates Challenge and Solution from source using only
pinned external package caches. Both stages replace inherited LEAN_PATH;
no sibling project `.olean` fallback is allowed. The default memory cap is
6144 MiB and all compiler/checker work is serial.

`derive_verification_metadata.py` parses primitive targets and the conditional
Quot builtin targets directly from the selected pinned
`src/lean/lake/Lake/CLI/Check.lean`, recording its SHA256. It does not maintain
a hand-copied primitive list. The axiom audit explicitly includes both
headlines, exact generator and inclusion compatibility, the CW construction
and dimension bounds, Hausdorff instance, retained relator-cell indexing,
and the every-group generator and genuine-2-cell consequences.

Direct local kernel stages use bundled leanchecker, leanchecker-paranoid,
NanoDa with strict enforcement of only `propext`, `Quot.sound`, and
`Classical.choice`, and `con-ron --verified --jobs=1`. An optional `lean4lean`
check can be selected separately. Individual checker logs and binary/export
hashes are recorded. An absent checker or incompatible checker format must
be reported as blocked or failed, not inferred to pass.

The Comparator stage preserves its normal bubblewrap sandbox. There is no
no-sandbox or custom-wrapper bypass. If the runtime cannot create the
sandbox, the report records the precise blocker. Direct kernel checks and
comparison of previously produced local exports do not establish sandboxed
source-build provenance or official hosted acceptance.

## Current boundary

Preparation and static checks do not certify Lean elaboration or any kernel.
Only completed stages in `reports/local-verification-results.json` may be
reported as passing. Official hosted full verification, trusted Challenge
rendering, registry intake, and registry acceptance remain separate outcomes.
This tooling neither performs network/publication/authentication actions nor
submits anything to a registry.
