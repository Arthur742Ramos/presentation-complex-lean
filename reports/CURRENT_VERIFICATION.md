# Current bounded-module verification

Verified proof-source commit: `29ab34cb685371dbe71dfd669c3a090e9a5e7e7d`. Later evidence/documentation commits do not change Lean inputs.
Base: merged main `a4e65503a5ac5e6255ba8eed23542d5b35a16e67`, exact tree of reviewed `8d28fa01d660ce8ade2d49c9bc4306b20b1df83d`.

| Gate | Result |
| --- | --- |
| Deterministic generation and static audit | PASS: all 90 active Lean files have module headers and at most 10,000 lines; exactly two Challenge holes; no proof dependency or selected-headline leak |
| Source preservation | PASS: 84 original declaration bodies and all 77 original generated source sections preserved, modulo module/import/visibility commands and blank lines |
| Isolated complete source replay | PASS: all 87 original/generated modules on the exact pin; frozen fingerprint unchanged |
| Fresh package compilation | PASS: Construction, Proof1, Proof2, Solution, Challenge |
| Standard-only axiom audit | PASS: all 21 selected/supplemental targets |
| Exact exports | PASS: Challenge and Solution, byte-bound in stage record |
| Direct kernels | PASS: leanchecker, leanchecker-paranoid, nanoda, con-ron |
| Normal Lake | PASS: 89 serial targets and aggregate 3,234 jobs, private cache |
| Independent source review | PASS before compilation; final publication consistency review pending |
| Supported local type/body Comparator | BLOCKED: unchanged sandbox cannot create NETLINK_ROUTE socket; no semantic comparison verdict |
| Old Challenge/new Solution Comparator | NOT RUN after same sandbox blocker; no bypass attempted |
| Remote ordinary CI for this repair | PENDING publication |
| Official hosted verification / trusted rendering | NOT RUN |
| Registry submission / acceptance | NOT SUBMITTED / NOT ACCEPTED |

## Exact package

- Construction: 5,877 lines; Proof1: 7,996; Proof2: 4,236; Solution: 229; Challenge: 265
- Lean: `4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Original reproduction files: 84; generated dependency modules: 3; entrypoints: 2; audit harness: 1
- Eleven previously private helpers are exposed only where required by public signatures or direct exposed terms; 31 remain private. Bodies and generated helper names are unchanged
- The 10,000-line cap is conservatively enforced from the user-provided constraint; current official policy has not been re-read

All three maintainers and original source/license notices are retained. Challenge physically shares only the construction module with Solution and never imports either proof chunk. The selected theorem types still require arbitrary independent-universe presentations, genuine indexed cells, Hausdorffness, connectedness, and ordinary fundamental-group equivalence. No target or hypothesis is weakened.

See [local stage results](local-verification-results.json), [normal build evidence](normal-lake-result.json), [line/header/dependency audit](static-source-audit.json), [body preservation](intake-packaging-preservation.json), [visibility inventory](module-visibility-inventory.json), [exact sandbox diagnostic](comparator-blocker.txt), and [review manifest](review-package-manifest.json).
Historical passes under `history/pre-bounded-a4e65503` describe previous bytes only. Local proofs and ordinary CI do not establish official readiness or registry acceptance.
