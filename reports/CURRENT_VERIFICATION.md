# Current exact-source verification

Source commit: `0d3c2d1fd36aa0aa94e56b5d309de25308267c1f`.
This is a local repair candidate, not a public readiness or official acceptance verdict.
The complete-package review/build gates below are not yet complete.

- Lean: `4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`
- Compiler SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Solution SHA-256: `c767e45dbf54df02239aec8e17adf709c43c8ba9c97508d8b7527dcbda83ef86`
- Challenge SHA-256: `1620d6f2a345f461657ad3be3dc512dcc2b6c5b2530a38325b649043afb68e96`

| Gate | Current result |
| --- | --- |
| Deterministic generation and static source/config audit | PASS; 84 modular sources; 77-module Solution closure; 16-module Challenge construction closure |
| Three changed modular sources | PASS on exact compiler |
| Isolated Solution and Challenge compilation | PASS; Challenge has exactly two intended theorem holes |
| Complete selected/supplemental standard-only axiom audit | PASS |
| Exact Challenge and Solution exports | PASS |
| Four direct kernel checks | RUNNING |
| Full 84-module isolated source replay | NOT RUN for repair |
| Normal serial and aggregate Lake build | NOT RUN for repair |
| Independent source/statement review | IN PROGRESS |
| Local exact type/body Comparator | NOT RUN for repair; prior checkpoint blocked at sandbox launch |
| Official hosted verification / trusted rendering | NOT RUN |
| Registry submission / acceptance | NOT SUBMITTED / NOT ACCEPTED |

The machine-readable local stage record is [local-verification-results.json](local-verification-results.json).
Its current hashes bind the standalone stages; earlier pass records under
[history](history/pre-packaging-4eb147d/) cannot certify this repair.
No official protocol or security gate is bypassed. A direct kernel pass is not
an official hosted verdict. See [the review manifest](../REVIEW.md) for the
minimal review inputs and retained reproduction sources.
