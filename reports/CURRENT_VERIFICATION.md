# Current bounded-module verification

Base: merged main `a4e65503a5ac5e6255ba8eed23542d5b35a16e67`, exact tree of reviewed `8d28fa01d660ce8ade2d49c9bc4306b20b1df83d`.

- Source/static checks: PASS, including 84 preserved reproduction bodies, all 77 preserved generated source sections, 90 active module headers, line cap, two holes and Challenge independence
- Deterministic package: Construction 5,877 lines; Proof1 7,996; Proof2 4,236; Solution 229; Challenge 265
- Fresh exact-toolchain compilation, full replay, ordinary Lake build, axiom audit, exports, kernels: NOT RUN
- Exact type/body Comparator and independent final review: pending
- Official hosted verification/rendering: NOT RUN
- Registry: NOT SUBMITTED / NOT ACCEPTED

Lean 4.35.0-rc2 and Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. All three maintainers and source licenses are retained. The 10,000-line cap is enforced conservatively from the user-provided constraint; current official policy has not been re-read. Historical passes under `history/pre-bounded-a4e65503` describe previous bytes only.
