# Compact Challenge desktop verification

The previous public Challenge was 257,036 bytes and exceeded the user-reported 102,400-byte intake cap. The compact Challenge is 74,913 bytes, with 1,691 lines and two intended theorem holes. Construction definitions moved into three construction-only modules; Solution uses the construction and three proof modules. Both selected headline statements are retained.

| Gate | Current result |
| --- | --- |
| Frozen generation, actual file-byte cap and static source audit | PASS; exact LF output; 74,913 bytes; no Solution/modular admissions or custom axioms |
| Project-sensitive compiler launcher regression | PASS; repository-local resolver and empty-directory negative control |
| Normal modular, Challenge, Solution and aggregate builds | PASS; each exit 0 |
| Every shipped source replay | PASS; 93 modules, exit 0 |
| Renamed dependency-only Challenge compilation | PASS; fresh directory; repository build paths excluded |
| Supplemental theorem/construction expression comparison | PASS; 252 declaration types and 94 definition bodies; equal serialized bytes; only six explicit private auxiliary names mapped bijectively |
| Isolated generated-package compilation | PASS; construction, Proof1, Proof2, Proof3, Solution and Challenge; exact source/artifact hashes recorded |
| Transitive axiom closures | PASS; 21 audited targets; only propext, Classical.choice and Quot.sound |
| Fresh Challenge and Solution exports | PASS; exact export hashes recorded |
| Direct bundled checkers | PASS; leanchecker, leanchecker-paranoid, lean4lean, nanoda_bin, con-leche, con-ron |
| Sandboxed Comparator | BLOCKED; pinned Lake requires Linux namespaces on this Windows host; sandbox preserved |
| Fresh independent review | PENDING for the compact source and desktop portability deltas |
| Remote CI, hosted verification and trusted rendering | NOT RUN |
| Registry submission and public push | NOT PERFORMED |

These are local gates. They do not establish hosted or sandboxed Comparator acceptance. Older source-replay and checker reports do not apply to this changed generated package.

The normal build used dependency-ordered library roots and an aggregate Lake build within a Windows Job Object. Every-source replay then compiled every shipped module serially. This replaces the repeated per-module Lake startup loop for this desktop run; the interrupted earlier attempt is retained as an operational interruption, not a theorem failure.

## Exact inputs and receipts

- Upstream source commit: `7a0c182015b38a5b851d1d9cca805531f63b9f89`; verified Git tree `5026d2d70a234373c18107ad1316c15da39b108c`
- Reviewed compact input patch: `59e22f7ae54ecc877606743338301ea02990a031a70a136450a21ad58cf6167f`
- Challenge SHA-256: `6ca5faef5b964e41aa2c45e343160218d5cdeb2f0fe73c72bec1a978b07b2446`
- Lean: `Lean (version 4.35.0-rc2, x86_64-w64-windows-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release)`
- Windows Lean binary SHA-256: `16e2c9c597d71fbbadd2b909c3fad5ea7830a4b7aa0123b93e0f3b19de7b959e`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- [Build and replay receipt](desktop-build-receipt.json), [supplemental stage receipt](desktop-supplemental-receipt.json), [isolated compile/axiom/export/checker receipt](desktop-local-verification.json), [final canonical comparison](desktop-final-canonical-challenge.json)

All heavy stages ran sequentially on CPC-arfre-036B6, restricted to four exposed CPUs and 24 GiB aggregate job memory, with a 16 GiB free-RAM floor and a 90-minute stage deadline. No credential, permission, network or security setting was changed. Both selected targets, all maintainers, source notices and licenses are retained. The original source snapshot is verified by tree contents; its local baseline commit is synthetic and does not supply upstream history.
