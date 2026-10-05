# Verification reports

**Canonical Challenge repair: dependency-only compilation and supplemental type/body comparison passed; official Comparator remains unverified.**
See [the current verification matrix](CURRENT_VERIFICATION.md). Historical proof checks apply to the byte-identical Solution package; the repaired Challenge has separate hash-bound evidence.

## Active script-managed paths

These paths remain in place because scripts or CI produce or consume them:

- `standalone-manifest.json` and `standalone-manifest.txt`: module lists and hashes
- `comparator-local.json`, `export-targets.json`, `solution-export-targets.json`,
  and `verification-plan.json`: derived comparison/export configuration
- `AuditSolution.lean`: generated target and transitive-axiom audit harness
- `static-source-audit.json`: source-only audit output
- `local-verification-results.json`: hash-bound, stage-by-stage local results
- `nanoda-config.json`: local checker configuration
- `canonical-challenge.json`: isolated renamed compilation and supplemental type/body comparison
- `canonical-challenge-negative-control.json`: exact historical missing-import failure
- `canonical-source-preservation.json`: unchanged proof-package source hashes

A generated manifest/configuration is not a passing verdict. Active files may
retain pre-repair data until their owning scripts regenerate them. Even `pass`
results apply only if their complete inputs match the reviewed source. New logs
are written here by the same scripts; logs already changed by a new run are
preserved in place during the history reorganization.

## Historical checkpoint

[history/pre-packaging-4eb147d](history/pre-packaging-4eb147d/README.md) preserves
all 33 tracked report artifacts from the previous public checkpoint, with their
original contents unchanged. Historical-only reports/logs have moved there;
script-managed metadata also retain active paths above.

See [../SETUP.md](../SETUP.md) for reproduction instructions and
[../REVIEW.md](../REVIEW.md) for the review manifest.
