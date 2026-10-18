# Local verification receipts

The publication files are an uncommitted local candidate based on the existing
public manuscript commit. Local receipts identify the exact source manifest and
proof digest. The base commit alone does not identify this candidate; the input
receipt therefore leaves `tested_commit` null while the working tree is dirty.

The earlier local receipts below belong to a previous target revision. The owner
subsequently requested testing on `KitaKen1/ci-test-sandbox`, and then requested
connecting the nine solved FC variants without changing their statements.

The current Challenge is the exact eighteen-statement FC file, with nine solved
variants selected by Comparator. Its frozen SHA-256 is enforced in
`lean/comparator/check-inputs.py`. The solution and coefficient bridges have been
rewritten for those exact targets. Current sandbox run metadata and outcomes are
recorded in `work-status.json`; earlier failed attempts remain archived.

[`local-review.json`](local-review.json) records the candidate hashes, toolchain,
manuscript hashes and the status of each local command. The Japanese review note is
[`STATEMENT-REVIEW.ja.md`](STATEMENT-REVIEW.ja.md).

| Check | Receipt |
|---|---|
| Source hashes, identical proof mirror, 14 written theorem types and standalone statement body | `local-inputs/input-check.json`, `source-check.log` |
| Mathlib-only reference build, with 14 intentional theorem holes | `challenge-build.log` |
| Previous FC-style draft, with 14 intentional theorem holes | Historical `fc-draft.log`; compact revision unchecked |
| Complete canonical proof build | Stopped at owner's request; `local-build.log` is partial |
| Target axiom audit | Not run |
| Comparator | Not run |

`lattice-bridge-probe.log` is empty because the early, successful compilation of
the lattice/theta/Epstein bridge subset emitted no diagnostics. The definitive
bridge check would require the complete `FCBridge` build, which was not completed.

The statement review is recorded in
[`TARGET-CORRESPONDENCE.md`](../lean/comparator/TARGET-CORRESPONDENCE.md).
Comparator compares formal expressions and their dependencies; the natural-language
interpretation is reviewed separately. A macOS development run uses upstream's
fake Landrun shim and does not establish the sandbox guarantees of Linux CI.

`work-status.json` records unfinished and held stages explicitly. No CI pass or
fresh standalone kernel replay is claimed by these local receipts.
