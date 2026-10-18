# Reproduce verification

`Challenge.lean` is an exact copy of the eighteen-statement FC draft.
Comparator selects the nine solved dimension variants in `comparator.json`.
The independent Challenge compilation is separate from proof verification.

`check-inputs.py` checks source hashes, the proof-only mirror, the exact FC copy,
its target inventory, and proof holes. `check-solution-targets.py` reports missing
solution declarations and source signature differences. `FCSolution.lean` supplies
the nine exact FC declarations, using the mathematical bridges described in
`TARGET-CORRESPONDENCE.md`.

Comparator checks the elaborated statements and dependent definitions in addition
to auditing proof axioms and replaying the solution. The frozen FC hash is enforced
before any build.

On a disposable Linux GitHub runner, `install-tools.sh` installs the exact Comparator,
Lean4export and Landrun sources in `pins.json`. Comparator and exporter use Lean
4.34.1, with a recorded toolchain-only patch from 4.34.0. `run-check.sh` uses real
Landrun under the systemd address-family restriction required by upstream Comparator.
`run-check.sh 2`, `run-check.sh 8` and `run-check.sh 24` each check the three
targets in that dimension. `dimension-config.py` validates that these groups
partition the nine fixed targets. Every group must pass Comparator's fresh
builtin-kernel replay and the all-nine-target axiom audit.

On macOS, the upstream `scripts/fake-landrun.sh` can be used for a development
comparison. It does not supply a Linux sandbox; local development results and
sandboxed Linux CI results are reported separately.

The proof build is split into six dependency-ordered batches, followed by separate
dimension-specific Comparator jobs. Every compile batch has a four-hour compile
budget and a 330-minute job limit. A timeout is a failed batch.
Each Comparator has a five-hour execution budget and a 330-minute job limit.

The optional `full_environment_replay` workflow-dispatch input additionally runs
`leanchecker --fresh FCSolution` on every imported declaration, including those
outside the selected proofs' dependency closure. This larger audit exceeded its
five-hour job limit in the sandbox. It is separate from the required fresh kernel
replay of each selected proof inside Comparator; if requested, it must succeed.

The default workflow starts without any previous-run project proof cache. Each
batch downloads the completed batches from this same run, verifies their commit,
run, attempt, source-manifest and file hashes, then uploads only its new or changed
products. It uses GitHub artifacts for these handoffs. Mathlib's pinned dependency
cache is still fetched normally. Thus a new repository can execute the whole chain
in one workflow without manually accumulating partial caches across reruns.

`build-stages.json` covers the complete 1,245-module import closure of `FCSolution`
and `FCAudit`. `build-stage.py` checks that coverage and dependency order. The
partition uses measured sandbox module timings plus estimates for unmeasured
modules; successful CI, rather than the estimates, establishes that every batch
fits its runtime budget.

The sandbox's three dimension jobs passed all nine targets in
[run 39109164457](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/39109164457),
using verified completed build products from an earlier run. Its receipts are in
`verification/sandbox-ci-39109164457-attempt-1/`. The public workflow uses the
same dimension partition after its own six-stage build.

Verification receipts are retained
for 90 days; regenerable intermediate build products for seven days. Archive the
receipts, job logs and tested commit in `verification/`. Intermediate product ZIPs
need not be published: their GitHub metadata and digests are recorded in the archive.

The pinned FC snapshot uses an older Mathlib than this proof project.
`prepare-fc-utils.py` verifies the upstream utility entry-point hash and removes
only its three imports of the unused `FormalConjecturesForMathlib` aggregate.
It retains Mathlib and every FC attribute and linter implementation, and saves
the exact patch and before/after hashes with the job receipts. The Challenge
remains byte-identical to the FC draft. This is a compatibility build with the
proof compiler, not an unmodified upstream FC project build.
