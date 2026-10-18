# Lean proof project

Use Lean 4.34.1 and the dependencies pinned in `lake-manifest.json`.

`Challenge.lean` is an exact copy of `../FClikelean/RieszEnergySpheres.lean`.
It contains eighteen statement drafts with `sorry`; Comparator selects the nine
solved variants. Never import Challenge into a solution.

`FCSolution.lean` supplies the nine exact FC declarations through
`FCDefinitions.lean` and the `FC*Bridge.lean` lemmas. These identify the
independent theta series, Epstein continuation, Gamma area, continuous energy
and cap discrepancy definitions with the existing sphere proof library.
`FCTargetDefinitions.lean` and `FCBridge.lean` are retained legacy sources and
are not imported by the current solution.

```sh
lake exe cache get
lake build Challenge
lake build FCSolution FCAudit
```

The workflow separately compiles the FC Challenge and builds the proof in six
dependency-ordered jobs. Completed build products pass through artifacts from
this same workflow; no previous-run project proof cache is required. Three
dimension-specific Comparator jobs then check all nine targets, their dependent
definitions, permitted axioms and fresh builtin-kernel replay. All three jobs
require all six completed batches and must pass.
Each batch has a four-hour compile budget; a timeout is a failure.
