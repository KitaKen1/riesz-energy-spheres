# Lean proof without Comparator

The mathematical sources are byte-identical to `../lean/`.
The project Comparator reference, axiom-audit entry point, checker scripts and unused upstream Comparator benchmark are omitted.
The retained third-party notices and original hash manifests describe the canonical vendored snapshot.
The default target remains the complete `FCSolution` containing the nine solved FClikelean variants.

```sh
lake exe cache get
lake build
```

Lean 4.34.1 and the fixed `lake-manifest.json` are required.
