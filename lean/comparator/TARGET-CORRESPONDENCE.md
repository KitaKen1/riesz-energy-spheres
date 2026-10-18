# Current FC target correspondence

`lean/Challenge.lean` is byte-identical to `FClikelean/RieszEnergySpheres.lean`.
There are eighteen statement drafts: nine open problems and nine solved variants.
`comparator.json` selects only the latter, in dimensions 2, 8 and 24.

| Family | Selected declaration prefix | Dimensions |
| --- | --- | --- |
| Riesz lattice coefficient | `RieszSphereFC.riesz_energy_lattice.variants` | 2, 8, 24 |
| Logarithmic lattice coefficient | `RieszSphereFC.log_energy_lattice.variants` | 2, 8, 24 |
| Cap discrepancy lattice coefficient | `RieszSphereFC.cap_discrepancy_lattice.variants` | 2, 8, 24 |

`FCSolution.lean` now declares exactly these nine target signatures. Its
independent `FCDefinitions.lean` is connected to the proof library by:

- `FCAreaBridge` and `FCDefinitionBridge`: area, physical energies and cap discrepancy;
- `FCBackgroundBridge`: the Gamma expression for the continuous Riesz energy;
- `FCThetaBridge`: triangular, E8 and Leech theta series;
- `FCCoefficientBridge` and `FCE8CoefficientBridge`: the regular Epstein continuation,
  the logarithmic derivative and the removable E8 value at distance exponent 2.

The Leech theta identity uses its weight-12 modular form and first two Fourier
coefficients, including the minimum-norm proof in `Riesz.FCLeechMinimum24`.

The frozen FC source SHA-256 is
`24c8bbfab4701aa7445ee2090e11f5b26e3a24bb1bb0ad278a3a03818ee95b57`.
`check-inputs.py` enforces this hash, the exact Challenge copy, the source manifest,
proof-hole checks and the proof-only mirror. `check-solution-targets.py` checks
all nine source signatures. Comparator independently compares their elaborated
statements and dependent definitions; its CI result is recorded separately.

The previous reference and its correspondence notes are retained in
`verification/legacy-targets/` as historical material only.
