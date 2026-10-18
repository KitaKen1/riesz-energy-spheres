# Natural-language and Lean correspondence

## Scope and conventions

This is a local mathematical review by the coding assistant, not an external referee report.
The table identifies the mathematical clauses that can be inspected mechanically.
Lean proves the bridge equalities; Comparator verifies the reference against the solution.
It does not itself interpret natural language.

| Natural-language clause | Lean representation | Review |
|---|---|---|
| Unit sphere of dimension d in R^(d+1) | `Sphere d`, `Metric.sphere 0 1` in `EuclideanSpace R (Fin (d+1))` | Ambient dimension and radius explicit. |
| N distinct points | `Fin N ↪ Sphere d` | Injectivity, not a list with repeated points. |
| Chordal distance | `dist` inherited from the Euclidean ambient space | No angular distance conversion. |
| Ordered pairs, diagonal excluded | Double sum over `Finset.univ.erase i` | Each unordered pair occurs twice. |
| Uniform probability and surface area | `uniform d`, inverse total `toSphere` mass; `area d` | Matches `sphereProbabilityD` and `sphereAreaD`. |
| Positive energy minimized | `sInf (range ...)` in `normalizedMin` | Parameter assumptions `0<s<d`; no optimizer assumed. |
| Negative energy maximized | `sSup (range ...)` in `normalizedMax` | Parameter assumptions `−2<s<0`. |
| Every sufficiently large integer N | `Tendsto ... atTop` on `N : Nat` | No subsequence or extra geometric hypotheses. |
| Covolume-one triangular lattice | Integer span of rows scaled by `(sqrt (sqrt 3/2))^−1` | `RieszSphereFC.triangular_eq` identifies the proved lattice. |
| Covolume-one Leech lattice | Integer span of the explicit 24 by 24 rows scaled by `1/sqrt 8` | `RieszSphereFC.leech_eq` identifies the proved lattice. |
| Epstein convention Z_L(s)=sum norm^−s | `hexZeta (s/2)`, `leechZeta (s/2)`, `e8Zeta (s/2)` | The Lean argument is u=s/2, not s. |
| Continued value at s=0 | `hexZetaCont`, `leechZetaCont` | Avoids the totalized Gamma quotient's value at zero. |
| Logarithmic coefficient Z_L prime(0) | `(1/2) * Re (deriv ... 0)` | Chain rule from u=s/2; not a missing factor of two. |
| Negative log kernel | `-Real.log (dist ...)` | Minimized, with `+(N/d) log N` in the normalized limit. |
| Cap directions and heights | `(uniform d).prod (volume.restrict (Icc (−1) 1))` | Height measure is dt, not dt/2. |
| L2 discrepancy of normalized counts | `Real.sqrt (capSquared d X)` | Square root taken before the configuration infimum. |
| E8 removable point s=2 | Dedicated `riesz_energy_two_sphere8` | The raw Riemann-zeta product is not used at its pole-zero point. |

## Target inventory

All statements are in `Challenge.lean`, all proofs in `FCSolution.lean`, and all
reference definitions in `FCTargetDefinitions.lean`. Neither the reference nor the
standalone FC draft imports the proof library. The FC submission draft imports
`FormalConjecturesUtil` and gives its own theta-series definition of the coefficients.

| Target | Mathematical statement |
|---|---|
| `riesz_energy_four_sphere8` | The inverse-fourth minimum on S⁸ has leading coefficient 7/16 and next coefficient −5√210/48. |
| `riesz_energy_sphere2` | For 0 < s < 2, the normalized minimum converges to A_2^(−s/2) Z_L(s). |
| `riesz_energy_neg_sphere2` | For −2 < s < 0, use a supremum; the normalized maximum on S^2 has the same continued Epstein coefficient. |
| `log_energy_sphere2` | The logarithmic minimum on S^2, after subtracting W N² and adding (N/2) log N, has the displayed linear coefficient. |
| `cap_discrepancy_sphere2` | The optimal L² cap discrepancy on S^2, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/4). |
| `riesz_energy_sphere8` | For 0 < s < 8, the normalized minimum converges to A_8^(−s/8) Z_L(s). The removable value s=2 is stated separately. |
| `riesz_energy_neg_sphere8` | For −2 < s < 0, use a supremum; the normalized maximum on S^8 has the same continued Epstein coefficient. |
| `log_energy_sphere8` | The logarithmic minimum on S^8, after subtracting W N² and adding (N/8) log N, has the displayed linear coefficient. |
| `cap_discrepancy_sphere8` | The optimal L² cap discrepancy on S^8, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/16). |
| `riesz_energy_sphere24` | For 0 < s < 24, the normalized minimum converges to A_24^(−s/24) Z_L(s). |
| `riesz_energy_neg_sphere24` | For −2 < s < 0, use a supremum; the normalized maximum on S^24 has the same continued Epstein coefficient. |
| `log_energy_sphere24` | The logarithmic minimum on S^24, after subtracting W N² and adding (N/24) log N, has the displayed linear coefficient. |
| `cap_discrepancy_sphere24` | The optimal L² cap discrepancy on S^24, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/48). |
| `riesz_energy_two_sphere8` | The removable E8 value s=2 uses 120 ζ′(−2), multiplied by A_8^(−1/4). |

## Checked bridge

`FCBridge.lean` checks agreement of the actual lattice sets, theta functions,
continued Epstein functions, normalized extremal energies, surface areas and
cap discrepancy. `check-inputs.py` compares the 14 written theorem types between
`Challenge.lean` and `FCSolution.lean`. The compact FC draft writes energy and
normalization formulas directly in its statements; only its target inventory is
compared automatically. Its mathematical correspondence requires the owner's
audit. Execution history is recorded separately in `verification/`.

The independent FC draft uses the distance exponent `s` as the argument of
`epstein`, so its logarithmic coefficient differentiates directly in `s`.
The canonical Comparator reference above uses `u=s/2` and a half-derivative.
The FC Leech theta series is written through the divisor-sum expansions of
E₄ and E₆, using `(7 E₄³ + 5 E₆²)/12`. No matrix from the proof project is used
in that draft. The draft has not been compiled or audited.

The manuscript clauses being compared are `eq:main` (positive and negative Riesz
limits), `eq:s8four` (inverse fourth power on S⁸), `eq:logmain` and `eq:log8`
(logarithmic limits), and `eq:discdef` and `eq:discmain` (cap discrepancy) in
`PDF/riesz-energy-spheres.tex`. The special S⁸ value at `s=2` is also given in
the manuscript's E8 coefficient section. The three positive-exponent targets,
three negative-exponent targets and the separate S⁸ `s=2` target cover the
entire stated Riesz range; the other targets cover the three logarithmic and
three discrepancy statements, plus the explicit inverse-fourth corollary.

In the S⁸ logarithmic target the coefficient is expanded, as in `eq:log8`.
From the displayed E8 zeta formula and the special zeta values,
`Z'_E8(0) = -60 ζ'(-3) - (log π)/2`. Adding
`(log A_8)/8`, with `A_8 = 32 π^4 / 105`, gives exactly
`-60 ζ'(-3) + (5/8) log 2 - (1/8) log 105`.

The existing manuscript presents an all-scale Gaussian minorant theorem as an
input. The Lean proof obtains the spherical Gaussian profiles needed for the
final results from the vendored OpenAI triangular certificates and E8Leech
certificates. For E8 and Leech, the certified lattice scales satisfy `β ≠ 1`;
the rescaling bridges `sphereGaussianSharpProfileLower8_of_schwartz_input_off`
and `sphereGaussianSharpProfileLower24_of_schwartz_input_off` recover all
required spherical scales. No such exceptional scale remains in any of the
14 published statements. This distinction in proof routes is documented in
the README; an all-scale lattice certificate theorem is not claimed here.

For the interpretation of the coefficient as a continued Epstein zeta function,
see `hexEpsteinZeta_hasSum` in `Riesz/HexLattice2.lean` and
`leechEpsteinZeta_hasSum` in `Riesz/LeechEpstein24.lean`: they identify the functions
with the actual lattice sums on their convergence half-planes. The corresponding
continuation-at-zero lemmas are in `Riesz/SphereLog2.lean` and
`Riesz/SphereLog24.lean`. The covolume-one identities are
`hexLattice_covolume` and `leechLattice_covolume`.
For E8, `e8Epstein_hasSum` in `Riesz/E8Epstein.lean` identifies the explicit
zeta product with the lattice sum when `Re u > 4`, and
`e8Lattice_covolume` in `Riesz/E8Covolume.lean` proves covolume one.
`leechRelabelIsometry_image_leechLattice` in `Riesz/LeechModelRelabel24.lean`
identifies the matrix lattice with the independent Golay-code Leech model up to
a coordinate permutation. Finally, `energyRpow_four` in
`Riesz/SphereRieszMellinRpow8.lean` identifies the inverse-fourth power convention
with the general real-power Riesz convention.
