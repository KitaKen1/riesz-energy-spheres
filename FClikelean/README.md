# Formal Conjectures draft

`RieszEnergySpheres.lean` is an independently written submission draft importing
`FormalConjecturesUtil`. It has eighteen theorem statements. Each of the three
families separates two open problems: existence of an asymptotic coefficient in
arbitrary dimensions, and its predicted lattice value in dimensions 2, 4, 8 and 24.
Each lattice-coefficient problem is followed by variants for S², S⁴, S⁸ and S²⁴,
in that order: the S⁴ variant is `research open`, while S², S⁸ and S²⁴ are
`research solved`. In total there are nine open statements and nine solved variants.
The theorem proofs intentionally contain `sorry`.

| Coefficient existence, open | Lattice coefficient, open | Source |
| --- | --- | --- |
| `riesz_energy` | `riesz_energy_lattice` | The two assertions in [BHS12], Conjecture 3 |
| `log_energy` | `log_energy_lattice` | [BHS12], equation (7) and Conjecture 4 |
| `cap_discrepancy` | `cap_discrepancy_lattice` | [Br11], §3; [BB25], §5.3 |

Each `_lattice` statement has `.variants.dimension_two`, `.variants.dimension_four`,
`.variants.dimension_eight` and `.variants.dimension_twenty_four` declarations
immediately below it. The four-dimensional variants cite the original predictions;
they do not claim a solution in [Ki26].

Every statement's docstring cites its source. The solved variants additionally cite
the Lean proof repository [Ki26] through a `formal_proof` URL. Bibliographic entries
and links are in the module docstring.

The two Riesz parent statements cover −2 < s < d + 2, excluding s = 0 and s = d. The solved
variants cover the manuscript's range −2 < s < d, s ≠ 0, combining minimization for
positive exponents and maximization for negative exponents. The regular theta
integral includes the E8 value at s = 2. The s = 4 example has no separate statement.
The open S⁴ Riesz variant covers the corresponding range −2 < s < 4, s ≠ 0.

The existence statements concern arbitrary dimensions d ≥ 2. The three lattice
statements concern dimensions 2, 4, 8 and 24. In particular, `log_energy_lattice`
retains the original Conjecture 4's scope, while `log_energy` records the separate
coefficient-existence question. The cap existence statement requires a positive
limit; its lattice statement specifies the predicted value.

The format follows the upstream FC contribution guide and problem files at
commit `c77fdd446d23539302aa73bcfae4a9fa962b8382`, including:

- [Fisher information convexity](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/2605.18081/FisherInformationConvexity.lean)
- [Riemann zeta moments](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Paper/RiemannZetaMoments.lean)
- [Pfister's problem and solved variants](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Paper/PfisterPythagorasNumber.lean)
- [Green's problem 42 and dimension variants](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/GreensOpenProblems/42.lean)
- [Atiyah–Sutcliffe](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/1102.4662/AtiyahSutcliffe.lean)

The proposed FC destination is `FormalConjectures/Paper/RieszEnergySpheres.lean`.

The coefficients use independently defined theta series: the triangular quadratic
form, the scaled D4 checkerboard lattice, the E8 divisor sum and the Leech identity
Θ = (7 E₄³ + 5 E₆²)/12. The continued Epstein function takes the distance exponent s,
including its regular value at zero. Thus the logarithmic coefficient differentiates
directly in s.

The Comparator Challenge is an exact copy of this file and selects its nine solved
variants. The existing fourteen legacy proof declarations have not yet been connected
to these exact FC definitions and target names. The six
open parent statements separate the general existence problems from the lattice
formulas; three additional open variants record the four-dimensional cases.

The file has no dependency on the repository's proof modules or ancillary files.
The sandbox CI compiles the exact Challenge and checks whether the solution provides
these targets. Results are recorded in `../verification/`; the solved labels in this
statement draft do not themselves certify equivalence to the proof project.
