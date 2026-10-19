# Lean proof of next-order Riesz and logarithmic energy on spheres

Conjecture 3 of [Brauchart, Hardin and Saff (2012)](https://arxiv.org/abs/1202.4037)
asks whether the following Riesz energy asymptotics hold.

> **Conjecture 3: next-order Riesz energy.**
> Let $d\ge2$ and $-2<s<d+2$, $s\ne0,d$. On the unit sphere
> $\mathbb S^d\subset\mathbb R^{d+1}$, let $\mathcal E_s(d,N)$ be the optimal
> ordered sum $\sum_{i\ne j}|x_i-x_j|^{-s}$ over configurations of $N$ distinct
> points, minimized for $s>0$ and maximized for $s<0$. Then there is a constant
> $C_{s,d}$ such that
>
> $$\mathcal E_s(d,N)=V_{s,d}N^2+A_d^{-s/d}C_{s,d}N^{1+s/d}+o(N^{1+s/d}).$$
>
> Here $A_d$ is the sphere's area. For $s<d$, $V_{s,d}$ is the continuous energy
> of uniform probability measure; for $s>d$, its analytic continuation is used.
> In dimensions $d=2,4,8,24$, the additional prediction is
>
> $$C_{s,d}=Z_{L_d}(s),$$
>
> where $L_2,L_4,L_8,L_{24}$ are the covolume-one triangular, D4, E8 and Leech
> lattices, and $Z_L$ is the continued Epstein zeta function in the distance exponent.

Conjecture 4 of [Brauchart, Hardin and Saff (2012)](https://arxiv.org/abs/1202.4037)
asks whether the following logarithmic energy asymptotics hold.

> **Conjecture 4: the logarithmic energy coefficient.**
> Let $d\in\{2,4,8,24\}$, and let $\mathcal E_{\log}(d,N)$ be the minimum of
> the ordered logarithmic sum $-\sum_{i\ne j}\log|x_i-x_j|$ on $\mathbb S^d$.
> Then
>
> $$\mathcal E_{\log}(d,N)=W_dN^2-\frac Nd\log N+
> \left(Z'_{L_d}(0)+\frac1d\log A_d\right)N+o(N),$$
>
> where $W_d$ is the continuous logarithmic energy of uniform probability measure
> on the sphere.

A related spherical cap discrepancy conjecture in
[Brauchart (2011), §3](https://arxiv.org/abs/1103.3088) asks for the following
asymptotics. Its predicted lattice coefficients are also discussed in
[Bilyk and Brauchart (2025), §5.3](https://arxiv.org/html/2502.15984v1#S5.SS3).

> **Conjecture: optimal spherical cap $L^2$ discrepancy.**
> Let $d\ge2$, and let $\sigma_d$ be uniform probability measure on $\mathbb S^d$.
> For an $N$-point configuration $X\subset\mathbb S^d$, let $D_2(X)$
> be the square root of the integral of
> $\bigl(|X\cap C|/N-\sigma_d(C)\bigr)^2$ over spherical caps
> $C(z,t)=\{x:\langle x,z\rangle\ge t\}$, using uniform directions $z$ and Lebesgue height measure
> $dt$ on $[-1,1]$. Then there is a constant $K_d>0$ such that
>
> $$\inf_{|X|=N}D_2(X)=K_dN^{-1/2-1/(2d)}+o\!\left(N^{-1/2-1/(2d)}\right).$$
>
> For $d=2,4,8,24$, the predicted coefficient is
>
> $$K_d=\sqrt{-\kappa_d A_d^{1/d}Z_{L_d}(-1)},\qquad
> \kappa_d=\frac{\Gamma((d+1)/2)}{d\sqrt\pi\,\Gamma(d/2)}.$$

This repository provides Lean **4.34.1** sources for $d=2,8,24$,
with $-2<s<d$, $s\ne0$ for Riesz energy.

| Problem | Scope | Status |
|---|---|---|
| Conjecture 3 (Riesz) | General $d\ge2$ | Open |
| Conjecture 3 (Riesz) | $d=2,8,24$; $-2<s<d$, $s\ne0$ | Solved |
| Conjecture 4 (logarithmic) | $d=2,4,8,24$ | Open |
| Conjecture 4 (logarithmic) | $d=2,8,24$ | Solved |
| Cap discrepancy conjecture | General $d\ge2$ | Open |
| Cap discrepancy conjecture | $d=2,8,24$ | Solved |

The repository has two main components:

1. **A Formal Conjectures style statement.**
   [FClikelean/](FClikelean/) contains an independent statement draft with nine open
   problems and nine solved dimension variants, with references in the docstrings.
2. **The Lean proof.**
   [FCSolution.lean](lean/FCSolution.lean) provides the nine solved FC variants through
   the existing sphere energy proofs and the [definition bridges](lean/comparator/TARGET-CORRESPONDENCE.md).

## Formal Conjectures like targets

### FClikelean

The proposed FC-style statements are in
[RieszEnergySpheres.lean](FClikelean/RieszEnergySpheres.lean).
The file imports `FormalConjecturesUtil` and groups eighteen declarations into three
families: Riesz energy, logarithmic energy and cap discrepancy. Each family separates
the open coefficient-existence problem in arbitrary dimensions from the open lattice
formula in dimensions 2, 4, 8 and 24. Each lattice problem is followed by
`.variants.dimension_two`, `.dimension_four`, `.dimension_eight` and
`.dimension_twenty_four` statements. The four-dimensional variants are tagged open;
the other three dimension variants are tagged solved.
The docstrings cite the original conjectures
in [BHS12], [Br11] and [BB25], and the dimension-specific results in [Ki26].

The Riesz variants combine positive and negative exponents in the range
$`-2<s<d`$, $`s\ne0`$, including the regular E8 value at $`s=2`$.
The logarithmic lattice problem retains Conjecture 4's original dimensions 2, 4, 8 and 24.
The $`s=4`$ example is contained in the S⁸ Riesz variant.

The theorem proofs contain `sorry`, as in an FC statement file. This is a submission
draft; correspondence with the proof project's targets remains for the owner's review.

### Comparator target

[Challenge.lean](lean/Challenge.lean) supplies the reference statements, and
[FCSolution.lean](lean/FCSolution.lean) supplies their proofs. The principal explicit
target is `RieszSphereFC.riesz_energy_four_sphere8`:

```math
\mathcal E_4(8,N)=\frac7{16}N^2-\frac{5\sqrt{210}}{48}N^{3/2}+o(N^{3/2}).
```

The other targets cover positive and negative Riesz exponents, logarithmic energy
and cap discrepancy in all three dimensions, including the removable E8 value
at $`s=2`$. The
[correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md) records the
natural-language clauses and their reference declarations.

## Mathematical explanation (AI generated)

Write $`a_N=(N/A_d)^{1/d}`$ for the microscopic scale. Then
$`Na_N^s=A_d^{-s/d}N^{1+s/d}`$, which gives the area factor in the next-order term.

**1. Obtain sharp Gaussian lower bounds.** Gaussian minorants for the triangular,
E8 and Leech lattices supply the local coefficients. Localization to sphere charts
and a positive-definiteness inequality compare arbitrary configurations with
the uniform background.

**2. Recover the Riesz coefficient.** Subtract the continuous Gaussian background
before taking the Mellin integral. The resulting coefficient is the continued
Epstein zeta function. For E8 it has the explicit form

```math
Z_{E_8}(s)=240\,2^{-s/2}\zeta(s/2)\zeta(s/2-3),
\qquad Z_{E_8}(2)=120\zeta'(-2).
```

For negative exponents the comparison gives an upper bound on the energy,
so the extremal problem uses a supremum.

**3. Construct matching configurations.** Place scaled lattice patches in
exact-area sphere charts. Boundary quadrature and residual cells control the
errors. Integer patch budgets produce configurations at every sufficiently large
size, giving a limit along all integers.

**4. Pass to logarithmic energy.** A Frullani integral gives the logarithmic limit,
with $`W_d=\iint-\log|x-y|\,d\sigma_d(x)d\sigma_d(y)`$:

```math
\mathcal E_{\log}(d,N)=W_dN^2-\frac Nd\log N+
\left(Z'_{L_d}(0)+\frac1d\log A_d\right)N+o(N).
```

**5. Recover cap discrepancy.** Stolarsky's identity relates discrepancy to the
negative Riesz exponent $`s=-1`$. For caps
$`C(z,t)=\{x:\langle x,z\rangle\ge t\}`$, let $`D_2`$ use uniform directions
and Lebesgue height measure $`dt`$ on $`[-1,1]`$. Then

```math
N^{1/2+1/(2d)}\inf_X D_2(X)\longrightarrow
\sqrt{-\kappa_d A_d^{1/d}Z_{L_d}(-1)},\qquad
\kappa_2=\frac14,\quad\kappa_8=\frac{35}{256},\quad
\kappa_{24}=\frac{676039}{8388608}.
```

The [proof note](PDF/riesz-energy-spheres.pdf) gives the mathematical argument.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Canonical proof, pinned dependencies, Challenge and FCSolution. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.34.1` | The same proof for browsing and building, with Comparator-only files removed. |
| [FClikelean/](FClikelean/) | Upstream FC environment | Independent proposed FC-style statements, prepared for review. |
| [lean/comparator/](lean/comparator/) | `v4.34.1` | Input pins, source correspondence, verification scripts and guide. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Prepared build, Comparator, axiom audit and fresh kernel replay workflow. |
| [PDF/](PDF/) | — | Proof note, TeX source and existing timestamp evidence. |

[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records the input hashes and the common
sources of the canonical and supplementary proof projects.

## Verification

### Lean execution results

The proof project pins Lean 4.34.1 and a fixed Mathlib commit.
[FCAudit.lean](lean/FCAudit.lean) lists the nine solved FC targets for an axiom audit.
The [public main CI](https://github.com/KitaKen1/riesz-energy-spheres/actions/runs/39173822333)
passed on commit `56b3016f2a3ce703ab7f0486dfbc0879742aeddf`. It compiled the exact
eighteen-statement FC Challenge and all nine solution targets, using the recorded
import-only compatibility patch for FC utilities. All three dimension-specific
Comparator jobs passed, including builtin-kernel replay and the permitted-axiom
audit. All nine targets use only `propext`, `Classical.choice` and `Quot.sound`.
The [original logs and receipts](verification/public-main-ci-39173822333-attempt-1/)
are archived in the repository.

The owner's statement review remains pending.

### Lean Comparator check

The prepared Comparator setup uses Lean 4.34.1 throughout. The tool revisions are
fixed in [pins.json](lean/comparator/pins.json); Comparator and Lean4export have
toolchain-only changes from 4.34.0 to 4.34.1.
The workflow selects the nine solved variants from an exact copy of the FC draft,
permits only `[propext, Classical.choice, Quot.sound]`, and requires Comparator's
fresh builtin-kernel replay in all three dimension jobs.

The proof build is divided into six jobs, with a four-hour compile budget per
job. Artifacts pass completed products along the same workflow, so a first run
needs no previous project proof cache. Comparator then runs separately for
$d=2,8,24$, with three unchanged FC targets in each job. This complete workflow
passed on public main without any previous-run project proof cache.

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| February 2012 | J. S. Brauchart, D. P. Hardin and E. B. Saff | Surveyed optimal sphere energy and formulated next-order Riesz and logarithmic energy conjectures ([paper](https://arxiv.org/abs/1202.4037)). |
| 2022 | Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko and Maryna Viazovska | Proved universal optimality of E8 and the Leech lattice for completely monotonic potentials, using sharp auxiliary functions and Fourier interpolation ([paper](https://annals.math.princeton.edu/2022/196-3/p03)). |
| October 2026 | Kenta Kitamura | Prepared the [sphere energy manuscript](PDF/riesz-energy-spheres.pdf), the Lean proof sources and the FC-style statement draft in this repository. |

The Euclidean lattice results provide Gaussian input. The spherical next-order
argument also requires localization, subtraction of the continuous background
and matching point configurations on the sphere.

## Appendix: Verification by Lean Comparator on GitHub CI runner

Comparator verifies each theorem and its dependent definitions against the reference,
checks the allowed axioms and replays the proof in Lean's builtin kernel.
Each dimension job replays the selected proofs and their dependencies from scratch.
An optional manual audit additionally replays every imported declaration with
`leanchecker --fresh FCSolution`.

### Certification Within 90 days: CI results

The workflow retains logs and artifacts for 90 days.
The [public main run](https://github.com/KitaKen1/riesz-energy-spheres/actions/runs/39173822333)
passed all six build batches and all three Comparator jobs, covering the nine
solved FC variants. Each Comparator accepted the proofs in Lean's builtin kernel.
The [axiom-audit output](verification/public-main-ci-39173822333-attempt-1/receipt/comparator-S24-39173822333-1/axioms.log)
lists only `propext`, `Classical.choice` and `Quot.sound` for every target.

### Certification After 90 days: archive

An archived run records the tested commit, run and attempt, and includes the original
artifact ZIPs, full job logs, run metadata, receipts and SHA-256 checksums.
The [public main archive](verification/public-main-ci-39173822333-attempt-1/)
contains the original successful artifacts, full job logs, checked target scope
and SHA-256 checksums. It records the tested proof commit separately from the
later documentation and archive commit.

### Reproduce the verification

From `lean/`, build with `lake exe cache get && lake build`.
For the complete Linux checks, run the [verification workflow](.github/workflows/comparator.yml)
in a repository you control. See [the verification guide](lean/comparator/README.md).
