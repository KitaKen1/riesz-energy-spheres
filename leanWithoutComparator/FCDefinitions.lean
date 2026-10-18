module

public import Mathlib

/-!
# Next-order energy on spheres

Conjecture 3 of [BHS12] asks whether the optimal Riesz energy on $\mathbb S^d$
has a two-term asymptotic expansion for every $d\ge2$. It additionally predicts
an explicit lattice Epstein zeta value for the coefficient when $d=2,4,8,24$.

[BHS12, equation (7)] asks whether the minimum logarithmic energy has an expansion
$W_dN^2-(N/d)\log N+C_{\log,d}N+o(N)$ in arbitrary dimensions. Conjecture 4
predicts the specific value $C_{\log,d}=Z'_{L_d}(0)+d^{-1}\log A_d$ for
$d=2,4,8,24$.

A related problem in [Br11, §3] asks whether the scaled optimal spherical cap
$L^2$ discrepancy has a limit in every dimension $d\ge2$. Stolarsky's invariance
principle connects this limit to the Riesz coefficient at $s=-1$; the specific
lattice values predicted for $d=2,4,8,24$ are discussed in [BB25, §5.3].

*References:*
- [BHS12] J. S. Brauchart, D. P. Hardin and E. B. Saff, *The next-order term for optimal
  Riesz and logarithmic energy asymptotics on the sphere* (2012), Conjectures 3 and 4,
  [arXiv:1202.4037](https://arxiv.org/abs/1202.4037).
- [Br11] J. S. Brauchart, *Optimal discrete Riesz energy and discrepancy*,
  Uniform Distribution Theory 6 (2011), 207–220, §3, Conjectures 3 and 4,
  [arXiv:1103.3088](https://arxiv.org/abs/1103.3088).
- [BB25] D. Bilyk and J. S. Brauchart, *On the lower bounds for the spherical cap
  discrepancy* (2025), §5.3, equations (30) and (33),
  [arXiv:2502.15984](https://arxiv.org/abs/2502.15984).
- [Ki26] Kenta Kitamura, *riesz-energy-spheres*, GitHub repository (2026),
  [repository](https://github.com/KitaKen1/riesz-energy-spheres).
- [dLV16] David de Laat and Frank Vallentin, *A breakthrough in sphere packing:
  the search for magic functions*, Nieuw Archief voor Wiskunde 5/17 (2016),
  184–192, p. 187, [article](https://ir.cwi.nl/pub/24759/24759D.pdf).
-/

@[expose] public section

noncomputable section

namespace RieszSphereFC

open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

/-- The unit sphere $\mathbb S^d\subset\mathbb R^{d+1}$ [BHS12, §1]. -/
abbrev Sphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

/-- Uniform probability measure $\sigma_d$ on $\mathbb S^d$ [BHS12, §1]. -/
def uniform (d : ℕ) : Measure (Sphere d) :=
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))).toSphere
  (μ univ)⁻¹ • μ

/-- The sphere area $A_d=2\pi^{(d+1)/2}/\Gamma((d+1)/2)$ [Ki26]. -/
def area (d : ℕ) : ℝ :=
  2 * Real.pi ^ (((d : ℝ) + 1) / 2) / Real.Gamma (((d : ℝ) + 1) / 2)

/-- The covolume-one triangular theta series [Ki26]. -/
def triangularTheta (t : ℝ) : ℝ :=
  ∑' m : ℤ × ℤ, Real.exp (-2 * Real.pi * t / Real.sqrt 3 *
    ((m.1 : ℝ) ^ 2 + (m.1 : ℝ) * (m.2 : ℝ) + (m.2 : ℝ) ^ 2))

/-- The Leech theta series $(7E_4(it)^3+5E_6(it)^2)/12$ [dLV16, p. 187]. -/
def leechTheta (t : ℝ) : ℝ :=
  let S : ℕ → ℝ := fun k => ∑' n : ℕ,
    (∑ a ∈ Nat.divisors (n + 1), (a : ℝ) ^ k) *
      Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)
  let E₄ := 1 + 240 * S 3
  let E₆ := 1 - 504 * S 5
  (7 * E₄ ^ 3 + 5 * E₆ ^ 2) / 12

/-- Theta series of the covolume-one triangular, $D_4$, $E_8$ and Leech lattices
[BHS12, Conjecture 2; dLV16, p. 187]. Set to $1$ in other dimensions. -/
def latticeTheta (d : ℕ) (t : ℝ) : ℝ :=
  if d = 2 then triangularTheta t
  else if d = 4 then
    ∑' m : Fin 4 → ℤ, if Even (∑ i, m i) then
      Real.exp (-Real.pi * t / Real.sqrt 2 * ∑ i, (m i : ℝ) ^ 2) else 0
  else if d = 8 then
    1 + 240 * ∑' n : ℕ, (∑ a ∈ Nat.divisors (n + 1), (a : ℝ) ^ 3) *
      Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)
  else if d = 24 then leechTheta t
  else 1

/-- The continued Epstein function $Z_L(s)$ in the distance exponent, regular at $s=0$,
using the theta integral for lattices isometric to their duals [Ki26]. -/
def epstein (d : ℕ) (θ : ℝ → ℝ) (s : ℂ) : ℂ :=
  let u := s / 2
  let J : ℂ := ∫ t in Ioi (1 : ℝ), ((θ t - 1 : ℝ) : ℂ) *
    ((t : ℂ) ^ (u - 1) + (t : ℂ) ^ ((d : ℂ) / 2 - u - 1))
  (Real.pi : ℂ) ^ u * ((J - ((d : ℂ) / 2 - u)⁻¹) * (Complex.Gamma u)⁻¹ -
    (Complex.Gamma (u + 1))⁻¹)

/-- The optimal ordered Riesz sum: a minimum for $s\ge0$, a maximum for $s<0$
[BHS12, equation (8)]. -/
def rieszEnergy (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  let E := fun X : Fin N ↪ Sphere d =>
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, dist (X i) (X j) ^ (-s)
  if s < 0 then sSup (range E) else sInf (range E)

/-- The continuous Riesz energy $V_s(\mathbb S^d)$ for $-2<s<d$, extended by its
gamma formula outside that range [BHS12, equation (10)]. -/
def rieszBackground (d : ℕ) (s : ℝ) : ℝ :=
  2 ^ ((d : ℝ) - s - 1) * Real.Gamma (((d : ℝ) + 1) / 2) *
    Real.Gamma (((d : ℝ) - s) / 2) /
      (Real.sqrt Real.pi * Real.Gamma ((d : ℝ) - s / 2))

/-- The minimum ordered logarithmic energy $\mathcal E_{\log}(d,N)$
[BHS12, equation (1)]. -/
def logEnergy (d : ℕ) (N : ℕ) : ℝ :=
  sInf (range fun X : Fin N ↪ Sphere d =>
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j)))

/-- The $L^2$ cap discrepancy, with uniform directions and Lebesgue height measure
on $[-1,1]$ [Br11, Definition 3; Ki26]. -/
def capDiscrepancy (d : ℕ) {N : ℕ} (X : Fin N ↪ Sphere d) : ℝ :=
  let ι : Sphere d → ℝ → Sphere d → ℝ := fun z t x =>
    if t ≤ ⟪(x : EuclideanSpace ℝ (Fin (d + 1))), (z : EuclideanSpace ℝ (Fin (d + 1)))⟫
      then 1 else 0
  Real.sqrt (∫ q, ((∑ i : Fin N, ι q.1 q.2 (X i)) / (N : ℝ) -
    ∫ y, ι q.1 q.2 y ∂(uniform d)) ^ 2
    ∂((uniform d).prod (volume.restrict (Icc (-1 : ℝ) 1))))

end RieszSphereFC
