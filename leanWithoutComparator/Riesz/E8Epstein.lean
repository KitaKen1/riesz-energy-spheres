import Riesz.E8Shells
import Riesz.E8Dirichlet

/-!
# The actual E8 Epstein series on its convergence domain

This is a sum over the unchanged actual integer basis, with the zero vector
removed. The shell cardinalities connect it to the theta Dirichlet series.
No Mellin exchange is needed for this convergence-domain identity.
The series at u=2 diverges; the zeta product alone does not identify the
smoothly regularized Riesz energy or a cutoff comparison limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SphericalRiesz

def e8EpsteinTerm (u : ℂ) (z : Fin 8 → ℤ) : ℂ :=
  if z = 0 then 0 else ((‖e8EuclideanPoint z‖^2 : ℝ) : ℂ)^(-u)

def e8Epstein (u : ℂ) : ℂ := ∑' z : Fin 8 → ℤ, e8EpsteinTerm u z

theorem e8EpsteinTerm_norm {u : ℂ} (hu : 4 < u.re) (z : Fin 8 → ℤ) :
    ‖e8EpsteinTerm u z‖ = ‖e8EuclideanPoint z‖^(-2*u.re) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have he : -(2*u.re) ≠ 0 := by linarith
    simp [e8EpsteinTerm, e8EuclideanPoint_zero, Real.zero_rpow he]
  · have hp : 0 < ‖e8EuclideanPoint z‖ := norm_pos_iff.mpr (fun h =>
      hz (e8EuclideanPoint_injective (h.trans e8EuclideanPoint_zero.symm)))
    rw [e8EpsteinTerm, if_neg hz, Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hp),
      Complex.neg_re]
    calc
      (‖e8EuclideanPoint z‖^2)^(-u.re) =
          (‖e8EuclideanPoint z‖^(2 : ℝ))^(-u.re) := by
            rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      _ = ‖e8EuclideanPoint z‖^(2*(-u.re)) := (Real.rpow_mul hp.le _ _).symm
      _ = ‖e8EuclideanPoint z‖^(-2*u.re) := by congr 1; ring

theorem e8Epstein_summable {u : ℂ} (hu : 4 < u.re) : Summable (e8EpsteinTerm u) := by
  have hr : -2*u.re < -(Module.finrank ℤ e8Lattice : ℝ) := by rw [e8Lattice_rank]; norm_num; linarith
  have h := (ZLattice.summable_norm_rpow e8Lattice (-2*u.re) hr).comp_injective
    e8LatticeEquiv.injective
  apply Summable.of_norm
  apply h.congr
  intro z
  rw [e8EpsteinTerm_norm hu]
  change ‖(e8LatticeEquiv z : E8Ambient)‖^(-2*u.re) = ‖e8EuclideanPoint z‖^(-2*u.re)
  rw [e8LatticeEquiv_coe]

theorem e8EpsteinTerm_shell {u : ℂ} {n : ℕ} (hn : n ≠ 0)
    (z : e8ShellIndex ⁻¹' {n}) :
    e8EpsteinTerm u z = (2 : ℂ)^(-u) * (n : ℂ)^(-u) := by
  have hindex : e8ShellIndex z = n := z.property
  have hz : (z : Fin 8 → ℤ) ≠ 0 := by
    intro h
    have he := (e8ShellIndex_zero_iff z).mpr h
    exact hn (hindex.symm.trans he)
  rw [e8EpsteinTerm, if_neg hz, e8ShellIndex_norm_sq, hindex]
  push_cast
  exact Complex.natCast_mul_natCast_cpow 2 n (-u)

theorem e8Epstein_fiber_sum (u : ℂ) (n : ℕ) :
    (∑' z : e8ShellIndex ⁻¹' {n}, e8EpsteinTerm u z) =
      (2 : ℂ)^(-u) * LSeries.term e8ThetaPositiveCoeff u n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have ht : ∀ z : e8ShellIndex ⁻¹' {0}, e8EpsteinTerm u z = 0 := by
      intro z
      have hz : (z : Fin 8 → ℤ) = 0 := (e8ShellIndex_zero_iff z).mp z.property
      simp [e8EpsteinTerm, hz]
    simp [ht]
  · have ht : (fun z : e8ShellIndex ⁻¹' {n} => e8EpsteinTerm u z) =
        (fun _ : e8ShellIndex ⁻¹' {n} => (2 : ℂ)^(-u) * (n : ℂ)^(-u)) := by
      funext z
      exact e8EpsteinTerm_shell hn z
    rw [ht, tsum_const]
    have hc : (e8ShellCount n : ℂ) = e8ThetaPositiveCoeff n := by
      rw [e8ThetaPositiveCoeff_eq, e8ShellCount_positive n hn]
      push_cast
      rfl
    change (e8ShellCount n) • ((2 : ℂ)^(-u) * (n : ℂ)^(-u)) = _
    rw [nsmul_eq_mul, hc, LSeries.term_of_ne_zero hn]
    simp only [Complex.cpow_neg]
    ring

theorem e8Epstein_eq_zeta_product {u : ℂ} (hu : 4 < u.re) :
    e8Epstein u = (2 : ℂ)^(-u) * (240 * riemannZeta u * riemannZeta (u-3)) := by
  have h := (e8Epstein_summable hu).hasSum.tsum_fiberwise e8ShellIndex
  have hg : HasSum (fun n => (2 : ℂ)^(-u) * LSeries.term e8ThetaPositiveCoeff u n)
      (e8Epstein u) := h.congr_fun (fun n => (e8Epstein_fiber_sum u n).symm)
  have hv := (e8ThetaDirichlet_hasSum hu).mul_left ((2 : ℂ)^(-u))
  simpa only [mul_assoc] using hg.unique hv

theorem e8Epstein_hasSum {u : ℂ} (hu : 4 < u.re) :
    HasSum (e8EpsteinTerm u) (e8EpsteinCandidate u) := by
  unfold e8EpsteinCandidate
  rw [← e8Epstein_eq_zeta_product hu]
  exact (e8Epstein_summable hu).hasSum

theorem e8Epstein_not_summable_at_two : ¬ Summable (e8EpsteinTerm 2) := by
  intro h
  have hg := (h.hasSum.tsum_fiberwise e8ShellIndex).summable.congr
    (fun n => e8Epstein_fiber_sum 2 n)
  have h2 : (2 : ℂ)^(-(2 : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  exact e8ThetaDirichlet_not_summable_at_two ((summable_mul_left_iff h2).mp hg)

theorem e8EpsteinCandidate_differentiableAt {u : ℂ} (h₁ : u ≠ 1) (h₄ : u ≠ 4) :
    DifferentiableAt ℂ e8EpsteinCandidate u := by
  have hs : u-3 ≠ 1 := by intro h; apply h₄; linear_combination h
  exact (differentiableAt_id.neg.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).mul
    (((differentiableAt_riemannZeta h₁).const_mul 240).mul
      ((differentiableAt_riemannZeta hs).comp u (differentiableAt_id.sub_const 3)))

theorem e8EpsteinCandidate_analyticOnNhd :
    AnalyticOnNhd ℂ e8EpsteinCandidate ({1,4} : Set ℂ)ᶜ := by
  have hd : DifferentiableOn ℂ e8EpsteinCandidate ({1,4} : Set ℂ)ᶜ := by
    intro u hu
    have hs : u ≠ 1 ∧ u ≠ 4 := by simpa using hu
    exact (e8EpsteinCandidate_differentiableAt hs.1 hs.2).differentiableWithinAt
  have hclosed : IsClosed ({1,4} : Set ℂ) := by
    exact Set.Finite.isClosed (by simp)
  exact hd.analyticOnNhd hclosed.isOpen_compl

theorem e8EpsteinCandidate_analyticAt_two : AnalyticAt ℂ e8EpsteinCandidate 2 :=
  e8EpsteinCandidate_analyticOnNhd 2 (by norm_num)

/-- Each sharp radial shell jump at inverse-fourth power grows at least linearly. -/
theorem e8_inverse_fourth_shell_mass_lower (n : ℕ) (hn : n ≠ 0) :
    60*(n : ℝ) ≤ (e8ShellCount n : ℝ) / (2*(n : ℝ))^2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : (n : ℝ)^3 ≤ (ArithmeticFunction.sigma 3 n : ℝ) := by
    exact_mod_cast pow_three_le_sigma_three n
  rw [e8ShellCount_positive n hn]
  push_cast
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 2*(n : ℝ)))).mpr
  nlinarith

#print axioms e8EpsteinTerm_norm
#print axioms e8Epstein_summable
#print axioms e8EpsteinTerm_shell
#print axioms e8Epstein_fiber_sum
#print axioms e8Epstein_eq_zeta_product
#print axioms e8Epstein_hasSum
#print axioms e8Epstein_not_summable_at_two
#print axioms e8EpsteinCandidate_differentiableAt
#print axioms e8EpsteinCandidate_analyticOnNhd
#print axioms e8EpsteinCandidate_analyticAt_two
#print axioms e8_inverse_fourth_shell_mass_lower
end SphericalRiesz
