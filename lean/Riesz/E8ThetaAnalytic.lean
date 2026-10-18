import Riesz.E8ThetaSummable
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Holomorphy and the cusp limit of the actual E8 theta series

Gaussian domination on each positive-height half-plane gives locally uniform
convergence. Complex differentiability then follows from the existing
Weierstrass theorem; no separate derivative-series estimate is required.
Dominated convergence gives the limit 1 uniformly in the real coordinate.
The inversion law and the resulting modular-form structure remain open.
-/

set_option autoImplicit false
noncomputable section
open Filter UpperHalfPlane
open scoped Topology
namespace SphericalRiesz

theorem e8LatticeThetaTerm_norm_le_of_im_le (τ υ : ℂ) (h : υ.im ≤ τ.im)
    (x : e8Lattice) : ‖e8LatticeThetaTerm τ x‖ ≤ ‖e8LatticeThetaTerm υ x‖ := by
  rw [e8LatticeThetaTerm_norm, e8LatticeThetaTerm_norm]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left h
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))

theorem e8LatticeTheta_uniform {T : ℝ} (hT : 0 < T) :
    HasSumUniformlyOn (fun x : e8Lattice => fun τ : ℂ => e8LatticeThetaTerm τ x)
      (fun τ => ∑' x : e8Lattice, e8LatticeThetaTerm τ x) {τ : ℂ | T ≤ τ.im} := by
  have hs := (e8LatticeThetaTerm_summable
    (τ := (T : ℂ)*Complex.I) (by simpa using hT)).norm
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hs
  intro x τ hτ
  apply e8LatticeThetaTerm_norm_le_of_im_le
  simpa using hτ

theorem e8LatticeTheta_locallyUniform :
    SummableLocallyUniformlyOn (fun x : e8Lattice => fun τ : ℂ => e8LatticeThetaTerm τ x)
      {τ : ℂ | 0 < τ.im} := by
  refine ⟨(fun τ => ∑' x : e8Lattice, e8LatticeThetaTerm τ x),
    hasSumLocallyUniformlyOn_of_of_forall_exists_nhds ?_⟩
  intro τ hτ
  change 0 < τ.im at hτ
  obtain ⟨T, hT, hTτ⟩ := exists_between hτ
  refine ⟨{υ : ℂ | T ≤ υ.im}, ?_, e8LatticeTheta_uniform hT⟩
  have ho : IsOpen {υ : ℂ | T < υ.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  apply mem_nhdsWithin_of_mem_nhds
  exact mem_of_superset (ho.mem_nhds hTτ)
    (fun υ h => (show T < υ.im from h).le)

theorem e8Theta_differentiableOn : DifferentiableOn ℂ e8Theta {τ : ℂ | 0 < τ.im} := by
  have hd := e8LatticeTheta_locallyUniform.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_im)
    (fun x τ _ => (by unfold e8LatticeThetaTerm; fun_prop))
  simpa only [← e8Theta_lattice_tsum] using hd

theorem e8Theta_continuousOn : ContinuousOn e8Theta {τ : ℂ | 0 < τ.im} :=
  e8Theta_differentiableOn.continuousOn

theorem e8LatticeThetaTerm_tendsto (x : e8Lattice) :
    Tendsto (fun τ : ℍ => e8LatticeThetaTerm τ x) atImInfty
      (𝓝 (if x = 0 then (1 : ℂ) else 0)) := by
  classical
  by_cases hx : x = 0
  · simpa [hx, e8LatticeThetaTerm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 1))
  · rw [ite_eq_right hx, tendsto_zero_iff_norm_tendsto_zero]
    have hp : 0 < ‖(x : E8Ambient)‖ := by
      apply norm_pos_iff.mpr
      exact fun h => hx (Subtype.ext h)
    have hc : -Real.pi*‖(x : E8Ambient)‖^2 < 0 :=
      mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos hp)
    have hi : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
    simpa only [Function.comp_def, e8LatticeThetaTerm_norm, UpperHalfPlane.coe_im] using
      Real.tendsto_exp_atBot.comp (hi.const_mul_atTop_of_neg hc)

theorem e8Theta_tendsto_atImInfty :
    Tendsto (fun τ : ℍ => e8Theta τ) atImInfty (𝓝 1) := by
  classical
  have hs := (e8LatticeThetaTerm_summable (τ := Complex.I) (by norm_num)).norm
  have hi : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hb : ∀ᶠ τ : ℍ in atImInfty, ∀ x : e8Lattice,
      ‖e8LatticeThetaTerm τ x‖ ≤ ‖e8LatticeThetaTerm Complex.I x‖ := by
    filter_upwards [hi.eventually (eventually_ge_atTop 1)] with τ hτ x
    exact e8LatticeThetaTerm_norm_le_of_im_le τ Complex.I (by simpa using hτ) x
  have ht := tendsto_tsum_of_dominated_convergence hs e8LatticeThetaTerm_tendsto hb
  simpa only [← e8Theta_lattice_tsum, tsum_ite_eq] using ht

theorem e8Theta_bounded_atImInfty :
    IsBoundedAtImInfty (fun τ : ℍ => e8Theta τ) :=
  e8Theta_tendsto_atImInfty.norm.isBoundedUnder_le.isBigO_one ℝ

#print axioms e8LatticeThetaTerm_norm_le_of_im_le
#print axioms e8LatticeTheta_uniform
#print axioms e8LatticeTheta_locallyUniform
#print axioms e8Theta_differentiableOn
#print axioms e8Theta_continuousOn
#print axioms e8LatticeThetaTerm_tendsto
#print axioms e8Theta_tendsto_atImInfty
#print axioms e8Theta_bounded_atImInfty

end SphericalRiesz
