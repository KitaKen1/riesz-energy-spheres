import Riesz.LeechTheta24
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Holomorphy and the cusp limit of the actual Leech theta series

Gaussian domination on each positive-height half-plane gives locally uniform
convergence. Complex differentiability then follows from the existing
Weierstrass theorem; no separate derivative-series estimate is required.
Dominated convergence gives the limit 1 uniformly in the real coordinate.
The inversion law and the resulting modular-form structure remain open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter UpperHalfPlane
open scoped Topology
namespace SphericalRiesz

theorem leechLatticeThetaTerm_norm_le_of_im_le (τ υ : ℂ) (h : υ.im ≤ τ.im)
    (x : leechLattice) : ‖leechLatticeThetaTerm τ x‖ ≤ ‖leechLatticeThetaTerm υ x‖ := by
  rw [leechLatticeThetaTerm_norm, leechLatticeThetaTerm_norm]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left h
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))

theorem leechLatticeTheta_uniform {T : ℝ} (hT : 0 < T) :
    HasSumUniformlyOn (fun x : leechLattice => fun τ : ℂ => leechLatticeThetaTerm τ x)
      (fun τ => ∑' x : leechLattice, leechLatticeThetaTerm τ x) {τ : ℂ | T ≤ τ.im} := by
  have hs := (leechLatticeThetaTerm_summable
    (τ := (T : ℂ)*Complex.I) (by simpa using hT)).norm
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hs
  intro x τ hτ
  apply leechLatticeThetaTerm_norm_le_of_im_le
  simpa using hτ

theorem leechLatticeTheta_locallyUniform :
    SummableLocallyUniformlyOn (fun x : leechLattice => fun τ : ℂ => leechLatticeThetaTerm τ x)
      {τ : ℂ | 0 < τ.im} := by
  refine ⟨(fun τ => ∑' x : leechLattice, leechLatticeThetaTerm τ x),
    hasSumLocallyUniformlyOn_of_of_forall_exists_nhds ?_⟩
  intro τ hτ
  change 0 < τ.im at hτ
  obtain ⟨T, hT, hTτ⟩ := exists_between hτ
  refine ⟨{υ : ℂ | T ≤ υ.im}, ?_, leechLatticeTheta_uniform hT⟩
  have ho : IsOpen {υ : ℂ | T < υ.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  apply mem_nhdsWithin_of_mem_nhds
  exact mem_of_superset (ho.mem_nhds hTτ)
    (fun υ h => (show T < υ.im from h).le)

theorem leechTheta_differentiableOn : DifferentiableOn ℂ leechTheta {τ : ℂ | 0 < τ.im} := by
  have hd := leechLatticeTheta_locallyUniform.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_im)
    (fun x τ _ => (by unfold leechLatticeThetaTerm; fun_prop))
  simpa only [leechTheta] using! hd

theorem leechTheta_continuousOn : ContinuousOn leechTheta {τ : ℂ | 0 < τ.im} :=
  leechTheta_differentiableOn.continuousOn

theorem leechLatticeThetaTerm_tendsto (x : leechLattice) :
    Tendsto (fun τ : ℍ => leechLatticeThetaTerm τ x) atImInfty
      (𝓝 (if x = 0 then (1 : ℂ) else 0)) := by
  classical
  by_cases hx : x = 0
  · simpa [hx, leechLatticeThetaTerm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 1))
  · rw [ite_eq_right hx, tendsto_zero_iff_norm_tendsto_zero]
    have hp : 0 < ‖(x : LeechAmbient)‖ := by
      apply norm_pos_iff.mpr
      exact fun h => hx (Subtype.ext h)
    have hc : -Real.pi*‖(x : LeechAmbient)‖^2 < 0 :=
      mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos hp)
    have hi : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
    simpa only [Function.comp_def, leechLatticeThetaTerm_norm, UpperHalfPlane.coe_im] using
      Real.tendsto_exp_atBot.comp (hi.const_mul_atTop_of_neg hc)

theorem leechTheta_tendsto_atImInfty :
    Tendsto (fun τ : ℍ => leechTheta τ) atImInfty (𝓝 1) := by
  classical
  have hs := (leechLatticeThetaTerm_summable (τ := Complex.I) (by norm_num)).norm
  have hi : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hb : ∀ᶠ τ : ℍ in atImInfty, ∀ x : leechLattice,
      ‖leechLatticeThetaTerm τ x‖ ≤ ‖leechLatticeThetaTerm Complex.I x‖ := by
    filter_upwards [hi.eventually (eventually_ge_atTop 1)] with τ hτ x
    exact leechLatticeThetaTerm_norm_le_of_im_le τ Complex.I (by simpa using hτ) x
  have ht := tendsto_tsum_of_dominated_convergence hs leechLatticeThetaTerm_tendsto hb
  simpa only [leechTheta, tsum_ite_eq] using ht

theorem leechTheta_bounded_atImInfty :
    IsBoundedAtImInfty (fun τ : ℍ => leechTheta τ) :=
  leechTheta_tendsto_atImInfty.norm.isBoundedUnder_le.isBigO_one ℝ

#print axioms leechLatticeThetaTerm_norm_le_of_im_le
#print axioms leechLatticeTheta_uniform
#print axioms leechLatticeTheta_locallyUniform
#print axioms leechTheta_differentiableOn
#print axioms leechTheta_continuousOn
#print axioms leechLatticeThetaTerm_tendsto
#print axioms leechTheta_tendsto_atImInfty
#print axioms leechTheta_bounded_atImInfty

end SphericalRiesz
