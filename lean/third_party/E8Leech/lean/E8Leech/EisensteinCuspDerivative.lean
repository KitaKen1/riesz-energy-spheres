import E8Leech.EisensteinProductIdentities
import Mathlib.NumberTheory.ModularForms.Derivative

/-!
# Derivatives at the cusp using the q coordinate

Use the actual analytic cusp function: D f = q * F'(q). This proves D f
tends to zero without a Cauchy sphere bound or termwise q-series derivative.
E2 only needs its value at the cusp, not a derivative identity.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open UpperHalfPlane Filter Function
open scoped Manifold Topology MatrixGroups

theorem normalizedDeriv_eq_q_mul_cusp_deriv {f : UpperHalfPlane → ℂ}
    (hp : Periodic (f ∘ ofComplex) 1) (hh : MDiff f)
    (hb : IsBoundedAtImInfty f) (z : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex f z =
      Periodic.qParam 1 z * deriv (cuspFunction 1 f) (Periodic.qParam 1 z) := by
  have hq : HasDerivAt (Periodic.qParam 1)
      (2 * (Real.pi : ℂ) * Complex.I * Periodic.qParam 1 z) (z : ℂ) := by
    change HasDerivAt (fun w : ℂ => Periodic.qParam 1 w) _ _
    simp only [Periodic.qParam, Complex.ofReal_one, div_one]
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      ((hasDerivAt_id (z : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  have hc := (differentiableAt_cuspFunction one_pos hp hh hb
    (Periodic.norm_qParam_lt_one one_pos z.im_pos)).hasDerivAt
  have h := hc.comp (z : ℂ) hq
  have heq : cuspFunction 1 f ∘ Periodic.qParam 1 = f ∘ ofComplex := by
    funext w
    exact Periodic.eq_cuspFunction one_ne_zero hp w
  rw [heq] at h
  unfold Derivative.normalizedDerivOfComplex
  rw [h.deriv]
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [hpi]

theorem normalizedDeriv_tendsto_zero_atImInfty {f : UpperHalfPlane → ℂ}
    (hp : Periodic (f ∘ ofComplex) 1) (hh : MDiff f)
    (hb : IsBoundedAtImInfty f) :
    Tendsto (Derivative.normalizedDerivOfComplex f) atImInfty (𝓝 0) := by
  have hdc : ContinuousAt (deriv (cuspFunction 1 f)) 0 :=
    (((differentiableOn_cuspFunction_ball one_pos hp hh hb).deriv Metric.isOpen_ball).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))).continuousAt
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have h := hq.mul (hdc.tendsto.comp hq)
  simpa only [zero_mul] using
    h.congr (fun z => (normalizedDeriv_eq_q_mul_cusp_deriv hp hh hb z).symm)

theorem normalizedDeriv_isBoundedAtImInfty {f : UpperHalfPlane → ℂ}
    (hp : Periodic (f ∘ ofComplex) 1) (hh : MDiff f)
    (hb : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex f) :=
  (show IsZeroAtImInfty (Derivative.normalizedDerivOfComplex f) from
    normalizedDeriv_tendsto_zero_atImInfty hp hh hb).isBoundedAtImInfty

theorem levelOne_tendsto_qExpansion_constant {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (f : UpperHalfPlane → ℂ) atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL
  have hc0 : (qExpansion 1 f).coeff 0 = cuspFunction 1 f 0 := by
    simp [qExpansion_coeff]
  rw [hc0]
  exact (ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun z => UpperHalfPlane.eq_cuspFunction z one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL))

theorem eisensteinTwo_periodic_comp_ofComplex :
    Periodic (EisensteinSeries.E2 ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    rw [EisensteinSeries.E2_eq_tsum_cexp, EisensteinSeries.E2_eq_tsum_cexp]
    have hq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w + 1)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) := by
      rw [mul_add, mul_one]
      exact Complex.exp_periodic _
    change 1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w + 1)) ^ (n : ℕ) =
      1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) ^ (n : ℕ)
    rw [hq]
  · have hw1 : (w + 1).im ≤ 0 := by simpa using le_of_not_gt hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1,
      ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

theorem eisensteinTwo_tendsto_one_atImInfty :
    Tendsto EisensteinSeries.E2 atImInfty (𝓝 1) := by
  have ha := analyticAt_cuspFunction_zero one_pos eisensteinTwo_periodic_comp_ofComplex
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hs : ∀ z : UpperHalfPlane, HasSum (fun m : ℕ =>
      (if m = 0 then 1 else -24 * ArithmeticFunction.sigma 1 m : ℂ) •
        Periodic.qParam 1 z ^ m) (EisensteinSeries.E2 z) := by
    intro z
    simpa only [Periodic.qParam, Complex.ofReal_one, div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z := z)
  have h0 : cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
    have h := (hasFPowerSeriesOnBall_cuspFunction one_pos ha hs).coeff_zero (fun _ => 1)
    simpa [FormalMultilinearSeries.ofScalars] using h.symm
  rw [← h0]
  exact (ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun z => UpperHalfPlane.eq_cuspFunction z one_ne_zero eisensteinTwo_periodic_comp_ofComplex)

theorem serreDerivative_tendsto_of_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (Derivative.serreDerivative k f) atImInfty
      (𝓝 (-(k : ℂ) / 12 * (qExpansion 1 f).coeff 0)) := by
  have hd := normalizedDeriv_tendsto_zero_atImInfty
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    f.holo' (ModularFormClass.bdd_at_infty f)
  have hk : Tendsto (fun _ : UpperHalfPlane => (k : ℂ) * 12⁻¹) atImInfty
      (𝓝 ((k : ℂ) * 12⁻¹)) := tendsto_const_nhds
  have h := hd.sub ((hk.mul eisensteinTwo_tendsto_one_atImInfty).mul
    (levelOne_tendsto_qExpansion_constant f))
  have hv : -(k : ℂ) / 12 * (qExpansion 1 f).coeff 0 =
      0 - (k : ℂ) * 12⁻¹ * 1 * (qExpansion 1 f).coeff 0 := by ring
  rw [hv]
  exact h

theorem serreDerivative_isBoundedAtImInfty_of_levelOne {k : ℤ}
    (f : ModularForm 𝒮ℒ k) : IsBoundedAtImInfty (Derivative.serreDerivative k f) := by
  have hd := normalizedDeriv_isBoundedAtImInfty
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    f.holo' (ModularFormClass.bdd_at_infty f)
  have hm : IsBoundedAtImInfty (fun z : UpperHalfPlane =>
      (k : ℂ) * 12⁻¹ * (EisensteinSeries.E2 z * f z)) :=
    (const_boundedAtFilter atImInfty ((k : ℂ) * 12⁻¹)).mul
      (EisensteinSeries.isBoundedAtImInfty_E2.mul (ModularFormClass.bdd_at_infty f))
  change IsBoundedAtImInfty (fun z : UpperHalfPlane =>
    Derivative.normalizedDerivOfComplex f z - (k : ℂ) * 12⁻¹ * EisensteinSeries.E2 z * f z)
  simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, mul_assoc] using hd.sub hm

end E8Leech
