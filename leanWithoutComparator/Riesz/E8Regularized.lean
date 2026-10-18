import Riesz.E8ThetaModular
import Mathlib.Analysis.MellinTransform

/-!
# Convergence of the actual E8 smooth regularization

The theta function here is the unchanged lattice sum, evaluated on the
imaginary axis. Cusp decay and Poisson inversion control both endpoints of
`Theta(t) - 1 - t^(-4)`. Its Mellin integral exists on `0 < re s < 4`.
This file does not yet identify the integral with the Epstein continuation
or with the spherical cell defect.
-/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics UpperHalfPlane
open scoped Topology Manifold
namespace SphericalRiesz

def e8ThetaImag (t : ℝ) : ℂ := e8Theta ((t : ℂ) * Complex.I)

def e8ThetaTail (t : ℝ) : ℂ := e8ThetaImag t - 1

def e8ThetaRegularized (t : ℝ) : ℂ := e8ThetaTail t - ((t : ℂ)^4)⁻¹

theorem e8ThetaImag_continuousOn : ContinuousOn e8ThetaImag (Ioi 0) := by
  apply e8Theta_continuousOn.comp
    (show ContinuousOn (fun t : ℝ => (t : ℂ)*Complex.I) (Ioi 0) by fun_prop)
  intro t ht
  simpa using ht

theorem e8ThetaTail_continuousOn : ContinuousOn e8ThetaTail (Ioi 0) :=
  e8ThetaImag_continuousOn.sub continuousOn_const

theorem e8ThetaRegularized_continuousOn : ContinuousOn e8ThetaRegularized (Ioi 0) := by
  apply e8ThetaTail_continuousOn.sub
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))

theorem e8ThetaImag_transform {t : ℝ} (ht : 0 < t) :
    e8ThetaImag t⁻¹ = (t : ℂ)^4 * e8ThetaImag t := by
  have h := e8Theta_transform_S (τ := (t : ℂ)*Complex.I) (by simpa using ht)
  simpa [e8ThetaImag, div_eq_mul_inv, mul_inv_rev, Complex.inv_I,
    mul_pow, Complex.I_pow_four, ← Complex.ofReal_inv, mul_comm] using h

theorem e8ThetaRegularized_inversion {t : ℝ} (ht : 0 < t) :
    e8ThetaRegularized t = ((t : ℂ)^4)⁻¹ * e8ThetaTail t⁻¹ - 1 := by
  have h := e8ThetaImag_transform ht
  have h0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold e8ThetaRegularized e8ThetaTail
  field_simp
  simp only [one_div]
  linear_combination -h

theorem e8ThetaTail_exp_decay :
    e8ThetaTail =O[atTop] (fun t : ℝ => Real.exp (-(2*Real.pi)*t)) := by
  have h := UpperHalfPlane.exp_decay_sub_atImInfty (h := 1) (by norm_num)
    e8ThetaUpper_periodic e8ThetaUpper_mdifferentiable e8Theta_bounded_atImInfty
  rw [e8ThetaUpper_valueAtInfty] at h
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop 0] with t ht ht0
  let τ : ℍ := ⟨(t : ℂ)*Complex.I, by simpa using ht0⟩
  have hτ : A ≤ τ.im := by simpa [τ] using ht
  simpa [τ, e8ThetaUpper, e8ThetaTail, e8ThetaImag, neg_mul] using hA τ hτ

theorem e8ThetaTail_littleO_rpow (a : ℝ) :
    e8ThetaTail =o[atTop] (fun t : ℝ => t^a) :=
  e8ThetaTail_exp_decay.trans_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity) a)

theorem e8ThetaTail_scaled_tendsto :
    Tendsto (fun t : ℝ => (t : ℂ)^4 * e8ThetaTail t) atTop (𝓝 0) := by
  have h := (e8ThetaTail_littleO_rpow (-4)).tendsto_inv_smul_nhds_zero (𝕜 := ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg ht.le, inv_inv,
    show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  simp [Complex.real_smul]

theorem e8ThetaRegularized_tendsto_zero :
    Tendsto e8ThetaRegularized (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have h := e8ThetaTail_scaled_tendsto.comp tendsto_inv_nhdsGT_zero
  have h' := h.sub_const (1 : ℂ)
  simp only [zero_sub] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [e8ThetaRegularized_inversion ht]
  simp [Complex.ofReal_inv, inv_pow]

theorem e8ThetaRegularized_bigO_zero :
    e8ThetaRegularized =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^(-(0 : ℝ))) := by
  simpa using e8ThetaRegularized_tendsto_zero.isBigO_one ℝ

theorem e8ThetaRegularized_bigO_infty :
    e8ThetaRegularized =O[atTop] (fun t : ℝ => t^(-(4 : ℝ))) := by
  have hp : (fun t : ℝ => ((t : ℂ)^4)⁻¹) =O[atTop]
      (fun t : ℝ => t^(-(4 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Real.rpow_neg ht.le, Real.rpow_ofNat]
  exact (e8ThetaTail_littleO_rpow (-4)).isBigO.sub hp

theorem e8ThetaRegularized_mellinConvergent {s : ℂ}
    (h0 : 0 < s.re) (h4 : s.re < 4) : MellinConvergent e8ThetaRegularized s :=
  mellinConvergent_of_isBigO_rpow
    (e8ThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    e8ThetaRegularized_bigO_infty h4 e8ThetaRegularized_bigO_zero h0

theorem e8ThetaRegularized_mellin_differentiableAt {s : ℂ}
    (h0 : 0 < s.re) (h4 : s.re < 4) :
    DifferentiableAt ℂ (mellin e8ThetaRegularized) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (e8ThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    e8ThetaRegularized_bigO_infty h4 e8ThetaRegularized_bigO_zero h0).2.differentiableAt

theorem e8ThetaRegularized_weighted_integrable :
    IntegrableOn (fun t : ℝ => (t : ℂ)*e8ThetaRegularized t) (Ioi 0) := by
  have h := e8ThetaRegularized_mellinConvergent (s := 2) (by norm_num) (by norm_num)
  simpa [MellinConvergent, smul_eq_mul, show (2 : ℂ)-1 = 1 by norm_num] using h

def e8SmoothEnergy : ℂ := (Real.pi : ℂ)^2 *
  ∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t

#print axioms e8ThetaImag_continuousOn
#print axioms e8ThetaTail_continuousOn
#print axioms e8ThetaRegularized_continuousOn
#print axioms e8ThetaImag_transform
#print axioms e8ThetaRegularized_inversion
#print axioms e8ThetaTail_exp_decay
#print axioms e8ThetaTail_littleO_rpow
#print axioms e8ThetaTail_scaled_tendsto
#print axioms e8ThetaRegularized_tendsto_zero
#print axioms e8ThetaRegularized_bigO_zero
#print axioms e8ThetaRegularized_bigO_infty
#print axioms e8ThetaRegularized_mellinConvergent
#print axioms e8ThetaRegularized_mellin_differentiableAt
#print axioms e8ThetaRegularized_weighted_integrable

end SphericalRiesz
