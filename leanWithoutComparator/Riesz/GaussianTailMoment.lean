import Riesz.E8SmoothValue

/-! A known primitive certificate for the shifted second Gaussian moment. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

def gaussianTailPrimitive (a ε t : ℝ) : ℝ :=
  -((t-ε)/a + 1/a^2) * Real.exp (-a*t)

theorem gaussianTailPrimitive_deriv {a : ℝ} (ha : 0 < a) (ε t : ℝ) :
    HasDerivAt (gaussianTailPrimitive a ε)
      ((t-ε)*Real.exp (-a*t)) t := by
  have hl := ((hasDerivAt_id t).sub_const ε).div_const a |>.add_const (1/a^2)
  have he := ((hasDerivAt_id t).const_mul (-a)).exp
  convert (hl.mul he).neg using 1
  · funext u
    simp [gaussianTailPrimitive, neg_mul] <;> ring
  · dsimp only [id_eq]
    field_simp
    simp only [mul_comm]
    ring

theorem gaussianTailPrimitive_tendsto {a : ℝ} (ha : 0 < a) (ε : ℝ) :
    Tendsto (gaussianTailPrimitive a ε) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-a*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))
  have ht : Tendsto (fun t : ℝ => t*Real.exp (-a*t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have h := (((ht.sub (he.const_mul ε)).div_const a).add (he.div_const (a^2))).neg
  simp only [mul_zero, sub_zero, zero_div, add_zero, neg_zero] at h
  apply h.congr'
  exact Eventually.of_forall (fun t => by unfold gaussianTailPrimitive; ring)

theorem gaussianTailMoment_integrable {a : ℝ} (ha : 0 < a) (ε : ℝ) :
    IntegrableOn (fun t : ℝ => (t-ε)*Real.exp (-a*t)) (Ioi ε) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => gaussianTailPrimitive_deriv ha ε t)
    (fun t ht => mul_nonneg (sub_nonneg.mpr (show ε < t from ht).le) (Real.exp_pos _).le)
    (gaussianTailPrimitive_tendsto ha ε)

theorem gaussianTailMoment_integral {a : ℝ} (ha : 0 < a) (ε : ℝ) :
    (∫ t : ℝ in Ioi ε, (t-ε)*Real.exp (-a*t)) = Real.exp (-a*ε)/a^2 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => gaussianTailPrimitive_deriv ha ε t)
    (gaussianTailMoment_integrable ha ε) (gaussianTailPrimitive_tendsto ha ε)]
  simp [gaussianTailPrimitive, div_eq_mul_inv, mul_comm]

#print axioms gaussianTailPrimitive_deriv
#print axioms gaussianTailPrimitive_tendsto
#print axioms gaussianTailMoment_integrable
#print axioms gaussianTailMoment_integral

end SphericalRiesz
