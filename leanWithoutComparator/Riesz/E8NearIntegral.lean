import Riesz.E8NearNodes
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# The actual singular near integral

One fixed inverse-fourth cutoff is integrable because 4 < 8. Haar scaling
and translation then give an exact r^4 integral for every positive radius.
The constant is the actual integral of the fixed kernel; no optimal ball
volume or theta value is needed for this coarse estimate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

def e8UnitNear (v : Fin 8 → ℝ) : ℝ := nearObliqueRieszFour 8 e8Map 1 0 v

theorem e8Near_nonneg (r : ℝ) (x v : Fin 8 → ℝ) :
    0 ≤ nearObliqueRieszFour 8 e8Map r x v := by
  apply mul_nonneg
  · unfold obliqueRieszFour flatRieszFour
    positivity
  · exact (outerUnitBump 8).nonneg

theorem e8Kernel_norm_bound (v : Fin 8 → ℝ) :
    ‖obliqueRieszFour 8 e8Map 0 v‖ ≤ (‖e8InverseMap‖+1)^4*‖v‖^(-4:ℝ) := by
  have hk : obliqueRieszFour 8 e8Map 0 v =
      ‖(WithLp.toLp 2 (e8Map v) : EuclideanSpace ℝ (Fin 8))‖⁻¹^4 := by
    simp only [obliqueRieszFour_eq_dist, map_zero, WithLp.toLp_zero, dist_zero_left]
  rw [hk, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hv : v = 0
  · subst v
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hM : 0 < ‖e8InverseMap‖+1 := by positivity
  have hb : ‖v‖ ≤ (‖e8InverseMap‖+1)*
      ‖(WithLp.toLp 2 (e8Map v) : EuclideanSpace ℝ (Fin 8))‖ := by
    calc
      _ = ‖e8InverseMap (e8Map v)‖ := by rw [e8InverseMap_e8Map]
      _ ≤ ‖e8InverseMap‖*‖e8Map v‖ := e8InverseMap.le_opNorm _
      _ ≤ (‖e8InverseMap‖+1)*‖e8Map v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pi_norm_le_euclidean _) hM.le
  have hlow : ‖v‖/(‖e8InverseMap‖+1) ≤
      ‖(WithLp.toLp 2 (e8Map v) : EuclideanSpace ℝ (Fin 8))‖ :=
    (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hb)
  have hinv : ‖(WithLp.toLp 2 (e8Map v) : EuclideanSpace ℝ (Fin 8))‖⁻¹ ≤
      (‖e8InverseMap‖+1)/‖v‖ := by
    simpa only [one_div, inv_div] using one_div_le_one_div_of_le (div_pos hn hM) hlow
  calc
    _ ≤ ((‖e8InverseMap‖+1)/‖v‖)^4 :=
      pow_le_pow_left₀ (by positivity) hinv 4
    _ = _ := by
      rw [Real.rpow_neg (norm_nonneg v) (4:ℝ), div_pow,
        div_eq_mul_inv]
      norm_num only [Real.rpow_ofNat]

theorem e8UnitNear_norm_bound (v : Fin 8 → ℝ) :
    ‖e8UnitNear v‖ ≤ (‖e8InverseMap‖+1)^4*‖v‖^(-4:ℝ) := by
  change ‖nearObliqueRieszFour 8 e8Map 1 0 v‖ ≤ _
  have hk : 0 ≤ obliqueRieszFour 8 e8Map 0 v := by
    unfold obliqueRieszFour flatRieszFour
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (e8Near_nonneg 1 0 v)]
  calc
    _ ≤ obliqueRieszFour 8 e8Map 0 v := by
      exact mul_le_of_le_one_right hk (outerUnitBump 8).le_one
    _ = ‖obliqueRieszFour 8 e8Map 0 v‖ := (Real.norm_of_nonneg hk).symm
    _ ≤ _ := e8Kernel_norm_bound v

theorem e8UnitNear_measurable : Measurable e8UnitNear := by
  have hA : Continuous (e8Map : (Fin 8 → ℝ) → (Fin 8 → ℝ)) := e8Map.continuous
  have hB : Continuous (outerUnitBump 8 : (Fin 8 → ℝ) → ℝ) := (outerUnitBump 8).continuous
  unfold e8UnitNear nearObliqueRieszFour obliqueRieszFour flatRieszFour squaredDistance
  fun_prop

theorem e8UnitNear_zero_outside (v : Fin 8 → ℝ) (hv : 2 ≤ ‖v‖) : e8UnitNear v = 0 := by
  have hb : outerUnitBump 8 v = 0 := (outerUnitBump 8).zero_of_le_dist (by
    simpa only [outerUnitBump, dist_zero_right] using hv)
  simp only [e8UnitNear, nearObliqueRieszFour, inv_one, sub_zero, one_smul, hb, mul_zero]

theorem e8UnitNear_integrable : Integrable e8UnitNear := by
  have hd : Module.finrank ℝ (Fin 8 → ℝ) = 8 := by simp
  have hi : IntegrableOn e8UnitNear (Metric.ball 0 3) :=
    integrableOn_ball_of_norm_le_rpow (by rw [hd]; norm_num)
      (by rw [hd]; norm_num : (4:ℝ) < Module.finrank ℝ (Fin 8 → ℝ))
      (Filter.Eventually.of_forall e8UnitNear_norm_bound) e8UnitNear_measurable.aestronglyMeasurable
  apply hi.integrable_of_forall_notMem_eq_zero
  intro v hv
  have hn : 3 ≤ ‖v‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hv
  exact e8UnitNear_zero_outside v (by linarith)

theorem e8Near_scaled (r : ℝ) (hr : 0 < r) (x v : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map r x v = (r⁻¹)^4*e8UnitNear (r⁻¹ • (v-x)) := by
  symm
  unfold e8UnitNear nearObliqueRieszFour obliqueRieszFour flatRieszFour
  simp only [inv_one, one_smul, sub_zero, map_smul]
  have hq := squaredDistance_scaled 8 r 0 (e8Map (v-x))
  simp only [sub_zero] at hq
  rw [hq, mul_pow, ← pow_mul]
  simp only [one_div, mul_inv, inv_pow, inv_inv]
  have hc : (r⁻¹)^4*r^4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  calc
    _ = ((r⁻¹)^4*r^4)*((squaredDistance 8 0 (e8Map (v-x)))^2)⁻¹*
        outerUnitBump 8 (r⁻¹ • (v-x)) := by ring
    _ = _ := by rw [hc, one_mul]

theorem e8Near_integrable (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    Integrable (nearObliqueRieszFour 8 e8Map r x) := by
  have h := ((e8UnitNear_integrable.comp_smul (inv_ne_zero hr.ne')).comp_sub_right x).const_mul
    ((r⁻¹)^4)
  exact h.congr (Filter.Eventually.of_forall (fun v => (e8Near_scaled r hr x v).symm))

def e8NearIntegralConstant : ℝ := ∫ v, e8UnitNear v

theorem e8NearIntegralConstant_nonneg : 0 ≤ e8NearIntegralConstant :=
  integral_nonneg (e8Near_nonneg 1 0)

theorem e8Near_integral (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    ∫ v, nearObliqueRieszFour 8 e8Map r x v = e8NearIntegralConstant*r^4 := by
  simp_rw [e8Near_scaled r hr x]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun v : Fin 8 → ℝ => e8UnitNear (r⁻¹ • v)) x,
    Measure.integral_comp_inv_smul_of_nonneg volume e8UnitNear hr.le]
  have hd : Module.finrank ℝ (Fin 8 → ℝ) = 8 := by simp
  rw [hd, smul_eq_mul]
  change (r⁻¹)^4*(r^8*e8NearIntegralConstant) = _
  field_simp

theorem e8Near_cubeIntegral_bound (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    |∫ v in UnitCube 8, nearObliqueRieszFour 8 e8Map r x v| ≤ e8NearIntegralConstant*r^4 := by
  rw [abs_of_nonneg (integral_nonneg (e8Near_nonneg r x)), ← e8Near_integral r hr x]
  exact setIntegral_le_integral (e8Near_integrable r hr x)
    (Filter.Eventually.of_forall (e8Near_nonneg r x))

#print axioms e8Near_nonneg
#print axioms e8Kernel_norm_bound
#print axioms e8UnitNear_norm_bound
#print axioms e8UnitNear_measurable
#print axioms e8UnitNear_zero_outside
#print axioms e8UnitNear_integrable
#print axioms e8Near_scaled
#print axioms e8Near_integrable
#print axioms e8NearIntegralConstant_nonneg
#print axioms e8Near_integral
#print axioms e8Near_cubeIntegral_bound

end SphericalRiesz
