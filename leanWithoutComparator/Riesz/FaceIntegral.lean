import Riesz.CubeLebesgue
import Riesz.E8Separation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# The seven-dimensional boundary-face majorant

The fifth derivative of an inverse-fourth kernel has singular order nine.
On a seven-dimensional face at distance δ > 0, its integrable majorant
has integral C δ⁻². We use the actual integral of a fixed Japanese bracket
as C; neither the exact ball volume nor a gamma integral is needed.

The norm on `Fin 7 → ℝ` is the supremum norm. This is a deliberately
coarse majorant and the measure is the actual product Lebesgue measure.
No derivative formula for the E8 potential is assumed or proved here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

def faceWeight (δ : ℝ) (z : Fin 7 → ℝ) : ℝ :=
  (δ^2 + ‖z‖^2)^(-(9 : ℝ)/2)

theorem faceWeight_nonneg (δ : ℝ) (z : Fin 7 → ℝ) : 0 ≤ faceWeight δ z := by
  unfold faceWeight
  exact Real.rpow_nonneg (by positivity) _

theorem faceWeight_one_integrable : Integrable (faceWeight 1) := by
  change Integrable (fun z : Fin 7 → ℝ => (1^2 + ‖z‖^2)^(-(9:ℝ)/2))
  simpa only [one_pow] using
    (integrable_rpow_neg_one_add_norm_sq
      (E := Fin 7 → ℝ) (μ := volume) (r := 9) (by norm_num))

theorem faceWeight_scaled (δ : ℝ) (hδ : 0 < δ) (z : Fin 7 → ℝ) :
    faceWeight δ z = (δ⁻¹)^9 * faceWeight 1 (δ⁻¹ • z) := by
  have hn : ‖δ⁻¹ • z‖ = δ⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  have hq : δ^2 + ‖z‖^2 = δ^2 * (1 + ‖δ⁻¹ • z‖^2) := by
    rw [hn]
    field_simp
  have hp : (δ^2)^(-(9 : ℝ)/2) = (δ⁻¹)^9 := by
    rw [← Real.rpow_natCast_mul hδ.le 2]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ)*(-9/2) = -9 by norm_num]
    rw [Real.rpow_neg hδ.le, Real.rpow_ofNat, inv_pow]
  unfold faceWeight
  rw [hq, Real.mul_rpow (by positivity) (by positivity), hp]
  simp only [one_pow]

theorem faceWeight_eq_sqrt (δ : ℝ) (hδ : 0 < δ) (z : Fin 7 → ℝ) :
    faceWeight δ z = ((Real.sqrt (δ^2+‖z‖^2))⁻¹)^9 := by
  have hq : 0 < δ^2+‖z‖^2 := by positivity
  have hp : (Real.sqrt (δ^2+‖z‖^2))^9 = (δ^2+‖z‖^2)^((9:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [faceWeight, show -(9:ℝ)/2 = -((9:ℝ)/2) by ring, Real.rpow_neg hq.le,
    inv_pow, hp]

theorem faceWeight_integrable (δ : ℝ) (hδ : 0 < δ) (a : Fin 7 → ℝ) :
    Integrable (fun z => faceWeight δ (z-a)) := by
  have hi := ((faceWeight_one_integrable.comp_smul (inv_ne_zero hδ.ne')).comp_sub_right a).const_mul
    ((δ⁻¹)^9)
  exact hi.congr (Filter.Eventually.of_forall fun z => (faceWeight_scaled δ hδ (z-a)).symm)

def faceIntegralConstant : ℝ := ∫ z, faceWeight 1 z

theorem faceIntegralConstant_nonneg : 0 ≤ faceIntegralConstant :=
  integral_nonneg (faceWeight_nonneg 1)

theorem faceWeight_integral (δ : ℝ) (hδ : 0 < δ) (a : Fin 7 → ℝ) :
    ∫ z, faceWeight δ (z-a) = faceIntegralConstant/δ^2 := by
  simp_rw [faceWeight_scaled δ hδ]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun z : Fin 7 → ℝ => faceWeight 1 (δ⁻¹ • z)) a,
    Measure.integral_comp_inv_smul_of_nonneg volume (faceWeight 1) hδ.le]
  have hd : Module.finrank ℝ (Fin 7 → ℝ) = 7 := by simp
  rw [hd, smul_eq_mul]
  change (δ⁻¹)^9*(δ^7*faceIntegralConstant) = _
  field_simp

theorem faceWeight_cubeIntegral_bound (δ : ℝ) (hδ : 0 < δ) (a : Fin 7 → ℝ) :
    |∫ z in UnitCube 7, faceWeight δ (z-a)| ≤ faceIntegralConstant/δ^2 := by
  rw [abs_of_nonneg (integral_nonneg fun z => faceWeight_nonneg δ (z-a)),
    ← faceWeight_integral δ hδ a]
  exact setIntegral_le_integral (faceWeight_integrable δ hδ a)
    (Filter.Eventually.of_forall fun z => faceWeight_nonneg δ (z-a))

/-- A measurable face integrand dominated by the actual weight is integrable. -/
theorem integrableOn_of_faceWeight_bound (δ : ℝ) (hδ : 0 < δ) (a : Fin 7 → ℝ)
    (f : (Fin 7 → ℝ) → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (UnitCube 7)))
    (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ z ∈ UnitCube 7, |f z| ≤ C * faceWeight δ (z-a)) :
    IntegrableOn f (UnitCube 7) := by
  apply ((faceWeight_integrable δ hδ a).integrableOn.const_mul C).mono' hf
  filter_upwards [ae_restrict_mem (unitCube_measurableSet 7)] with z hz
  simpa [Real.norm_eq_abs] using hb z hz

theorem faceIntegral_bound (δ : ℝ) (hδ : 0 < δ) (a : Fin 7 → ℝ)
    (f : (Fin 7 → ℝ) → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (UnitCube 7)))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ∈ UnitCube 7, |f z| ≤ C * faceWeight δ (z-a)) :
    |∫ z in UnitCube 7, f z| ≤ C*faceIntegralConstant/δ^2 := by
  have hi := integrableOn_of_faceWeight_bound δ hδ a f hf C hC hb
  calc
    _ ≤ ∫ z in UnitCube 7, |f z| := abs_integral_le_integral_abs
    _ ≤ ∫ z in UnitCube 7, C*faceWeight δ (z-a) := by
      apply integral_mono_ae hi.abs ((faceWeight_integrable δ hδ a).integrableOn.const_mul C)
      filter_upwards [ae_restrict_mem (unitCube_measurableSet 7)] with z hz
      exact hb z hz
    _ = C*(∫ z in UnitCube 7, faceWeight δ (z-a)) := integral_const_mul _ _
    _ ≤ C*(faceIntegralConstant/δ^2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (le_abs_self _).trans (faceWeight_cubeIntegral_bound δ hδ a)
    _ = _ := by ring

/-- The actual Euclidean inverse ninth power on any E8 coordinate face. -/
def e8FaceInverseNine (i : Fin 8) (δ : ℝ) (a z : Fin 7 → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (e8Map (i.insertNth δ (z-a))) : EuclideanSpace ℝ (Fin 8))‖⁻¹^9

theorem e8FaceInverseNine_bound (i : Fin 8) (δ : ℝ) (hδ : 0 < δ)
    (a z : Fin 7 → ℝ) :
    e8FaceInverseNine i δ a z ≤ (2*(‖e8InverseMap‖+1))^9 * faceWeight δ (z-a) := by
  let v : Fin 8 → ℝ := i.insertNth δ (z-a)
  let M : ℝ := ‖e8InverseMap‖+1
  let ρ : ℝ := ‖(WithLp.toLp 2 (e8Map v) : EuclideanSpace ℝ (Fin 8))‖
  have hM : 0 < M := by dsimp only [M]; positivity
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hv : ‖v‖ ≤ M*ρ := by
    calc
      _ = ‖e8InverseMap (e8Map v)‖ := by rw [e8InverseMap_e8Map]
      _ ≤ ‖e8InverseMap‖*‖e8Map v‖ := e8InverseMap.le_opNorm _
      _ ≤ M*‖e8Map v‖ := mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith)
        (norm_nonneg _)
      _ ≤ M*ρ := mul_le_mul_of_nonneg_left (pi_norm_le_euclidean _) hM.le
  have hδv : δ ≤ ‖v‖ := by
    simpa only [v, Fin.insertNth_apply_same, Real.norm_eq_abs, abs_of_pos hδ] using
      norm_le_pi_norm v i
  have hzv : ‖z-a‖ ≤ ‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro j
    simpa only [v, Fin.insertNth_apply_succAbove] using norm_le_pi_norm v (i.succAbove j)
  have hq : 0 < δ^2+‖z-a‖^2 := by positivity
  have hsum : δ^2+‖z-a‖^2 ≤ (2*M*ρ)^2 := by
    have h1 := pow_le_pow_left₀ hδ.le (hδv.trans hv) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg (z-a)) (hzv.trans hv) 2
    nlinarith [sq_nonneg (M*ρ)]
  have hp : 0 < Real.sqrt (δ^2+‖z-a‖^2) := Real.sqrt_pos.mpr hq
  have hs : Real.sqrt (δ^2+‖z-a‖^2)/(2*M) ≤ ρ := by
    apply (div_le_iff₀ (by positivity : 0 < 2*M)).mpr
    have h := (sq_le_sq₀ hp.le (by positivity : 0 ≤ 2*M*ρ)).mp (by
      rw [Real.sq_sqrt hq.le]
      exact hsum)
    nlinarith only [h]
  have hinv : ρ⁻¹ ≤ (2*M)/Real.sqrt (δ^2+‖z-a‖^2) := by
    simpa only [one_div, inv_div] using
      one_div_le_one_div_of_le (div_pos hp (by positivity : 0 < 2*M)) hs
  change ρ⁻¹^9 ≤ (2*M)^9 * faceWeight δ (z-a)
  calc
    _ ≤ ((2*M)/Real.sqrt (δ^2+‖z-a‖^2))^9 :=
      pow_le_pow_left₀ (by positivity) hinv 9
    _ = _ := by rw [div_pow, faceWeight_eq_sqrt δ hδ, inv_pow, div_eq_mul_inv]

theorem e8FaceInverseNine_measurable (i : Fin 8) (δ : ℝ) (a : Fin 7 → ℝ) :
    Measurable (e8FaceInverseNine i δ a) := by
  unfold e8FaceInverseNine
  fun_prop

theorem e8FaceInverseNine_integrable (i : Fin 8) (δ : ℝ) (hδ : 0 < δ)
    (a : Fin 7 → ℝ) : Integrable (e8FaceInverseNine i δ a) := by
  apply ((faceWeight_integrable δ hδ a).const_mul ((2*(‖e8InverseMap‖+1))^9)).mono'
    (e8FaceInverseNine_measurable i δ a).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold e8FaceInverseNine; positivity)]
  exact e8FaceInverseNine_bound i δ hδ a z

theorem e8FaceInverseNine_cubeIntegral_bound (i : Fin 8) (δ : ℝ) (hδ : 0 < δ)
    (a : Fin 7 → ℝ) :
    |∫ z in UnitCube 7, e8FaceInverseNine i δ a z| ≤
      (2*(‖e8InverseMap‖+1))^9 * faceIntegralConstant/δ^2 := by
  apply faceIntegral_bound δ hδ a (e8FaceInverseNine i δ a)
    (e8FaceInverseNine_measurable i δ a).aestronglyMeasurable _ (by positivity)
  intro z _
  rw [abs_of_nonneg (by unfold e8FaceInverseNine; positivity)]
  exact e8FaceInverseNine_bound i δ hδ a z

#print axioms faceWeight_nonneg
#print axioms faceWeight_one_integrable
#print axioms faceWeight_scaled
#print axioms faceWeight_eq_sqrt
#print axioms faceWeight_integrable
#print axioms faceIntegralConstant_nonneg
#print axioms faceWeight_integral
#print axioms faceWeight_cubeIntegral_bound
#print axioms integrableOn_of_faceWeight_bound
#print axioms faceIntegral_bound
#print axioms e8FaceInverseNine_bound
#print axioms e8FaceInverseNine_measurable
#print axioms e8FaceInverseNine_integrable
#print axioms e8FaceInverseNine_cubeIntegral_bound

end SphericalRiesz
