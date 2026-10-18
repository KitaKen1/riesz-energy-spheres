import Riesz.SphereGaussianMonotone8

/-! Physical-space square form of Gaussian quadratic forms on `Ambient9`.

`e^{-t|x-y|²} = (4t/π)^{9/2} ∫ e^{-2t|x-z|²} e^{-2t|y-z|²} dz`.  Hence for finite measures the
neutralized Gaussian energy is `(4t/π)^{9/2} ∫ (B_μ(z) - M B_ν(z))² dz` with the bump fields
`B_μ(z) = ∫ e^{-2t|x-z|²} dμ(x)`.  The bump field is local in `z`, so two-sided quadrature of a
Gaussian energy reduces to one-sided errors of single Gaussian bumps (no mixed derivatives). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- The ambient Gaussian bump `e^{-2t|x-z|²}`. -/
def ambientBump9 (t : ℝ) (x z : Ambient9) : ℝ := Real.exp (-(2*t*‖x-z‖^2))

theorem ambientBump9_nonneg (t : ℝ) (x z : Ambient9) : 0 ≤ ambientBump9 t x z :=
  (Real.exp_pos _).le

theorem ambientBump9_le_one {t : ℝ} (ht : 0 ≤ t) (x z : Ambient9) : ambientBump9 t x z ≤ 1 := by
  unfold ambientBump9
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ 2*t*‖x-z‖^2 := by positivity
  linarith

theorem continuous_ambientBump9 (t : ℝ) :
    Continuous (fun p : Ambient9 × Ambient9 => ambientBump9 t p.1 p.2) := by
  unfold ambientBump9
  fun_prop

theorem ambient9_gaussian_integrable {b : ℝ} (hb : 0 < b) (m : Ambient9) :
    Integrable (fun z : Ambient9 => Real.exp (-(b*‖z-m‖^2))) := by
  have h := (integrable_rexp_neg_mul_sq_norm9 hb).comp_sub_right m
  simpa only [neg_mul] using h

theorem ambient9_gaussian_integral {b : ℝ} (hb : 0 < b) (m : Ambient9) :
    ∫ z : Ambient9, Real.exp (-(b*‖z-m‖^2)) = (Real.pi/b)^((9:ℝ)/2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Ambient9) hb
  rw [finrank_euclideanSpace_fin] at h
  have h2 := integral_sub_right_eq_self (μ := (volume : Measure Ambient9))
    (fun z : Ambient9 => Real.exp (-b*‖z‖^2)) m
  simp only [neg_mul] at h2 h
  rw [h2, h]
  norm_num

/-- Completing the square: the product of two bumps is a Gaussian in `x-y` times a bump at the
midpoint. -/
theorem ambientBump9_mul_eq (t : ℝ) (x y z : Ambient9) :
    ambientBump9 t x z*ambientBump9 t y z =
      Real.exp (-(t*‖x-y‖^2))*Real.exp (-((4*t)*‖z-(1/2:ℝ)•(x+y)‖^2)) := by
  unfold ambientBump9
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hpar := parallelogram_law_with_norm ℝ (x-z) (y-z)
  have h1 : x-z+(y-z) = (-2:ℝ)•(z-(1/2:ℝ)•(x+y)) := by module
  have h2 : x-z-(y-z) = x-y := by abel
  have hn : ‖(-2:ℝ)‖ = 2 := by norm_num
  rw [h1, h2, norm_smul, hn] at hpar
  linear_combination t*hpar

theorem ambientBump9_mul_integrable {t : ℝ} (ht : 0 < t) (x y : Ambient9) :
    Integrable (fun z => ambientBump9 t x z*ambientBump9 t y z) := by
  simp_rw [ambientBump9_mul_eq]
  exact (ambient9_gaussian_integrable (by positivity) _).const_mul _

theorem ambientBump9_mul_integral {t : ℝ} (ht : 0 < t) (x y : Ambient9) :
    ∫ z, ambientBump9 t x z*ambientBump9 t y z =
      (Real.pi/(4*t))^((9:ℝ)/2)*gaussianKernel t x y := by
  simp_rw [ambientBump9_mul_eq]
  rw [integral_const_mul, ambient9_gaussian_integral (by positivity)]
  unfold gaussianKernel
  ring

theorem ambientBump9_triple_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (Function.uncurry fun (z : Ambient9) (q : Ambient9 × Ambient9) =>
      ambientBump9 t q.1 z*ambientBump9 t q.2 z) (volume.prod (μ.prod ν)) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : Ambient9) (q : Ambient9 × Ambient9) =>
      ambientBump9 t q.1 z*ambientBump9 t q.2 z) (volume.prod (μ.prod ν)) := by
    apply Continuous.aestronglyMeasurable
    unfold ambientBump9 Function.uncurry
    fun_prop
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun q => ambientBump9_mul_integrable ht q.1 q.2, ?_⟩
  have he : (fun q : Ambient9 × Ambient9 =>
      ∫ z, ‖Function.uncurry (fun (z : Ambient9) (q : Ambient9 × Ambient9) =>
        ambientBump9 t q.1 z*ambientBump9 t q.2 z) (z, q)‖) =
      fun q => (Real.pi/(4*t))^((9:ℝ)/2)*gaussianKernel t q.1 q.2 := by
    funext q
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (mul_nonneg (ambientBump9_nonneg _ _ _) (ambientBump9_nonneg _ _ _))]
    exact ambientBump9_mul_integral ht q.1 q.2
  rw [he]
  exact (gaussianKernel_product_integrable ht.le _).const_mul _

/-- The bump field of a finite measure. -/
def bumpField9 (t : ℝ) (μ : Measure Ambient9) (z : Ambient9) : ℝ :=
  ∫ x, ambientBump9 t x z ∂μ

theorem bumpField9_mul_eq (t : ℝ) (μ ν : Measure Ambient9) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (z : Ambient9) :
    bumpField9 t μ z*bumpField9 t ν z =
      ∫ q, ambientBump9 t q.1 z*ambientBump9 t q.2 z ∂(μ.prod ν) := by
  unfold bumpField9
  exact (integral_prod_mul (fun x => ambientBump9 t x z) (fun y => ambientBump9 t y z)).symm

theorem bumpField9_mul_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z => bumpField9 t μ z*bumpField9 t ν z) := by
  simp_rw [bumpField9_mul_eq t μ ν]
  exact (ambientBump9_triple_integrable ht μ ν).integral_prod_left

/-- Square form of the Gaussian pair energy of two finite measures. -/
theorem gaussianMeasurePair_eq_bump {t : ℝ} (ht : 0 < t) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasurePair t μ ν =
      (4*t/Real.pi)^((9:ℝ)/2)*∫ z, bumpField9 t μ z*bumpField9 t ν z := by
  simp_rw [bumpField9_mul_eq t μ ν]
  rw [integral_integral_swap (ambientBump9_triple_integrable ht μ ν)]
  simp_rw [ambientBump9_mul_integral ht]
  rw [integral_const_mul, ← mul_assoc]
  have hc : (4*t/Real.pi)^((9:ℝ)/2)*(Real.pi/(4*t))^((9:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : 4*t/Real.pi*(Real.pi/(4*t)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]
  rw [hc, one_mul]
  rfl

/-- Square form of the neutralized Gaussian energy. -/
theorem gaussianMeasureDefect_eq_bump_sq {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasureDefect t M μ ν =
      (4*t/Real.pi)^((9:ℝ)/2)*∫ z, (bumpField9 t μ z-M*bumpField9 t ν z)^2 := by
  unfold gaussianMeasureDefect
  rw [gaussianMeasurePair_eq_bump ht μ μ, gaussianMeasurePair_eq_bump ht μ ν,
    gaussianMeasurePair_eq_bump ht ν ν]
  have hμμ := bumpField9_mul_integrable ht μ μ
  have hμν := bumpField9_mul_integrable ht μ ν
  have hνν := bumpField9_mul_integrable ht ν ν
  have hsq : (fun z => (bumpField9 t μ z-M*bumpField9 t ν z)^2) =
      fun z => bumpField9 t μ z*bumpField9 t μ z-2*M*(bumpField9 t μ z*bumpField9 t ν z)+
        M^2*(bumpField9 t ν z*bumpField9 t ν z) := by
    funext z
    ring
  have hA : Integrable (fun z => bumpField9 t μ z*bumpField9 t μ z-
      2*M*(bumpField9 t μ z*bumpField9 t ν z)) := hμμ.sub (hμν.const_mul _)
  have hB : Integrable (fun z => M^2*(bumpField9 t ν z*bumpField9 t ν z)) := hνν.const_mul _
  rw [hsq, integral_add hA hB, integral_sub hμμ (hμν.const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- Upper bound of the neutralized Gaussian energy by a pointwise majorant of the bump error. -/
theorem gaussianMeasureDefect_le_of_bump {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {W : Ambient9 → ℝ} (hW : Integrable (fun z => W z^2))
    (hle : ∀ z, |bumpField9 t μ z-M*bumpField9 t ν z| ≤ W z) :
    gaussianMeasureDefect t M μ ν ≤ (4*t/Real.pi)^((9:ℝ)/2)*∫ z, W z^2 := by
  rw [gaussianMeasureDefect_eq_bump_sq ht]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) hW
  refine ae_of_all _ fun z => ?_
  have h := hle z
  have h0 : 0 ≤ W z := (abs_nonneg _).trans h
  calc (bumpField9 t μ z-M*bumpField9 t ν z)^2 = |bumpField9 t μ z-M*bumpField9 t ν z|^2 :=
        (sq_abs _).symm
    _ ≤ W z^2 := pow_le_pow_left₀ (abs_nonneg _) h 2

end SphericalRiesz
