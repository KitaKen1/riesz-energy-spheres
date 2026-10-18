import Riesz.LeechGaussianEnds24

/-! Physical-space square form of Gaussian quadratic forms on the actual ambient space R25.

`e^{-t|x-y|²} = (4t/π)^{25/2} ∫ e^{-2t|x-z|²} e^{-2t|y-z|²} dz`.  Hence for finite measures the
neutralized Gaussian energy is `(4t/π)^{25/2} ∫ (B_μ(z) - M B_ν(z))² dz` with the bump fields
`B_μ(z) = ∫ e^{-2t|x-z|²} dμ(x)`.  The bump field is local in `z`, so two-sided quadrature of a
Gaussian energy reduces to one-sided errors of single Gaussian bumps (no mixed derivatives). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- The ambient Gaussian bump `e^{-2t|x-z|²}`. -/
def ambientBump25 (t : ℝ) (x z : (AmbientD 24)) : ℝ := Real.exp (-(2*t*‖x-z‖^2))

theorem ambientBump25_nonneg (t : ℝ) (x z : (AmbientD 24)) : 0 ≤ ambientBump25 t x z :=
  (Real.exp_pos _).le

theorem ambientBump25_le_one {t : ℝ} (ht : 0 ≤ t) (x z : (AmbientD 24)) : ambientBump25 t x z ≤ 1 := by
  unfold ambientBump25
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ 2*t*‖x-z‖^2 := by positivity
  linarith

theorem continuous_ambientBump25 (t : ℝ) :
    Continuous (fun p : (AmbientD 24) × (AmbientD 24) => ambientBump25 t p.1 p.2) := by
  unfold ambientBump25
  fun_prop

theorem ambient25_gaussian_integrable {b : ℝ} (hb : 0 < b) (m : (AmbientD 24)) :
    Integrable (fun z : (AmbientD 24) => Real.exp (-(b*‖z-m‖^2))) := by
  have h := (integrable_rexp_neg_mul_sq_norm25 hb).comp_sub_right m
  simpa only [neg_mul] using h

theorem ambient25_gaussian_integral {b : ℝ} (hb : 0 < b) (m : (AmbientD 24)) :
    ∫ z : (AmbientD 24), Real.exp (-(b*‖z-m‖^2)) = (Real.pi/b)^((25:ℝ)/2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := (AmbientD 24)) hb
  rw [finrank_euclideanSpace_fin] at h
  have h2 := integral_sub_right_eq_self (μ := (volume : Measure (AmbientD 24)))
    (fun z : (AmbientD 24) => Real.exp (-b*‖z‖^2)) m
  simp only [neg_mul] at h2 h
  rw [h2, h]
  norm_num

/-- Completing the square: the product of two bumps is a Gaussian in `x-y` times a bump at the
midpoint. -/
theorem ambientBump25_mul_eq (t : ℝ) (x y z : (AmbientD 24)) :
    ambientBump25 t x z*ambientBump25 t y z =
      Real.exp (-(t*‖x-y‖^2))*Real.exp (-((4*t)*‖z-(1/2:ℝ)•(x+y)‖^2)) := by
  unfold ambientBump25
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hpar := parallelogram_law_with_norm ℝ (x-z) (y-z)
  have h1 : x-z+(y-z) = (-2:ℝ)•(z-(1/2:ℝ)•(x+y)) := by module
  have h2 : x-z-(y-z) = x-y := by abel
  have hn : ‖(-2:ℝ)‖ = 2 := by norm_num
  rw [h1, h2, norm_smul, hn] at hpar
  linear_combination t*hpar

theorem ambientBump25_mul_integrable {t : ℝ} (ht : 0 < t) (x y : (AmbientD 24)) :
    Integrable (fun z => ambientBump25 t x z*ambientBump25 t y z) := by
  simp_rw [ambientBump25_mul_eq]
  exact (ambient25_gaussian_integrable (by positivity) _).const_mul _

theorem ambientBump25_mul_integral {t : ℝ} (ht : 0 < t) (x y : (AmbientD 24)) :
    ∫ z, ambientBump25 t x z*ambientBump25 t y z =
      (Real.pi/(4*t))^((25:ℝ)/2)*gaussianKernel t x y := by
  simp_rw [ambientBump25_mul_eq]
  rw [integral_const_mul, ambient25_gaussian_integral (by positivity)]
  unfold gaussianKernel
  ring

theorem ambientBump25_triple_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 24))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (Function.uncurry fun (z : (AmbientD 24)) (q : (AmbientD 24) × (AmbientD 24)) =>
      ambientBump25 t q.1 z*ambientBump25 t q.2 z) (volume.prod (μ.prod ν)) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : (AmbientD 24)) (q : (AmbientD 24) × (AmbientD 24)) =>
      ambientBump25 t q.1 z*ambientBump25 t q.2 z) (volume.prod (μ.prod ν)) := by
    apply Continuous.aestronglyMeasurable
    unfold ambientBump25 Function.uncurry
    fun_prop
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun q => ambientBump25_mul_integrable ht q.1 q.2, ?_⟩
  have he : (fun q : (AmbientD 24) × (AmbientD 24) =>
      ∫ z, ‖Function.uncurry (fun (z : (AmbientD 24)) (q : (AmbientD 24) × (AmbientD 24)) =>
        ambientBump25 t q.1 z*ambientBump25 t q.2 z) (z, q)‖) =
      fun q => (Real.pi/(4*t))^((25:ℝ)/2)*gaussianKernel t q.1 q.2 := by
    funext q
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (mul_nonneg (ambientBump25_nonneg _ _ _) (ambientBump25_nonneg _ _ _))]
    exact ambientBump25_mul_integral ht q.1 q.2
  rw [he]
  exact (gaussianKernel_product_integrable ht.le _).const_mul _

/-- The bump field of a finite measure. -/
def bumpField25 (t : ℝ) (μ : Measure (AmbientD 24)) (z : (AmbientD 24)) : ℝ :=
  ∫ x, ambientBump25 t x z ∂μ

theorem bumpField25_mul_eq (t : ℝ) (μ ν : Measure (AmbientD 24)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (z : (AmbientD 24)) :
    bumpField25 t μ z*bumpField25 t ν z =
      ∫ q, ambientBump25 t q.1 z*ambientBump25 t q.2 z ∂(μ.prod ν) := by
  unfold bumpField25
  exact (integral_prod_mul (fun x => ambientBump25 t x z) (fun y => ambientBump25 t y z)).symm

theorem bumpField25_mul_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 24))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z => bumpField25 t μ z*bumpField25 t ν z) := by
  simp_rw [bumpField25_mul_eq t μ ν]
  exact (ambientBump25_triple_integrable ht μ ν).integral_prod_left

/-- Square form of the Gaussian pair energy of two finite measures. -/
theorem gaussianMeasurePair_eq_bump25 {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 24))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasurePair t μ ν =
      (4*t/Real.pi)^((25:ℝ)/2)*∫ z, bumpField25 t μ z*bumpField25 t ν z := by
  simp_rw [bumpField25_mul_eq t μ ν]
  rw [integral_integral_swap (ambientBump25_triple_integrable ht μ ν)]
  simp_rw [ambientBump25_mul_integral ht]
  rw [integral_const_mul, ← mul_assoc]
  have hc : (4*t/Real.pi)^((25:ℝ)/2)*(Real.pi/(4*t))^((25:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : 4*t/Real.pi*(Real.pi/(4*t)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]
  rw [hc, one_mul]
  rfl

/-- Square form of the neutralized Gaussian energy. -/
theorem gaussianMeasureDefect_eq_bump_sq25 {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure (AmbientD 24))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasureDefect t M μ ν =
      (4*t/Real.pi)^((25:ℝ)/2)*∫ z, (bumpField25 t μ z-M*bumpField25 t ν z)^2 := by
  unfold gaussianMeasureDefect
  rw [gaussianMeasurePair_eq_bump25 ht μ μ, gaussianMeasurePair_eq_bump25 ht μ ν,
    gaussianMeasurePair_eq_bump25 ht ν ν]
  have hμμ := bumpField25_mul_integrable ht μ μ
  have hμν := bumpField25_mul_integrable ht μ ν
  have hνν := bumpField25_mul_integrable ht ν ν
  have hsq : (fun z => (bumpField25 t μ z-M*bumpField25 t ν z)^2) =
      fun z => bumpField25 t μ z*bumpField25 t μ z-2*M*(bumpField25 t μ z*bumpField25 t ν z)+
        M^2*(bumpField25 t ν z*bumpField25 t ν z) := by
    funext z
    ring
  have hA : Integrable (fun z => bumpField25 t μ z*bumpField25 t μ z-
      2*M*(bumpField25 t μ z*bumpField25 t ν z)) := hμμ.sub (hμν.const_mul _)
  have hB : Integrable (fun z => M^2*(bumpField25 t ν z*bumpField25 t ν z)) := hνν.const_mul _
  rw [hsq, integral_add hA hB, integral_sub hμμ (hμν.const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- Upper bound of the neutralized Gaussian energy by a pointwise majorant of the bump error. -/
theorem gaussianMeasureDefect_le_of_bump25 {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure (AmbientD 24))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {W : (AmbientD 24) → ℝ} (hW : Integrable (fun z => W z^2))
    (hle : ∀ z, |bumpField25 t μ z-M*bumpField25 t ν z| ≤ W z) :
    gaussianMeasureDefect t M μ ν ≤ (4*t/Real.pi)^((25:ℝ)/2)*∫ z, W z^2 := by
  rw [gaussianMeasureDefect_eq_bump_sq25 ht]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) hW
  refine ae_of_all _ fun z => ?_
  have h := hle z
  have h0 : 0 ≤ W z := (abs_nonneg _).trans h
  calc (bumpField25 t μ z-M*bumpField25 t ν z)^2 = |bumpField25 t μ z-M*bumpField25 t ν z|^2 :=
        (sq_abs _).symm
    _ ≤ W z^2 := pow_le_pow_left₀ (abs_nonneg _) h 2

end SphericalRiesz
