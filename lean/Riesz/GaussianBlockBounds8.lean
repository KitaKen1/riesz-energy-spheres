import Riesz.SphereLongRangeBlock8
import Riesz.RationalPatchSeparation8

/-! Measurability and size of Gaussian blocks as functions of the scale, and integrals of the
weight `α^p` on `Ioc 0 b`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

theorem gaussianBlock_alpha_measurable {ι : Type*} [Fintype ι] (c : ℝ) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    StronglyMeasurable (fun α : ℝ => kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M) := by
  apply Measurable.stronglyMeasurable
  unfold kernelBlock8
  exact (((gaussianKernelPair8_alpha_continuous c X).measurable).sub
    ((Finset.measurable_sum _ fun i _ =>
      (gaussianKernelPotential8_alpha_measurable c S (X i)).measurable).const_mul (2*M))).add
    ((gaussianKernelBackground8_alpha_measurable c S).measurable.const_mul (M^2))

theorem gaussianBlock_abs_le {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    |kernelBlock8 (sphereGaussianKernel8 t) X S M| ≤
      (Fintype.card ι:ℝ)^2 + 2 * |M| * (Fintype.card ι:ℝ) + M^2 := by
  unfold kernelBlock8
  have h1 := gaussianKernelPair8_abs_le ht X
  have h2 : |∑ i, kernelPotential8 (sphereGaussianKernel8 t) S (X i)| ≤ (Fintype.card ι:ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |kernelPotential8 (sphereGaussianKernel8 t) S (X i)| ≤ ∑ _i : ι, (1:ℝ) :=
          Finset.sum_le_sum fun i _ => gaussianKernelPotential8_abs_le ht S (X i)
      _ = _ := by simp
  have h3 := gaussianKernelBackground8_abs_le ht S
  have hA := abs_add_le (kernelPair8 (sphereGaussianKernel8 t) X-
    2*M*∑ i, kernelPotential8 (sphereGaussianKernel8 t) S (X i))
    (M^2*kernelBackground8 (sphereGaussianKernel8 t) S S)
  have hB := abs_sub (kernelPair8 (sphereGaussianKernel8 t) X)
    (2*M*∑ i, kernelPotential8 (sphereGaussianKernel8 t) S (X i))
  have hC : |2*M*∑ i, kernelPotential8 (sphereGaussianKernel8 t) S (X i)| ≤
      2 * |M| * (Fintype.card ι:ℝ) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hD : |M^2*kernelBackground8 (sphereGaussianKernel8 t) S S| ≤ M^2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg M)]
    exact mul_le_of_le_one_right (sq_nonneg M) h3
  linarith

/-- `α^p` times a bounded measurable function is integrable on `Ioc 0 b`. -/
theorem weighted_bounded_integrable_Ioc {p B b : ℝ} (hp : -1 < p) (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) (hbd : ∀ α ∈ Ioc (0:ℝ) b, |f α| ≤ B) :
    IntegrableOn (fun α : ℝ => α^p*f α) (Ioc 0 b) := by
  have hw : IntegrableOn (fun α : ℝ => α^p) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp (intervalIntegral.intervalIntegrable_rpow' hp)
  refine (hw.const_mul B).mono' (((measurable_id.pow_const p).mul hf.measurable).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hbd α hα) h0

theorem weight_integral_Ioc {p b : ℝ} (hp : -1 < p) (hb : 0 ≤ b) :
    ∫ α in Ioc (0:ℝ) b, α^p = b^(p+1)/(p+1) := by
  rw [← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hp),
    Real.zero_rpow (by linarith : p+1 ≠ 0), sub_zero]

end SphericalRiesz
