import Riesz.CompactKernelCorrelation
import Riesz.SchwartzMeasurePSD
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
The exact flat chart background, with actual coordinate Lebesgue integrals.
Translation, dilation and Fubini give the autocorrelation formula.  The
compact-cutoff correlation theorem then gives its density limit and the
original Schwartz Fourier value at zero.  No geometric sphere transport or
rotation-average identity is supplied or asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace SphericalRiesz

variable {d : ℕ}

def compactKernelBackground (q k : (EuclideanSpace ℝ (Fin d)) → ℝ) (a : ℝ) : ℝ :=
  ∫ u, ∫ v, q u*q v*k (a • (u-v))

theorem compactKernelBackground_row (q k : (EuclideanSpace ℝ (Fin d)) → ℝ) {a : ℝ} (ha : 0 < a) (u : (EuclideanSpace ℝ (Fin d))) :
    (∫ v, q u*q v*k (a • (u-v))) = (a ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹ *
      ∫ z, q u*q (u-a⁻¹ • z)*k z := by
  calc
    _ = ∫ w, q u*q (u-w)*k (a • w) := by
      have h := integral_sub_left_eq_self
        (fun v => q u*q v*k (a • (u-v))) (volume : Measure (EuclideanSpace ℝ (Fin d))) u
      simpa only [sub_sub_cancel] using h.symm
    _ = _ := by
      have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (fun z => q u*q (u-a⁻¹ • z)*k z) a (hR := ha.le)
      simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, smul_eq_mul] using h

theorem compactKernelBackground_transformed_integrable (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k) (a : ℝ) :
    Integrable (fun p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => q p.1*q (p.1-a⁻¹ • p.2)*k p.2)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
  obtain ⟨B,hB⟩ := hq.bounded_above_of_compact_support hqs
  have hqi : Integrable q := hq.integrable_of_hasCompactSupport hqs
  apply ((hqi.norm.mul_prod hk.norm).mul_const B).mono' ?_ ?_
  · have hprod : AEStronglyMeasurable (fun p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => k p.2)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := hk.aestronglyMeasurable.comp_snd
    have hc : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        q p.1*q (p.1-a⁻¹ • p.2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hprod
  · filter_upwards [] with p
    change ‖q p.1*q (p.1-a⁻¹ • p.2)*k p.2‖ ≤ (‖q p.1‖*‖k p.2‖)*B
    simp only [norm_mul]
    calc
      _ = (‖q p.1‖*‖k p.2‖)*‖q (p.1-a⁻¹ • p.2)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem compactKernelBackground_eq_correlation (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    {a : ℝ} (ha : 0 < a) :
    compactKernelBackground q k a = (a ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹ *
      ∫ z, k z*compactCutoffCorrelation q (a⁻¹ • z) := by
  unfold compactKernelBackground
  simp_rw [compactKernelBackground_row q k ha]
  rw [integral_const_mul,
    integral_integral_swap (compactKernelBackground_transformed_integrable q hq hqs hk a)]
  simp_rw [integral_mul_const]
  simp only [compactCutoffCorrelation, mul_comm]

theorem compactKernelBackground_scaled_eq_correlation (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    {a : ℝ} (ha : 0 < a) :
    a ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) * compactKernelBackground q k a =
      ∫ z, k z*compactCutoffCorrelation q (a⁻¹ • z) := by
  rw [compactKernelBackground_eq_correlation q hq hqs hk ha,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem compactKernelBackground_scaled_tendsto (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) * compactKernelBackground q k (a n))
      atTop (𝓝 (compactCutoffSquareMass q * ∫ z, k z)) := by
  simp_rw [compactKernelBackground_scaled_eq_correlation q hq hqs hk (ha0 _)]
  exact compactCutoffCorrelation_kernel_dilation_tendsto q hq hqs hk ha

theorem schwartzRealPart_integrable (f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ)) : Integrable (fun z => (f z).re) := by
  have h := (f.integrable (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))).re
  change Integrable (fun z => (f z).re) at h
  exact h

theorem schwartzFourier_zero_re_eq_integral (f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ)) :
    ((𝓕 f) 0).re = ∫ z, (f z).re := by
  have hF0 : (𝓕 f) 0 = ∫ z, f z := by
    change (𝓕 (f : (EuclideanSpace ℝ (Fin d)) → ℂ)) 0 = ∫ z, f z
    simp [Real.fourier_eq, inner_zero_right]
  have hRe := integral_re (f.integrable (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))))
  change (∫ z, (f z).re) = (∫ z, f z).re at hRe
  rw [hF0, hRe]

theorem compactSchwartzBackground_integrable (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ)) (a : ℝ) :
    Integrable (fun p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => q p.1*q p.2*(f (a • (p.1-p.2))).re)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
  have hqi : Integrable q := hq.integrable_of_hasCompactSupport hqs
  apply ((hqi.norm.mul_prod hqi.norm).mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (by fun_prop) ?_
  filter_upwards [] with p
  change ‖q p.1*q p.2*(f (a • (p.1-p.2))).re‖ ≤
    (‖q p.1‖*‖q p.2‖)*SchwartzMap.seminorm ℝ 0 0 f
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hr : ‖(f (a • (p.1-p.2))).re‖ ≤ ‖f (a • (p.1-p.2))‖ := by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (f (a • (p.1-p.2)))
  exact hr.trans (SchwartzMap.norm_le_seminorm ℝ f _)

theorem compactSchwartzBackground_scaled_tendsto (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) *
      compactKernelBackground q (fun z => (f z).re) (a n)) atTop
      (𝓝 (compactCutoffSquareMass q * ((𝓕 f) 0).re)) := by
  rw [schwartzFourier_zero_re_eq_integral]
  exact compactKernelBackground_scaled_tendsto q hq hqs (schwartzRealPart_integrable f) ha ha0

theorem compactSchwartzBackground_normalized_tendsto (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (hQ : 0 < compactCutoffSquareMass q) (f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) *
      compactKernelBackground q (fun z => (f z).re) (a n)/compactCutoffSquareMass q) atTop
      (𝓝 (((𝓕 f) 0).re)) := by
  have h := (compactSchwartzBackground_scaled_tendsto q hq hqs f ha ha0).div_const
    (compactCutoffSquareMass q)
  simpa only [mul_div_cancel_left₀ _ hQ.ne'] using h

end SphericalRiesz
