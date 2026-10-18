import E8Leech.CountingKernel

/-!
# First-moment integration from intensity alone

The mean counting measure is the bind of the law and the counting kernel. Equality of
expected Borel counts identifies it with intensity times volume. Its nonnegative integration
formula needs neither Poisson independence, Palm distributions, nor ergodicity.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

def meanCountingMeasure {d : ℕ} (μ : Measure (Configuration (Ambient d))) : Measure (Ambient d) :=
  μ.bind (countingKernel d)

theorem meanCountingMeasure_eq_volume {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) :
    meanCountingMeasure μ = ρ • volume := by
  ext W hW
  rw [meanCountingMeasure, Measure.bind_apply hW (countingKernel d).measurable.aemeasurable]
  simp_rw [countingKernel_apply _ hW]
  simpa only [Measure.smul_apply, smul_eq_mul] using hρ W hW

theorem expected_counting_integral {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    {f : Ambient d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ c, ∫⁻ x, f x ∂countingKernel d c ∂μ) = ρ * ∫⁻ x, f x := by
  rw [← Measure.lintegral_bind (countingKernel d).measurable.aemeasurable hf.aemeasurable]
  change (∫⁻ x, f x ∂meanCountingMeasure μ) = _
  rw [meanCountingMeasure_eq_volume μ ρ hρ, lintegral_smul_measure, smul_eq_mul]

end E8Leech
