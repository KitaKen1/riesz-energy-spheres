import E8Leech.RapidDecayPairIntegrals
import Mathlib.Analysis.Complex.Exponential

/-!
# A concrete Gaussian kernel and certified point-pair integrability

An exponential-series term gives a factorial bound. This avoids optimizing a
radial function or importing smooth Schwartz-space infrastructure. It covers
each fixed positive Gaussian scale, not arbitrary mixtures over scales.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def gaussianKernel {d : ℕ} (α : ℝ) (x : Ambient d) : ℝ :=
  Real.exp (-α * ‖x‖ ^ 2)

theorem gaussianKernel_pos {d : ℕ} (α : ℝ) (x : Ambient d) :
    0 < gaussianKernel α x := Real.exp_pos _

theorem gaussianKernel_le_one {d : ℕ} {α : ℝ} (hα : 0 ≤ α) (x : Ambient d) :
    gaussianKernel α x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (sq_nonneg _)

theorem continuous_gaussianKernel {d : ℕ} (α : ℝ) :
    Continuous (@gaussianKernel d α) := by
  unfold gaussianKernel
  fun_prop

/-- A known exponential-series coefficient replaces a maximum calculation. -/
theorem pow_mul_exp_neg_le_factorial_div {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (n : ℕ) :
    t ^ n * Real.exp (-α * t) ≤ (n.factorial : ℝ) / α ^ n := by
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (α * t) (mul_nonneg hα.le ht) n)
  rw [mul_pow] at hs
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-α * t)).le
  have he : Real.exp (α * t) * Real.exp (-α * t) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  have hb : α ^ n * (t ^ n * Real.exp (-α * t)) ≤ (n.factorial : ℝ) := by
    calc
      _ = (α ^ n * t ^ n) * Real.exp (-α * t) := by ring
      _ ≤ (Real.exp (α * t) * (n.factorial : ℝ)) * Real.exp (-α * t) := hm
      _ = (Real.exp (α * t) * Real.exp (-α * t)) * (n.factorial : ℝ) := by ring
      _ = _ := by rw [he, one_mul]
  exact (le_div_iff₀ (pow_pos hα n)).mpr (by simpa only [mul_comm] using hb)

theorem weighted_gaussianKernel_bound {d : ℕ} {α : ℝ} (hα : 0 < α)
    (n : ℕ) (x : Ambient d) :
    ‖x‖ ^ n * |gaussianKernel α x| ≤ 1 + (n.factorial : ℝ) / α ^ n := by
  have heven : (‖x‖ ^ 2) ^ n = (‖x‖ ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  have hpower : ‖x‖ ^ n ≤ 1 + (‖x‖ ^ 2) ^ n := by
    rw [heven]
    nlinarith [sq_nonneg (‖x‖ ^ n - 1), pow_nonneg (norm_nonneg x) n]
  calc
    _ = ‖x‖ ^ n * Real.exp (-α * ‖x‖ ^ 2) := by
      rw [abs_of_pos (gaussianKernel_pos α x)]
      rfl
    _ ≤ (1 + (‖x‖ ^ 2) ^ n) * Real.exp (-α * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ = Real.exp (-α * ‖x‖ ^ 2) + (‖x‖ ^ 2) ^ n * Real.exp (-α * ‖x‖ ^ 2) := by ring
    _ ≤ 1 + (n.factorial : ℝ) / α ^ n := add_le_add (gaussianKernel_le_one hα.le x)
      (pow_mul_exp_neg_le_factorial_div hα (sq_nonneg _) n)

theorem hasRapidDecay_gaussianKernel {d : ℕ} {α : ℝ} (hα : 0 < α) :
    HasRapidDecay (@gaussianKernel d α) := by
  intro n
  exact ⟨1 + (n.factorial : ℝ) / α ^ n, by positivity, weighted_gaussianKernel_bound hα n⟩

theorem expected_abs_gaussian_pair_univ_ne_top_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {α : ℝ} (hα : 0 < α) (a : Ambient d) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |gaussianKernel α (x - y)|) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ) ≠ ∞ :=
  expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (gaussianKernel α) (continuous_gaussianKernel α).measurable (hasRapidDecay_gaussianKernel hα) a

theorem integrable_signed_gaussian_pair_univ_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {α : ℝ} (hα : 0 < α) (a : Ambient d) :
    Integrable (fun c => signedLocalizedPairIntegral (fun x y => gaussianKernel α (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ) μ :=
  integrable_signed_difference_pair_univ_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (gaussianKernel α) (continuous_gaussianKernel α).measurable (hasRapidDecay_gaussianKernel hα) a

theorem exists_uniform_abs_gaussian_pair_tail_cutoff
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞)
    {α : ℝ} (hα : 0 < α) (a : Ambient d) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F₀ : Finset (IntegerCellIndex d),
      ∀ F : Finset (IntegerCellIndex d), F₀ ⊆ F →
      ∀ μ : Measure (Configuration (Ambient d)), IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |gaussianKernel α (x - y)|) c
        ((fun x => a + x) ⁻¹' unitWindow d) (integerCellTail F) ∂μ) < ε :=
  exists_uniform_abs_difference_pair_tail_cutoff_of_rapidDecay hs L Δ hLtop hΔtop
    (gaussianKernel α) (continuous_gaussianKernel α).measurable (hasRapidDecay_gaussianKernel hα)
    a ε hε

end E8Leech
