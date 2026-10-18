import E8Leech.SpectralWindowMoments
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-window spectral LP with an explicit intensity-square contribution

Product integrability is derived from |g| times the energy-derived square
count moment. Thus expectation and frequency integration genuinely commute.
The exact mean character sum gives the intensity-square window-transform term.
The expanding-window approximate-identity and boundary limits remain separate.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem spectralPhase_comm {d : ℕ} (ξ x : Ambient d) :
    spectralPhase ξ x = spectralPhase x ξ := by
  simp only [spectralPhase, real_inner_comm]

theorem spectral_window_integral_eq_inverseKernel {d : ℕ} (W : Set (Ambient d))
    (ξ : Ambient d) : (∫ x, W.indicator (spectralPhase ξ) x) =
      inverseSpectralKernel volume (W.indicator (fun _ => 1)) ξ := by
  unfold inverseSpectralKernel
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ W <;> simp [hx, spectralPhase_comm]

theorem continuous_spectral_window_integral {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Continuous (fun ξ => ∫ x, W.indicator (spectralPhase ξ) x) := by
  have hI : Integrable (W.indicator (fun _ : Ambient d => (1 : ℝ))) volume :=
    integrable_real_window_indicator_of_bound _ measurable_const hW hbW 1 (by simp)
  have he : (fun ξ => ∫ x, W.indicator (spectralPhase ξ) x) =
      inverseSpectralKernel volume (W.indicator (fun _ => 1)) :=
    funext (spectral_window_integral_eq_inverseKernel W)
  rw [he]
  exact continuous_inverseSpectralKernel volume _ hI

theorem spectral_window_integral_norm_le_volume {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (ξ : Ambient d) :
    ‖∫ x, W.indicator (spectralPhase ξ) x‖ ≤ (volume W).toReal := by
  calc
    _ ≤ ∫ x, ‖W.indicator (spectralPhase ξ) x‖ := norm_integral_le_integral_norm _
    _ = ∫ x, W.indicator (fun _ : Ambient d => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ W <;> simp [hx]
    _ = _ := by simp only [integral_indicator_const (1 : ℝ) hW, smul_eq_mul, mul_one, Measure.real]

theorem integrable_spectral_window_mean_density {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (ρ : ℝ≥0∞) {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun ξ => g ξ * (ρ.toReal ^ 2 *
      Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x))) ν := by
  have hmeas : AEStronglyMeasurable (fun ξ => g ξ * (ρ.toReal ^ 2 *
      Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x))) ν :=
    hg.aestronglyMeasurable.mul (continuous_const.mul
      (Complex.continuous_normSq.comp (continuous_spectral_window_integral hW hbW))).aestronglyMeasurable
  apply (hg.norm.mul_const (ρ.toReal ^ 2 * (volume W).toReal ^ 2)).mono' hmeas
  filter_upwards with ξ
  change ‖g ξ * (ρ.toReal ^ 2 * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x))‖ ≤
    ‖g ξ‖ * (ρ.toReal ^ 2 * (volume W).toReal ^ 2)
  have hs : Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ≤ (volume W).toReal ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (spectral_window_integral_norm_le_volume hW ξ) 2
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ.toReal),
    abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) (abs_nonneg _)

theorem integrable_spectral_window_product_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun p : Ambient d × Configuration (Ambient d) =>
      g p.1 * Complex.normSq (spectralWindowSum W hbW p.1 p.2)) (ν.prod μ) := by
  have hc := integrable_square_of_memLp_two
    (memLp_bounded_window_count_two hs μ hμ ρ hρ hρtop henergy hW hbW)
  have hm : Measurable (fun p : Ambient d × Configuration (Ambient d) =>
      Complex.normSq (spectralWindowSum W hbW p.1 p.2)) :=
    Complex.continuous_normSq.measurable.comp (measurable_spectralWindowSum_joint hW hbW)
  apply (hg.norm.mul_prod hc).mono' (hg.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable)
  filter_upwards with p
  change ‖g p.1 * Complex.normSq (spectralWindowSum W hbW p.1 p.2)‖ ≤
    ‖g p.1‖ * (p.2.count W).toReal ^ 2
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (spectralWindowSum_normSq_le_count_sq W hbW p.1 p.2) (abs_nonneg _)

theorem integrable_expected_spectral_square_density_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun ξ => g ξ * ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ) ν := by
  have hi := (integrable_spectral_window_product_of_riesz hs μ hμ ρ hρ hρtop
    henergy ν g hg hW hbW).integral_prod_left
  simpa only [integral_const_mul] using hi

theorem integral_spectral_pair_eq_integral_expected_square {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ) =
      ∫ ξ, g ξ * ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ ∂ν := by
  have hprod := integrable_spectral_window_product_of_riesz hs μ hμ ρ hρ hρtop
    henergy ν g hg hW hbW
  calc
    _ = ∫ c, ∫ ξ, g ξ * Complex.normSq (spectralWindowSum W hbW ξ c) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      simpa only [spectralWindowSum] using
        realLocalized_spectral_pair_eq_integral_square ν g hg c hW hbW
    _ = ∫ ξ, ∫ c, g ξ * Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ ∂ν :=
      (integral_integral_swap hprod).symm
    _ = _ := by simp only [integral_const_mul]

theorem integral_spectral_pair_window_lower {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ ξ, g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ := by
  rw [integral_spectral_pair_eq_integral_expected_square hs μ hμ ρ hρ hρtop henergy ν g hg hW hbW]
  have hleft : (ρ.toReal ^ 2 * ∫ ξ,
      g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) =
      ∫ ξ, g ξ * (ρ.toReal ^ 2 * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x)) ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    ring
  rw [hleft]
  apply integral_mono_ae (integrable_spectral_window_mean_density ν g hg ρ hW hbW)
    (integrable_expected_spectral_square_density_of_riesz hs μ hμ ρ hρ hρtop henergy ν g hg hW hbW)
  filter_upwards [hgnonneg] with ξ hξ
  exact mul_le_mul_of_nonneg_left
    (spectralWindowSum_mean_square_lower hs μ hμ ρ hρ hρtop henergy hW hbW ξ) hξ

theorem integrable_real_pair_window_diagonal_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (hρtop : ρ ≠ ∞) (a : ℝ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => if y = x then a else 0) c W W) μ := by
  apply (integrable_realWindowIntegral_of_intensity μ ρ hρ hρtop
    (fun _ => a) measurable_const hW hbW |a| (by simp)).congr
  filter_upwards with c
  rw [realLocalizedPairIntegral_diagonal _ c hW hbW, realWindowIntegral_eq_sum _ c hW hbW]

theorem integral_real_pair_window_diagonal_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (hρtop : ρ ≠ ∞) (a : ℝ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => if y = x then a else 0) c W W ∂μ) =
      a * ρ.toReal * (volume W).toReal := by
  calc
    _ = ∫ c, realWindowIntegral (fun _ => a) c W ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      rw [realLocalizedPairIntegral_diagonal _ c hW hbW, realWindowIntegral_eq_sum _ c hW hbW]
    _ = _ := by
      rw [integral_realWindowIntegral_of_intensity μ ρ hρ hρtop _ measurable_const
        hW hbW |a| (by simp), integral_indicator_const a hW]
      simp only [Measure.real, smul_eq_mul]
      ring

theorem integrable_spectral_window_offDiagonal_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun c => realLocalizedPairIntegral
      (fun x y => if y = x then 0 else realSpectralKernel ν g (x - y)) c W W) μ := by
  have hfull := integrable_realLocalized_spectral_pair_of_riesz hs μ hμ ρ hρ hρtop henergy ν g hg hW hbW
  have hdiag := integrable_real_pair_window_diagonal_of_intensity μ ρ hρ hρtop (∫ ξ, g ξ ∂ν) hW hbW
  apply (hfull.sub hdiag).congr
  filter_upwards with c
  simp only [Pi.sub_apply]
  rw [realLocalizedPairIntegral_difference_split _ c hW hbW, realSpectralKernel_zero,
    realLocalizedPairIntegral_const_diagonal _ c hW hbW]
  simp

theorem integral_spectral_window_diagonal_split {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ) =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W ∂μ) +
      (∫ ξ, g ξ ∂ν) * ρ.toReal * (volume W).toReal := by
  have hoff := integrable_spectral_window_offDiagonal_of_riesz hs μ hμ ρ hρ hρtop henergy ν g hg hW hbW
  have hdiag := integrable_real_pair_window_diagonal_of_intensity μ ρ hρ hρtop (∫ ξ, g ξ ∂ν) hW hbW
  calc
    _ = ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W +
        realLocalizedPairIntegral (fun x y => if y = x then (∫ ξ, g ξ ∂ν) else 0) c W W ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      rw [realLocalizedPairIntegral_difference_split _ c hW hbW, realSpectralKernel_zero,
        realLocalizedPairIntegral_const_diagonal _ c hW hbW]
    _ = _ := by rw [integral_add hoff hdiag,
      integral_real_pair_window_diagonal_of_intensity μ ρ hρ hρtop _ hW hbW]

theorem integral_spectral_window_offDiagonal_lower {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ ξ, g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) -
      (∫ ξ, g ξ ∂ν) * ρ.toReal * (volume W).toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W ∂μ := by
  have hp := integral_spectral_pair_window_lower hs μ hμ ρ hρ hρtop henergy ν g hg hgnonneg hW hbW
  rw [integral_spectral_window_diagonal_split hs μ hμ ρ hρ hρtop henergy ν g hg hW hbW] at hp
  linarith

end E8Leech
