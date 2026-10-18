import E8Leech.SpectralWindowLP

/-!
# Replace the window spectral square by a deterministic real-space pair integral

Unit-modulus characters and a finite spatial measure make the spectral/product
integrand dominated by |g|. Genuine Fubini then identifies its pair integral with
the mean character square. Bounded volume windows give a real-space version of
the previously checked finite-window LP. No large-window limit is asserted here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ComplexConjugate
open scoped ENNReal Classical

attribute [local irreducible] spectralPhase

theorem inverseSpectralKernel_norm_le {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (x : Ambient d) :
    ‖inverseSpectralKernel ν g x‖ ≤ ∫ ξ, ‖g ξ‖ ∂ν := by
  unfold inverseSpectralKernel
  calc
    _ ≤ ∫ ξ, ‖(g ξ : ℂ) * spectralPhase ξ x‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_real, spectralPhase_norm, mul_one]

theorem integrable_spectralPhase_finite_measure {d : ℕ}
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] (ξ : Ambient d) :
    Integrable (spectralPhase ξ) σ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_spectralPhase_point ξ).aestronglyMeasurable
  filter_upwards with x
  simp

theorem integrable_spectral_difference_product {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] :
    Integrable (fun p : Ambient d × (Ambient d × Ambient d) =>
      (g p.1 : ℂ) * spectralPhase p.1 (p.2.1 - p.2.2)) (ν.prod (σ.prod σ)) := by
  have hp : Continuous (fun p : Ambient d × (Ambient d × Ambient d) =>
      spectralPhase p.1 (p.2.1 - p.2.2)) :=
    continuous_spectralPhase_joint.comp (continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))
  apply (hg.norm.mul_prod (integrable_const (1 : ℝ))).mono'
    (hg.ofReal.aestronglyMeasurable.comp_fst.mul hp.aestronglyMeasurable)
  filter_upwards with p
  change ‖(g p.1 : ℂ) * spectralPhase p.1 (p.2.1 - p.2.2)‖ ≤ ‖g p.1‖ * 1
  simp only [norm_mul, Complex.norm_real, spectralPhase_norm, mul_one, le_refl]

theorem integrable_inverseSpectralKernel_pair_finite_measure {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] :
    Integrable (fun p : Ambient d × Ambient d => inverseSpectralKernel ν g (p.1 - p.2))
      (σ.prod σ) := by
  simpa only [inverseSpectralKernel] using
    (integrable_spectral_difference_product ν g hg σ).integral_prod_right

theorem integral_pair_spectralPhase_eq_normSq {d : ℕ}
    (σ : Measure (Ambient d)) [SFinite σ] (ξ : Ambient d) :
    (∫ p : Ambient d × Ambient d, spectralPhase ξ (p.1 - p.2) ∂σ.prod σ) =
      (Complex.normSq (∫ x, spectralPhase ξ x ∂σ) : ℂ) := by
  calc
    _ = ∫ p : Ambient d × Ambient d,
        spectralPhase ξ p.1 * conj (spectralPhase ξ p.2) ∂σ.prod σ := by
      apply integral_congr_ae
      filter_upwards with p
      exact spectralPhase_sub ξ p.1 p.2
    _ = (∫ x, spectralPhase ξ x ∂σ) * (∫ y, conj (spectralPhase ξ y) ∂σ) :=
      integral_prod_mul (spectralPhase ξ) (fun y => conj (spectralPhase ξ y))
    _ = _ := by rw [integral_conj, Complex.mul_conj]

theorem integral_inverseSpectralKernel_pair_eq_spectral_square {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] :
    (∫ x, ∫ y, inverseSpectralKernel ν g (x - y) ∂σ ∂σ) =
      (∫ ξ, g ξ * Complex.normSq (∫ x, spectralPhase ξ x ∂σ) ∂ν : ℝ) := by
  have hp := integrable_spectral_difference_product ν g hg σ
  calc
    _ = ∫ p : Ambient d × Ambient d, inverseSpectralKernel ν g (p.1 - p.2) ∂σ.prod σ :=
      integral_integral (integrable_inverseSpectralKernel_pair_finite_measure ν g hg σ)
    _ = ∫ ξ, ∫ p : Ambient d × Ambient d,
        (g ξ : ℂ) * spectralPhase ξ (p.1 - p.2) ∂σ.prod σ ∂ν := by
      unfold inverseSpectralKernel
      exact (integral_integral_swap hp).symm
    _ = ∫ ξ, (g ξ : ℂ) * (Complex.normSq (∫ x, spectralPhase ξ x ∂σ) : ℂ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [integral_const_mul, integral_pair_spectralPhase_eq_normSq σ ξ]
    _ = _ := by simp only [← Complex.ofReal_mul, integral_complex_ofReal]

theorem integral_realSpectralKernel_pair_eq_spectral_square {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] :
    (∫ x, ∫ y, realSpectralKernel ν g (x - y) ∂σ ∂σ) =
      ∫ ξ, g ξ * Complex.normSq (∫ x, spectralPhase ξ x ∂σ) ∂ν := by
  have hp := integrable_inverseSpectralKernel_pair_finite_measure ν g hg σ
  have hr : Integrable (fun p : Ambient d × Ambient d =>
      realSpectralKernel ν g (p.1 - p.2)) (σ.prod σ) := hp.re
  calc
    _ = ∫ p : Ambient d × Ambient d, realSpectralKernel ν g (p.1 - p.2) ∂σ.prod σ :=
      integral_integral hr
    _ = (∫ p : Ambient d × Ambient d, inverseSpectralKernel ν g (p.1 - p.2) ∂σ.prod σ).re := by
      exact integral_re hp
    _ = (∫ x, ∫ y, inverseSpectralKernel ν g (x - y) ∂σ ∂σ).re :=
      congrArg Complex.re (integral_integral
        (f := fun x y => inverseSpectralKernel ν g (x - y)) hp).symm
    _ = _ := by rw [integral_inverseSpectralKernel_pair_eq_spectral_square ν g hg σ]; rfl

theorem spectral_window_square_eq_real_volume_pair {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ ξ, g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) =
      ∫ x in W, ∫ y in W, realSpectralKernel ν g (x - y) := by
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hbW.measure_lt_top⟩
  simpa only [integral_indicator hW] using
    (integral_realSpectralKernel_pair_eq_spectral_square ν g hg (volume.restrict W)).symm

theorem integral_spectral_pair_window_lower_real_volume {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ x in W, ∫ y in W, realSpectralKernel ν g (x - y)) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ := by
  rw [← spectral_window_square_eq_real_volume_pair ν g hg hW hbW]
  exact integral_spectral_pair_window_lower hs μ hμ ρ hρ hρtop henergy ν g hg hgnonneg hW hbW

theorem integrable_realSpectralKernel_pair_finite_measure {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (σ : Measure (Ambient d)) [IsFiniteMeasure σ] :
    Integrable (fun p : Ambient d × Ambient d => realSpectralKernel ν g (p.1 - p.2))
      (σ.prod σ) :=
  (integrable_inverseSpectralKernel_pair_finite_measure ν g hg σ).re

theorem real_volume_spectral_pair_nonneg {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    0 ≤ ∫ x in W, ∫ y in W, realSpectralKernel ν g (x - y) := by
  rw [← spectral_window_square_eq_real_volume_pair ν g hg hW hbW]
  apply integral_nonneg_of_ae
  filter_upwards [hgnonneg] with ξ hξ
  exact mul_nonneg hξ (Complex.normSq_nonneg _)

theorem integral_spectral_window_offDiagonal_lower_real_volume {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ x in W, ∫ y in W, realSpectralKernel ν g (x - y)) -
      (∫ ξ, g ξ ∂ν) * ρ.toReal * (volume W).toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W ∂μ := by
  rw [← spectral_window_square_eq_real_volume_pair ν g hg hW hbW]
  exact integral_spectral_window_offDiagonal_lower hs μ hμ ρ hρ hρtop henergy ν g hg hgnonneg hW hbW

end E8Leech
