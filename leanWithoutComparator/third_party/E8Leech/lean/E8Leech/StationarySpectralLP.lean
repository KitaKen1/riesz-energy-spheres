import E8Leech.StationaryRealBoxLimits

/-!
# Sharp stationary full-pair spectral LP from the two box limits

The normalized finite-window mean-square LP passes to the ORIGINAL law's unit
anchor and the actual volume integral of the real inverse spectral kernel.
The zero-frequency constant below is the actual Fourier transform of that real
kernel, not the point value of an arbitrary L1 spectral-density representative.
Actual CKMRV kernel construction and nondegenerate slack remain separate inputs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology FourierTransform RealInnerProductSpace

theorem fourier_real_kernel_zero_re {d : ℕ} (h : Ambient d → ℝ) :
    (𝓕 (fun x => (h x : ℂ)) (0 : Ambient d)).re = ∫ x, h x := by
  rw [Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul]
  rw [integral_complex_ofReal]
  simp

theorem stationary_spectral_pair_anchor_lower_of_abs_unit
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hvolume : Integrable (realSpectralKernel ν g) volume)
    (hunit : (∫⁻ c, localizedPairIntegral
      (fun x y => ENNReal.ofReal |realSpectralKernel ν g (x - y)|) c
        (unitWindow d) univ ∂μ) ≠ ∞) :
    ρ.toReal ^ 2 * (∫ v, realSpectralKernel ν g v) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (unitWindow d) univ ∂μ := by
  have href := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ.toReal ^ 2)
      atTop (𝓝 (ρ.toReal ^ 2))).mul
    (tendsto_normalized_box_pair_integral (realSpectralKernel ν g) hvolume)
  have hpair := tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) (continuous_realSpectralKernel ν g hg).measurable hunit
  apply le_of_tendsto_of_tendsto' href hpair
  intro n
  have hv : 0 < (volume (periodCell d ((n : ℝ) + 1))).toReal := by
    rw [volume_periodCell, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show 0 ≤ (n : ℝ) + 1 by positivity)]
    positivity
  have h := integral_spectral_pair_window_lower_real_volume hs μ hμ ρ hρ hρtop henergy
    ν g hg hgnonneg (measurable_periodCell d ((n : ℝ) + 1))
      (isBounded_periodCell d ((n : ℝ) + 1))
  have hd := div_le_div_of_nonneg_right
    (c := (volume (periodCell d ((n : ℝ) + 1))).toReal) h hv.le
  simpa only [mul_div_assoc] using hd

theorem stationary_spectral_pair_anchor_lower_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g)) :
    ρ.toReal ^ 2 * (∫ v, realSpectralKernel ν g v) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (unitWindow d) univ ∂μ := by
  have hm := (continuous_realSpectralKernel ν g hg).measurable
  exact stationary_spectral_pair_anchor_lower_of_abs_unit hs μ hμ ρ hρ hρtop henergy ν g hg
    hgnonneg (integrable_of_hasRapidDecay _ hm hdecay)
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      _ hm hdecay)

theorem stationary_spectral_pair_anchor_zero_frequency_lower_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g)) :
    ρ.toReal ^ 2 * (𝓕 (fun v => (realSpectralKernel ν g v : ℂ)) (0 : Ambient d)).re ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (unitWindow d) univ ∂μ := by
  rw [fourier_real_kernel_zero_re]
  exact stationary_spectral_pair_anchor_lower_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    ν g hg hgnonneg hdecay

end E8Leech
