import E8Leech.StationarySpectralLP

/-!
# Genuine full-second-endpoint diagonal subtraction and sharp off-diagonal LP

Remove the value at zero from the difference kernel. Its absolute unit mass is
dominated by the original kernel's. The real box limit and the already checked
finite-window diagonal identity have unique limits, yielding the full-space
diagonal identity without another infinite inner-integral decomposition.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology FourierTransform

def differenceOffDiagonal {d : ℕ} (h : Ambient d → ℝ) (v : Ambient d) : ℝ :=
  if v = 0 then 0 else h v

theorem measurable_differenceOffDiagonal {d : ℕ}
    (h : Ambient d → ℝ) (hh : Measurable h) : Measurable (differenceOffDiagonal h) := by
  exact Measurable.ite (measurableSet_singleton (0 : Ambient d)) measurable_const hh

theorem abs_differenceOffDiagonal_le {d : ℕ} (h : Ambient d → ℝ) (v : Ambient d) :
    |differenceOffDiagonal h v| ≤ |h v| := by
  unfold differenceOffDiagonal
  split_ifs <;> simp

theorem differenceOffDiagonal_sub {d : ℕ} (h : Ambient d → ℝ) (x y : Ambient d) :
    differenceOffDiagonal h (x - y) = if y = x then 0 else h (x - y) := by
  simp only [differenceOffDiagonal, sub_eq_zero, eq_comm]

theorem expected_abs_differenceOffDiagonal_unit_ne_top {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (h : Ambient d → ℝ)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal
      |differenceOffDiagonal h (x - y)|) c (unitWindow d) univ ∂μ) ≠ ∞ := by
  exact ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_mono c (unitWindow d) univ
    (fun x _ y _ => ENNReal.ofReal_le_ofReal (abs_differenceOffDiagonal_le h (x - y)))).trans_lt
      hunit.lt_top)

theorem tendsto_normalized_expected_real_offDiagonal_box_of_abs_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (h : Ambient d → ℝ) (hh : Measurable h)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    Tendsto (fun n : ℕ => (∫ c, realLocalizedPairIntegral
      (fun x y => if y = x then 0 else h (x - y)) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop
      (𝓝 (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0 else h (x - y)) c
        (unitWindow d) univ ∂μ)) := by
  simpa only [differenceOffDiagonal_sub] using
    tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ
      (differenceOffDiagonal h) (measurable_differenceOffDiagonal h hh)
      (expected_abs_differenceOffDiagonal_unit_ne_top μ h hunit)

theorem integral_spectral_pair_anchor_diagonal_split_of_abs_unit
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hunit : (∫⁻ c, localizedPairIntegral
      (fun x y => ENNReal.ofReal |realSpectralKernel ν g (x - y)|) c
        (unitWindow d) univ ∂μ) ≠ ∞) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
      (unitWindow d) univ ∂μ) =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) univ ∂μ) +
      (∫ ξ, g ξ ∂ν) * ρ.toReal := by
  have hm := (continuous_realSpectralKernel ν g hg).measurable
  have hfull := tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) hm hunit
  have hoff := (tendsto_normalized_expected_real_offDiagonal_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) hm hunit).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (∫ ξ, g ξ ∂ν) * ρ.toReal)
      atTop (𝓝 ((∫ ξ, g ξ ∂ν) * ρ.toReal)))
  have he (n : ℕ) :
      (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
        (volume (periodCell d ((n : ℝ) + 1))).toReal =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
        (volume (periodCell d ((n : ℝ) + 1))).toReal + (∫ ξ, g ξ ∂ν) * ρ.toReal := by
    have hden : (volume (periodCell d ((n : ℝ) + 1))).toReal ≠ 0 := by
      rw [volume_periodCell, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (show 0 ≤ (n : ℝ) + 1 by positivity)]
      positivity
    rw [integral_spectral_window_diagonal_split hs μ hμ ρ hρ hρtop henergy ν g hg
      (measurable_periodCell d ((n : ℝ) + 1)) (isBounded_periodCell d ((n : ℝ) + 1)),
      add_div, mul_div_assoc, div_self hden, mul_one]
  have hsame := hfull
  simp only [he] at hsame
  exact tendsto_nhds_unique hsame hoff

theorem stationary_spectral_offDiagonal_anchor_lower_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g)) :
    ρ.toReal ^ 2 * (∫ v, realSpectralKernel ν g v) -
      realSpectralKernel ν g 0 * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) univ ∂μ := by
  have hp := stationary_spectral_pair_anchor_lower_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    ν g hg hgnonneg hdecay
  have hunit := expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (realSpectralKernel ν g) (continuous_realSpectralKernel ν g hg).measurable hdecay
  rw [integral_spectral_pair_anchor_diagonal_split_of_abs_unit hs μ hμ ρ hρ hρtop henergy
    ν g hg hunit] at hp
  rw [realSpectralKernel_zero]
  linarith

theorem stationary_spectral_offDiagonal_zero_frequency_lower_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g)) :
    ρ.toReal ^ 2 * (𝓕 (fun v => (realSpectralKernel ν g v : ℂ)) (0 : Ambient d)).re -
      realSpectralKernel ν g 0 * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) univ ∂μ := by
  rw [fourier_real_kernel_zero_re]
  exact stationary_spectral_offDiagonal_anchor_lower_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    ν g hg hgnonneg hdecay

end E8Leech
