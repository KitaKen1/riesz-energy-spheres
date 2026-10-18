import E8Leech.StationaryPairHaar

/-!
# Actual signed pair expectations scale with the anchor-window volume

Haar uniqueness applies separately to the nonnegative Jordan parts. Absolute
unit-window convergence is checked before passing to the real expectations.
The rapid-decay corollaries use only the original stationary finite-intensity,
finite-Riesz-energy hypotheses. The second endpoint stays unrestricted here;
removing the two-window boundary error is a separate limit theorem.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem integrable_real_difference_pair_bounded_of_abs_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (h : Ambient d → ℝ) (hh : Measurable h)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => h (x - y)) c W univ) μ := by
  exact integrable_real_pair_of_expected_abs μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd)) hW hbW MeasurableSet.univ
    (expected_difference_pair_bounded_ne_top_of_unit μ hμ _ hh.norm.ennreal_ofReal
      hunit hW hbW)

theorem expected_real_difference_pair_univ_eq_volume_mul_unit_of_abs_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (h : Ambient d → ℝ) (hh : Measurable h)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c W univ ∂μ) =
      (volume W).toReal *
        ∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (unitWindow d) univ ∂μ := by
  have hH : Measurable (Function.uncurry (fun x y => h (x - y))) :=
    hh.comp (measurable_fst.sub measurable_snd)
  have hfinite := expected_difference_pair_bounded_ne_top_of_unit μ hμ _
    hh.norm.ennreal_ofReal hunit hW hbW
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ
    (fun x y => h (x - y)) (unitWindow d) univ hunit
  have hepos := expected_difference_pair_univ_eq_unit_mul_volume μ hμ
    (fun v => ENNReal.ofReal (h v)) hh.ennreal_ofReal hp hW
  have heneg := expected_difference_pair_univ_eq_unit_mul_volume μ hμ
    (fun v => ENNReal.ofReal (-h v)) hh.neg.ennreal_ofReal hn hW
  rw [integral_real_pair_eq_pos_sub_neg_of_expected_abs μ _ hH hW hbW
      MeasurableSet.univ hfinite,
    integral_real_pair_eq_pos_sub_neg_of_expected_abs μ _ hH (measurable_unitWindow d)
      (isBounded_unitWindow d) MeasurableSet.univ hunit,
    hepos, heneg, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

theorem integrable_real_difference_pair_bounded_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => h (x - y)) c W univ) μ := by
  exact integrable_real_difference_pair_bounded_of_abs_unit μ hμ h hh
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay) hW hbW

theorem expected_real_difference_pair_univ_eq_volume_mul_unit_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c W univ ∂μ) =
      (volume W).toReal *
        ∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (unitWindow d) univ ∂μ := by
  exact expected_real_difference_pair_univ_eq_volume_mul_unit_of_abs_unit μ hμ h hh
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay) hW hbW

theorem normalized_expected_real_difference_pair_box_univ_eq_unit_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    {L : ℝ} (hL : 0 < L) :
    (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (periodCell d L) univ ∂μ) /
      (volume (periodCell d L)).toReal =
        ∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (unitWindow d) univ ∂μ := by
  have hvol : (volume (periodCell d L)).toReal ≠ 0 := by
    rw [volume_periodCell, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]
    positivity
  rw [expected_real_difference_pair_univ_eq_volume_mul_unit_of_rapidDecay hs μ hμ
    ρ hρ hρtop henergy h hh hdecay (measurable_periodCell d L) (isBounded_periodCell d L)]
  exact mul_div_cancel_left₀ _ hvol

end E8Leech
