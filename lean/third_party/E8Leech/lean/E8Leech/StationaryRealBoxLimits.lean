import E8Leech.StationaryBoxPairLimits

/-!
# Original-law real two-window box expectations tend to the full unit anchor

Apply the nonnegative box limit to the two Jordan parts after verifying their
finiteness. Existing Bochner identification connects their difference with the
actual real pair integrals. Rapid decay discharges absolute unit convergence
from the original energy; no convergence assumption is added to the law.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

theorem tendsto_normalized_expected_real_difference_pair_box_of_abs_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (h : Ambient d → ℝ) (hh : Measurable h)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    Tendsto (fun n : ℕ => (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop
      (𝓝 (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (unitWindow d) univ ∂μ)) := by
  have hH : Measurable (Function.uncurry (fun x y => h (x - y))) :=
    hh.comp (measurable_fst.sub measurable_snd)
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ
    (fun x y => h (x - y)) (unitWindow d) univ hunit
  have ht := (tendsto_normalized_expected_difference_pair_box μ hμ
    (fun v => ENNReal.ofReal (h v)) hh.ennreal_ofReal hp).sub
    (tendsto_normalized_expected_difference_pair_box μ hμ
      (fun v => ENNReal.ofReal (-h v)) hh.neg.ennreal_ofReal hn)
  have he (n : ℕ) :
      (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
        (volume (periodCell d ((n : ℝ) + 1))).toReal =
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (h (x - y))) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ).toReal /
        (volume (periodCell d ((n : ℝ) + 1))).toReal -
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-h (x - y))) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ).toReal /
        (volume (periodCell d ((n : ℝ) + 1))).toReal := by
    have hf := expected_difference_pair_bounded_ne_top_of_unit μ hμ _ hh.norm.ennreal_ofReal
      hunit (measurable_periodCell d ((n : ℝ) + 1)) (isBounded_periodCell d ((n : ℝ) + 1))
    rw [integral_real_pair_eq_pos_sub_neg_of_expected_abs μ _ hH
      (measurable_periodCell d ((n : ℝ) + 1)) (isBounded_periodCell d ((n : ℝ) + 1))
      (measurable_periodCell d ((n : ℝ) + 1))
      (expected_pair_right_ne_top_of_full μ _ _ (periodCell d ((n : ℝ) + 1)) hf), sub_div]
  rw [integral_real_pair_eq_pos_sub_neg_of_expected_abs μ _ hH (measurable_unitWindow d)
    (isBounded_unitWindow d) MeasurableSet.univ hunit]
  simpa only [he] using ht

theorem tendsto_normalized_expected_real_difference_pair_box_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) :
    Tendsto (fun n : ℕ => (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop
      (𝓝 (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c (unitWindow d) univ ∂μ)) := by
  exact tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ h hh
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay)

end E8Leech
