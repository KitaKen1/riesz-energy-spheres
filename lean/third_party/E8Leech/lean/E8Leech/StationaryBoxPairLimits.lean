import E8Leech.BoxPairBoundary

/-!
# The original-law nonnegative two-window box limit

Haar scaling controls the boundary layer and the relative-displacement tail.
Choose the tail radius first, then the box size. Absolute unit-anchor finiteness
is the only convergence gate; rapid value decay and original energy discharge
it in the later real-kernel specialization. No uniform-in-law convergence
premise is inserted into the stationary LP statement.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

theorem localizedPairIntegral_right_add_compl {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral V c W U + localizedPairIntegral V c W Uᶜ =
      localizedPairIntegral V c W univ := by
  simp only [localizedPairIntegral_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx, mem_univ, if_true]
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) ∈ U <;> simp [hy]
  · simp [hx]

theorem expected_localizedPairIntegral_right_add_compl {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (Function.uncurry V))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U) :
    (∫⁻ c, localizedPairIntegral V c W U ∂μ) +
      (∫⁻ c, localizedPairIntegral V c W Uᶜ ∂μ) =
        ∫⁻ c, localizedPairIntegral V c W univ ∂μ := by
  rw [← lintegral_add_left (measurable_localizedPairIntegral hV hW hU)]
  exact lintegral_congr fun c => localizedPairIntegral_right_add_compl V c W U

theorem expected_difference_pair_box_compl_le_boundary_add_tail {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) (L R : ℝ) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (periodCell d L) (periodCell d L)ᶜ ∂μ) ≤
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
        (unitWindow d) univ ∂μ) * volume (pairBoxBoundary d L R) +
      (∫⁻ c, localizedPairIntegral (fun x y => differenceTail V R (x - y)) c
        (unitWindow d) univ ∂μ) * volume (periodCell d L) := by
  have hb := measurable_localizedPairIntegral (V := fun x y => V (x - y))
    (hV.comp (measurable_fst.sub measurable_snd))
    (measurable_pairBoxBoundary d L R) MeasurableSet.univ
  calc
    _ ≤ ∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (pairBoxBoundary d L R) univ +
        localizedPairIntegral (fun x y => differenceTail V R (x - y)) c (periodCell d L) univ ∂μ :=
      lintegral_mono fun c => localized_difference_pair_box_compl_le_boundary_add_tail V c L R
    _ = _ := by
      rw [lintegral_add_left hb,
        expected_difference_pair_univ_eq_unit_mul_volume μ hμ V hV hunit
          (measurable_pairBoxBoundary d L R),
        expected_difference_pair_univ_eq_unit_mul_volume μ hμ (differenceTail V R)
          (measurable_differenceTail V hV R)
          (expected_differenceTail_ne_top_of_full μ V (unitWindow d) hunit R)
          (measurable_periodCell d L)]

theorem normalized_expected_difference_pair_box_compl_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) {L : ℝ} (hL : 0 < L) (R : ℝ) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (periodCell d L) (periodCell d L)ᶜ ∂μ).toReal / (volume (periodCell d L)).toReal ≤
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (unitWindow d) univ ∂μ).toReal *
        ((volume (pairBoxBoundary d L R)).toReal / (volume (periodCell d L)).toReal) +
      (∫⁻ c, localizedPairIntegral (fun x y => differenceTail V R (x - y)) c
        (unitWindow d) univ ∂μ).toReal := by
  have htail := expected_differenceTail_ne_top_of_full μ V (unitWindow d) hunit R
  have hb := (isBounded_pairBoxBoundary d L R).measure_lt_top (μ := volume) |>.ne
  have hw := (isBounded_periodCell d L).measure_lt_top (μ := volume) |>.ne
  have hden : (volume (periodCell d L)).toReal ≠ 0 := by
    rw [volume_periodCell, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]
    positivity
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hunit hb, ENNReal.mul_ne_top htail hw⟩)
    (expected_difference_pair_box_compl_le_boundary_add_tail μ hμ V hV hunit L R)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hunit hb) (ENNReal.mul_ne_top htail hw),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  have hd := div_le_div_of_nonneg_right (c := (volume (periodCell d L)).toReal)
    h ENNReal.toReal_nonneg
  simpa only [add_div, mul_div_assoc, div_self hden, mul_one] using hd

theorem tendsto_normalized_expected_difference_pair_box_compl_zero {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    Tendsto (fun n : ℕ => (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1))ᶜ ∂μ).toReal /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop (𝓝 0) := by
  have htail : Tendsto (fun R : ℕ => (∫⁻ c, localizedPairIntegral
      (fun x y => differenceTail V (R : ℝ) (x - y)) c (unitWindow d) univ ∂μ).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_expected_differenceTail_zero_of_full μ V hV (measurable_unitWindow d)
        (isBounded_unitWindow d) hunit)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · intro ε hε
    obtain ⟨R, hR⟩ := (htail.eventually (Iio_mem_nhds (half_pos hε))).exists
    have hb : Tendsto (fun n : ℕ =>
        (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (unitWindow d) univ ∂μ).toReal *
          ((volume (pairBoxBoundary d ((n : ℝ) + 1) (R : ℝ))).toReal /
            (volume (periodCell d ((n : ℝ) + 1))).toReal)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_pairBoxBoundary_ratio_zero d (show 0 ≤ (R : ℝ) by positivity))
    filter_upwards [hb.eventually (Iio_mem_nhds (half_pos hε))] with n hn
    exact (normalized_expected_difference_pair_box_compl_le μ hμ V hV hunit
      (by positivity : 0 < (n : ℝ) + 1) (R : ℝ)).trans_lt (by linarith)

theorem normalized_expected_difference_pair_box_eq_unit_sub_compl {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) {L : ℝ} (hL : 0 < L) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (periodCell d L) (periodCell d L) ∂μ).toReal / (volume (periodCell d L)).toReal =
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (unitWindow d) univ ∂μ).toReal -
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
        (periodCell d L) (periodCell d L)ᶜ ∂μ).toReal / (volume (periodCell d L)).toReal := by
  have hfull := expected_difference_pair_bounded_ne_top_of_unit μ hμ V hV hunit
    (measurable_periodCell d L) (isBounded_periodCell d L)
  have hp := expected_pair_right_ne_top_of_full μ (fun x y => V (x - y))
    (periodCell d L) (periodCell d L) hfull
  have hc := expected_pair_right_ne_top_of_full μ (fun x y => V (x - y))
    (periodCell d L) (periodCell d L)ᶜ hfull
  have hden : (volume (periodCell d L)).toReal ≠ 0 := by
    rw [volume_periodCell, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]
    positivity
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div, ← ENNReal.toReal_add hp hc,
    expected_localizedPairIntegral_right_add_compl μ (fun x y => V (x - y))
      (hV.comp (measurable_fst.sub measurable_snd)) (measurable_periodCell d L)
      (measurable_periodCell d L),
    expected_difference_pair_univ_eq_unit_mul_volume μ hμ V hV hunit (measurable_periodCell d L),
    ENNReal.toReal_mul]
  exact mul_div_cancel_right₀ _ hden

theorem tendsto_normalized_expected_difference_pair_box {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    Tendsto (fun n : ℕ => (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ).toReal /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop
      (𝓝 (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (unitWindow d) univ ∂μ).toReal) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c (unitWindow d) univ ∂μ).toReal)
      atTop (𝓝 (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
        (unitWindow d) univ ∂μ).toReal)).sub
    (tendsto_normalized_expected_difference_pair_box_compl_zero μ hμ V hV hunit)
  have he (n : ℕ) := normalized_expected_difference_pair_box_eq_unit_sub_compl μ hμ V hV hunit
    (by positivity : 0 < (n : ℝ) + 1)
  simpa only [he, sub_zero] using ht

end E8Leech
