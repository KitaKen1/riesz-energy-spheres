import E8Leech.FullSpacePairForms

/-!
# Certified finite-cell limits of the genuine signed pair integral

An additive split of the finite Jordan parts gives an exact signed tail
identity. Its absolute error is bounded by the actual nonnegative tail.
Consequently the original finite-energy process has L1 convergence of finite
cell computations and convergence of their expectations. This is not yet the
geometric large-first-window boundary limit or a sharp Fourier LP estimate.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical

theorem expected_pair_right_ne_top_of_full {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → Ambient d → ℝ≥0∞)
    (W U : Set (Ambient d))
    (hfinite : (∫⁻ c, localizedPairIntegral V c W univ ∂μ) ≠ ∞) :
    (∫⁻ c, localizedPairIntegral V c W U ∂μ) ≠ ∞ :=
  ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_right_le_univ V c W U).trans_lt
    hfinite.lt_top)

theorem finite_cell_sum_add_signed_pair_tail {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (F : Finset (IntegerCellIndex d))
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ≠ ∞) :
    (∑ z ∈ F, signedLocalizedPairIntegral H c W (integerCell z)) +
      signedLocalizedPairIntegral H c W (integerCellTail F) =
      signedLocalizedPairIntegral H c W univ := by
  have hparts := ENNReal.add_ne_top.mp
    ((localizedPairIntegral_pos_add_neg H c W univ).symm ▸ hfinite)
  have hp := finite_cell_sum_add_pair_tail (fun x y => ENNReal.ofReal (H x y)) c W F
  have hn := finite_cell_sum_add_pair_tail (fun x y => ENNReal.ofReal (-H x y)) c W F
  have hpf := ENNReal.add_ne_top.mp (hp.symm ▸ hparts.1)
  have hnf := ENNReal.add_ne_top.mp (hn.symm ▸ hparts.2)
  have hpr := congrArg ENNReal.toReal hp
  have hnr := congrArg ENNReal.toReal hn
  rw [ENNReal.toReal_add hpf.1 hpf.2,
    ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hpf.1)] at hpr
  rw [ENNReal.toReal_add hnf.1 hnf.2,
    ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hnf.1)] at hnr
  simp only [signedLocalizedPairIntegral, Finset.sum_sub_distrib]
  linarith

theorem finite_cell_sum_add_real_pair_tail {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (F : Finset (IntegerCellIndex d))
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ≠ ∞) :
    (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z)) +
      realLocalizedPairIntegral H c W (integerCellTail F) =
      realLocalizedPairIntegral H c W univ := by
  have he (U : Set (Ambient d)) (hU : MeasurableSet U) :
      realLocalizedPairIntegral H c W U = signedLocalizedPairIntegral H c W U :=
    (signedLocalizedPairIntegral_eq_real_of_finite_abs H hH c hW hbW hU
      (ne_of_lt ((localizedPairIntegral_right_le_univ _ c W U).trans_lt hfinite.lt_top))).symm
  simp_rw [he _ (measurableSet_integerCell _)]
  rw [he _ (measurableSet_integerCellTail F), he _ MeasurableSet.univ]
  exact finite_cell_sum_add_signed_pair_tail H c W F hfinite

theorem real_cell_truncation_error_eq_tail {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (F : Finset (IntegerCellIndex d))
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ≠ ∞) :
    realLocalizedPairIntegral H c W univ -
      (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z)) =
      realLocalizedPairIntegral H c W (integerCellTail F) := by
  linarith [finite_cell_sum_add_real_pair_tail H hH c hW hbW F hfinite]

theorem ofReal_abs_real_cell_truncation_error_le {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (F : Finset (IntegerCellIndex d))
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ≠ ∞) :
    ENNReal.ofReal |realLocalizedPairIntegral H c W univ -
      (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z))| ≤
      localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W (integerCellTail F) := by
  have hf : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|)
      c W (integerCellTail F) ≠ ∞ :=
    ne_of_lt ((localizedPairIntegral_right_le_univ _ c W _).trans_lt hfinite.lt_top)
  rw [real_cell_truncation_error_eq_tail H hH c hW hbW F hfinite]
  exact (ENNReal.ofReal_le_ofReal (abs_realLocalizedPairIntegral_le_of_finite_abs
    H hH c hW hbW (measurableSet_integerCellTail F) hf)).trans_eq
    (ENNReal.ofReal_toReal hf)

theorem expected_real_cell_truncation_error_le_pair_tail {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (F : Finset (IntegerCellIndex d))
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ∂μ) ≠ ∞) :
    (∫⁻ c, ENNReal.ofReal |realLocalizedPairIntegral H c W univ -
      (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z))| ∂μ) ≤
      ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|)
        c W (integerCellTail F) ∂μ := by
  apply lintegral_mono_ae
  filter_upwards [ae_lt_top (measurable_localizedPairIntegral
    (measurable_ofReal_abs_pair_kernel H hH) hW MeasurableSet.univ) hfinite] with c hc
  exact ofReal_abs_real_cell_truncation_error_le H hH c hW hbW F hc.ne

theorem integrable_real_cell_truncation_of_expected_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (F : Finset (IntegerCellIndex d))
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ∂μ) ≠ ∞) :
    Integrable (fun c => ∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z)) μ := by
  apply integrable_finsetSum
  intro z _
  exact integrable_real_pair_of_expected_abs μ H hH hW hbW (measurableSet_integerCell z)
    (expected_pair_right_ne_top_of_full μ _ W _ hfinite)

theorem tendsto_real_cell_truncation_L1_of_expected_tail {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ∂μ) ≠ ∞)
    (htail : Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|)
        c W (integerCellTail F) ∂μ) atTop (nhds 0)) :
    Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, ENNReal.ofReal |realLocalizedPairIntegral H c W univ -
        (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z))| ∂μ) atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail (fun _ => zero_le)
    (fun F => expected_real_cell_truncation_error_le_pair_tail μ H hH hW hbW F hfinite)

/-- This limit is of genuine real expectations, not just a nonnegative tail. -/
theorem tendsto_integral_real_cell_truncation_of_expected_tail {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W univ ∂μ) ≠ ∞)
    (htail : Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|)
        c W (integerCellTail F) ∂μ) atTop (nhds 0)) :
    Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫ c, (∑ z ∈ F, realLocalizedPairIntegral H c W (integerCell z)) ∂μ)
      atTop (nhds (∫ c, realLocalizedPairIntegral H c W univ ∂μ)) := by
  apply tendsto_integral_of_L1 _
    (integrable_real_pair_of_expected_abs μ H hH hW hbW MeasurableSet.univ hfinite).aestronglyMeasurable
    (Eventually.of_forall fun F => integrable_real_cell_truncation_of_expected_abs μ H hH hW hbW F hfinite)
  have ht := tendsto_real_cell_truncation_L1_of_expected_tail μ H hH hW hbW hfinite htail
  simpa only [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm] using ht

theorem tendsto_real_difference_cell_truncation_L1_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, ENNReal.ofReal |realLocalizedPairIntegral (fun x y => h (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) univ -
        (∑ z ∈ F, realLocalizedPairIntegral (fun x y => h (x - y)) c
          ((fun x => a + x) ⁻¹' unitWindow d) (integerCell z))| ∂μ) atTop (nhds 0) :=
  tendsto_real_cell_truncation_L1_of_expected_tail μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd))
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (isBounded_translated_unitWindow a)
    (expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy h hh hdecay a)
    (tendsto_expected_abs_difference_pair_tail_zero_of_rapidDecay hs μ hμ ρ hρ hρtop henergy h hh hdecay a)

theorem tendsto_integral_real_difference_cell_truncation_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫ c, (∑ z ∈ F, realLocalizedPairIntegral (fun x y => h (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) (integerCell z)) ∂μ)
      atTop (nhds (∫ c, realLocalizedPairIntegral (fun x y => h (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ)) :=
  tendsto_integral_real_cell_truncation_of_expected_tail μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd))
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (isBounded_translated_unitWindow a)
    (expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy h hh hdecay a)
    (tendsto_expected_abs_difference_pair_tail_zero_of_rapidDecay hs μ hμ ρ hρ hρtop henergy h hh hdecay a)

theorem tendsto_integral_real_gaussian_cell_truncation_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {α : ℝ} (hα : 0 < α) (a : Ambient d) :
    Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫ c, (∑ z ∈ F, realLocalizedPairIntegral (fun x y => gaussianKernel α (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) (integerCell z)) ∂μ)
      atTop (nhds (∫ c, realLocalizedPairIntegral (fun x y => gaussianKernel α (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ)) :=
  tendsto_integral_real_difference_cell_truncation_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (gaussianKernel α) (continuous_gaussianKernel α).measurable (hasRapidDecay_gaussianKernel hα) a

/-- The L1 error cutoff is selected before the law and its excess. -/
theorem exists_uniform_real_difference_cell_truncation_L1_cutoff_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    (a : Ambient d) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F₀ : Finset (IntegerCellIndex d),
      ∀ F : Finset (IntegerCellIndex d), F₀ ⊆ F →
      ∀ μ : Measure (Configuration (Ambient d)), IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      (∫⁻ c, ENNReal.ofReal |realLocalizedPairIntegral (fun x y => h (x - y)) c
        ((fun x => a + x) ⁻¹' unitWindow d) univ -
        (∑ z ∈ F, realLocalizedPairIntegral (fun x y => h (x - y)) c
          ((fun x => a + x) ⁻¹' unitWindow d) (integerCell z))| ∂μ) < ε := by
  obtain ⟨F₀, hF₀⟩ := exists_uniform_abs_difference_pair_tail_cutoff_of_rapidDecay
    hs L Δ hLtop hΔtop h hh hdecay a ε hε
  refine ⟨F₀, ?_⟩
  intro F hF μ hμ hρ δ hδ hexcess
  have henergy : rieszEnergy s μ ≠ ∞ := ne_of_lt (hexcess.2.trans_lt
    (ENNReal.add_lt_top.mpr ⟨hLtop.lt_top, hδ.trans_lt hΔtop.lt_top⟩))
  exact (expected_real_cell_truncation_error_le_pair_tail μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd))
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (isBounded_translated_unitWindow a) F
    (expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ 1 hρ (by simp) henergy h hh hdecay a)).trans_lt
    (hF₀ F hF μ hμ hρ δ hδ hexcess)

end E8Leech
