import E8Leech.CountableCellPairs
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Law-uniform full-space and cell-tail estimates

The energy reference and excess cap are fixed first. A finite second-moment
coefficient then works for every stationary intensity-one law under that cap.
A fixed summable kernel envelope selects a finite truncation before either the
law or its excess is chosen. The envelope itself is still a proof obligation.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- The coefficient is chosen before the law, excess, kernel and envelope. -/
theorem exists_uniform_pair_cell_bound {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ μ : Measure (Configuration (Ambient d)), IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      ∀ (V : Ambient d → Ambient d → ℝ≥0∞), Measurable (Function.uncurry V) →
      ∀ (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞),
      (∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
        ∀ y ∈ integerCell z, V x y ≤ M z) →
      (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ) ≤
        (∑' z, M z) * B ∧
      ∀ F : Finset (IntegerCellIndex d),
        (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d)
          (integerCellTail F) ∂μ) ≤
          (∑' z : {z : IntegerCellIndex d // z ∉ F}, M z.val) * B := by
  obtain ⟨A, hA, hboundA⟩ := exists_uniform_unit_second_moment_bound (d := d) hs L Δ hLtop hΔtop
  refine ⟨2 * A, ENNReal.mul_ne_top (by simp) hA, ?_⟩
  intro μ hμ hρ δ hδ hexcess V hV a M hbound
  have hmoment : (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≤ 2 * A :=
    mul_le_mul_of_nonneg_left (hboundA μ hρ δ hδ hexcess) zero_le
  constructor
  · exact (expected_pair_univ_le_cell_envelope μ hμ V hV a M hbound).trans
      (mul_le_mul_of_nonneg_left hmoment zero_le)
  · intro F
    exact (expected_pair_tail_le_cell_envelope μ hμ V hV a M hbound F).trans
      (mul_le_mul_of_nonneg_left hmoment zero_le)

/-- The finite cell set can be chosen before the law and its excess.
This is uniform integrability of the second endpoint, not a geometric
large-window boundary or a Fourier LP lower bound. -/
theorem exists_uniform_pair_tail_cutoff {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞) (hM : (∑' z, M z) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F₀ : Finset (IntegerCellIndex d),
      ∀ F : Finset (IntegerCellIndex d), F₀ ⊆ F →
      ∀ μ : Measure (Configuration (Ambient d)), IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d)
        (integerCellTail F) ∂μ) < ε := by
  obtain ⟨B, hB, hboundB⟩ := exists_uniform_pair_cell_bound (d := d) hs L Δ hLtop hΔtop
  have ht := (ENNReal.continuous_mul_const hB).tendsto 0 |>.comp
    (ENNReal.tendsto_tsum_compl_atTop_zero hM)
  simp only [zero_mul] at ht
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hε))
  refine ⟨F₀, ?_⟩
  intro F hF μ hμ hρ δ hδ hexcess
  exact ((hboundB μ hμ hρ δ hδ hexcess V hV a M hbound).2 F).trans_lt (hF₀ F hF)

/-- A certified tail expectation also controls the probability of exceeding a
fixed error tolerance; the event is measurable in the original configuration. -/
theorem pair_tail_probability_le_cell_envelope {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z)
    (F : Finset (IntegerCellIndex d)) (η : ℝ≥0∞) (hη : η ≠ 0) (hηtop : η ≠ ∞) :
    μ {c | η ≤ localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d)
      (integerCellTail F)} ≤
      ((∑' z : {z : IntegerCellIndex d // z ∉ F}, M z.val) *
        (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ)) / η := by
  have hm := measurable_localizedPairIntegral hV (W := (fun x => a + x) ⁻¹' unitWindow d)
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (measurableSet_integerCellTail F)
  exact (meas_ge_le_lintegral_div hm.aemeasurable hη hηtop).trans
    (ENNReal.div_le_div_right (expected_pair_tail_le_cell_envelope μ hμ V hV a M hbound F) η)

end E8Leech
