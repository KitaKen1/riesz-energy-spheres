import E8Leech.GlobalDeletion
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Probability bounds for deletion and periodization

The only supplied analytic input is an expectation bound. Measurability of the globally
deleted-point count is explicit; it is not silently assumed by defining a thinning operation.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
  [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem window_changed_implies_deleted_point {s W : Set X} {r : ℝ}
    (h : globalKeptPoints s r ∩ W ≠ s ∩ W) :
    (globalBadPoints s r ∩ W).Nonempty := by
  by_contra hempty
  exact h (restore_window (Set.not_nonempty_iff_eq_empty.mp hempty))

/-- A union-free restoration estimate for the entire original window. -/
theorem window_change_probability_le (μ : Measure Ω) (c : Ω → Configuration X)
    (W : Set X) (r : ℝ)
    (hm : AEMeasurable (fun ω => (c ω).count (globalBadPoints (c ω).support r ∩ W)) μ) :
    μ {ω | globalKeptPoints (c ω).support r ∩ W ≠ (c ω).support ∩ W} ≤
      ∫⁻ ω, (c ω).count (globalBadPoints (c ω).support r ∩ W) ∂μ := by
  apply meas_le_lintegral₀ hm
  intro ω hω
  obtain ⟨x, hx⟩ := window_changed_implies_deleted_point hω
  exact Configuration.one_le_count_of_mem _ _ ⟨hx.1.1, hx⟩

/-- With a stationary deleted-point intensity bound, only the volume factor remains. -/
theorem window_change_probability_le_of_intensity
    (μ : Measure Ω) (c : Ω → Configuration X) (W : Set X) (r : ℝ)
    (hm : AEMeasurable (fun ω => (c ω).count (globalBadPoints (c ω).support r ∩ W)) μ)
    (q v : ℝ≥0∞)
    (hmean : (∫⁻ ω, (c ω).count (globalBadPoints (c ω).support r ∩ W) ∂μ) ≤ q * v) :
    μ {ω | globalKeptPoints (c ω).support r ∩ W ≠ (c ω).support ∩ W} ≤ q * v :=
  (window_change_probability_le μ c W r hm).trans hmean

/-- Separate density, periodic stability, and boundary failures. -/
theorem periodization_failure_probability_le
    (μ : Measure Ω) (deficit : Ω → ℝ≥0∞) (η ε : ℝ≥0∞)
    (hη : η ≠ 0) (hηtop : η ≠ ∞) (hm : AEMeasurable deficit μ)
    (hmean : (∫⁻ ω, deficit ω ∂μ) ≤ ε)
    (F S B : Set Ω) (p b : ℝ≥0∞)
    (hcover : F ⊆ {ω | η ≤ deficit ω} ∪ S ∪ B)
    (hS : μ S ≤ p) (hB : μ B ≤ b) : μ F ≤ ε / η + p + b := by
  have hdensity : μ {ω | η ≤ deficit ω} ≤ ε / η :=
    (meas_ge_le_lintegral_div hm hη hηtop).trans (ENNReal.div_le_div_right hmean η)
  calc
    μ F ≤ μ ({ω | η ≤ deficit ω} ∪ S ∪ B) := measure_mono hcover
    _ ≤ μ ({ω | η ≤ deficit ω} ∪ S) + μ B := measure_union_le _ _
    _ ≤ (μ {ω | η ≤ deficit ω} + μ S) + μ B :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ε / η + p + b := add_le_add (add_le_add hdensity hS) hB

end E8Leech
