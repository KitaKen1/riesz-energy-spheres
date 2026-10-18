import E8Leech.Measurability

/-!
# Charging deleted points to a nonnegative pair cost

One close neighbour suffices to charge each deleted first endpoint. The neighbour may
lie outside the window. This is a conditional combinatorial transfer, not the analytic
claim that a CKMRV slack has a uniform positive lower bound or small expected cost.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false in
theorem deletedCount_cost_le {d : ℕ} (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (r : ℝ) (κ : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y) :
    κ * c.count (globalBadPoints c.support r ∩ W) ≤ orderedWindowEnergy V c W := by
  classical
  let B := globalBadPoints c.support r ∩ W
  have hB : MeasurableSet B :=
    ((c.countable_support 0).mono (fun _ hx => hx.1.1)).measurableSet
  rw [← countingKernel_apply c hB, ← lintegral_indicator_const hB κ,
    countingKernel_lintegral_eq_tsum]
  unfold orderedWindowEnergy
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : (x : Ambient d) ∈ B
  · rw [Set.indicator_of_mem hx]
    obtain ⟨⟨_, y, hy, hxy, hdist⟩, hxW⟩ := hx
    rw [if_pos hxW]
    let f : c.support → ℝ≥0∞ := fun z =>
      @ite ℝ≥0∞ ((z : Ambient d) = (x : Ambient d)) (Classical.propDecidable _) 0 (V x z)
    change κ ≤ ∑' z, f z
    have hyterm : κ ≤ f ⟨y, hy⟩ := by
      dsimp only [f]
      rw [if_neg hxy.symm]
      exact hV x y hxy hdist
    exact hyterm.trans (ENNReal.le_tsum (f := f) ⟨y, hy⟩)
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

theorem expected_deletedCount_cost_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (r : ℝ) (κ : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y) :
    κ * (∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy V c W ∂μ := by
  rw [← lintegral_const_mul κ (measurable_deletedCount r hW)]
  exact lintegral_mono fun c => deletedCount_cost_le c W r κ V hV

theorem expected_deletedCount_le_of_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (r : ℝ) (κ q : ℝ≥0∞)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c W ∂μ) ≤ q) :
    (∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ) ≤ q / κ := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hκ0) (Or.inl hκtop)).mpr
  simpa only [mul_comm] using (expected_deletedCount_cost_le μ hW r κ V hV).trans hcost

end E8Leech
