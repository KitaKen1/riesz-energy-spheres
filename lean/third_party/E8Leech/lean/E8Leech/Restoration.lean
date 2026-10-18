import E8Leech.Target
import E8Leech.ProbabilityBounds

/-!
# Restoring a measurable good subevent to the original point process

The thinning-count measurability and its expectation bound are explicit hypotheses. This
finishes the probability-loss step once a good event for the thinned process is supplied;
it does not prove that the thinned process satisfies the periodic stability inputs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem localCrystal_restore {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (r R error loss : ℝ)
    (h : globalBadPoints c.support r ∩ Metric.closedBall 0 R = ∅)
    (hgood : LocalCrystal Λ (c.deleteClose r) R error loss) :
    LocalCrystal Λ c R error loss := by
  simpa only [LocalCrystal, Configuration.count, Configuration.deleteClose_support,
    restore_window h] using hgood

/-- Keep a measurable part of the original good event and pay the expected deleted count. -/
theorem measurable_good_event_restoration {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (Λ : Set (Ambient d))
    (r R error loss : ℝ) (G : Set (Configuration (Ambient d)))
    (hG : MeasurableSet G)
    (hgood : G ⊆ {c | LocalCrystal Λ (c.deleteClose r) R error loss})
    (hm : Measurable (fun c : Configuration (Ambient d) =>
      c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R))) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧
      H ⊆ {c | LocalCrystal Λ c R error loss} ∧
      μ G - (∫⁻ c, c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R) ∂μ) ≤ μ H := by
  let B := {c : Configuration (Ambient d) |
    c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R) ≠ 0}
  have hB : MeasurableSet B := by
    have heq : B = ((fun c : Configuration (Ambient d) =>
        c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R)) ⁻¹' {0})ᶜ := by
      ext c
      rfl
    rw [heq]
    exact (hm (measurableSet_singleton 0)).compl
  have hmean : μ B ≤ ∫⁻ c,
      c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R) ∂μ := by
    apply meas_le_lintegral₀ hm.aemeasurable
    intro c hc
    have hnonempty : (globalBadPoints c.support r ∩ Metric.closedBall 0 R).Nonempty := by
      by_contra h
      have hempty := Set.not_nonempty_iff_eq_empty.mp h
      exact hc (by simp [Configuration.count, hempty])
    obtain ⟨x, hx⟩ := hnonempty
    exact Configuration.one_le_count_of_mem _ _ ⟨hx.1.1, hx⟩
  refine ⟨G \ B, hG.diff hB, ?_, ?_⟩
  · intro c hc
    apply localCrystal_restore Λ c r R error loss _ (hgood hc.1)
    have hz : c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R) = 0 :=
      not_not.mp hc.2
    have heq := Configuration.count_eq_zero_iff _ _ |>.mp hz
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxempty : x ∈ (∅ : Set (Ambient d)) := heq ▸ ⟨hx.1.1, hx⟩
    exact hxempty.elim
  · exact (tsub_le_tsub_left hmean _).trans le_measure_sdiff

end E8Leech
