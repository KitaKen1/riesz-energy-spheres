import E8Leech.Measurability
import E8Leech.Restoration

/-!
# Stationary thinning and restoration without a measurability assumption

The globally defined deletion commutes with translations, so its measurable pushforward
preserves stationarity. The restoration theorem now gets thinning-count measurability from
the counting-kernel proof rather than accepting it as an extra hypothesis.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem translate_deleteClose {d : ℕ} (a : Ambient d)
    (c : Configuration (Ambient d)) (r : ℝ) :
    translate a (c.deleteClose r) = (translate a c).deleteClose r := by
  apply Configuration.ext
  change (fun x : Ambient d => a + x) '' globalKeptPoints c.support r =
    globalKeptPoints ((fun x : Ambient d => a + x) '' c.support) r
  have he : Isometry (fun x : Ambient d => a + x) :=
    Isometry.of_dist_eq fun x y => dist_add_left a x y
  have hj : Function.Injective (fun x : Ambient d => a + x) := fun _ _ h => add_left_cancel h
  rw [globalKeptPoints, globalKeptPoints, Set.image_sdiff hj,
    badPoints_image_isometry _ he hj]

theorem stationary_deleteClose {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (hμ : IsStationary μ) (r : ℝ) :
    IsStationary (μ.map (fun c => c.deleteClose r)) := by
  intro a
  refine ⟨measurable_translate a, ?_⟩
  have hm := measurable_deleteClose (d := d) r
  have hcomm : translate a ∘ (fun c : Configuration (Ambient d) => c.deleteClose r) =
      (fun c : Configuration (Ambient d) => c.deleteClose r) ∘ translate a := by
    funext c
    exact translate_deleteClose a c r
  rw [Measure.map_map (measurable_translate a) hm, hcomm,
    ← Measure.map_map hm (measurable_translate a), (hμ a).map_eq]

def StationaryPointProcess.deleteClose {d : ℕ} (Ξ : StationaryPointProcess d) (r : ℝ) :
    StationaryPointProcess d where
  law := Ξ.law.map (fun c => c.deleteClose r)
  probability := by
    have := Ξ.probability
    exact inferInstance
  stationary := stationary_deleteClose Ξ.law Ξ.stationary r

theorem count_deletion_partition {d : ℕ} (c : Configuration (Ambient d))
    (r : ℝ) (W : Set (Ambient d)) :
    c.count W = (c.deleteClose r).count W + c.count (globalBadPoints c.support r ∩ W) := by
  have heq : c.support ∩ W =
      (globalKeptPoints c.support r ∩ W) ∪ (globalBadPoints c.support r ∩ W) := by
    ext x
    simp only [globalKeptPoints, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union]
    constructor
    · intro hx
      by_cases hb : x ∈ globalBadPoints c.support r
      · exact Or.inr ⟨hb, hx.2⟩
      · exact Or.inl ⟨⟨hx.1, hb⟩, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1.1, hx.2⟩
      · exact ⟨hx.1.1, hx.2⟩
  have hd : Disjoint (globalKeptPoints c.support r ∩ W) (globalBadPoints c.support r ∩ W) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.1.2 hy.1
  have hb : MeasurableSet (globalBadPoints c.support r ∩ W) :=
    ((c.countable_support 0).mono (fun _ hx => hx.1.1)).measurableSet
  have hdup : c.support ∩ (globalBadPoints c.support r ∩ W) = globalBadPoints c.support r ∩ W := by
    ext x
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨hx.1.1, hx⟩
  change Measure.count (c.support ∩ W) =
    Measure.count (globalKeptPoints c.support r ∩ W) +
      Measure.count (c.support ∩ (globalBadPoints c.support r ∩ W))
  rw [heq, hdup, measure_union hd hb]

theorem expected_count_deletion_partition {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, c.count W ∂μ) = (∫⁻ c, (c.deleteClose r).count W ∂μ) +
      ∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ := by
  exact (lintegral_congr fun c => count_deletion_partition c r W).trans
    (lintegral_add_left (measurable_retainedCount r hW) _)

theorem expected_retained_count_lower_bound {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ q : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (r : ℝ) {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hdel : (∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ) ≤ q * volume W) :
    ρ * volume W - q * volume W ≤
      ∫⁻ c, c.count W ∂μ.map (fun c => c.deleteClose r) := by
  rw [lintegral_map (Configuration.measurable_count hW) (measurable_deleteClose r)]
  apply tsub_le_iff_right.mpr
  rw [← hρ W hW, expected_count_deletion_partition μ r hW]
  exact add_le_add le_rfl hdel

theorem measurable_good_event_restoration_euclidean {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (Λ : Set (Ambient d))
    (r R error loss : ℝ) (G : Set (Configuration (Ambient d)))
    (hG : MeasurableSet G)
    (hgood : G ⊆ {c | LocalCrystal Λ (c.deleteClose r) R error loss}) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧
      H ⊆ {c | LocalCrystal Λ c R error loss} ∧
      μ G - (∫⁻ c, c.count (globalBadPoints c.support r ∩ Metric.closedBall 0 R) ∂μ) ≤ μ H :=
  measurable_good_event_restoration μ Λ r R error loss G hG hgood
    (measurable_deletedCount r measurableSet_closedBall)

end E8Leech
