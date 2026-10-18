import E8Leech.CountingKernel
import E8Leech.StationaryProcess
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint measurability of translating a configuration

The translation vector may depend on a random observation centre. Counts are
queries in a Borel relation, so no measurable enumeration of points is needed.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem measurable_translate_joint {d : ℕ} :
    Measurable (fun p : Configuration (Ambient d) × Ambient d => translate p.2 p.1) := by
  apply Configuration.measurable_of_counts
  intro W hW
  let T : Set ((Configuration (Ambient d) × Ambient d) × Ambient d) :=
    {p | p.1.2 + p.2 ∈ W}
  have hT : MeasurableSet T :=
    hW.preimage (measurable_fst.snd.add measurable_snd)
  have h := measurable_count_query
    (fun p : Configuration (Ambient d) × Ambient d => p.1) measurable_fst hT
  simp only [count_translate]
  exact h

theorem measurable_translate_param {d : ℕ} {A : Type*} [MeasurableSpace A]
    (f : A → Configuration (Ambient d)) (a : A → Ambient d)
    (hf : Measurable f) (ha : Measurable a) :
    Measurable (fun x => translate (a x) (f x)) :=
  measurable_translate_joint.comp (hf.prodMk ha)

theorem measurable_translate_negative_center {d : ℕ} :
    Measurable (fun p : Configuration (Ambient d) × Ambient d => translate (-p.2) p.1) :=
  measurable_translate_param _ _ measurable_fst measurable_snd.neg

/-- Averaging observation centres preserves the probability of an original-law event. -/
theorem stationary_random_center_event {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ν : Measure (Ambient d)) [SFinite μ] [SFinite ν]
    {G : Set (Configuration (Ambient d))} (hG : MeasurableSet G) :
    (μ.prod ν) {p | translate (-p.2) p.1 ∈ G} = μ G * ν Set.univ := by
  have hE : MeasurableSet {p : Configuration (Ambient d) × Ambient d |
      translate (-p.2) p.1 ∈ G} := hG.preimage measurable_translate_negative_center
  rw [Measure.prod_apply_symm hE]
  have he : ∀ u : Ambient d,
      μ ((fun c => (c, u)) ⁻¹' {p | translate (-p.2) p.1 ∈ G}) = μ G := by
    intro u
    exact (hμ (-u)).measure_preimage hG.nullMeasurableSet
  simp_rw [he]
  exact lintegral_const _

theorem translate_negative_cancel {d : ℕ} (u : Ambient d)
    (c : Configuration (Ambient d)) : translate (-u) (translate u c) = c := by
  apply Configuration.ext
  change (fun x => -u + x) '' ((fun x => u + x) '' c.support) = c.support
  rw [Set.image_image]
  have he : (fun x : Ambient d => -u + (u + x)) = id := by
    funext x
    simp
  rw [he, Set.image_id]

/-- Descend a measurable product good event without assuming that the whole target
existential property is measurable. A strict probability budget permits one good section. -/
theorem measurable_good_event_of_center_map {d : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) [SFinite μ]
    (ν : Measure A) [IsProbabilityMeasure ν] (b : A → Ambient d)
    (P : Configuration (Ambient d) → Prop)
    (H : Set (Configuration (Ambient d) × A)) (hH : MeasurableSet H)
    (hgood : ∀ p ∈ H, P (translate (-(b p.2)) p.1))
    (q : ℝ≥0∞) (hq : q < (μ.prod ν) H) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | P c} ∧ q < μ G := by
  let S : A → Set (Configuration (Ambient d)) := fun u =>
    (fun c => (c, u)) ⁻¹' H
  have hS : ∀ u, MeasurableSet (S u) := fun u =>
    hH.preimage measurable_prodMk_right
  obtain ⟨u, hu⟩ : ∃ u : A, q < μ (S u) := by
    by_contra! h
    have hh : (μ.prod ν) H ≤ q := by
      rw [Measure.prod_apply_symm hH]
      calc
        _ ≤ ∫⁻ _, q ∂ν := lintegral_mono h
        _ = q := by simp
    exact (not_le_of_gt hq) hh
  refine ⟨translate (b u) ⁻¹' S u,
    (hS u).preimage (measurable_translate (b u)), ?_, ?_⟩
  · intro c hc
    change P c
    have hh := hgood (translate (b u) c, u) hc
    simpa only [translate_negative_cancel] using hh
  · rwa [(hμ (b u)).measure_preimage (hS u).nullMeasurableSet]

/-- The unscaled centre case. No measurability of the whole predicate `P` is required. -/
theorem measurable_good_event_of_random_centers {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) [SFinite μ]
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (P : Configuration (Ambient d) → Prop)
    (H : Set (Configuration (Ambient d) × Ambient d)) (hH : MeasurableSet H)
    (hgood : ∀ p ∈ H, P (translate (-p.2) p.1))
    (q : ℝ≥0∞) (hq : q < (μ.prod ν) H) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | P c} ∧ q < μ G :=
  measurable_good_event_of_center_map μ hμ ν id P H hH hgood q hq

end E8Leech
