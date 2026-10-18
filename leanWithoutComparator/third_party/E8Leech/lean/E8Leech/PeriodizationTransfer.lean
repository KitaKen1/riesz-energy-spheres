import E8Leech.UniformCenter
import E8Leech.Target

/-!
# Transfer of local crystallinity from one guarded periodic sample

The periodic and expanded configurations agree on an interior observation ball.
Translate that ball to the origin, retain both directions of the finite lattice
matching and the count lower bound, and descend a measurable product good event
to the original stationary law. The original centre is contracted by `1 - t`.
The input good event and its probability bound remain explicit hypotheses;
this file does not prove BRR stability or a packing density upper bound.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem restrict_translate {d : ℕ} (c : Configuration (Ambient d))
    (a : Ambient d) (W : Set (Ambient d)) :
    (translate a c).restrict W =
      translate a (c.restrict ((fun x => a + x) ⁻¹' W)) := by
  apply Configuration.ext
  change ((fun x => a + x) '' c.support) ∩ W =
    (fun x => a + x) '' (c.support ∩ ((fun x => a + x) ⁻¹' W))
  exact (Set.image_inter_preimage _ _ _).symm

theorem translate_negative_closedBall_preimage {d : ℕ} (u : Ambient d) (R : ℝ) :
    (fun x : Ambient d => -u + x) ⁻¹' Metric.closedBall 0 R = Metric.closedBall u R := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [sub_eq_add_neg, add_comm x (-u)]

theorem restrict_translate_negative_center {d : ℕ}
    (c : Configuration (Ambient d)) (u : Ambient d) (R : ℝ) :
    (translate (-u) c).restrict (Metric.closedBall 0 R) =
      translate (-u) (c.restrict (Metric.closedBall u R)) := by
  rw [restrict_translate, translate_negative_closedBall_preimage]

/-- A window identity transfers the two approximation directions and the point count. -/
theorem localCrystal_iff_of_restrict_eq {d : ℕ} (Λ : Set (Ambient d))
    (c c' : Configuration (Ambient d)) (R error loss : ℝ)
    (h : c.restrict (Metric.closedBall 0 R) = c'.restrict (Metric.closedBall 0 R)) :
    LocalCrystal Λ c R error loss ↔ LocalCrystal Λ c' R error loss := by
  have hw := congrArg Configuration.support h
  change c.support ∩ Metric.closedBall 0 R = c'.support ∩ Metric.closedBall 0 R at hw
  simp only [LocalCrystal, Configuration.count, hw]

theorem localCrystal_of_guardedPeriodization_center {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (L r R error loss : ℝ)
    (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y)
    {u : Ambient d} (hu : u ∈ guardObservationCenters d L r R)
    (hgood : LocalCrystal Λ
      (translate (-u) (guardedPeriodization c L r hr hL hs)) R error loss) :
    LocalCrystal Λ (translate (-u) c) R error loss := by
  apply (localCrystal_iff_of_restrict_eq Λ _ _ R error loss ?_).mp hgood
  rw [restrict_translate_negative_center, restrict_translate_negative_center,
    guardedPeriodization_restrict_ball c L r R hr hL hs hu]

theorem expandAfterDeletion_translate {d : ℕ} (c : Configuration (Ambient d))
    (r t : ℝ) (ht : t < 1) (b : Ambient d) :
    expandAfterDeletion (translate b c) r t ht =
      translate ((1 - t)⁻¹ • b) (expandAfterDeletion c r t ht) := by
  unfold expandAfterDeletion
  rw [← translate_deleteClose, dilate_translate]

/-- The centre in the original configuration is `(1 - t) • u`, not `u`. -/
theorem expandAfterDeletion_translate_negative_center {d : ℕ}
    (c : Configuration (Ambient d)) (r t : ℝ) (ht : t < 1) (u : Ambient d) :
    expandAfterDeletion (translate (-((1 - t) • u)) c) r t ht =
      translate (-u) (expandAfterDeletion c r t ht) := by
  rw [expandAfterDeletion_translate, smul_neg,
    inv_smul_smul₀ (ne_of_gt (sub_pos.mpr ht))]

theorem measurable_centered_guardedExpanded {d : ℕ}
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      translate (-p.2) (guardedExpandedConfiguration p.1 L r t hr hL ht)) :=
  measurable_translate_param _ _
    ((measurable_guardedExpandedConfiguration L r t hr hL ht).comp measurable_fst)
    measurable_snd.neg

theorem localCrystal_of_guardedExpanded_center {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (L r t R error loss : ℝ)
    (hr : 0 < r) (hL : r < L) (ht : t < 1)
    {u : Ambient d} (hu : u ∈ guardObservationCenters d L r R)
    (hgood : LocalCrystal Λ
      (translate (-u) (guardedExpandedConfiguration c L r t hr hL ht)) R error loss) :
    LocalCrystal Λ (expandAfterDeletion (translate (-((1 - t) • u)) c) r t ht)
      R error loss := by
  rw [expandAfterDeletion_translate_negative_center]
  exact localCrystal_of_guardedPeriodization_center Λ _ L r R error loss hr hL
    (expandAfterDeletion_separated c r t ht) hu hgood

/-- Remove boundary centres and select one section using stationarity. The target
event need not be measurable as a whole, and no isometry selection is used. -/
theorem measurable_good_event_of_guardedExpanded {d : ℕ} (Λ : Set (Ambient d))
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (L r t R error loss : ℝ)
    (hr : 0 < r) (hL : r < L) (ht : t < 1) (hR : 0 ≤ R) (hw : r + 2 * R ≤ L)
    (H : Set (Configuration (Ambient d) × Ambient d)) (hH : MeasurableSet H)
    (hgood : ∀ p ∈ H, LocalCrystal Λ
      (translate (-p.2) (guardedExpandedConfiguration p.1 L r t hr hL ht)) R error loss)
    (q : ℝ≥0∞)
    (hq : q < (μ.prod (uniformPeriodCell d L)) H -
      ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L)) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | LocalCrystal Λ (expandAfterDeletion c r t ht) R error loss} ∧ q < μ G := by
  have hL0 : 0 < L := hr.trans hL
  let ν := uniformPeriodCell d L
  let _ : IsProbabilityMeasure ν := uniformPeriodCell_probability d L hL0
  let B : Set (Configuration (Ambient d) × Ambient d) :=
    {p | p.2 ∉ guardObservationCenters d L r R}
  have hB : MeasurableSet B :=
    (measurable_guardObservationCenters d L r R).compl.preimage measurable_snd
  have hBprob : (μ.prod ν) B ≤ ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L) := by
    have he : B = Set.univ ×ˢ (guardObservationCenters d L r R)ᶜ := by
      ext p
      simp [B]
    rw [he, Measure.prod_prod, measure_univ, one_mul]
    exact uniformPeriodCell_boundary_probability_le L r R hr.le hR hL0 hw
  have hq' : q < (μ.prod ν) (H \ B) :=
    hq.trans_le ((tsub_le_tsub_left hBprob _).trans le_measure_sdiff)
  apply measurable_good_event_of_center_map μ hμ ν (fun u => (1 - t) • u)
    (fun c => LocalCrystal Λ (expandAfterDeletion c r t ht) R error loss)
    (H \ B) (hH.diff hB) _ q hq'
  intro p hp
  have hu : p.2 ∈ guardObservationCenters d L r R := by
    simpa only [B, Set.mem_ofPred_eq, not_not] using hp.2
  exact localCrystal_of_guardedExpanded_center Λ p.1 L r t R error loss
    hr hL ht hu (hgood p hp.1)

/-- A BRR good-event failure budget plus a boundary budget suffices for descent. -/
theorem measurable_good_event_of_guardedExpanded_failure {d : ℕ}
    (Λ : Set (Ambient d))
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (L r t R error loss : ℝ)
    (hr : 0 < r) (hL : r < L) (ht : t < 1) (hR : 0 ≤ R) (hw : r + 2 * R ≤ L)
    (H : Set (Configuration (Ambient d) × Ambient d)) (hH : MeasurableSet H)
    (hgood : ∀ p ∈ H, LocalCrystal Λ
      (translate (-p.2) (guardedExpandedConfiguration p.1 L r t hr hL ht)) R error loss)
    (failure q : ℝ≥0∞)
    (hfailure : (μ.prod (uniformPeriodCell d L)) Hᶜ ≤ failure)
    (hq : q < 1 - failure - ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L)) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | LocalCrystal Λ (expandAfterDeletion c r t ht) R error loss} ∧ q < μ G := by
  let _ := uniformPeriodCell_probability d L (hr.trans hL)
  have hmass : (μ.prod (uniformPeriodCell d L)) H +
      (μ.prod (uniformPeriodCell d L)) Hᶜ = 1 := by
    rw [measure_add_measure_compl hH, measure_univ]
  have hle : 1 - failure ≤ (μ.prod (uniformPeriodCell d L)) H := by
    apply tsub_le_iff_right.mpr
    rw [← hmass]
    exact add_le_add le_rfl hfailure
  exact measurable_good_event_of_guardedExpanded Λ μ hμ L r t R error loss
    hr hL ht hR hw H hH hgood q (hq.trans_le (tsub_le_tsub_right hle _))

end E8Leech
