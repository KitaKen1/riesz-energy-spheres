import E8Leech.IntensityIntegration
import E8Leech.WindowNormalization
import E8Leech.StationaryDeletion
import E8Leech.DeletionCost
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Intensity of stationary thinning from Haar uniqueness

The mean counting measure is translation invariant. If it is finite on compacts,
Haar uniqueness identifies it with the unit-window expected count times volume.
For thinning, domination by the original finite-intensity mean measure supplies
the compact finiteness. No ergodicity or additional retained-intensity hypothesis
is required.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem meanCountingMeasure_apply {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    meanCountingMeasure μ W = ∫⁻ c, c.count W ∂μ := by
  rw [meanCountingMeasure,
    Measure.bind_apply hW (countingKernel d).measurable.aemeasurable]
  simp_rw [countingKernel_apply _ hW]

theorem meanCountingMeasure_addInvariant {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) :
    Measure.IsAddLeftInvariant (meanCountingMeasure μ) := by
  refine ⟨fun a => ?_⟩
  ext W hW
  rw [Measure.map_apply (measurable_const_add a) hW,
    meanCountingMeasure_apply μ (hW.preimage (measurable_const_add a)),
    meanCountingMeasure_apply μ hW]
  exact expected_count_translate μ hμ a hW

def processIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ c, c.count (unitWindow d) ∂μ

theorem hasIntensity_of_stationary {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    [IsFiniteMeasureOnCompacts (meanCountingMeasure μ)] :
    HasIntensity μ (processIntensity μ) := by
  let := meanCountingMeasure_addInvariant μ hμ
  let κ : NNReal := Measure.addHaarScalarFactor (meanCountingMeasure μ) volume
  have hm : meanCountingMeasure μ = κ • volume :=
    Measure.isAddLeftInvariant_eq_smul (meanCountingMeasure μ) volume
  have hi : processIntensity μ = (κ : ℝ≥0∞) := by
    rw [processIntensity, ← meanCountingMeasure_apply μ (measurable_unitWindow d), hm]
    simp [volume_unitWindow]
  intro W hW
  rw [← meanCountingMeasure_apply μ hW, hm, hi]
  simp

theorem processIntensity_eq {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) :
    processIntensity μ = ρ := expected_count_unitWindow μ ρ hρ

theorem retained_meanCountingMeasure_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ) :
    meanCountingMeasure (μ.map (fun c => c.deleteClose r)) ≤ meanCountingMeasure μ := by
  apply Measure.le_iff.mpr
  intro W hW
  rw [meanCountingMeasure_apply _ hW, meanCountingMeasure_apply _ hW,
    lintegral_map (Configuration.measurable_count hW) (measurable_deleteClose r)]
  apply lintegral_mono
  intro c
  change Measure.count (globalKeptPoints c.support r ∩ W) ≤
    Measure.count (c.support ∩ W)
  apply measure_mono
  exact fun x hx => ⟨hx.1.1, hx.2⟩

theorem meanCountingMeasure_finiteOnCompacts_of_le {d : ℕ}
    (ν : Measure (Configuration (Ambient d))) {ρ : ℝ≥0∞} (hρ : ρ ≠ ∞)
    (hν : meanCountingMeasure ν ≤ ρ • volume) :
    IsFiniteMeasureOnCompacts (meanCountingMeasure ν) := by
  let := IsFiniteMeasureOnCompacts.smul (volume : Measure (Ambient d)) hρ
  refine ⟨fun K hK => ?_⟩
  exact (hν K).trans_lt hK.measure_lt_top

theorem retained_hasIntensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (r : ℝ) :
    HasIntensity (μ.map (fun c => c.deleteClose r))
      (processIntensity (μ.map (fun c => c.deleteClose r))) := by
  have hdom := (retained_meanCountingMeasure_le μ r).trans
    (meanCountingMeasure_eq_volume μ ρ hρ).le
  let := meanCountingMeasure_finiteOnCompacts_of_le _ hρtop hdom
  exact hasIntensity_of_stationary _ (stationary_deleteClose μ hμ r)

def Configuration.deletedClose {X : Type*} [PseudoMetricSpace X]
    (c : Configuration X) (r : ℝ) : Configuration X :=
  c.restrict (globalBadPoints c.support r)

@[simp] theorem Configuration.deletedClose_support {X : Type*} [PseudoMetricSpace X]
    (c : Configuration X) (r : ℝ) :
    (c.deletedClose r).support = globalBadPoints c.support r := by
  ext x
  change x ∈ c.support ∩ globalBadPoints c.support r ↔ x ∈ globalBadPoints c.support r
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

@[simp] theorem Configuration.deletedClose_count {d : ℕ}
    (c : Configuration (Ambient d)) (r : ℝ) (W : Set (Ambient d)) :
    (c.deletedClose r).count W = c.count (globalBadPoints c.support r ∩ W) := by
  change Measure.count ((c.support ∩ globalBadPoints c.support r) ∩ W) =
    Measure.count (c.support ∩ (globalBadPoints c.support r ∩ W))
  rw [Set.inter_assoc]

theorem measurable_deletedClose {d : ℕ} (r : ℝ) :
    Measurable (fun c : Configuration (Ambient d) => c.deletedClose r) := by
  apply Configuration.measurable_of_counts
  intro W hW
  simpa only [Configuration.deletedClose_count] using measurable_deletedCount r hW

theorem translate_deletedClose {d : ℕ} (a : Ambient d)
    (c : Configuration (Ambient d)) (r : ℝ) :
    translate a (c.deletedClose r) = (translate a c).deletedClose r := by
  apply Configuration.ext
  change (fun x : Ambient d => a + x) '' (c.deletedClose r).support =
    ((translate a c).deletedClose r).support
  rw [Configuration.deletedClose_support, Configuration.deletedClose_support]
  change (fun x : Ambient d => a + x) '' globalBadPoints c.support r =
    globalBadPoints ((fun x : Ambient d => a + x) '' c.support) r
  exact (badPoints_image_isometry _
    (Isometry.of_dist_eq fun x y => dist_add_left a x y)
    (fun _ _ h => add_left_cancel h) _ r).symm

theorem stationary_deletedClose {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (hμ : IsStationary μ) (r : ℝ) :
    IsStationary (μ.map (fun c => c.deletedClose r)) := by
  intro a
  refine ⟨measurable_translate a, ?_⟩
  have hm := measurable_deletedClose (d := d) r
  have hcomm : translate a ∘ (fun c : Configuration (Ambient d) => c.deletedClose r) =
      (fun c : Configuration (Ambient d) => c.deletedClose r) ∘ translate a := by
    funext c
    exact translate_deletedClose a c r
  rw [Measure.map_map (measurable_translate a) hm, hcomm,
    ← Measure.map_map hm (measurable_translate a), (hμ a).map_eq]

def StationaryPointProcess.deletedClose {d : ℕ} (Ξ : StationaryPointProcess d) (r : ℝ) :
    StationaryPointProcess d where
  law := Ξ.law.map (fun c => c.deletedClose r)
  probability := by
    have := Ξ.probability
    exact inferInstance
  stationary := stationary_deletedClose Ξ.law Ξ.stationary r

def retainedIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) (r : ℝ) : ℝ≥0∞ :=
  processIntensity (μ.map (fun c => c.deleteClose r))

def deletedIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) (r : ℝ) : ℝ≥0∞ :=
  processIntensity (μ.map (fun c => c.deletedClose r))

theorem retainedIntensity_eq_unitCount {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ) :
    retainedIntensity μ r = ∫⁻ c, (c.deleteClose r).count (unitWindow d) ∂μ := by
  rw [retainedIntensity, processIntensity,
    lintegral_map (Configuration.measurable_count (measurable_unitWindow d))
      (measurable_deleteClose r)]

theorem deletedIntensity_eq_unitCount {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ) :
    deletedIntensity μ r =
      ∫⁻ c, c.count (globalBadPoints c.support r ∩ unitWindow d) ∂μ := by
  rw [deletedIntensity, processIntensity,
    lintegral_map (Configuration.measurable_count (measurable_unitWindow d))
      (measurable_deletedClose r)]
  simp only [Configuration.deletedClose_count]

theorem deleted_meanCountingMeasure_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ) :
    meanCountingMeasure (μ.map (fun c => c.deletedClose r)) ≤ meanCountingMeasure μ := by
  apply Measure.le_iff.mpr
  intro W hW
  rw [meanCountingMeasure_apply _ hW, meanCountingMeasure_apply _ hW,
    lintegral_map (Configuration.measurable_count hW) (measurable_deletedClose r)]
  apply lintegral_mono
  intro c
  change (c.deletedClose r).count W ≤ c.count W
  rw [Configuration.deletedClose_count]
  change Measure.count (c.support ∩ (globalBadPoints c.support r ∩ W)) ≤
    Measure.count (c.support ∩ W)
  exact measure_mono fun _ hx => ⟨hx.1, hx.2.2⟩

theorem deleted_hasIntensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (r : ℝ) :
    HasIntensity (μ.map (fun c => c.deletedClose r)) (deletedIntensity μ r) := by
  have hdom := (deleted_meanCountingMeasure_le μ r).trans
    (meanCountingMeasure_eq_volume μ ρ hρ).le
  let := meanCountingMeasure_finiteOnCompacts_of_le _ hρtop hdom
  exact hasIntensity_of_stationary _ (stationary_deletedClose μ hμ r)

theorem expected_deletedCount_eq_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (r : ℝ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ) =
      deletedIntensity μ r * volume W := by
  have h := deleted_hasIntensity μ hμ ρ hρ hρtop r W hW
  rw [lintegral_map (Configuration.measurable_count hW) (measurable_deletedClose r)] at h
  simpa only [Configuration.deletedClose_count] using h

theorem expected_retainedCount_eq_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (r : ℝ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, (c.deleteClose r).count W ∂μ) = retainedIntensity μ r * volume W := by
  have h := retained_hasIntensity μ hμ ρ hρ hρtop r W hW
  rw [lintegral_map (Configuration.measurable_count hW) (measurable_deleteClose r)] at h
  exact h

theorem intensity_deletion_partition {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (r : ℝ) :
    ρ = retainedIntensity μ r + deletedIntensity μ r := by
  rw [retainedIntensity_eq_unitCount, deletedIntensity_eq_unitCount,
    ← expected_count_deletion_partition μ r (measurable_unitWindow d),
    expected_count_unitWindow μ ρ hρ]

theorem deletedIntensity_le_of_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (r : ℝ) (κ q : ℝ≥0∞)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q) :
    deletedIntensity μ r ≤ q / κ := by
  rw [deletedIntensity_eq_unitCount]
  exact expected_deletedCount_le_of_cost μ (measurable_unitWindow d) r κ q
    hκ0 hκtop V hV hcost

theorem retainedIntensity_lower_bound_of_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (r : ℝ) (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q) :
    ρ - q / κ ≤ retainedIntensity μ r := by
  apply tsub_le_iff_right.mpr
  rw [intensity_deletion_partition μ ρ hρ r]
  exact add_le_add le_rfl (deletedIntensity_le_of_cost μ r κ q hκ0 hκtop V hV hcost)

theorem retainedIntensity_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (r : ℝ) :
    retainedIntensity μ r ≤ ρ := by
  rw [intensity_deletion_partition μ ρ hρ r]
  exact le_add_right le_rfl

theorem deletedIntensity_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (r : ℝ) :
    deletedIntensity μ r ≤ ρ := by
  rw [intensity_deletion_partition μ ρ hρ r]
  exact le_add_left le_rfl

theorem expected_deletedCount_le_of_unit_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (r : ℝ) (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, c.count (globalBadPoints c.support r ∩ W) ∂μ) ≤ q / κ * volume W := by
  rw [expected_deletedCount_eq_intensity μ hμ ρ hρ hρtop r hW]
  gcongr
  exact deletedIntensity_le_of_cost μ r κ q hκ0 hκtop V hV hcost

theorem window_change_probability_le_of_unit_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (r : ℝ) (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    μ {c | (c.deleteClose r).support ∩ W ≠ c.support ∩ W} ≤ q / κ * volume W := by
  have hp := window_change_probability_le μ
    (fun c : Configuration (Ambient d) => c) W r (measurable_deletedCount r hW).aemeasurable
  have hb := expected_deletedCount_le_of_unit_cost μ hμ ρ hρ hρtop r κ q
    hκ0 hκtop V hV hcost hW
  exact hp.trans hb

theorem measurable_good_event_restoration_of_unit_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (Λ : Set (Ambient d)) (r R error loss : ℝ)
    (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q)
    (G : Set (Configuration (Ambient d))) (hG : MeasurableSet G)
    (hgood : G ⊆ {c | LocalCrystal Λ (c.deleteClose r) R error loss}) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧
      H ⊆ {c | LocalCrystal Λ c R error loss} ∧
      μ G - q / κ * volume (Metric.closedBall (0 : Ambient d) R) ≤ μ H := by
  obtain ⟨H, hm, hg, hb⟩ :=
    measurable_good_event_restoration_euclidean μ Λ r R error loss G hG hgood
  refine ⟨H, hm, hg, ?_⟩
  have he := expected_deletedCount_le_of_unit_cost
    (W := Metric.closedBall (0 : Ambient d) R) μ hμ ρ hρ hρtop r κ q
    hκ0 hκtop V hV hcost measurableSet_closedBall
  exact (tsub_le_tsub_left he _).trans hb

theorem retainedIntensity_toReal_lower_bound {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hρ : HasIntensity μ 1) (r : ℝ)
    (q : ℝ≥0∞) (hq : q ≠ ∞) (hdel : deletedIntensity μ r ≤ q) :
    1 - q.toReal ≤ (retainedIntensity μ r).toReal := by
  have hk := retainedIntensity_le μ 1 hρ r
  have hd := deletedIntensity_le μ 1 hρ r
  have hkfinite : retainedIntensity μ r ≠ ∞ := (hk.trans_lt (by norm_num)).ne
  have hdfinite : deletedIntensity μ r ≠ ∞ := (hd.trans_lt (by norm_num)).ne
  have he : (retainedIntensity μ r).toReal + (deletedIntensity μ r).toReal = 1 := by
    rw [← ENNReal.toReal_add hkfinite hdfinite, ← intensity_deletion_partition μ 1 hρ r]
    norm_num
  have hqreal := ENNReal.toReal_mono hq hdel
  linarith

end E8Leech
