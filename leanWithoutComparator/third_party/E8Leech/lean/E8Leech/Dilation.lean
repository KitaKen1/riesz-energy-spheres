import E8Leech.StationaryIntensity
import E8Leech.Deletion
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilation of a stationary process and its intensity

Positive dilation increases the separation and divides intensity by the d-th
power of the scale. Applied after close-pair deletion, this is the density and
hard-core interface needed by guarded periodization.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

def dilationHomeomorph {d : ℕ} (a : ℝ) (ha : a ≠ 0) : Ambient d ≃ₜ Ambient d :=
  Homeomorph.smul (Units.mk0 a ha)

@[simp] theorem dilationHomeomorph_apply {d : ℕ} (a : ℝ) (ha : a ≠ 0) (x : Ambient d) :
    dilationHomeomorph a ha x = a • x := rfl

def Configuration.dilate {d : ℕ} (c : Configuration (Ambient d)) (a : ℝ) (ha : a ≠ 0) :
    Configuration (Ambient d) := c.mapHomeomorph (dilationHomeomorph a ha)

@[simp] theorem Configuration.dilate_support {d : ℕ}
    (c : Configuration (Ambient d)) (a : ℝ) (ha : a ≠ 0) :
    (c.dilate a ha).support = (fun x => a • x) '' c.support := rfl

@[simp] theorem Configuration.dilate_count {d : ℕ}
    (c : Configuration (Ambient d)) (a : ℝ) (ha : a ≠ 0) (W : Set (Ambient d)) :
    (c.dilate a ha).count W = c.count ((fun x => a • x) ⁻¹' W) := by
  exact Configuration.count_mapHomeomorph _ _ _

theorem measurable_dilate {d : ℕ} (a : ℝ) (ha : a ≠ 0) :
    Measurable (fun c : Configuration (Ambient d) => c.dilate a ha) :=
  Configuration.measurable_mapHomeomorph _

theorem dilate_translate {d : ℕ} (c : Configuration (Ambient d))
    (a : ℝ) (ha : a ≠ 0) (b : Ambient d) :
    (translate b c).dilate a ha = translate (a • b) (c.dilate a ha) := by
  apply Configuration.ext
  change (fun x => a • x) '' ((fun x => b + x) '' c.support) =
    (fun x => a • b + x) '' ((fun x => a • x) '' c.support)
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact smul_add a b x

theorem stationary_dilate {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (hμ : IsStationary μ) (a : ℝ) (ha : a ≠ 0) :
    IsStationary (μ.map (fun c => c.dilate a ha)) := by
  intro b
  refine ⟨measurable_translate b, ?_⟩
  have hm := measurable_dilate (d := d) a ha
  have hcomm : translate b ∘ (fun c : Configuration (Ambient d) => c.dilate a ha) =
      (fun c : Configuration (Ambient d) => c.dilate a ha) ∘ translate (a⁻¹ • b) := by
    funext c
    change translate b (c.dilate a ha) = (translate (a⁻¹ • b) c).dilate a ha
    simpa only [smul_inv_smul₀ ha] using (dilate_translate c a ha (a⁻¹ • b)).symm
  rw [Measure.map_map (measurable_translate b) hm, hcomm,
    ← Measure.map_map hm (measurable_translate (a⁻¹ • b)), (hμ _).map_eq]

def StationaryPointProcess.dilate {d : ℕ} (Ξ : StationaryPointProcess d)
    (a : ℝ) (ha : a ≠ 0) : StationaryPointProcess d where
  law := Ξ.law.map (fun c => c.dilate a ha)
  probability := by
    have := Ξ.probability
    exact inferInstance
  stationary := stationary_dilate Ξ.law Ξ.stationary a ha

theorem hasIntensity_dilate {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (a : ℝ) (ha : a ≠ 0) :
    HasIntensity (μ.map (fun c => c.dilate a ha))
      (ρ * ENNReal.ofReal |(a ^ d)⁻¹|) := by
  intro W hW
  rw [lintegral_map (Configuration.measurable_count hW) (measurable_dilate a ha)]
  simp_rw [Configuration.dilate_count]
  rw [hρ _ (hW.preimage (measurable_const_smul a)),
    Measure.addHaar_preimage_smul volume ha]
  have hdim : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
  rw [hdim, mul_assoc]

theorem dilate_separated {d : ℕ} (c : Configuration (Ambient d))
    (r a : ℝ) (ha : 0 < a)
    (hr : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    ∀ x ∈ (c.dilate a ha.ne').support, ∀ y ∈ (c.dilate a ha.ne').support,
      x ≠ y → a * r ≤ dist x y := by
  intro x hx y hy hne
  rw [Configuration.dilate_support] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have huv : u ≠ v := fun h => hne (congrArg (fun z => a • z) h)
  simpa only [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha] using
    mul_le_mul_of_nonneg_left (hr u hu v hv huv) ha.le

theorem dilated_deleteClose_separated {d : ℕ} (c : Configuration (Ambient d))
    (r a : ℝ) (ha : 0 < a) :
    ∀ x ∈ ((c.deleteClose r).dilate a ha.ne').support,
      ∀ y ∈ ((c.deleteClose r).dilate a ha.ne').support,
        x ≠ y → a * r ≤ dist x y := by
  apply dilate_separated (c.deleteClose r) r a ha
  intro x hx y hy hne
  exact globalKeptPoints_separated hx hy hne

def expandAfterDeletion {d : ℕ} (c : Configuration (Ambient d))
    (r₀ t : ℝ) (ht : t < 1) : Configuration (Ambient d) :=
  (c.deleteClose (r₀ * (1 - t))).dilate (1 - t)⁻¹
    (inv_ne_zero (ne_of_gt (sub_pos.mpr ht)))

theorem measurable_expandAfterDeletion {d : ℕ} (r₀ t : ℝ) (ht : t < 1) :
    Measurable (fun c : Configuration (Ambient d) => expandAfterDeletion c r₀ t ht) :=
  (measurable_dilate _ _).comp (measurable_deleteClose _)

theorem stationary_expandAfterDeletion {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (r₀ t : ℝ) (ht : t < 1) :
    IsStationary (μ.map (fun c => expandAfterDeletion c r₀ t ht)) := by
  change IsStationary (μ.map
    ((fun c : Configuration (Ambient d) => c.dilate (1 - t)⁻¹
      (inv_ne_zero (ne_of_gt (sub_pos.mpr ht)))) ∘
        (fun c => c.deleteClose (r₀ * (1 - t)))))
  rw [← Measure.map_map (measurable_dilate _ _) (measurable_deleteClose _)]
  exact stationary_dilate _ (stationary_deleteClose μ hμ _) _ _

theorem expandAfterDeletion_separated {d : ℕ}
    (c : Configuration (Ambient d)) (r₀ t : ℝ) (ht : t < 1) :
    ∀ x ∈ (expandAfterDeletion c r₀ t ht).support,
      ∀ y ∈ (expandAfterDeletion c r₀ t ht).support, x ≠ y → r₀ ≤ dist x y := by
  have ha : 0 < (1 - t)⁻¹ := inv_pos.mpr (sub_pos.mpr ht)
  have he : (1 - t)⁻¹ * (r₀ * (1 - t)) = r₀ := by
    field_simp [ne_of_gt (sub_pos.mpr ht)]
  simpa only [expandAfterDeletion, he] using
    dilated_deleteClose_separated c (r₀ * (1 - t)) (1 - t)⁻¹ ha

theorem hasIntensity_expandAfterDeletion {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (r₀ t : ℝ) (ht : t < 1) :
    HasIntensity (μ.map (fun c => expandAfterDeletion c r₀ t ht))
      (retainedIntensity μ (r₀ * (1 - t)) * ENNReal.ofReal ((1 - t) ^ d)) := by
  have h := hasIntensity_dilate (μ.map (fun c => c.deleteClose (r₀ * (1 - t))))
    (retainedIntensity μ (r₀ * (1 - t))) (retained_hasIntensity μ hμ ρ hρ hρtop _)
    (1 - t)⁻¹ (inv_ne_zero (ne_of_gt (sub_pos.mpr ht)))
  rw [Measure.map_map (measurable_dilate _ _) (measurable_deleteClose _)] at h
  have he : |(((1 - t)⁻¹) ^ d)⁻¹| = (1 - t) ^ d := by
    rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg (sub_pos.mpr ht).le d)]
  simpa only [Function.comp_def, expandAfterDeletion, he] using h

theorem expandedIntensity_eq {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (r₀ t : ℝ) (ht : t < 1) :
    processIntensity (μ.map (fun c => expandAfterDeletion c r₀ t ht)) =
      retainedIntensity μ (r₀ * (1 - t)) * ENNReal.ofReal ((1 - t) ^ d) :=
  processIntensity_eq _ _ (hasIntensity_expandAfterDeletion μ hμ ρ hρ hρtop r₀ t ht)

theorem contraction_power_lower_bound (d : ℕ) {t : ℝ} (ht : t ≤ 1) :
    1 - (d : ℝ) * t ≤ (1 - t) ^ d := by
  simpa only [mul_neg, ← sub_eq_add_neg] using
    one_add_mul_le_pow (a := -t) (by linarith) d

theorem density_after_expansion_lower_bound (d : ℕ) {ρ₁ q t : ℝ}
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁1 : ρ₁ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hρ₁ : 1 - q ≤ ρ₁) : 1 - q - (d : ℝ) * t ≤ ρ₁ * (1 - t) ^ d := by
  have hb := mul_le_mul_of_nonneg_left (contraction_power_lower_bound d ht1) hρ₁0
  have hd := mul_le_mul_of_nonneg_right hρ₁1 (mul_nonneg (Nat.cast_nonneg d) ht0)
  nlinarith

theorem expandedIntensity_lower_bound_of_deletedIntensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (r₀ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hdel : deletedIntensity μ (r₀ * (1 - t)) ≤ q) :
    1 - q.toReal - (d : ℝ) * t ≤
      (processIntensity (μ.map (fun c => expandAfterDeletion c r₀ t ht1))).toReal := by
  rw [expandedIntensity_eq μ hμ 1 hρ (by norm_num) r₀ t ht1,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (sub_pos.mpr ht1).le d)]
  apply density_after_expansion_lower_bound d ENNReal.toReal_nonneg
  · simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (retainedIntensity_le μ 1 hρ _)
  · exact ht0
  · exact ht1.le
  · exact retainedIntensity_toReal_lower_bound μ hρ _ q hq hdel

theorem expandedIntensity_lower_bound_of_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (r₀ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞) (hqtop : q ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r₀ * (1 - t) → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q) :
    1 - (q / κ).toReal - (d : ℝ) * t ≤
      (processIntensity (μ.map (fun c => expandAfterDeletion c r₀ t ht1))).toReal :=
  expandedIntensity_lower_bound_of_deletedIntensity μ hμ hρ r₀ t ht0 ht1 (q / κ)
    (ENNReal.div_ne_top hqtop hκ0)
    (deletedIntensity_le_of_cost μ _ κ q hκ0 hκtop V hV hcost)

theorem expandedIntensity_lower_bound_of_balanced_loss {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (r₀ t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (q : ℝ≥0∞) (hq : q ≠ ∞) (hdel : deletedIntensity μ (r₀ * (1 - t)) ≤ q)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ t ^ 3) (hbound : q.toReal ≤ C * (δ / t ^ 2)) :
    1 - (C + d) * t ≤
      (processIntensity (μ.map (fun c => expandAfterDeletion c r₀ t ht1))).toReal := by
  have hr := expandedIntensity_lower_bound_of_deletedIntensity μ hμ hρ r₀ t ht0.le ht1 q hq hdel
  have hqreal := deletion_loss ht0 hC hδ hbound
  nlinarith

end E8Leech
