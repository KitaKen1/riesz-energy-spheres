import E8Leech.Dilation
import E8Leech.Target

/-!
# Returning a local lattice approximation to the original scale

Inverse dilation is not an isometry. Re-anchor the finite lattice patch at one of
its lattice points and adjust only the translation of the witnessing isometry.
The resulting additional error depends on the window radius, not on the original
translation vector. No classification of Euclidean isometries is needed.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def anchoredIsometry {d : ℕ} (Φ : Ambient d ≃ᵢ Ambient d)
    (z₀ : Ambient d) (b : ℝ) : Ambient d ≃ᵢ Ambient d :=
  (IsometryEquiv.addRight z₀).trans
    (Φ.trans (IsometryEquiv.addRight (b • Φ z₀ - Φ z₀)))

@[simp] theorem anchoredIsometry_apply {d : ℕ} (Φ : Ambient d ≃ᵢ Ambient d)
    (z₀ w : Ambient d) (b : ℝ) :
    anchoredIsometry Φ z₀ b w = Φ (w + z₀) - Φ z₀ + b • Φ z₀ := by
  change Φ (w + z₀) + (b • Φ z₀ - Φ z₀) = _
  abel

theorem anchoredIsometry_distance {d : ℕ} (Φ : Ambient d ≃ᵢ Ambient d)
    (z₀ z : Ambient d) (b : ℝ) :
    dist (b • Φ z) (anchoredIsometry Φ z₀ b (z - z₀)) =
      |b - 1| * ‖Φ z - Φ z₀‖ := by
  rw [anchoredIsometry_apply, sub_add_cancel, dist_eq_norm]
  have he : b • Φ z - (Φ z - Φ z₀ + b • Φ z₀) = (b - 1) • (Φ z - Φ z₀) := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [he, norm_smul, Real.norm_eq_abs]

theorem dilation_mem_closedBall_zero {d : ℕ} (a : ℝ) (ha : 0 < a)
    (R : ℝ) (x : Ambient d) :
    a • x ∈ Metric.closedBall 0 (a * R) ↔ x ∈ Metric.closedBall 0 R := by
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  exact mul_le_mul_iff_right₀ ha

theorem count_dilate_closedBall {d : ℕ} (c : Configuration (Ambient d))
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    (c.dilate a ha.ne').count (Metric.closedBall 0 (a * R)) =
      c.count (Metric.closedBall 0 R) := by
  rw [Configuration.dilate_count]
  congr 1
  ext x
  exact dilation_mem_closedBall_zero a ha R x

theorem inverse_dilation_distance {d : ℕ} (a : ℝ) (ha : 0 < a)
    (x y : Ambient d) :
    dist x (a⁻¹ • y) = a⁻¹ * dist (a • x) y := by
  calc
    dist x (a⁻¹ • y) = dist (a⁻¹ • (a • x)) (a⁻¹ • y) := by
      rw [inv_smul_smul₀ ha.ne']
    _ = _ := by rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]

def scaleRestorationError (a R error : ℝ) : ℝ :=
  a⁻¹ * error + 2 * |a⁻¹ - 1| * (a * R + error)

theorem localCrystal_mono_error {d : ℕ} {Λ : Set (Ambient d)}
    {c : Configuration (Ambient d)} {R error error' loss : ℝ}
    (hgood : LocalCrystal Λ c R error loss) (he : error ≤ error') :
    LocalCrystal Λ c R error' loss := by
  obtain ⟨⟨Φ, Z, hZ, hf, hb⟩, hc⟩ := hgood
  refine ⟨⟨Φ, Z, hZ, ?_, ?_⟩, hc⟩
  · intro x hx
    obtain ⟨z, hz, hd⟩ := hf x hx
    exact ⟨z, hz, hd.trans he⟩
  · intro z hz
    obtain ⟨x, hx, hd⟩ := hb z hz
    exact ⟨x, hx, hd.trans he⟩

theorem localCrystal_of_dilate {d : ℕ} (Λ : Set (Ambient d))
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (c : Configuration (Ambient d)) (a : ℝ) (ha : 1 ≤ a)
    (R error loss : ℝ) (hR : 0 ≤ R)
    (hgood : LocalCrystal Λ (c.dilate a (by linarith)) (a * R) error loss) :
    LocalCrystal Λ c R (scaleRestorationError a R error) loss := by
  have ha0 : 0 < a := by linarith
  obtain ⟨⟨Φ, Z, hZ, hf, hb⟩, hc⟩ := hgood
  refine ⟨?_, ?_⟩
  · by_cases hne : Z.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      let Z' := Z.image (fun z => z - z₀)
      let Ψ := anchoredIsometry Φ z₀ a⁻¹
      have hn : ∀ z ∈ Z, ‖Φ z‖ ≤ a * R + error := by
        intro z hz
        obtain ⟨x, hx, hd⟩ := hb z hz
        have hxR := Metric.mem_closedBall.mp hx.2
        calc
          ‖Φ z‖ ≤ dist (Φ z) x + dist x 0 := by
            simpa only [dist_zero_right] using dist_triangle (Φ z) x 0
          _ ≤ error + a * R := add_le_add hd hxR
          _ = _ := add_comm _ _
      have hanchor : ∀ z ∈ Z, dist (a⁻¹ • Φ z) (Ψ (z - z₀)) ≤
          2 * |a⁻¹ - 1| * (a * R + error) := by
        intro z hz
        have hnorm : ‖Φ z - Φ z₀‖ ≤ 2 * (a * R + error) :=
          (norm_sub_le _ _).trans (by linarith [hn z hz, hn z₀ hz₀])
        rw [anchoredIsometry_distance]
        simpa only [mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_left hnorm (abs_nonneg (a⁻¹ - 1))
      refine ⟨Ψ, Z', ?_, ?_, ?_⟩
      · intro w hw
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
        exact hΛ z (hZ hz) z₀ (hZ hz₀)
      · intro x hx
        have hax : a • x ∈ (c.dilate a ha0.ne').support ∩
            Metric.closedBall 0 (a * R) :=
          ⟨⟨x, hx.1, rfl⟩, (dilation_mem_closedBall_zero a ha0 R x).mpr hx.2⟩
        obtain ⟨z, hz, hd⟩ := hf (a • x) hax
        refine ⟨z - z₀, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
        have hd' : dist x (a⁻¹ • Φ z) ≤ a⁻¹ * error := by
          rw [inverse_dilation_distance a ha0]
          exact mul_le_mul_of_nonneg_left hd (inv_pos.mpr ha0).le
        exact (dist_triangle x (a⁻¹ • Φ z) (Ψ (z - z₀))).trans
          (add_le_add hd' (hanchor z hz))
      · intro w hw
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨x, hx, hd⟩ := hb z hz
        rw [Configuration.dilate_support] at hx
        obtain ⟨y, hy, rfl⟩ := hx.1
        have hyR := (dilation_mem_closedBall_zero a ha0 R y).mp hx.2
        refine ⟨y, ⟨hy, hyR⟩, ?_⟩
        have hd' : dist (a⁻¹ • Φ z) y ≤ a⁻¹ * error := by
          rw [dist_comm, inverse_dilation_distance a ha0, dist_comm (a • y)]
          exact mul_le_mul_of_nonneg_left hd (inv_pos.mpr ha0).le
        have hd'' : dist (Ψ (z - z₀)) (a⁻¹ • Φ z) ≤
            2 * |a⁻¹ - 1| * (a * R + error) := by
          rw [dist_comm]
          exact hanchor z hz
        have ht := (dist_triangle (Ψ (z - z₀)) (a⁻¹ • Φ z) y).trans
          (add_le_add hd'' hd')
        simpa only [scaleRestorationError, add_comm] using ht
    · refine ⟨Φ, ∅, by simp, ?_, by simp⟩
      intro x hx
      have hax : a • x ∈ (c.dilate a ha0.ne').support ∩
          Metric.closedBall 0 (a * R) :=
        ⟨⟨x, hx.1, rfl⟩, (dilation_mem_closedBall_zero a ha0 R x).mpr hx.2⟩
      obtain ⟨z, hz, _⟩ := hf (a • x) hax
      exact False.elim (hne ⟨z, hz⟩)
  · rw [← count_dilate_closedBall c a ha0 R]
    refine le_trans ?_ hc
    have hball : Metric.closedBall (0 : Ambient d) R ⊆ Metric.closedBall 0 (a * R) :=
      Metric.closedBall_subset_closedBall (by nlinarith)
    gcongr

theorem scaleRestorationError_le {t R error : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hR : 0 ≤ R) (he : 0 ≤ error) :
    scaleRestorationError (1 - t)⁻¹ R error ≤ 2 * error + 4 * t * R := by
  have hpos : 0 < 1 - t := by linarith
  have ha : (1 - t)⁻¹ ≤ 2 :=
    (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num; linarith)
  have habs : |(1 - t) - 1| = t := by
    rw [abs_of_nonpos (by linarith : (1 - t) - 1 ≤ 0)]
    ring
  have hm := mul_le_mul_of_nonneg_right ha hR
  have hm' := mul_le_mul_of_nonneg_left hm ht0
  have he' := mul_le_mul_of_nonneg_right (by linarith : t ≤ 1) he
  simp only [scaleRestorationError, inv_inv, habs]
  nlinarith

theorem localCrystal_of_expandAfterDeletion {d : ℕ} (Λ : Set (Ambient d))
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (c : Configuration (Ambient d)) (r₀ t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (R error loss : ℝ) (hR : 0 ≤ R) (he : 0 ≤ error)
    (hgood : LocalCrystal Λ (expandAfterDeletion c r₀ t (by linarith))
      ((1 - t)⁻¹ * R) error loss) :
    LocalCrystal Λ (c.deleteClose (r₀ * (1 - t))) R (2 * error + 4 * t * R) loss := by
  have ha : 1 ≤ (1 - t)⁻¹ :=
    (one_le_inv₀ (by linarith : 0 < 1 - t)).mpr (by linarith)
  have h := localCrystal_of_dilate Λ hΛ (c.deleteClose (r₀ * (1 - t)))
    (1 - t)⁻¹ ha R error loss hR hgood
  exact localCrystal_mono_error h (scaleRestorationError_le ht0 ht hR he)

theorem measurable_good_event_scale_restoration {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (Λ : Set (Ambient d))
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r₀ t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (R error loss : ℝ) (hR : 0 ≤ R) (he : 0 ≤ error)
    (G : Set (Configuration (Ambient d))) (hG : MeasurableSet G)
    (hgood : G ⊆ {c | LocalCrystal Λ c ((1 - t)⁻¹ * R) error loss}) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧
      H ⊆ {c | LocalCrystal Λ (c.deleteClose (r₀ * (1 - t)))
        R (2 * error + 4 * t * R) loss} ∧
      μ H = (μ.map (fun c => expandAfterDeletion c r₀ t (by linarith))) G := by
  let f : Configuration (Ambient d) → Configuration (Ambient d) :=
    fun c => expandAfterDeletion c r₀ t (by linarith)
  have hf : Measurable f := measurable_expandAfterDeletion r₀ t _
  refine ⟨f ⁻¹' G, hG.preimage hf, ?_, ?_⟩
  · intro c hc
    exact localCrystal_of_expandAfterDeletion Λ hΛ c r₀ t ht0 ht R error loss hR he
      (hgood hc)
  · exact (Measure.map_apply hf hG).symm

theorem measurable_good_event_expansion_restoration_of_unit_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r₀ t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (R error loss : ℝ) (hR : 0 ≤ R) (he : 0 ≤ error)
    (κ q : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r₀ * (1 - t) → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ q)
    (G : Set (Configuration (Ambient d))) (hG : MeasurableSet G)
    (hgood : G ⊆ {c | LocalCrystal Λ c ((1 - t)⁻¹ * R) error loss}) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧
      H ⊆ {c | LocalCrystal Λ c R (2 * error + 4 * t * R) loss} ∧
      (μ.map (fun c => expandAfterDeletion c r₀ t (by linarith))) G -
        q / κ * volume (Metric.closedBall (0 : Ambient d) R) ≤ μ H := by
  obtain ⟨F, hF, hFg, hFm⟩ :=
    measurable_good_event_scale_restoration μ Λ hΛ r₀ t ht0 ht R error loss hR he G hG hgood
  obtain ⟨H, hH, hHg, hHm⟩ :=
    measurable_good_event_restoration_of_unit_cost μ hμ ρ hρ hρtop Λ
      (r₀ * (1 - t)) R (2 * error + 4 * t * R) loss κ q hκ0 hκtop V hV hcost F hF hFg
  exact ⟨H, hH, hHg, by simpa only [hFm] using hHm⟩

end E8Leech
