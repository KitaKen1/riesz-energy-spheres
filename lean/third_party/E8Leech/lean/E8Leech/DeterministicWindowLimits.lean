import E8Leech.BoxOverlap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The normalized deterministic box pair integral tends to the full kernel integral

The actual double volume integral is first identified with the translate-overlap
integral by a dominated Fubini calculation. The exact box overlap ratio then
converges to one, bounded by one, so an L1 kernel gives the large-window limit.
This resolves the deterministic reference term of finite-window spectral LP;
the original-law anchored pair limit is a separate obligation.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

def windowOverlapVolume {d : ℕ} (W : Set (Ambient d)) (v : Ambient d) : ℝ :=
  (volume (W ∩ (fun x => x - v) ⁻¹' W)).toReal

theorem integral_window_overlap_indicator {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (v : Ambient d) :
    (∫ x in W, W.indicator (fun _ : Ambient d => (1 : ℝ)) (x - v)) = windowOverlapVolume W v := by
  rw [← integral_indicator hW]
  have he : W.indicator (fun x => W.indicator (fun _ : Ambient d => (1 : ℝ)) (x - v)) =
      (W ∩ (fun x => x - v) ⁻¹' W).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ W <;> by_cases hv : x - v ∈ W <;> simp [hx, hv]
  rw [he]
  have hm : Measurable (fun x : Ambient d => x - v) := measurable_id.sub_const v
  have hi := integral_indicator_const (μ := volume) (1 : ℝ) (hW.inter (hW.preimage hm))
  simpa only [windowOverlapVolume, Measure.real, smul_eq_mul, mul_one] using hi

theorem integrable_window_difference_product {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun p : Ambient d × Ambient d =>
      h p.1 * W.indicator (fun _ : Ambient d => (1 : ℝ)) (p.2 - p.1))
      (volume.prod (volume.restrict W)) := by
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hbW.measure_lt_top⟩
  have hm : Measurable (fun p : Ambient d × Ambient d =>
      W.indicator (fun _ : Ambient d => (1 : ℝ)) (p.2 - p.1)) :=
    (measurable_const.indicator hW).comp (measurable_snd.sub measurable_fst)
  apply (hh.norm.mul_prod (integrable_const (1 : ℝ))).mono'
    (hh.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable)
  filter_upwards with p
  change ‖h p.1 * W.indicator (fun _ : Ambient d => (1 : ℝ)) (p.2 - p.1)‖ ≤ ‖h p.1‖ * 1
  by_cases hx : p.2 - p.1 ∈ W <;> simp [hx]

theorem integral_window_difference_eq_overlap {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ x in W, ∫ y in W, h (x - y)) = ∫ v, h v * windowOverlapVolume W v := by
  have hp := integrable_window_difference_product h hh hW hbW
  calc
    _ = ∫ x in W, ∫ v, h v * W.indicator (fun _ : Ambient d => (1 : ℝ)) (x - v) := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        _ = ∫ y, W.indicator (fun y => h (x - y)) y := (integral_indicator hW).symm
        _ = ∫ v, W.indicator (fun y => h (x - y)) (x - v) :=
          (integral_sub_left_eq_self _ volume x).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with v
          by_cases hv : x - v ∈ W <;> simp [hv]
    _ = ∫ v, ∫ x in W, h v * W.indicator (fun _ : Ambient d => (1 : ℝ)) (x - v) :=
      (integral_integral_swap hp).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with v
      rw [integral_const_mul, integral_window_overlap_indicator hW v]

theorem integrable_overlap_weighted_kernel {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun v => h v * windowOverlapVolume W v) volume := by
  have hi := (integrable_window_difference_product h hh hW hbW).integral_prod_left
  apply hi.congr
  filter_upwards with v
  rw [integral_const_mul, integral_window_overlap_indicator hW v]

theorem normalized_box_pair_eq_overlap_ratio {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) (L : ℝ) :
    (∫ x in periodCell d L, ∫ y in periodCell d L, h (x - y)) /
      (volume (periodCell d L)).toReal = ∫ v, h v * boxOverlapRatio L v := by
  rw [integral_window_difference_eq_overlap h hh (measurable_periodCell d L)
    (isBounded_periodCell d L), ← integral_div]
  apply integral_congr_ae
  filter_upwards with v
  simp only [boxOverlapRatio, boxOverlap, windowOverlapVolume]
  ring

theorem integrable_kernel_boxOverlapRatio {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) {L : ℝ} (hL : 0 < L) :
    Integrable (fun v => h v * boxOverlapRatio L v) volume := by
  apply hh.norm.mono' (hh.aestronglyMeasurable.mul
    (continuous_boxOverlapRatio hL).aestronglyMeasurable)
  filter_upwards with v
  change ‖h v * boxOverlapRatio L v‖ ≤ ‖h v‖
  rw [norm_mul, Real.norm_eq_abs (boxOverlapRatio L v), abs_of_nonneg (boxOverlapRatio_nonneg L v)]
  exact mul_le_of_le_one_right (norm_nonneg _) (boxOverlapRatio_le_one hL v)

theorem tendsto_integral_kernel_boxOverlapRatio {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) :
    Tendsto (fun n : ℕ => ∫ v, h v * boxOverlapRatio ((n : ℝ) + 1) v)
      atTop (𝓝 (∫ v, h v)) := by
  apply tendsto_integral_of_dominated_convergence (fun v => ‖h v‖)
  · intro n
    exact (integrable_kernel_boxOverlapRatio h hh (by positivity)).aestronglyMeasurable
  · exact hh.norm
  · intro n
    filter_upwards with v
    rw [norm_mul, Real.norm_eq_abs (boxOverlapRatio _ v), abs_of_nonneg (boxOverlapRatio_nonneg _ v)]
    exact mul_le_of_le_one_right (norm_nonneg _) (boxOverlapRatio_le_one (by positivity) v)
  · filter_upwards with v
    simpa only [mul_one] using tendsto_const_nhds.mul (tendsto_boxOverlapRatio v)

theorem tendsto_normalized_box_pair_integral {d : ℕ}
    (h : Ambient d → ℝ) (hh : Integrable h volume) :
    Tendsto (fun n : ℕ => (∫ x in periodCell d ((n : ℝ) + 1),
      ∫ y in periodCell d ((n : ℝ) + 1), h (x - y)) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop (𝓝 (∫ v, h v)) := by
  simpa only [normalized_box_pair_eq_overlap_ratio h hh] using
    tendsto_integral_kernel_boxOverlapRatio h hh

theorem tendsto_normalized_spectral_window_square {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hh : Integrable (realSpectralKernel ν g) volume) :
    Tendsto (fun n : ℕ => (∫ ξ, g ξ * Complex.normSq
      (∫ x, (periodCell d ((n : ℝ) + 1)).indicator (spectralPhase ξ) x) ∂ν) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal)
      atTop (𝓝 (∫ v, realSpectralKernel ν g v)) := by
  simpa only [spectral_window_square_eq_real_volume_pair ν g hg
    (measurable_periodCell _ _) (isBounded_periodCell _ _)] using
    tendsto_normalized_box_pair_integral (realSpectralKernel ν g) hh

end E8Leech
