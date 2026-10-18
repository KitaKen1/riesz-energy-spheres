import E8Leech.ContinuousWindowSpectral
import E8Leech.GuardedPeriodization

/-!
# Exact overlap volumes and the expanding-box overlap limit

The LP averaging window may be a half-open coordinate box, independently of the
ball in the final crystallization conclusion. Its translate overlap has an exact
product formula. The normalized overlap converges pointwise to one and lies in
[0,1], supplying the deterministic dominated-convergence geometry.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

def coordinateRectangle {d : ℕ} (lo hi : Fin d → ℝ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Ico (lo i) (hi i)}

theorem measurable_coordinateRectangle {d : ℕ} (lo hi : Fin d → ℝ) :
    MeasurableSet (coordinateRectangle lo hi) := by
  have he : coordinateRectangle lo hi = ⋂ i : Fin d,
      (fun x : Ambient d => x i) ⁻¹' Ico (lo i) (hi i) := by
    ext x
    simp [coordinateRectangle]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable

theorem isBounded_coordinateRectangle {d : ℕ} (lo hi : Fin d → ℝ) :
    Bornology.IsBounded (coordinateRectangle lo hi) := by
  let Q : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Icc (lo i) (hi i)}
  have hQ : IsCompact Q := isCompact_pi_infinite fun _ => isCompact_Icc
  have hK : IsCompact ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Q) :=
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr hQ
  apply hK.isBounded.subset
  intro x hx
  exact fun i => ⟨(hx i).1, (hx i).2.le⟩

theorem volume_coordinateRectangle {d : ℕ} (lo hi : Fin d → ℝ) :
    volume (coordinateRectangle lo hi) = ∏ i, ENNReal.ofReal (hi i - lo i) := by
  let Q : Set (Fin d → ℝ) := Set.pi univ (fun i => Ico (lo i) (hi i))
  have hQ : MeasurableSet Q := MeasurableSet.pi (Set.to_countable univ)
    (fun _ _ => measurableSet_Ico)
  have he : coordinateRectangle lo hi = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' Q := by
    ext x
    simp [coordinateRectangle, Q, Set.mem_pi]
  rw [he, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hQ.nullMeasurableSet]
  exact Real.volume_pi_Ico

theorem isBounded_periodCell (d : ℕ) (L : ℝ) : Bornology.IsBounded (periodCell d L) :=
  isBounded_coordinateRectangle (fun _ => 0) (fun _ => L)

def boxOverlap {d : ℕ} (L : ℝ) (v : Ambient d) : Set (Ambient d) :=
  periodCell d L ∩ (fun x => x - v) ⁻¹' periodCell d L

theorem measurable_boxOverlap {d : ℕ} (L : ℝ) (v : Ambient d) :
    MeasurableSet (boxOverlap L v) :=
  (measurable_periodCell d L).inter
    ((measurable_periodCell d L).preimage (continuous_id.sub continuous_const).measurable)

theorem boxOverlap_eq_rectangle {d : ℕ} (L : ℝ) (v : Ambient d) :
    boxOverlap L v = coordinateRectangle (fun i => max 0 (v i)) (fun i => min L (L + v i)) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < L) ∧ (∀ i, 0 ≤ (x - v) i ∧ (x - v) i < L)) ↔
    ∀ i, max 0 (v i) ≤ x i ∧ x i < min L (L + v i)
  simp only [PiLp.sub_apply, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨hx, hy⟩ i
    exact ⟨⟨(hx i).1, by linarith [(hy i).1]⟩, ⟨(hx i).2, by linarith [(hy i).2]⟩⟩
  · intro h
    exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩,
      fun i => ⟨by linarith [(h i).1.2], by linarith [(h i).2.2]⟩⟩

theorem overlap_coordinate_length (L a : ℝ) : min L (L + a) - max 0 a = L - |a| := by
  by_cases ha : 0 ≤ a
  · rw [min_eq_left (by linarith), max_eq_right ha, abs_of_nonneg ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [min_eq_right (by linarith), max_eq_left ha', abs_of_nonpos ha']
    ring

theorem volume_boxOverlap {d : ℕ} (L : ℝ) (v : Ambient d) :
    volume (boxOverlap L v) = ∏ i, ENNReal.ofReal (L - |v i|) := by
  rw [boxOverlap_eq_rectangle, volume_coordinateRectangle]
  congr 1
  funext i
  rw [overlap_coordinate_length]

theorem real_volume_boxOverlap {d : ℕ} (L : ℝ) (v : Ambient d) :
    (volume (boxOverlap L v)).toReal = ∏ i, max (L - |v i|) 0 := by
  rw [volume_boxOverlap, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal']

def boxOverlapRatio {d : ℕ} (L : ℝ) (v : Ambient d) : ℝ :=
  (volume (boxOverlap L v)).toReal / (volume (periodCell d L)).toReal

theorem boxOverlapRatio_eq_product {d : ℕ} {L : ℝ} (hL : 0 < L) (v : Ambient d) :
    boxOverlapRatio L v = ∏ i : Fin d, max (1 - |v i| / L) 0 := by
  rw [boxOverlapRatio, real_volume_boxOverlap, volume_periodCell, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hL.le]
  have hden : L ^ d = ∏ _ : Fin d, L := by simp
  rw [hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← max_div_div_right hL.le, zero_div]
  congr 1
  field_simp

theorem boxOverlapRatio_nonneg {d : ℕ} (L : ℝ) (v : Ambient d) : 0 ≤ boxOverlapRatio L v := by
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem boxOverlapRatio_le_one {d : ℕ} {L : ℝ} (hL : 0 < L) (v : Ambient d) :
    boxOverlapRatio L v ≤ 1 := by
  rw [boxOverlapRatio_eq_product hL]
  apply Finset.prod_le_one₀
  · intro i _
    exact le_max_right _ _
  · intro i _
    apply max_le
    · have hn := div_nonneg (abs_nonneg (v i)) hL.le
      linarith
    · norm_num

theorem continuous_boxOverlapRatio {d : ℕ} {L : ℝ} (hL : 0 < L) :
    Continuous (@boxOverlapRatio d L) := by
  have he : boxOverlapRatio (d := d) L = fun v => ∏ i : Fin d, max (1 - |v i| / L) 0 :=
    funext (boxOverlapRatio_eq_product hL)
  rw [he]
  fun_prop

theorem tendsto_boxOverlapRatio {d : ℕ} (v : Ambient d) :
    Tendsto (fun n : ℕ => boxOverlapRatio ((n : ℝ) + 1) v) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have he : (fun n : ℕ => boxOverlapRatio ((n : ℝ) + 1) v) =
      fun n : ℕ => ∏ i : Fin d, max (1 - |v i| / ((n : ℝ) + 1)) 0 := by
    funext n
    exact boxOverlapRatio_eq_product (by positivity) v
  rw [he]
  have hc (i : Fin d) : Tendsto (fun n : ℕ => max (1 - |v i| / ((n : ℝ) + 1)) 0)
      atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ => |v i| / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => |v i|) atTop (𝓝 |v i|)).div_atTop ht
    have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdiv
    simpa only [sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)] using
      hsub.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa using tendsto_finsetProd Finset.univ (fun i _ => hc i)

end E8Leech
