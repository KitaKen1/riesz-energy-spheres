import E8Leech.DifferencePairTails

/-!
# Missing second-window pairs: a boundary layer plus a displacement tail

Reuse the already checked guarded observation-centre box with zero packing
guard. The same coordinate inequalities and Bernoulli volume estimate apply
to an arbitrary point configuration, without minimum-distance assumptions.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

def pairBoxBoundary (d : ℕ) (L R : ℝ) : Set (Ambient d) :=
  periodCell d L \ guardObservationCenters d L 0 R

theorem measurable_pairBoxBoundary (d : ℕ) (L R : ℝ) :
    MeasurableSet (pairBoxBoundary d L R) :=
  (measurable_periodCell d L).diff (measurable_guardObservationCenters d L 0 R)

theorem isBounded_pairBoxBoundary (d : ℕ) (L R : ℝ) :
    Bornology.IsBounded (pairBoxBoundary d L R) :=
  (isBounded_periodCell d L).subset sdiff_subset

theorem near_point_mem_periodCell {d : ℕ} (L R : ℝ)
    {x y : Ambient d} (hx : x ∈ guardObservationCenters d L 0 R)
    (hnear : ‖x - y‖ ≤ R) : y ∈ periodCell d L := by
  have hy : y ∈ Metric.closedBall x R := by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hnear
  have h := closedBall_subset_guardInnerBox L 0 R hx hy
  simpa only [guardInnerBox, periodCell, zero_div, sub_zero] using h

theorem real_pairBoxBoundary_ratio_le {d : ℕ} {L R : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L) (hw : 2 * R ≤ L) :
    (volume (pairBoxBoundary d L R)).toReal / (volume (periodCell d L)).toReal ≤
      (d : ℝ) * (2 * R) / L := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (guard_boundary_fraction_le (d := d) L 0 R (by norm_num) hR hL (by linarith))
  have hnonneg : 0 ≤ (d : ℝ) * (2 * R) / L := by positivity
  simpa only [pairBoxBoundary, ENNReal.toReal_div, zero_add,
    ENNReal.toReal_ofReal hnonneg] using h

theorem tendsto_pairBoxBoundary_ratio_zero (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ => (volume (pairBoxBoundary d ((n : ℝ) + 1) R)).toReal /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ n : ℕ in atTop, 2 * R ≤ (n : ℝ) + 1 :=
    hL.eventually (eventually_ge_atTop (2 * R))
  have ht : Tendsto (fun n : ℕ => (d : ℝ) * (2 * R) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (d : ℝ) * (2 * R))
      atTop (𝓝 ((d : ℝ) * (2 * R)))).div_atTop hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun n => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact hb.mono fun n hn => real_pairBoxBoundary_ratio_le hR (by positivity) hn

/-- Every missing pair is near the boundary or has displacement larger than R. -/
theorem localized_difference_pair_box_compl_le_boundary_add_tail {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (c : Configuration (Ambient d)) (L R : ℝ) :
    localizedPairIntegral (fun x y => V (x - y)) c (periodCell d L) (periodCell d L)ᶜ ≤
      localizedPairIntegral (fun x y => V (x - y)) c (pairBoxBoundary d L R) univ +
        localizedPairIntegral (fun x y => differenceTail V R (x - y)) c (periodCell d L) univ := by
  simp only [localizedPairIntegral_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : (x : Ambient d) ∈ periodCell d L
  · simp only [if_pos hx, mem_univ, if_true]
    by_cases hi : (x : Ambient d) ∈ guardObservationCenters d L 0 R
    · have hxb : (x : Ambient d) ∉ pairBoxBoundary d L R := fun h => h.2 hi
      simp only [if_neg hxb, zero_add]
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : (y : Ambient d) ∈ (periodCell d L)ᶜ
      · have hfar : R < ‖(x : Ambient d) - (y : Ambient d)‖ := by
          apply lt_of_not_ge
          intro hnear
          exact hy (near_point_mem_periodCell L R hi hnear)
        simp [hy, differenceTail, hfar]
      · simp [hy]
    · have hxb : (x : Ambient d) ∈ pairBoxBoundary d L R := ⟨hx, hi⟩
      simp only [if_pos hxb]
      apply le_add_of_le_left
      apply ENNReal.tsum_le_tsum
      intro y
      split_ifs <;> simp
  · have hxb : (x : Ambient d) ∉ pairBoxBoundary d L R := fun h => hx h.1
    simp [hx, hxb]

end E8Leech
