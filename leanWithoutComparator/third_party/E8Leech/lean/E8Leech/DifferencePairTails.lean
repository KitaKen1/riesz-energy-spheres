import E8Leech.StationaryRealPairScaling
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Relative-displacement tails of full-second-endpoint point pairs

The cutoff depends on x-y, so simultaneous translation preserves it. Absolute
unit-anchor finiteness supplies a dominated convergence bound. For each sample
with finite full pair mass, the bounded first window gives a finite outer sum;
only the inner counting integral needs dominated convergence. Then apply it
once more over the original law. No new moment or independence premise.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

def differenceTail {d : ℕ} (V : Ambient d → ℝ≥0∞) (R : ℝ) (v : Ambient d) : ℝ≥0∞ :=
  if R < ‖v‖ then V v else 0

theorem measurable_differenceTail {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (R : ℝ) :
    Measurable (differenceTail V R) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) hV measurable_const

theorem differenceTail_le {d : ℕ} (V : Ambient d → ℝ≥0∞) (R : ℝ) (v : Ambient d) :
    differenceTail V R v ≤ V v := by
  unfold differenceTail
  split_ifs <;> simp

theorem tendsto_differenceTail_zero {d : ℕ} (V : Ambient d → ℝ≥0∞) (v : Ambient d) :
    Tendsto (fun n : ℕ => differenceTail V (n : ℝ) v) atTop (𝓝 0) := by
  have he : (fun n : ℕ => differenceTail V (n : ℝ) v) =ᶠ[atTop] fun _ => 0 := by
    have hb : ∀ᶠ n : ℕ in atTop, ‖v‖ ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop ‖v‖)
    filter_upwards [hb] with n hn
    simp [differenceTail, not_lt_of_ge hn]
  exact tendsto_const_nhds.congr' he.symm

theorem tendsto_localized_differenceTail_zero_of_finite {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hfinite : localizedPairIntegral (fun x y => V (x - y)) c W univ ≠ ∞) :
    Tendsto (fun n : ℕ => localizedPairIntegral
      (fun x y => differenceTail V (n : ℝ) (x - y)) c W univ) atTop (𝓝 0) := by
  rw [localizedPairIntegral_eq_outer_sum _ c hW hbW univ] at hfinite
  simp only [Set.indicator_univ] at hfinite
  have ht (x : Ambient d) (hx : x ∈ windowPointFinset c W hbW) :
      Tendsto (fun n : ℕ => ∫⁻ y, differenceTail V (n : ℝ) (x - y) ∂countingKernel d c)
        atTop (𝓝 0) := by
    have hf : (∫⁻ y, V (x - y) ∂countingKernel d c) ≠ ∞ :=
      (ENNReal.sum_ne_top.mp hfinite) x hx
    have hm : Measurable (fun y : Ambient d => x - y) :=
      measurable_const.sub measurable_id
    have h := tendsto_lintegral_of_dominated_convergence (μ := countingKernel d c)
      (F := fun n y => differenceTail V (n : ℝ) (x - y)) (f := fun _ => 0)
      (fun y => V (x - y))
      (fun n => (measurable_differenceTail V hV (n : ℝ)).comp hm)
      (fun n => ae_of_all _ fun y => differenceTail_le V (n : ℝ) (x - y)) hf
      (ae_of_all _ fun y => tendsto_differenceTail_zero V (x - y))
    simpa only [lintegral_zero] using h
  have hsum := tendsto_finsetSum (windowPointFinset c W hbW) ht
  simpa only [localizedPairIntegral_eq_outer_sum _ c hW hbW univ,
    Set.indicator_univ, Finset.sum_const_zero] using hsum

theorem expected_differenceTail_ne_top_of_full {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → ℝ≥0∞)
    (W : Set (Ambient d))
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ) ≠ ∞)
    (R : ℝ) :
    (∫⁻ c, localizedPairIntegral (fun x y => differenceTail V R (x - y)) c W univ ∂μ) ≠ ∞ := by
  exact ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_mono c W univ
    (fun x _ y _ => differenceTail_le V R (x - y))).trans_lt hfinite.lt_top)

theorem tendsto_expected_differenceTail_zero_of_full {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ) ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ c, localizedPairIntegral
      (fun x y => differenceTail V (n : ℝ) (x - y)) c W univ ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (f := fun _ => 0)
    (fun c => localizedPairIntegral (fun x y => V (x - y)) c W univ)
    (fun n => measurable_localizedPairIntegral (V := fun x y => differenceTail V (n : ℝ) (x - y))
      ((measurable_differenceTail V hV (n : ℝ)).comp (measurable_fst.sub measurable_snd))
      hW MeasurableSet.univ)
    (fun n => ae_of_all _ fun c => localizedPairIntegral_mono c W univ
      (fun x _ y _ => differenceTail_le V (n : ℝ) (x - y))) hfinite ?_
  · simpa only [lintegral_zero] using h
  · filter_upwards [ae_lt_top (measurable_localizedPairIntegral (V := fun x y => V (x - y))
      (hV.comp (measurable_fst.sub measurable_snd)) hW MeasurableSet.univ) hfinite] with c hc
    exact tendsto_localized_differenceTail_zero_of_finite V hV c hW hbW hc.ne

end E8Leech
