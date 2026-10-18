import E8Leech.RapidDecayVolume
import E8Leech.StationaryIntensity
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The original-law expected full-second-endpoint pair measure

Weight each counting measure by its full second-endpoint nonnegative difference
sum, then bind over the law. The existing parameter counting-integral machinery
constructs the kernel without measurable enumeration or a globally SFinite
counting-kernel assumption. Stationarity makes its mean measure translation
invariant. Local finiteness of this mean is proved separately from original energy.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

def pairAnchorWeight {d : ℕ} (V : Ambient d → ℝ≥0∞)
    (c : Configuration (Ambient d)) (x : Ambient d) : ℝ≥0∞ :=
  ∫⁻ y, V (x - y) ∂countingKernel d c

theorem measurable_pairAnchorWeight_joint {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) :
    Measurable (fun p : Configuration (Ambient d) × Ambient d => pairAnchorWeight V p.1 p.2) := by
  exact measurable_countingKernel_lintegral_param
    (fun p : Configuration (Ambient d) × Ambient d => p.1) measurable_fst
    (hV.comp (measurable_fst.snd.sub measurable_snd))

theorem localized_difference_pair_univ_eq_weight {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    localizedPairIntegral (fun x y => V (x - y)) c W univ =
      ∫⁻ x, W.indicator (pairAnchorWeight V c) x ∂countingKernel d c := by
  simp only [localizedPairIntegral, mem_univ, if_true]
  rfl

theorem pairAnchorWeight_measure_apply {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (countingKernel d c).withDensity (pairAnchorWeight V c) W =
      localizedPairIntegral (fun x y => V (x - y)) c W univ := by
  rw [withDensity_apply _ hW, ← lintegral_indicator hW,
    localized_difference_pair_univ_eq_weight]

def pairAnchorKernel {d : ℕ} (V : Ambient d → ℝ≥0∞) (hV : Measurable V) :
    Kernel (Configuration (Ambient d)) (Ambient d) where
  toFun c := (countingKernel d c).withDensity (pairAnchorWeight V c)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun W hW => ?_
    simp_rw [pairAnchorWeight_measure_apply V _ hW]
    exact measurable_localizedPairIntegral
      (V := fun x y => V (x - y)) (hV.comp (measurable_fst.sub measurable_snd))
      hW MeasurableSet.univ

theorem pairAnchorKernel_apply {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    pairAnchorKernel V hV c W = localizedPairIntegral (fun x y => V (x - y)) c W univ :=
  pairAnchorWeight_measure_apply V c hW

theorem countingKernel_translate_eq_map {d : ℕ}
    (a : Ambient d) (c : Configuration (Ambient d)) :
    countingKernel d (translate a c) = (countingKernel d c).map (fun x => a + x) := by
  ext W hW
  rw [countingKernel_apply _ hW, count_translate,
    Measure.map_apply (measurable_const_add a) hW,
    countingKernel_apply c (hW.preimage (measurable_const_add a))]

theorem lintegral_countingKernel_translate {d : ℕ}
    (a : Ambient d) (c : Configuration (Ambient d))
    (f : Ambient d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂countingKernel d (translate a c)) =
      ∫⁻ x, f (a + x) ∂countingKernel d c := by
  rw [countingKernel_translate_eq_map, lintegral_map hf (measurable_const_add a)]

theorem pairAnchorWeight_translate {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (a : Ambient d)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    pairAnchorWeight V (translate a c) (a + x) = pairAnchorWeight V c x := by
  have hf : Measurable (fun y : Ambient d => V (a + x - y)) :=
    hV.comp (measurable_const.sub measurable_id)
  rw [pairAnchorWeight, lintegral_countingKernel_translate a c _ hf]
  simp only [pairAnchorWeight, add_sub_add_left_eq_sub]

theorem localized_difference_pair_univ_translate {d : ℕ}
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (a : Ambient d)
    (c : Configuration (Ambient d)) {W : Set (Ambient d)} (hW : MeasurableSet W) :
    localizedPairIntegral (fun x y => V (x - y)) (translate a c) W univ =
      localizedPairIntegral (fun x y => V (x - y)) c ((fun x => a + x) ⁻¹' W) univ := by
  have hm : Measurable (pairAnchorWeight V (translate a c)) :=
    (measurable_pairAnchorWeight_joint V hV).comp measurable_prodMk_left
  rw [localized_difference_pair_univ_eq_weight,
    lintegral_countingKernel_translate a c _ (hm.indicator hW),
    localized_difference_pair_univ_eq_weight]
  apply lintegral_congr
  intro x
  by_cases hx : a + x ∈ W <;> simp [hx, pairAnchorWeight_translate V hV]

theorem expected_difference_pair_univ_translate {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) (a : Ambient d)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c ((fun x => a + x) ⁻¹' W) univ ∂μ) =
      ∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ := by
  have hm := measurable_localizedPairIntegral (V := fun x y => V (x - y))
    (hV.comp (measurable_fst.sub measurable_snd)) hW MeasurableSet.univ
  simpa only [localized_difference_pair_univ_translate V hV a _ hW] using
    (hμ a).lintegral_comp hm

def meanPairAnchorMeasure {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) : Measure (Ambient d) :=
  μ.bind (pairAnchorKernel V hV)

theorem meanPairAnchorMeasure_apply {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    meanPairAnchorMeasure μ V hV W = ∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ := by
  rw [meanPairAnchorMeasure, Measure.bind_apply hW (pairAnchorKernel V hV).measurable.aemeasurable]
  simp_rw [pairAnchorKernel_apply V hV _ hW]

theorem meanPairAnchorMeasure_addInvariant {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V) :
    Measure.IsAddLeftInvariant (meanPairAnchorMeasure μ V hV) := by
  refine ⟨fun a => ?_⟩
  ext W hW
  rw [Measure.map_apply (measurable_const_add a) hW,
    meanPairAnchorMeasure_apply μ V hV (hW.preimage (measurable_const_add a)),
    meanPairAnchorMeasure_apply μ V hV hW]
  exact expected_difference_pair_univ_translate μ hμ V hV a hW

end E8Leech
