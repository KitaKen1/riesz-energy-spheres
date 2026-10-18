import E8Leech.PairAnchorMeasure

/-!
# Haar identification of expected full-second-endpoint point pairs

Finite mass in the unit anchor window, together with stationarity, implies
finite mass in every bounded window. Haar uniqueness then gives the exact
volume scaling. For rapidly decaying difference kernels the unit finiteness
comes from the original finite Riesz energy, rather than an extra moment
assumption on the law.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem expected_difference_pair_bounded_ne_top_of_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ) ≠ ∞ := by
  obtain ⟨t, ht⟩ := exists_finite_unitWindow_cover hbW
  let U := fun a : Ambient d => (fun x => a + x) ⁻¹' unitWindow d
  have hU : ∀ a, MeasurableSet (U a) := fun a =>
    (measurable_unitWindow d).preimage (measurable_const_add a)
  have hfinite : ∀ a, meanPairAnchorMeasure μ V hV (U a) ≠ ∞ := by
    intro a
    rw [meanPairAnchorMeasure_apply μ V hV (hU a)]
    exact (expected_difference_pair_univ_translate μ hμ V hV a
      (measurable_unitWindow d)) ▸ hunit
  have hsum : (∑ a ∈ t, meanPairAnchorMeasure μ V hV (U a)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun a _ => hfinite a
  rw [← meanPairAnchorMeasure_apply μ V hV hW]
  apply ne_of_lt
  calc
    meanPairAnchorMeasure μ V hV W
        ≤ meanPairAnchorMeasure μ V hV (⋃ a ∈ t, U a) := measure_mono ht
    _ ≤ ∑ a ∈ t, meanPairAnchorMeasure μ V hV (U a) := measure_biUnion_finset_le t U
    _ < ∞ := hsum.lt_top

theorem meanPairAnchorMeasure_finiteOnCompacts {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞) :
    IsFiniteMeasureOnCompacts (meanPairAnchorMeasure μ V hV) := by
  refine ⟨fun K hK => ?_⟩
  rw [meanPairAnchorMeasure_apply μ V hV hK.measurableSet]
  exact (expected_difference_pair_bounded_ne_top_of_unit μ hμ V hV hunit
    hK.measurableSet hK.isBounded).lt_top

/-- Exact scaling for every Borel first window, even an unbounded one. -/
theorem expected_difference_pair_univ_eq_unit_mul_volume {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    (hunit : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) ≠ ∞)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c W univ ∂μ) =
      (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
        (unitWindow d) univ ∂μ) * volume W := by
  let := meanPairAnchorMeasure_addInvariant μ hμ V hV
  let := meanPairAnchorMeasure_finiteOnCompacts μ hμ V hV hunit
  let κ : NNReal := Measure.addHaarScalarFactor (meanPairAnchorMeasure μ V hV) volume
  have hm : meanPairAnchorMeasure μ V hV = κ • volume :=
    Measure.isAddLeftInvariant_eq_smul (meanPairAnchorMeasure μ V hV) volume
  have hi : (∫⁻ c, localizedPairIntegral (fun x y => V (x - y)) c
      (unitWindow d) univ ∂μ) = (κ : ℝ≥0∞) := by
    rw [← meanPairAnchorMeasure_apply μ V hV (measurable_unitWindow d), hm]
    simp [volume_unitWindow]
  rw [← meanPairAnchorMeasure_apply μ V hV hW, hm, hi]
  simp

theorem expected_abs_difference_pair_unit_ne_top_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞ := by
  simpa using
    expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay 0

theorem expected_abs_difference_pair_bounded_ne_top_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c W univ ∂μ) ≠ ∞ := by
  exact expected_difference_pair_bounded_ne_top_of_unit μ hμ _ hh.norm.ennreal_ofReal
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay) hW hbW

theorem expected_abs_difference_pair_univ_eq_unit_mul_volume_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c W univ ∂μ) =
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
        (unitWindow d) univ ∂μ) * volume W := by
  exact expected_difference_pair_univ_eq_unit_mul_volume μ hμ _ hh.norm.ennreal_ofReal
    (expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay) hW

end E8Leech
