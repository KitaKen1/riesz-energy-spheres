import Mathlib

/-! Exact-mass cuts (stage NEG, second half: exact-mass cells).

For a finite measure `μ` and a bounded measurable coordinate `f` whose level sets are null, every
mass `0 ≤ m ≤ μ(univ)` is the mass of a half-space `{f ≤ c}`: the normalized distribution
function of `f` is a Stieltjes function without jumps (null level sets), hence continuous, and the
intermediate value theorem applies on `[-R-1, R]`. Restricting `μ` to a set gives exact-mass cuts
of any region; iterating gives cells of prescribed masses. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SphericalRiesz

theorem cdf_continuous_of_null {P : Measure ℝ} [IsProbabilityMeasure P]
    (hnull : ∀ c, P {c} = 0) : Continuous (cdf P) := by
  rw [continuous_iff_continuousAt]
  intro c
  have hmono : Monotone (cdf P) := monotone_cdf P
  have hright : ContinuousWithinAt (cdf P) (Ici c) c := (cdf P).right_continuous c
  have hsing : (cdf P).measure {c} = 0 := by rw [measure_cdf]; exact hnull c
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hle : Function.leftLim (cdf P) c ≤ cdf P c := hmono.leftLim_le le_rfl
  have hleft : Function.leftLim (cdf P) c = cdf P c := le_antisymm hle (by linarith)
  have hIio : ContinuousWithinAt (cdf P) (Iio c) c :=
    (hmono.continuousWithinAt_Iio_iff_leftLim_eq).mpr hleft
  have hIic : ContinuousWithinAt (cdf P) (Iic c) c := by
    have := hIio.union (continuousWithinAt_singleton (f := cdf P) (x := c))
    rwa [Iio_union_right] at this
  exact continuousAt_iff_continuous_left_right.mpr ⟨hIic, hright⟩

/-- Exact-mass cut by a half-space. -/
theorem exists_cut_measure_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {R : ℝ} (hR : ∀ x, |f x| ≤ R)
    (hnull : ∀ c, μ (f ⁻¹' {c}) = 0) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ μ.real univ) :
    ∃ c, μ.real (f ⁻¹' Iic c) = m := by
  by_cases h0 : μ univ = 0
  · have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp h0
    subst hμ
    refine ⟨0, ?_⟩
    simp at hm1 ⊢
    linarith
  set ν : Measure ℝ := μ.map f with hν
  have hνu : ν univ = μ univ := by
    rw [hν, Measure.map_apply hf MeasurableSet.univ, preimage_univ]
  have hνfin : ν univ ≠ ⊤ := by rw [hνu]; exact measure_ne_top μ univ
  have hν0 : ν univ ≠ 0 := by rw [hνu]; exact h0
  set P : Measure ℝ := (ν univ)⁻¹ • ν with hP
  have hPprob : IsProbabilityMeasure P := by
    constructor
    rw [hP, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hν0 hνfin]
  have hPnull : ∀ c, P {c} = 0 := by
    intro c
    rw [hP, Measure.smul_apply, hν, Measure.map_apply hf (measurableSet_singleton c), hnull c,
      smul_zero]
  have hcont := cdf_continuous_of_null hPnull
  have hG : ∀ c, μ.real (f ⁻¹' Iic c) = μ.real univ * cdf P c := by
    intro c
    rw [cdf_eq_real]
    have h1 : P.real (Iic c) = (μ.real univ)⁻¹ * μ.real (f ⁻¹' Iic c) := by
      rw [Measure.real, hP, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_inv, hνu, hν, Measure.map_apply hf measurableSet_Iic]
      rfl
    have hpos : 0 < μ.real univ := by
      rw [Measure.real]
      exact ENNReal.toReal_pos h0 (measure_ne_top μ univ)
    rw [h1]
    field_simp
  have hlow : cdf P (-R-1) = 0 := by
    have hempty : f ⁻¹' Iic (-R-1) = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      have := (abs_le.mp (hR x)).1
      linarith
    have h := hG (-R-1)
    rw [hempty, measureReal_empty] at h
    have hpos : 0 < μ.real univ := by
      rw [Measure.real]
      exact ENNReal.toReal_pos h0 (measure_ne_top μ univ)
    nlinarith
  have hhigh : cdf P R = 1 := by
    have hfull : f ⁻¹' Iic R = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (abs_le.mp (hR x)).2
    have h := hG R
    rw [hfull] at h
    have hpos : 0 < μ.real univ := by
      rw [Measure.real]
      exact ENNReal.toReal_pos h0 (measure_ne_top μ univ)
    nlinarith
  have hX : Nonempty X := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (by rw [Set.univ_eq_empty_iff.mpr hne, measure_empty])
  have hRR : -R-1 ≤ R := by
    have := (abs_nonneg (f (Classical.arbitrary X))).trans (hR (Classical.arbitrary X))
    linarith
  have hpos : 0 < μ.real univ := by
    rw [Measure.real]
    exact ENNReal.toReal_pos h0 (measure_ne_top μ univ)
  have hm' : m/μ.real univ ∈ Icc (cdf P (-R-1)) (cdf P R) := by
    rw [hlow, hhigh]
    exact ⟨div_nonneg hm0 hpos.le, (div_le_one hpos).mpr hm1⟩
  obtain ⟨c, _, hc⟩ := intermediate_value_Icc hRR hcont.continuousOn hm'
  refine ⟨c, ?_⟩
  rw [hG, hc]
  field_simp

/-- Exact-mass cut of a region `S` by a half-space. -/
theorem exists_cut_measure_eq_restrict {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (S : Set X) {f : X → ℝ} (hf : Measurable f) {R : ℝ}
    (hR : ∀ x, |f x| ≤ R) (hnull : ∀ c, μ (f ⁻¹' {c} ∩ S) = 0) {m : ℝ} (hm0 : 0 ≤ m)
    (hm1 : m ≤ μ.real S) :
    ∃ c, μ.real (f ⁻¹' Iic c ∩ S) = m := by
  have h := exists_cut_measure_eq (μ.restrict S) hf hR
    (fun c => by rw [Measure.restrict_apply (hf (measurableSet_singleton c))]; exact hnull c)
    hm0 (by rwa [measureReal_restrict_apply_univ])
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rwa [measureReal_restrict_apply (hf measurableSet_Iic)] at hc

#print axioms cdf_continuous_of_null
#print axioms exists_cut_measure_eq
#print axioms exists_cut_measure_eq_restrict

end SphericalRiesz
