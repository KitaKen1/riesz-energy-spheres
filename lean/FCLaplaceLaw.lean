import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace RieszSphereFC

private theorem integrableExpSet_eq_univ_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {C : ℝ} (hC : ∀ᵐ ω ∂μ, |X ω| ≤ C) : integrableExpSet X μ = univ := by
  apply eq_univ_of_forall
  intro t
  change Integrable (fun ω => Real.exp (t * X ω)) μ
  apply (integrable_const (Real.exp (|t| * C))).mono'
    (Real.continuous_exp.measurable.comp (hX.const_mul t)).aestronglyMeasurable
  filter_upwards [hC] with ω hω
  change ‖Real.exp (t * X ω)‖ ≤ Real.exp (|t| * C)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * C := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- Bounded real random variables are determined by their positive-parameter Laplace integrals. -/
theorem map_eq_of_bounded_laplace {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {C D : ℝ} (hC : ∀ᵐ ω ∂μ, |X ω| ≤ C) (hD : ∀ᵐ ω ∂ν, |Y ω| ≤ D)
    (hLaplace : ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (t * X ω) ∂μ) = ∫ ω, Real.exp (t * Y ω) ∂ν) :
    μ.map X = ν.map Y := by
  have hSX := integrableExpSet_eq_univ_of_bounded hX hC
  have hSY := integrableExpSet_eq_univ_of_bounded hY hD
  have hAX : AnalyticOnNhd ℂ (complexMGF X μ) univ := by
    simpa only [hSX, interior_univ, mem_univ, ofPred_true] using
      (analyticOnNhd_complexMGF (X := X) (μ := μ))
  have hAY : AnalyticOnNhd ℂ (complexMGF Y ν) univ := by
    simpa only [hSY, interior_univ, mem_univ, ofPred_true] using
      (analyticOnNhd_complexMGF (X := Y) (μ := ν))
  have hReal : ∃ᶠ (t : ℝ) in 𝓝[≠] (1 : ℝ),
      complexMGF X μ t = complexMGF Y ν t := by
    have hp : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), 0 < t :=
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    apply (hp.mono fun t ht => ?_).frequently
    rw [complexMGF_ofReal, complexMGF_ofReal]
    exact congrArg (fun x : ℝ => (x : ℂ)) (hLaplace t ht)
  have hFreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), complexMGF X μ z = complexMGF Y ν z := by
    rw [frequently_iff_seq_forall] at hReal ⊢
    obtain ⟨xs, hx, he⟩ := hReal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · simpa only [Complex.ofReal_one] using (tendsto_ofReal_iff.mpr hx.1)
    · simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_one] using hx.2
  have hEq := hAX.eqOn_of_preconnected_of_frequently_eq hAY
    isPreconnected_univ (z₀ := (1 : ℂ)) (mem_univ _) hFreq
  apply Measure.ext_of_complexMGF_eq hX.aemeasurable hY.aemeasurable
  funext z
  exact hEq (mem_univ z)

end RieszSphereFC
