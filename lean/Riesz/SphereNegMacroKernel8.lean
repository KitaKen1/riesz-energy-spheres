import Riesz.CellFirstMoment
import Riesz.SphereRieszNegMellin8

/-! The subtracted macroscopic kernel for negative exponents (stage NEG, second half).

For `-2 < p` (the relevant range is `-2 < p < -1`, where `∫₀ α^p dα` diverges) the kernel
`K'(x,y) = ∫_{(0,δ]} α^p (e^(-cα|x-y|²) - 1) dα` is finite: `0 ≤ 1 - e^(-cα d²) ≤ cα d²` and
`α^(p+1)` is integrable at `0`. It is symmetric, vanishes on the diagonal, is nonpositive, and
`0 - K'(x,y) ≤ c |x-y|² δ^(p+2)/(p+2)`. Hence, in the stratified first-moment selection, a cell of
diameter `d` contributes at most `c d² δ^(p+2)/(p+2)`: for cells at the density scale this is
`O(δ^(p+2))`, small as `δ → 0`. Constants cancel in neutralized blocks with exact masses, so `K'`
computes the macroscopic end `∫₀^δ α^p D(cα) dα` of the negative-exponent Mellin integral. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The subtracted macroscopic Gaussian kernel. -/
def negMacroKernel8 (c p δ : ℝ) (x y : Sphere8) : ℝ :=
  ∫ α in Ioc 0 δ, α^p*(sphereGaussianKernel8 (c*α) x y-1)

theorem negMacro_integrand_bounds {c α d : ℝ} (hc : 0 ≤ c) (hα : 0 < α) (hd : 0 ≤ d) (p : ℝ) :
    -(α^p*(c*α*d^2)) ≤ α^p*(Real.exp (-(c*α*d^2))-1) ∧ α^p*(Real.exp (-(c*α*d^2))-1) ≤ 0 := by
  have hw : 0 ≤ α^p := Real.rpow_nonneg hα.le _
  have hu : 0 ≤ c*α*d^2 := by positivity
  obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds hu
  constructor
  · have := mul_le_mul_of_nonneg_left (h2.trans (min_le_left _ _)) hw
    linarith
  · exact mul_nonpos_of_nonneg_of_nonpos hw (by linarith)

theorem negMacro_integrableOn {c p δ : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hδ : 0 ≤ δ)
    (x y : Sphere8) :
    IntegrableOn (fun α : ℝ => α^p*(sphereGaussianKernel8 (c*α) x y-1)) (Ioc 0 δ) := by
  have hdom : IntegrableOn (fun α : ℝ => (c*(dist x y)^2)*α^(p+1)) (Ioc 0 δ) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro α hα
    have hα0 : α ≠ 0 := ne_of_gt hα.1
    exact ((Real.continuousAt_rpow_const α p (Or.inl hα0)).mul
      ((by unfold sphereGaussianKernel8; fun_prop :
        Continuous (fun α : ℝ => sphereGaussianKernel8 (c*α) x y-1)).continuousAt)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
    obtain ⟨h1, h2⟩ := negMacro_integrand_bounds hc hα.1 (dist_nonneg (x := x) (y := y)) p
    have he : sphereGaussianKernel8 (c*α) x y = Real.exp (-(c*α*(dist x y)^2)) := by
      unfold sphereGaussianKernel8; ring_nf
    rw [Real.norm_eq_abs, he, abs_of_nonpos h2]
    have hpa : α^p*α = α^(p+1) := by rw [Real.rpow_add_one (ne_of_gt hα.1)]
    calc -(α^p*(Real.exp (-(c*α*(dist x y)^2))-1)) ≤ α^p*(c*α*(dist x y)^2) := by linarith
      _ = (c*(dist x y)^2)*(α^p*α) := by ring
      _ = (c*(dist x y)^2)*α^(p+1) := by rw [hpa]

@[simp]
theorem negMacroKernel8_self (c p δ : ℝ) (x : Sphere8) : negMacroKernel8 c p δ x x = 0 := by
  simp [negMacroKernel8]

theorem negMacroKernel8_symm (c p δ : ℝ) (x y : Sphere8) :
    negMacroKernel8 c p δ x y = negMacroKernel8 c p δ y x := by
  unfold negMacroKernel8 sphereGaussianKernel8
  rw [dist_comm]

theorem negMacroKernel8_nonpos {c p δ : ℝ} (hc : 0 ≤ c) (x y : Sphere8) :
    negMacroKernel8 c p δ x y ≤ 0 := by
  unfold negMacroKernel8
  apply setIntegral_nonpos measurableSet_Ioc
  intro α hα
  have he : sphereGaussianKernel8 (c*α) x y = Real.exp (-(c*α*(dist x y)^2)) := by
    unfold sphereGaussianKernel8; ring_nf
  rw [he]
  exact (negMacro_integrand_bounds hc hα.1 dist_nonneg p).2

/-- The cell variance bound: `0 - K'(x,y) ≤ c |x-y|² δ^(p+2)/(p+2)`. -/
theorem negMacroKernel8_variance {c p δ : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hδ : 0 ≤ δ)
    (x y : Sphere8) :
    0-negMacroKernel8 c p δ x y ≤ c*(dist x y)^2*(δ^(p+2)/(p+2)) := by
  have hint := negMacro_integrableOn hc hp hδ x y
  have hdom : IntegrableOn (fun α : ℝ => (c*(dist x y)^2)*α^(p+1)) (Ioc 0 δ) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  have hmono : (∫ α in Ioc 0 δ, -(α^p*(sphereGaussianKernel8 (c*α) x y-1))) ≤
      ∫ α in Ioc 0 δ, (c*(dist x y)^2)*α^(p+1) := by
    apply setIntegral_mono_on hint.neg hdom measurableSet_Ioc
    intro α hα
    obtain ⟨h1, _⟩ := negMacro_integrand_bounds hc hα.1 (dist_nonneg (x := x) (y := y)) p
    have he : sphereGaussianKernel8 (c*α) x y = Real.exp (-(c*α*(dist x y)^2)) := by
      unfold sphereGaussianKernel8; ring_nf
    have hpa : α^p*α = α^(p+1) := by rw [Real.rpow_add_one (ne_of_gt hα.1)]
    show -(α^p*(sphereGaussianKernel8 (c*α) x y-1)) ≤ (c*(dist x y)^2)*α^(p+1)
    rw [he]
    calc -(α^p*(Real.exp (-(c*α*(dist x y)^2))-1)) ≤ α^p*(c*α*(dist x y)^2) := by linarith
      _ = (c*(dist x y)^2)*(α^p*α) := by ring
      _ = (c*(dist x y)^2)*α^(p+1) := by rw [hpa]
  have hval : (∫ α in Ioc 0 δ, (c*(dist x y)^2)*α^(p+1)) = c*(dist x y)^2*(δ^(p+2)/(p+2)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hδ,
      integral_rpow (Or.inl (by linarith : -1 < p+1))]
    have hp2 : p+1+1 = p+2 := by ring
    rw [hp2, Real.zero_rpow (by linarith)]
    ring
  unfold negMacroKernel8
  rw [integral_neg] at hmono
  linarith

#print axioms negMacro_integrand_bounds
#print axioms negMacro_integrableOn
#print axioms negMacroKernel8_self
#print axioms negMacroKernel8_symm
#print axioms negMacroKernel8_nonpos
#print axioms negMacroKernel8_variance

end SphericalRiesz
