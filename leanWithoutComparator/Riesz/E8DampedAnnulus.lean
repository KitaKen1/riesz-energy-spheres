import Riesz.E8GaussianSchwartz
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform actual E8 annular derivatives for every damping parameter

The actual compact inverse-fourth kernel is smooth and supported away from zero.
Schwartz dilations bound all Gaussian derivatives on that support uniformly in u≥0.
No compactness of the unbounded parameter set is invoked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped ContDiff
namespace SphericalRiesz

theorem unitAnnularCutoff_zero_inside (d : ℕ) (v : Fin d → ℝ)
    (hv : ‖v‖ ≤ (1/2:ℝ)) : unitAnnularCutoff d v = 0 := by
  have ho : outerUnitBump d v = 1 := (outerUnitBump d).one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_zero_right, outerUnitBump]
    linarith)
  have hi : innerUnitBump d v = 1 := (innerUnitBump d).one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, innerUnitBump] using hv)
  rw [unitAnnularCutoff, ho, hi, sub_self]

theorem unitObliqueAnnularRieszFour_tsupport_away (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    tsupport (unitObliqueAnnularRieszFour d A) ⊆ {v | (1/2:ℝ) ≤ ‖v‖} := by
  apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
  intro v hv
  by_contra hn
  apply Function.mem_support.mp hv
  rw [unitObliqueAnnularRieszFour, unitAnnularCutoff_zero_inside d v (not_le.mp hn).le,
    mul_zero]

def e8UnitDampedAnnulus (u : ℝ) (v : Fin 8 → ℝ) : ℝ :=
  unitObliqueAnnularRieszFour 8 e8Map v * e8CoordinateGaussian u v

theorem e8UnitDampedAnnulus_contDiff {u : ℝ} (hu : 0 ≤ u) :
    ContDiff ℝ ∞ (e8UnitDampedAnnulus u) :=
  (unitObliqueAnnularRieszFour_contDiff 8 e8Map e8Map_injective).mul
    (e8CoordinateGaussian_contDiff hu)

theorem e8UnitDampedAnnulus_hasCompactSupport (u : ℝ) :
    HasCompactSupport (e8UnitDampedAnnulus u) :=
  (unitObliqueAnnularRieszFour_hasCompactSupport 8 e8Map).mul_right

theorem e8UnitDampedAnnulus_tsupport_subset (u : ℝ) :
    tsupport (e8UnitDampedAnnulus u) ⊆ Metric.closedBall 0 2 := by
  exact tsupport_mul_subset_left.trans (unitObliqueAnnularRieszFour_tsupport_subset 8 e8Map)

/-- C is independent of the unbounded parameter u, derivative order n≤6, and v. -/
theorem e8UnitDampedAnnulus_derivatives_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ, n ≤ 6 →
      ∀ v : Fin 8 → ℝ, ‖iteratedFDeriv ℝ n (e8UnitDampedAnnulus u) v‖ ≤ C := by
  obtain ⟨A, hA, hAb⟩ :=
    (unitObliqueAnnularRieszFour_hasCompactSupport 8 e8Map).exists_bound_iteratedFDeriv
      (unitObliqueAnnularRieszFour_contDiff 8 e8Map e8Map_injective) 6
  obtain ⟨B, hB, hBb⟩ := e8CoordinateGaussian_derivatives_uniform 6
    (show (0:ℝ) < 1/2 by norm_num)
  let c (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A*B
  have hc : ∀ n, 0 ≤ c n := fun n => Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨∑ n ∈ Finset.range 7, c n, Finset.sum_nonneg (fun n _ => hc n), ?_⟩
  intro u hu n hn v
  have hsum : c n ≤ ∑ j ∈ Finset.range 7, c j :=
    Finset.single_le_sum (s := Finset.range 7) (a := n) (f := c)
      (fun j _ => hc j) (Finset.mem_range.mpr (by omega))
  apply le_trans _ hsum
  apply (norm_iteratedFDeriv_mul_le
    (unitObliqueAnnularRieszFour_contDiff 8 e8Map e8Map_injective)
    (e8CoordinateGaussian_contDiff hu) v (by simp : (n : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  by_cases hv : (1/2:ℝ) ≤ ‖v‖
  · exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hAb i (hi'.trans hn) v) (by positivity))
      (hBb u hu (n-i) (by omega) v hv) (norm_nonneg _) (by positivity)
  · have hz : iteratedFDeriv ℝ i (unitObliqueAnnularRieszFour 8 e8Map) v = 0 := by
      apply Function.notMem_support.mp
      intro hs
      exact hv (unitObliqueAnnularRieszFour_tsupport_away 8 e8Map
        (support_iteratedFDeriv_subset i hs))
    rw [hz, norm_zero, mul_zero, zero_mul]
    positivity

#print axioms unitAnnularCutoff_zero_inside
#print axioms unitObliqueAnnularRieszFour_tsupport_away
#print axioms e8UnitDampedAnnulus_contDiff
#print axioms e8UnitDampedAnnulus_hasCompactSupport
#print axioms e8UnitDampedAnnulus_tsupport_subset
#print axioms e8UnitDampedAnnulus_derivatives_uniform
end SphericalRiesz
