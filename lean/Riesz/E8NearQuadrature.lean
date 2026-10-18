import Riesz.E8NearIntegral

/-!
# The actual cutoff near finite sum at the original nodes

The original corrected nodes are used. At a center node the diagonal
has value zero and can be erased. The actual cutoff's finite sum is
bounded by the checked coordinate-truncated near sum, uniformly in
every center index, including boundary corrections. The full row is
assembled with the actual integrals and far error in E8FlatRow.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

theorem e8Near_self (r : ℝ) (x : Fin 8 → ℝ) : nearObliqueRieszFour 8 e8Map r x x = 0 := by
  simp [nearObliqueRieszFour, obliqueRieszFour, flatRieszFour, squaredDistance]

theorem e8Near_le_kernel (r : ℝ) (x y : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map r x y ≤ obliqueRieszFour 8 e8Map x y := by
  have hk : 0 ≤ obliqueRieszFour 8 e8Map x y := by
    unfold obliqueRieszFour flatRieszFour
    positivity
  exact mul_le_of_le_one_right hk (outerUnitBump 8).le_one

theorem e8Near_zero_outside_coordinates (r : ℝ) (hr : 0 < r) (x y : Fin 8 → ℝ)
    (hy : ¬ ∀ i, |y i-x i| ≤ 2*r) : nearObliqueRieszFour 8 e8Map r x y = 0 := by
  have hn := scaled_annular_argument_norm 8 r hr x y hy
  have hb : outerUnitBump 8 (r⁻¹ • (y-x)) = 0 :=
    (outerUnitBump 8).zero_of_le_dist (by
      simpa only [outerUnitBump, dist_zero_right] using hn.le)
  rw [nearObliqueRieszFour, hb, mul_zero]

theorem e8Near_quadrature_nonneg (m : ℕ) (r : ℝ) (x : Fin 8 → ℝ) :
    0 ≤ cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map r x) := by
  rw [cubeQuadrature_as_node_sum]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => e8Near_nonneg r x _)) (by positivity)

theorem e8Near_quadrature_bound {m : ℕ} (hm : 8 ≤ m) (L : ℝ) (hL : 0 < L)
    (v : Fin 8 → NodeIndex m) :
    |cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (L/(m:ℝ)) (cubeNode 8 m v))| ≤
      (4*L+2)^8/(e8SeparationConstant^4*(m:ℝ)^4) := by
  classical
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let x := cubeNode 8 m v
  let r := L/(m:ℝ)
  let s := cubeLocalNodeSet 8 m x ((2*L)/(m:ℝ))
  have hr : 0 < r := div_pos hL hm0
  have hrad : (2*L)/(m:ℝ) = 2*r := by dsimp only [r]; ring
  have hsum : (∑ w : Fin 8 → NodeIndex m, nearObliqueRieszFour 8 e8Map r x (cubeNode 8 m w)) =
      ∑ w ∈ s.erase v, nearObliqueRieszFour 8 e8Map r x (cubeNode 8 m w) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ (s.erase v))
    intro w _ hw
    by_cases hwv : w = v
    · subst w
      exact e8Near_self r x
    have hws : w ∉ s := fun h => hw (Finset.mem_erase.mpr ⟨hwv, h⟩)
    apply e8Near_zero_outside_coordinates r hr x (cubeNode 8 m w)
    intro h
    apply hws
    simp only [s, cubeLocalNodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hrad]
    exact h
  have hb : (∑ w ∈ s.erase v, nearObliqueRieszFour 8 e8Map r x (cubeNode 8 m w)) ≤
      ∑ w ∈ s.erase v,
        (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
          (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4 := by
    apply Finset.sum_le_sum
    intro w _
    simpa only [obliqueRieszFour_eq_dist, e8TensorNode, x] using
      e8Near_le_kernel r x (cubeNode 8 m w)
  rw [abs_of_nonneg (e8Near_quadrature_nonneg _ _ _), cubeQuadrature_as_node_sum]
  change (∑ w : Fin 8 → NodeIndex m, nearObliqueRieszFour 8 e8Map r x (cubeNode 8 m w))/(m:ℝ)^8 ≤ _
  rw [hsum]
  calc
    _ ≤ e8NearNodeSum m (2*L) v := div_le_div_of_nonneg_right hb (by positivity)
    _ ≤ (2*(2*L)+2)^8/(e8SeparationConstant^4*(m:ℝ)^4) :=
      e8NearNodeSum_bound hm (2*L) (by positivity) v
    _ = _ := by ring

#print axioms e8Near_self
#print axioms e8Near_le_kernel
#print axioms e8Near_zero_outside_coordinates
#print axioms e8Near_quadrature_nonneg
#print axioms e8Near_quadrature_bound

end SphericalRiesz
