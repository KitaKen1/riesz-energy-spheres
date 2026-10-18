import Riesz.E8FlatRow

/-!
# Actual physical singular rows on the E8 parallelepiped

The full Euclidean inverse-fourth kernel is integrated against actual
Lebesgue volume, and summed at exactly the original corrected tensor
nodes with the diagonal erased. The bound is uniform in all center
indices. This is a coarse flat-row estimate, not the sharp coefficient
or the sphere recovery construction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

def e8PhysicalKernel (x z : Fin 8 → ℝ) : ℝ :=
  (dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 z))⁻¹^4

theorem e8PhysicalKernel_pullback (x y : Fin 8 → ℝ) :
    e8PhysicalKernel x (e8Map y) = obliqueRieszFour 8 e8Map x y :=
  (obliqueRieszFour_eq_dist 8 e8Map x y).symm

theorem e8PhysicalKernel_self (x : Fin 8 → ℝ) : e8PhysicalKernel x (e8Map x) = 0 := by
  simp only [e8PhysicalKernel, dist_self, inv_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0)]

theorem e8PhysicalKernel_integrableOn_image (x : Fin 8 → ℝ) :
    IntegrableOn (e8PhysicalKernel x) (e8Map '' UnitCube 8) := by
  apply (e8Map_measurePreserving.integrableOn_image e8Map_measurableEmbedding).mpr
  exact (e8Kernel_integrableOn_cube x).congr_fun
    (fun y _ => (e8PhysicalKernel_pullback x y).symm) (unitCube_measurableSet 8)

theorem e8Kernel_imageIntegral (x : Fin 8 → ℝ) :
    (∫ y in UnitCube 8, obliqueRieszFour 8 e8Map x y) =
      ∫ z in e8Map '' UnitCube 8, e8PhysicalKernel x z := by
  rw [e8Map_integral_image]
  simp only [e8PhysicalKernel_pullback]

/-- Actual off-diagonal finite sum versus actual singular volume integral. -/
theorem e8FlatPhysicalRow_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ v : Fin 8 → NodeIndex m,
      |(∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex m)).erase v,
          (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4)/(m:ℝ)^8-
        ∫ z in e8Map '' UnitCube 8,
          (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 z))⁻¹^4| ≤ C/(m:ℝ)^4 := by
  classical
  obtain ⟨C, hC, hb⟩ := e8FlatRow_error_bound
  refine ⟨C, hC, ?_⟩
  intro m hm v
  have h := hb m hm v
  rw [cubeQuadrature_as_node_sum, e8Kernel_imageIntegral] at h
  simp only [← e8PhysicalKernel_pullback] at h
  change |(∑ w : Fin 8 → NodeIndex m, e8PhysicalKernel (cubeNode 8 m v) (e8TensorNode m w))/(m:ℝ)^8-
    ∫ z in e8Map '' UnitCube 8, e8PhysicalKernel (cubeNode 8 m v) z| ≤ C/(m:ℝ)^4 at h
  have hsum : (∑ w : Fin 8 → NodeIndex m, e8PhysicalKernel (cubeNode 8 m v) (e8TensorNode m w)) =
      ∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex m)).erase v,
        e8PhysicalKernel (cubeNode 8 m v) (e8TensorNode m w) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ (Finset.univ.erase v))
    intro w hw hn
    have hwv : w = v := by
      by_contra hne
      exact hn (Finset.mem_erase.mpr ⟨hne, hw⟩)
    subst w
    exact e8PhysicalKernel_self _
  rw [hsum] at h
  simpa only [e8PhysicalKernel, e8TensorNode] using h

#print axioms e8PhysicalKernel_pullback
#print axioms e8PhysicalKernel_self
#print axioms e8PhysicalKernel_integrableOn_image
#print axioms e8Kernel_imageIntegral
#print axioms e8FlatPhysicalRow_error_bound

end SphericalRiesz
