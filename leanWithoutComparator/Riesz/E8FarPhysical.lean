import Riesz.CubeLebesgue
import Riesz.E8Volume
import Riesz.ObliquePartition

/-!
# The far error as an actual integral on the E8 basis image

The coordinate cube is mapped to a physical parallelepiped. The inverse
basis map supplies the cutoff coordinates, while the kernel is the
actual Euclidean inverse fourth power. The original tensor nodes and
Lebesgue measure, with determinant one, are kept unchanged.
This is still a far-part estimate; no near coefficient or sphere recovery
is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

def e8InverseMap : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  e8Basis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

theorem e8InverseMap_e8Map (v : Fin 8 → ℝ) : e8InverseMap (e8Map v) = v :=
  e8Basis.equivFun.apply_symm_apply v

theorem e8Map_e8InverseMap (v : Fin 8 → ℝ) : e8Map (e8InverseMap v) = v :=
  e8Basis.equivFun.symm_apply_apply v

def e8PhysicalFar (r : ℝ) (x z : Fin 8 → ℝ) : ℝ :=
  farObliqueRieszFour 8 e8Map r x (e8InverseMap z)

theorem e8PhysicalFar_eq_dist (r : ℝ) (x z : Fin 8 → ℝ) :
    e8PhysicalFar r x z =
      (dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 z))⁻¹^4*
        (1-outerUnitBump 8 ((r/2)⁻¹ • (e8InverseMap z-x))) := by
  simp only [e8PhysicalFar, farObliqueRieszFour, nearObliqueRieszFour,
    obliqueRieszFour_eq_dist, e8Map_e8InverseMap]
  ring

theorem e8PhysicalFar_pullback (r : ℝ) (x v : Fin 8 → ℝ) :
    e8PhysicalFar r x (e8Map v) = farObliqueRieszFour 8 e8Map r x v := by
  rw [e8PhysicalFar, e8InverseMap_e8Map]

/-- The existing nested integral is now the actual physical Lebesgue integral. -/
theorem e8Far_imageIntegral (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    cubeIntegral 8 (farObliqueRieszFour 8 e8Map r x) =
      ∫ z in e8Map '' UnitCube 8, e8PhysicalFar r x z := by
  rw [e8Map_integral_image]
  simp only [e8PhysicalFar_pullback]
  exact cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr x).continuousOn

theorem e8Far_physical_node_error_small :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℕ, 8 ≤ m → ∀ x : Fin 8 → ℝ,
      |(∑ v : Fin 8 → NodeIndex m, e8PhysicalFar (L/(m:ℝ)) x (e8TensorNode m v))/(m:ℝ)^8-
        ∫ z in e8Map '' UnitCube 8, e8PhysicalFar (L/(m:ℝ)) x z| ≤ ε/(m:ℝ)^4 := by
  intro ε hε
  obtain ⟨L, hL, hb⟩ := e8FarRieszFour_error_small ε hε
  refine ⟨L, hL, ?_⟩
  intro m hm x
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hL0 : 0 < L := by linarith
  have h := hb m hm x
  rw [cubeQuadrature_as_node_sum, e8Far_imageIntegral _ (div_pos hL0 hm0)] at h
  simpa only [e8TensorNode, e8PhysicalFar_pullback] using h

#print axioms e8PhysicalFar_eq_dist
#print axioms e8Far_imageIntegral
#print axioms e8Far_physical_node_error_small

end SphericalRiesz
