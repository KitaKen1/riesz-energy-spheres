import Riesz.EqualAreaPatchBackground8
import Riesz.E8FullRowMean

/-! Dominate the near finite sums at the unchanged corrected nodes.
The coarse (4R+2)^8 count is sufficient: R is fixed before eta is chosen.
This file proves finite inequalities, not an asymptotic coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def CurvedRelativeE8DistanceTolerance8 (F : (Fin 8 → ℝ) → Ambient9) (η : ℝ) : Prop :=
  ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
    |dist (F x) (F y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
      η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))

theorem curvedRelativeE8DistanceTolerance8_half (F : (Fin 8 → ℝ) → Ambient9)
    (η : ℝ) (hη : η ≤ 1/2) (hd : CurvedRelativeE8DistanceTolerance8 F η) :
    CurvedRelativeE8Distance8 F := by
  intro x hx y hy
  exact (hd x hx y hy).trans (mul_le_mul_of_nonneg_right hη dist_nonneg)

theorem originalNode8_mem_cube (m : ℕ) (hm : 8 ≤ m) (v : Fin 8 → NodeIndex m) :
    cubeNode 8 m v ∈ UnitCube 8 :=
  fun i => Ioo_subset_Icc_self (cubeNode_mem_open 8 m hm v i)

theorem cubeQuadrature_abs_domination_nodes8 (m : ℕ) (hm : 8 ≤ m)
    (f g : (Fin 8 → ℝ) → ℝ)
    (hb : ∀ v : Fin 8 → NodeIndex m, |f (cubeNode 8 m v)| ≤ g (cubeNode 8 m v)) :
    |cubeQuadrature 8 m f| ≤ cubeQuadrature 8 m g := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  simp only [cubeQuadrature_as_node_sum,abs_div,abs_of_pos (pow_pos hm0 8)]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hm0.le 8)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ => hb v))

theorem cubeQuadrature_abs_le_nodes8 (m : ℕ) (hm : 8 ≤ m)
    (f : (Fin 8 → ℝ) → ℝ) (M : ℝ)
    (hb : ∀ v : Fin 8 → NodeIndex m, |f (cubeNode 8 m v)| ≤ M) :
    |cubeQuadrature 8 m f| ≤ M := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := cubeQuadrature_abs_domination_nodes8 m hm f (fun _ => M) hb
  have he : cubeQuadrature 8 m (fun _ => M) = M := by
    simp only [cubeQuadrature_as_node_sum,Finset.sum_const,Finset.card_univ,
      cubeNode_card 8 m hm,nsmul_eq_mul,Nat.cast_pow]
    field_simp [hm0.ne']
  simpa only [he] using h

def curvedNearRowComparisonConstant8 (R : ℝ) : ℝ :=
  (4*R+2)^8/e8SeparationConstant^4+e8NearIntegralConstant*R^4

theorem curvedNearRowComparisonConstant8_nonneg (R : ℝ) :
    0 ≤ curvedNearRowComparisonConstant8 R := by
  unfold curvedNearRowComparisonConstant8
  exact add_nonneg (by positivity) (mul_nonneg e8NearIntegralConstant_nonneg (by positivity))

theorem curvedNearQuadrature8_relative_bound (F : (Fin 8 → ℝ) → Ambient9)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (hd : CurvedRelativeE8DistanceTolerance8 F η)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 8 ≤ m) (v : Fin 8 → NodeIndex m) :
    |(m:ℝ)^4*(cubeQuadrature 8 m (curvedNearRieszFour F (R/(m:ℝ)) (cubeNode 8 m v))-
      cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (cubeNode 8 m v)))| ≤
        64*η*((4*R+2)^8/e8SeparationConstant^4) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hdq : |cubeQuadrature 8 m (curvedNearRieszFour F (R/(m:ℝ)) (cubeNode 8 m v))-
      cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (cubeNode 8 m v))| ≤
        64*η*cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (cubeNode 8 m v)) := by
    rw [← cubeQuadrature_sub,← cubeQuadrature_const_mul]
    apply cubeQuadrature_abs_domination_nodes8 m hm
    intro w
    exact curvedNearRieszFour_relative_error F _ _ _ η hη hη1
      (hd _ (originalNode8_mem_cube m hm v) _ (originalNode8_mem_cube m hm w))
  have hq := e8Near_quadrature_bound hm R hR v
  rw [abs_mul,abs_of_nonneg (pow_nonneg hm0.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(64*η*( (4*R+2)^8/(e8SeparationConstant^4*(m:ℝ)^4))) :=
      mul_le_mul_of_nonneg_left
        (hdq.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hq) (by positivity))) (by positivity)
    _ = _ := by field_simp [hm0.ne',e8SeparationConstant_pos.ne']

theorem curvedNearRow8_relative_bound (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : CurvedRelativeE8DistanceTolerance8 F η)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 8 ≤ m) (v : Fin 8 → NodeIndex m) :
    |(m:ℝ)^4*((cubeQuadrature 8 m (curvedNearRieszFour F (R/(m:ℝ)) (cubeNode 8 m v))-
        curvedNearPotential F (R/(m:ℝ)) (cubeNode 8 m v))-
      (cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (cubeNode 8 m v))-
        e8NearPotential (R/(m:ℝ)) (cubeNode 8 m v)))| ≤
          64*η*curvedNearRowComparisonConstant8 R := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hq := curvedNearQuadrature8_relative_bound F η hη hη1 hd R hR m hm v
  have hi := curvedNearPotential_relative_error F hF.measurable _ (div_pos hR hm0)
    (cubeNode 8 m v) η hη hη1 (hd _ (originalNode8_mem_cube m hm v))
  have his : |(m:ℝ)^4*(curvedNearPotential F (R/(m:ℝ)) (cubeNode 8 m v)-
      e8NearPotential (R/(m:ℝ)) (cubeNode 8 m v))| ≤ 64*η*e8NearIntegralConstant*R^4 := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hm0.le 4)]
    calc
      _ ≤ (m:ℝ)^4*(64*η*e8NearIntegralConstant*(R/(m:ℝ))^4) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by field_simp [hm0.ne']
  calc
    _ = |(m:ℝ)^4*(cubeQuadrature 8 m (curvedNearRieszFour F (R/(m:ℝ)) (cubeNode 8 m v))-
        cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (cubeNode 8 m v)))-
      (m:ℝ)^4*(curvedNearPotential F (R/(m:ℝ)) (cubeNode 8 m v)-
        e8NearPotential (R/(m:ℝ)) (cubeNode 8 m v))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 64*η*((4*R+2)^8/e8SeparationConstant^4)+64*η*e8NearIntegralConstant*R^4 := add_le_add hq his
    _ = _ := by unfold curvedNearRowComparisonConstant8; ring

end SphericalRiesz
