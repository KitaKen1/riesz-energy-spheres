import Riesz.CenteredGrid
import Riesz.E8NearQuadrature
import Riesz.E8Theta

/-!
# The actual compact E8 defect at the unchanged corrected nodes

This constructs the finite cutoff coefficient that occurs in interior
rows. It does not identify its large-radius limit with the heat defect.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
namespace SphericalRiesz
open Boundary

def e8CompactTerm (R : ℝ) (z : Fin 8 → ℤ) : ℝ :=
  nearObliqueRieszFour 8 e8Map R 0 (fun i => (z i : ℝ))

def e8CompactLatticeSum (R : ℝ) : ℝ := ∑' z : Fin 8 → ℤ, e8CompactTerm R z

def e8CompactDefect (R : ℝ) : ℝ := e8CompactLatticeSum R -
  ∫ y : Fin 8 → ℝ, nearObliqueRieszFour 8 e8Map R 0 y

theorem e8CompactTerm_eq (R : ℝ) (z : Fin 8 → ℤ) :
    e8CompactTerm R z = outerUnitBump 8 (R⁻¹ • (fun i => (z i : ℝ))) /
      ‖e8EuclideanPoint z‖^4 := by
  unfold e8CompactTerm nearObliqueRieszFour
  rw [obliqueRieszFour_eq_dist]
  simp only [map_zero, WithLp.toLp_zero, dist_zero_left, sub_zero]
  change ‖e8EuclideanPoint z‖⁻¹^4 * outerUnitBump 8 (R⁻¹ • (fun i => (z i : ℝ))) = _
  rw [inv_pow, div_eq_mul_inv]
  ring

theorem e8CompactTerm_zero (R : ℝ) : e8CompactTerm R 0 = 0 := by
  simp only [e8CompactTerm, Pi.zero_apply, Int.cast_zero]
  exact e8Near_self R (0 : Fin 8 → ℝ)

theorem e8CompactTerm_nonneg (R : ℝ) (z : Fin 8 → ℤ) : 0 ≤ e8CompactTerm R z :=
  e8Near_nonneg R 0 _

theorem e8CompactTerm_zero_outside {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q)
    (z : Fin 8 → ℤ) (hz : z ∉ centeredIntegerBox 8 q) : e8CompactTerm R z = 0 := by
  apply e8Near_zero_outside_coordinates R hR
  intro hb
  apply hz
  rw [centeredIntegerBox_mem]
  intro i
  have hi := abs_le.mp (hb i)
  simp only [Pi.zero_apply, sub_zero] at hi
  constructor
  · exact_mod_cast (show -(q : ℝ) ≤ (z i : ℝ) by linarith)
  · exact_mod_cast (show (z i : ℝ) ≤ (q : ℝ) by linarith)

theorem e8CompactTerm_summable {R : ℝ} (hR : 0 < R) : Summable (e8CompactTerm R) := by
  obtain ⟨q, hq⟩ := exists_nat_ge (2*R)
  exact summable_of_ne_finset_zero (e8CompactTerm_zero_outside hR q hq)

theorem e8CompactLatticeSum_eq_finite {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q) :
    e8CompactLatticeSum R = ∑ z ∈ centeredIntegerBox 8 q, e8CompactTerm R z :=
  tsum_eq_sum (e8CompactTerm_zero_outside hR q hq)

theorem e8CompactLatticeSum_eq_corrected {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q) :
    e8CompactLatticeSum R = ∑ v : Fin 8 → NodeIndex (centeredMesh q),
      nearObliqueRieszFour 8 e8Map R 0 (centeredCubeCoordinate 8 q v) := by
  symm
  apply centeredNodeSum_eq_tsum 8 q (2*R) hq
  intro y hy
  apply e8Near_zero_outside_coordinates R hR 0 y
  simpa only [Pi.zero_apply, sub_zero] using hy

theorem e8Compact_background_value {R : ℝ} (hR : 0 < R) :
    (∫ y : Fin 8 → ℝ, nearObliqueRieszFour 8 e8Map R 0 y) =
      e8NearIntegralConstant*R^4 := e8Near_integral R hR 0

theorem e8CompactDefect_eq {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q) :
    e8CompactDefect R = (∑ z ∈ centeredIntegerBox 8 q, e8CompactTerm R z) -
      e8NearIntegralConstant*R^4 := by
  rw [e8CompactDefect, e8CompactLatticeSum_eq_finite hR q hq,
    e8Compact_background_value hR]

theorem e8Near_centered_scale {R : ℝ} (hR : 0 < R) (q : ℕ) (y : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map (R/(centeredMesh q : ℝ)) (fun _ => (1/2 : ℝ)) y =
      (centeredMesh q : ℝ)^4 * nearObliqueRieszFour 8 e8Map R 0
        ((centeredMesh q : ℝ) • (y-(fun _ => (1/2 : ℝ)))) := by
  have hm : (0 : ℝ) < centeredMesh q := by positivity
  rw [e8Near_scaled _ (div_pos hR hm), e8Near_scaled R hR]
  simp only [sub_zero, inv_div, smul_smul]
  have hs : (centeredMesh q : ℝ)/R = R⁻¹*(centeredMesh q : ℝ) := by ring
  rw [hs]
  ring

theorem e8Near_centered_cubeIntegral {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q) :
    (∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (R/(centeredMesh q : ℝ))
      (fun _ => (1/2 : ℝ)) y) = e8NearIntegralConstant*(R/(centeredMesh q : ℝ))^4 := by
  have hm : (0 : ℝ) < centeredMesh q := by positivity
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact e8Near_integral _ (div_pos hR hm) _
  · intro y hy
    apply e8Near_zero_outside_coordinates _ (div_pos hR hm)
    intro hb
    apply hy
    intro i
    have hi := abs_le.mp (hb i)
    have hh : 2*(R/(centeredMesh q : ℝ)) ≤ 1/2 := by
      have hq0 : (0 : ℝ) ≤ q := by positivity
      have hmesh : (centeredMesh q : ℝ) = 2*(q : ℝ)+9 := by simp [centeredMesh]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      rw [show 2*(R/(centeredMesh q : ℝ))*2 = (4*R)/(centeredMesh q : ℝ) by ring]
      apply (div_le_one hm).mpr
      nlinarith
    change y i ∈ Set.Icc (0 : ℝ) 1
    change -(2*(R/(centeredMesh q : ℝ))) ≤ y i-1/2 ∧
      y i-1/2 ≤ 2*(R/(centeredMesh q : ℝ)) at hi
    constructor <;> linarith

theorem e8CompactDefect_eq_scaled_row {R : ℝ} (hR : 0 < R) (q : ℕ) (hq : 2*R ≤ q) :
    e8CompactDefect R = (centeredMesh q : ℝ)^4 *
      (cubeQuadrature 8 (centeredMesh q)
        (nearObliqueRieszFour 8 e8Map (R/(centeredMesh q : ℝ)) (fun _ => (1/2 : ℝ))) -
       ∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (R/(centeredMesh q : ℝ))
        (fun _ => (1/2 : ℝ)) y) := by
  have hm : (centeredMesh q : ℝ) ≠ 0 := by positivity
  rw [cubeQuadrature_as_node_sum, e8Near_centered_cubeIntegral hR q hq]
  simp_rw [e8Near_centered_scale hR q]
  change e8CompactDefect R = (centeredMesh q : ℝ)^4 *
    ((∑ v : Fin 8 → NodeIndex (centeredMesh q), (centeredMesh q : ℝ)^4 *
      nearObliqueRieszFour 8 e8Map R 0 (centeredCubeCoordinate 8 q v))/(centeredMesh q : ℝ)^8 - _)
  rw [← Finset.mul_sum, ← e8CompactLatticeSum_eq_corrected hR q hq,
    e8CompactDefect, e8Compact_background_value hR]
  field_simp <;> ring

#print axioms e8CompactTerm_eq
#print axioms e8CompactTerm_zero
#print axioms e8CompactTerm_nonneg
#print axioms e8CompactTerm_zero_outside
#print axioms e8CompactTerm_summable
#print axioms e8CompactLatticeSum_eq_finite
#print axioms e8CompactLatticeSum_eq_corrected
#print axioms e8Compact_background_value
#print axioms e8CompactDefect_eq
#print axioms e8Near_centered_scale
#print axioms e8Near_centered_cubeIntegral
#print axioms e8CompactDefect_eq_scaled_row

end SphericalRiesz
