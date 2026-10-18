import Riesz.E8DampedQuadrature
import Riesz.CenteredGrid
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The actual damped E8 annular discrepancy on the whole integer lattice

The unchanged centered corrected rule is used only as a finite certificate.
Its actual cube integral is moved to the whole coordinate space by support
and the eight-dimensional Haar scaling formula. No lattice enumeration.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
namespace SphericalRiesz
open Boundary

def e8AnnularDefect (u R : ℝ) : ℝ :=
  (∑' z : Fin 8 → ℤ, e8ScaledDampedAnnulus u R 0 (fun i => (z i : ℝ))) -
    ∫ y : Fin 8 → ℝ, e8ScaledDampedAnnulus u R 0 y

theorem e8DampedAnnulus_integer_summable (u : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (fun z : Fin 8 → ℤ => e8ScaledDampedAnnulus u R 0 (fun i => (z i : ℝ))) := by
  obtain ⟨q, hq⟩ := exists_nat_ge (2*R)
  apply summable_of_ne_finset_zero (s := centeredIntegerBox 8 q)
  intro z hz
  apply e8ScaledDampedAnnulus_zero_outside u R hR
  intro hb
  apply hz
  rw [centeredIntegerBox_mem]
  intro i
  have hi := abs_le.mp (hb i)
  simp only [Pi.zero_apply, sub_zero] at hi
  constructor
  · exact_mod_cast (show -(q : ℝ) ≤ (z i : ℝ) by linarith)
  · exact_mod_cast (show (z i : ℝ) ≤ (q : ℝ) by linarith)

theorem e8DampedAnnulus_centered_node_sum (u : ℝ) {R : ℝ} (hR : 0 < R)
    (q : ℕ) (hq : 2*R ≤ q) :
    (∑' z : Fin 8 → ℤ, e8ScaledDampedAnnulus u R 0 (fun i => (z i : ℝ))) =
      ∑ v : Fin 8 → NodeIndex (centeredMesh q),
        e8ScaledDampedAnnulus u R 0 (centeredCubeCoordinate 8 q v) := by
  symm
  apply centeredNodeSum_eq_tsum 8 q (2*R) hq
  intro y hy
  apply e8ScaledDampedAnnulus_zero_outside u R hR 0 y
  simpa only [Pi.zero_apply, sub_zero] using hy

theorem e8DampedAnnulus_centered_scale (u R : ℝ) (q : ℕ) (y : Fin 8 → ℝ) :
    e8ScaledDampedAnnulus u (R/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ)) y =
      (centeredMesh q : ℝ)^4 * e8ScaledDampedAnnulus u R 0
        ((centeredMesh q : ℝ) • (y-(fun _ => (1/2:ℝ)))) := by
  unfold e8ScaledDampedAnnulus
  simp only [sub_zero, inv_div, smul_smul]
  have hs : (centeredMesh q : ℝ)/R = R⁻¹*(centeredMesh q : ℝ) := by ring
  rw [hs, mul_pow]
  ring

theorem e8DampedAnnulus_centered_integral (u R : ℝ) (q : ℕ) :
    (∫ y : Fin 8 → ℝ,
      e8ScaledDampedAnnulus u (R/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ)) y) =
        (centeredMesh q : ℝ)^4 * ((centeredMesh q : ℝ)^8)⁻¹ *
          ∫ y : Fin 8 → ℝ, e8ScaledDampedAnnulus u R 0 y := by
  simp_rw [e8DampedAnnulus_centered_scale]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : Fin 8 → ℝ => e8ScaledDampedAnnulus u R 0 ((centeredMesh q : ℝ) • y))]
  rw [Measure.integral_comp_smul_of_nonneg volume (e8ScaledDampedAnnulus u R 0)
    (centeredMesh q : ℝ) (hR := by positivity)]
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, Nat.mul_one,
    smul_eq_mul, mul_assoc]

theorem e8DampedAnnulus_centered_cube_integral (u : ℝ) {R : ℝ} (hR : 0 < R)
    (q : ℕ) (hq : 2*R ≤ q) :
    (∫ y in UnitCube 8,
      e8ScaledDampedAnnulus u (R/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ)) y) =
        (centeredMesh q : ℝ)^4 * ((centeredMesh q : ℝ)^8)⁻¹ *
          ∫ y : Fin 8 → ℝ, e8ScaledDampedAnnulus u R 0 y := by
  have hm : (0:ℝ) < centeredMesh q := by positivity
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact e8DampedAnnulus_centered_integral u R q
  · intro y hy
    apply e8ScaledDampedAnnulus_zero_outside u _ (div_pos hR hm)
    intro hb
    apply hy
    intro i
    have hi := abs_le.mp (hb i)
    have hh : 2*(R/(centeredMesh q : ℝ)) ≤ 1/2 := by
      have hq0 : (0:ℝ) ≤ q := by positivity
      have hmesh : (centeredMesh q : ℝ) = 2*(q:ℝ)+9 := by simp [centeredMesh]
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
      rw [show 2*(R/(centeredMesh q : ℝ))*2 = (4*R)/(centeredMesh q : ℝ) by ring]
      apply (div_le_one hm).mpr
      nlinarith
    change y i ∈ Set.Icc (0:ℝ) 1
    change -(2*(R/(centeredMesh q : ℝ))) ≤ y i-1/2 ∧
      y i-1/2 ≤ 2*(R/(centeredMesh q : ℝ)) at hi
    constructor <;> linarith

theorem e8AnnularDefect_eq_scaled_row {u R : ℝ} (hu : 0 ≤ u) (hR : 0 < R)
    (q : ℕ) (hq : 2*R ≤ q) :
    e8AnnularDefect u R = (centeredMesh q : ℝ)^4 *
      (cubeQuadrature 8 (centeredMesh q)
        (e8ScaledDampedAnnulus u (R/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ))) -
       cubeIntegral 8
        (e8ScaledDampedAnnulus u (R/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ)))) := by
  have hm : (centeredMesh q : ℝ) ≠ 0 := by positivity
  rw [cubeQuadrature_as_node_sum, cubeIntegral_eq_setIntegral 8 _
    (e8ScaledDampedAnnulus_contDiff hu _ _).continuous,
    e8DampedAnnulus_centered_cube_integral u hR q hq]
  simp_rw [e8DampedAnnulus_centered_scale]
  change e8AnnularDefect u R = (centeredMesh q : ℝ)^4 *
    ((∑ v : Fin 8 → NodeIndex (centeredMesh q), (centeredMesh q : ℝ)^4 *
      e8ScaledDampedAnnulus u R 0 (centeredCubeCoordinate 8 q v))/(centeredMesh q : ℝ)^8 - _)
  rw [← Finset.mul_sum, ← e8DampedAnnulus_centered_node_sum u hR q hq, e8AnnularDefect]
  field_simp <;> ring

/-- Whole-lattice/whole-space discrepancy; one C for every u≥0 and R≥1. -/
theorem e8AnnularDefect_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ R : ℝ, 1 ≤ R →
      |e8AnnularDefect u R| ≤ C/R^2 := by
  obtain ⟨C, hC, hb⟩ := e8ScaledDampedAnnulus_eight_bound
  refine ⟨C, hC, ?_⟩
  intro u hu R hR
  have hR0 : 0 < R := by linarith
  obtain ⟨q, hq⟩ := exists_nat_ge (2*R)
  have hm : (0:ℝ) < centeredMesh q := by positivity
  have hm8 : 8 ≤ centeredMesh q := by simp only [centeredMesh]; omega
  rw [e8AnnularDefect_eq_scaled_row hu hR0 q hq, abs_mul,
    abs_of_nonneg (pow_nonneg hm.le 4)]
  have hmesh : 1/(centeredMesh q : ℝ) ≤ R/(centeredMesh q : ℝ) :=
    div_le_div_of_nonneg_right hR hm.le
  calc
    _ ≤ (centeredMesh q : ℝ)^4 *
        (C/((centeredMesh q : ℝ)^6*(R/(centeredMesh q : ℝ))^2)) :=
      mul_le_mul_of_nonneg_left (hb u hu _ hm8 _ (div_pos hR0 hm) hmesh _) (by positivity)
    _ = C/R^2 := by field_simp [hm.ne', hR0.ne']

#print axioms e8DampedAnnulus_integer_summable
#print axioms e8DampedAnnulus_centered_node_sum
#print axioms e8DampedAnnulus_centered_scale
#print axioms e8DampedAnnulus_centered_integral
#print axioms e8DampedAnnulus_centered_cube_integral
#print axioms e8AnnularDefect_eq_scaled_row
#print axioms e8AnnularDefect_uniform_bound
end SphericalRiesz
