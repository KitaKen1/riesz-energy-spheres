import Riesz.E8FlatPhysicalRow

/-!
# Uniform removal of the actual singular near potential

The difference from the existing smooth far cutoff is the actual near
integral, uniformly bounded by C*(r/2)^4. The unchanged finite quadrature
has norm one, so its potential average has the same perturbation bound.
The derivative/face estimate and C6 regularity of the regularized
potential remain separate proof obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz
open Boundary

def e8Potential (x : Fin 8 → ℝ) : ℝ :=
  ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map x y

def e8FarPotential (r : ℝ) (x : Fin 8 → ℝ) : ℝ :=
  ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y

theorem e8Potential_far_error (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    |e8Potential x-e8FarPotential r x| ≤ e8NearIntegralConstant*(r/2)^4 := by
  unfold e8Potential e8FarPotential
  rw [e8Kernel_integral_partition r hr x, add_sub_cancel_left]
  exact e8Near_cubeIntegral_bound (r/2) (by positivity) x

theorem e8Potential_far_quadrature_error {m : ℕ} (hm : 8 ≤ m)
    (r : ℝ) (hr : 0 < r) :
    |cubeQuadrature 8 m e8Potential-cubeQuadrature 8 m (e8FarPotential r)| ≤
      e8NearIntegralConstant*(r/2)^4 := by
  rw [← cubeQuadrature_sub]
  exact cubeQuadrature_abs_le 8 m hm _ _ (fun x _ => e8Potential_far_error r hr x)

theorem e8Potential_far_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ x : Fin 8 → ℝ,
      |e8Potential x-e8FarPotential r x| ≤ ε := by
  intro ε hε
  have hC := e8NearIntegralConstant_nonneg
  let r := min 1 (ε/(e8NearIntegralConstant+1))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hre : r ≤ ε/(e8NearIntegralConstant+1) := min_le_right _ _
  have hs : (e8NearIntegralConstant+1)*r ≤ ε := by
    simpa only [mul_comm] using
      (le_div_iff₀ (by positivity : 0 < e8NearIntegralConstant+1)).mp hre
  have hp : (r/2)^4 ≤ r := by
    calc
      _ ≤ r^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ ≤ r := pow_le_of_le_one hr.le hr1 (by norm_num : (4:ℕ) ≠ 0)
  refine ⟨r, hr, fun x => ?_⟩
  calc
    _ ≤ e8NearIntegralConstant*(r/2)^4 := e8Potential_far_error r hr x
    _ ≤ e8NearIntegralConstant*r := mul_le_mul_of_nonneg_left hp hC
    _ ≤ ε := by nlinarith

#print axioms e8Potential_far_error
#print axioms e8Potential_far_quadrature_error
#print axioms e8Potential_far_uniform

end SphericalRiesz
