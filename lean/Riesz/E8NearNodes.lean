import Riesz.E8Separation

/-!
# A boundary-uniform bound on the actual near-node finite sum

The center is an actual node and the diagonal is erased. The original
corrections remain in place, including at the boundary. Quantitative
separation and local counts suffice for an O(m^-4) upper bound for each
fixed coordinate cutoff L/m. This is not the sharp lattice coefficient
or a sum-minus-integral estimate; the near integral is a separate task.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz
open Boundary

theorem e8TensorNode_kernel_bound {m : ℕ} (hm : 8 ≤ m)
    (v w : Fin 8 → NodeIndex m) (hvw : v ≠ w) :
    (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4 ≤ ((m:ℝ)/e8SeparationConstant)^4 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsep := e8TensorNode_dist_separated hm v w hvw
  have hinv : (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m w)))⁻¹ ≤ (m:ℝ)/e8SeparationConstant := by
    simpa only [one_div, inv_div] using
      one_div_le_one_div_of_le (div_pos e8SeparationConstant_pos hm0) hsep.le
  exact pow_le_pow_left₀ (inv_nonneg.mpr dist_nonneg) hinv 4

def e8NearNodeSum (m : ℕ) (L : ℝ) (v : Fin 8 → NodeIndex m) : ℝ := by
  classical
  exact (∑ w ∈ (cubeLocalNodeSet 8 m (cubeNode 8 m v) (L/(m:ℝ))).erase v,
    (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4)/(m:ℝ)^8

theorem e8NearNodeSum_nonneg (m : ℕ) (L : ℝ) (v : Fin 8 → NodeIndex m) :
    0 ≤ e8NearNodeSum m L v := by
  classical
  unfold e8NearNodeSum
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

/-- Uniform in the center node; no boundary-distance hypothesis is used. -/
theorem e8NearNodeSum_bound {m : ℕ} (hm : 8 ≤ m) (L : ℝ) (hL : 0 ≤ L)
    (v : Fin 8 → NodeIndex m) :
    e8NearNodeSum m L v ≤ (2*L+2)^8/(e8SeparationConstant^4*(m:ℝ)^4) := by
  classical
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let s := cubeLocalNodeSet 8 m (cubeNode 8 m v) (L/(m:ℝ))
  have hcard : (s.card:ℝ) ≤ (2*L+2)^8 := by
    have h := cubeNode_local_card_bound 8 hm (cubeNode 8 m v) (L/(m:ℝ))
      (div_nonneg hL hm0.le)
    have heq : 2*(m:ℝ)*(L/(m:ℝ))+2 = 2*L+2 := by
      field_simp [ne_of_gt hm0]
    simpa only [heq] using h
  have herase : ((s.erase v).card:ℝ) ≤ (s.card:ℝ) := by
    exact_mod_cast (Finset.card_erase_le : (s.erase v).card ≤ s.card)
  have hsum : (∑ w ∈ s.erase v,
      (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4) ≤ (2*L+2)^8*((m:ℝ)/e8SeparationConstant)^4 := by
    calc
      _ ≤ ∑ _w ∈ s.erase v, ((m:ℝ)/e8SeparationConstant)^4 :=
        Finset.sum_le_sum (fun w hw => e8TensorNode_kernel_bound hm v w
          (Ne.symm (Finset.mem_erase.mp hw).1))
      _ = ((s.erase v).card:ℝ)*((m:ℝ)/e8SeparationConstant)^4 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (herase.trans hcard) (by positivity)
  have heq : ((2*L+2)^8*((m:ℝ)/e8SeparationConstant)^4)/(m:ℝ)^8 =
      (2*L+2)^8/(e8SeparationConstant^4*(m:ℝ)^4) := by
    field_simp [ne_of_gt hm0, ne_of_gt e8SeparationConstant_pos]
  unfold e8NearNodeSum
  exact (div_le_div_of_nonneg_right hsum (by positivity)).trans_eq heq

#print axioms e8TensorNode_kernel_bound
#print axioms e8NearNodeSum_nonneg
#print axioms e8NearNodeSum_bound

end SphericalRiesz
