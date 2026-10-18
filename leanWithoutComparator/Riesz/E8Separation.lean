import Riesz.NodeSeparation
import Riesz.E8FarPhysical

/-!
# Physical Euclidean separation, including boundary corrections

The inverse basis map gives one fixed positive separation constant.
Its optimal value is unnecessary. These bounds apply to actual nodes,
with distinct indices, and not to an arbitrary free center.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz
open Boundary

theorem pi_norm_le_euclidean (v : Fin 8 → ℝ) :
    ‖v‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 8))‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 v) i

def e8SeparationConstant : ℝ := 1/(2*(‖e8InverseMap‖+1))

theorem e8SeparationConstant_pos : 0 < e8SeparationConstant := by
  unfold e8SeparationConstant
  positivity

theorem e8TensorNode_dist_separated {m : ℕ} (hm : 8 ≤ m)
    (v w : Fin 8 → NodeIndex m) (hvw : v ≠ w) :
    e8SeparationConstant/(m:ℝ) <
      dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hc : 0 < ‖e8InverseMap‖+1 := by positivity
  have hb : ‖cubeNode 8 m v-cubeNode 8 m w‖ ≤
      (‖e8InverseMap‖+1)*‖e8Map (cubeNode 8 m v-cubeNode 8 m w)‖ := by
    calc
      _ = ‖e8InverseMap (e8Map (cubeNode 8 m v-cubeNode 8 m w))‖ := by
        rw [e8InverseMap_e8Map]
      _ ≤ ‖e8InverseMap‖*‖e8Map (cubeNode 8 m v-cubeNode 8 m w)‖ :=
        e8InverseMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h := (cubeNode_norm_separated 8 hm v w hvw).trans_le hb
  have h' : (1/(2*(m:ℝ)))/(‖e8InverseMap‖+1) <
      ‖e8Map (cubeNode 8 m v-cubeNode 8 m w)‖ :=
    (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using h)
  have he : ‖e8Map (cubeNode 8 m v-cubeNode 8 m w)‖ ≤
      dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)) := by
    rw [dist_eq_norm]
    simpa only [e8TensorNode, map_sub, ← WithLp.toLp_sub] using
      pi_norm_le_euclidean (e8Map (cubeNode 8 m v-cubeNode 8 m w))
  have heq : (1/(2*(m:ℝ)))/(‖e8InverseMap‖+1) = e8SeparationConstant/(m:ℝ) := by
    unfold e8SeparationConstant
    rw [div_div, div_div]
    congr 1
    ring
  rw [heq] at h'
  exact h'.trans_le he

#print axioms pi_norm_le_euclidean
#print axioms e8SeparationConstant_pos
#print axioms e8TensorNode_dist_separated

end SphericalRiesz
