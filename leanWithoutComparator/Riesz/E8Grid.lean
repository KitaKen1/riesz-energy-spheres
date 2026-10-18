import Riesz.ObliqueAnnulus

/-!
# The unchanged interior grid is a translate of an integer basis image

Only the original interior nodes are used. Their differences are exactly
the mesh scale times integer combinations of the concrete basis rows.
Boundary corrections are not replaced by a new rule in each cell.
The equivalence with the parity description is proved separately.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz
open Boundary

def e8IntegerPoint (z : Fin 8 → ℤ) : Fin 8 → ℝ := e8Map (fun i => (z i : ℝ))

def interiorNodeIndex {m : ℕ} (j : Fin (m-8)) : NodeIndex m := Sum.inr (Sum.inl j)

theorem interiorNodeIndex_injective (m : ℕ) :
    Function.Injective (@interiorNodeIndex m) := by
  intro i j h
  simpa only [interiorNodeIndex, Sum.inr.injEq, Sum.inl.injEq] using h

theorem interiorRuleNode (m : ℕ) (j : Fin (m-8)) :
    ruleNode m (interiorNodeIndex j) = ((j:ℝ)+9/2)/(m:ℝ) := by
  simp only [ruleNode, unscaledRuleNode, interiorNodeIndex, Sum.elim_inr, Sum.elim_inl]
  congr 1
  ring

theorem interiorCubeNode (m : ℕ) (j : Fin 8 → Fin (m-8)) :
    cubeNode 8 m (fun i => interiorNodeIndex (j i)) =
      (m:ℝ)⁻¹ • (fun i => (j i : ℝ)) + (9/(2*(m:ℝ))) • (fun _ => (1:ℝ)) := by
  funext i
  simp only [cubeNode, interiorRuleNode, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

theorem e8InteriorNode_eq_translate (m : ℕ) (j : Fin 8 → Fin (m-8)) :
    e8TensorNode m (fun i => interiorNodeIndex (j i)) =
      (m:ℝ)⁻¹ • e8IntegerPoint (fun i => (j i : ℤ)) +
        (9/(2*(m:ℝ))) • e8Map (fun _ => (1:ℝ)) := by
  rw [e8TensorNode, interiorCubeNode, map_add, map_smul, map_smul]
  simp only [e8IntegerPoint, Int.cast_natCast]

theorem e8IntegerPoint_sub (z w : Fin 8 → ℤ) :
    e8IntegerPoint z-e8IntegerPoint w = e8IntegerPoint (z-w) := by
  rw [e8IntegerPoint, e8IntegerPoint, ← map_sub, e8IntegerPoint]
  congr 1
  funext i
  simp only [Pi.sub_apply, Int.cast_sub]

theorem e8InteriorNode_sub (m : ℕ) (j k : Fin 8 → Fin (m-8)) :
    e8TensorNode m (fun i => interiorNodeIndex (j i))-
      e8TensorNode m (fun i => interiorNodeIndex (k i)) =
      (m:ℝ)⁻¹ • e8IntegerPoint (fun i => (j i:ℤ)-(k i:ℤ)) := by
  rw [e8InteriorNode_eq_translate, e8InteriorNode_eq_translate, add_sub_add_right_eq_sub,
    ← smul_sub, e8IntegerPoint_sub]
  rfl

#print axioms interiorNodeIndex_injective
#print axioms interiorRuleNode
#print axioms interiorCubeNode
#print axioms e8InteriorNode_eq_translate
#print axioms e8IntegerPoint_sub
#print axioms e8InteriorNode_sub

end SphericalRiesz
