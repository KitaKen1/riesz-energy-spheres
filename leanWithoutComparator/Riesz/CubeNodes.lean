import Riesz.CubeQuadrature

/-!
# The actual finite tensor nodes

The recursive operator is the equal-weight average over all coordinate
choices. The nodes are distinct, lie in the open cube, and their number
is exactly m^d. This connects the operator bounds to a finite rule.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def cubeNode (d m : ℕ) (v : Fin d → NodeIndex m) : Fin d → ℝ :=
  fun i => ruleNode m (v i)

theorem cubeNode_card (d m : ℕ) (hm : 8 ≤ m) :
    Fintype.card (Fin d → NodeIndex m) = m^d := by
  rw [Fintype.card_pi_const, nodeIndex_card hm]

theorem cubeNode_injective (d m : ℕ) (hm : 8 ≤ m) : Function.Injective (cubeNode d m) := by
  intro v u h
  funext i
  exact ruleNode_injective hm (congrFun h i)

theorem cubeNode_mem_open (d m : ℕ) (hm : 8 ≤ m) (v : Fin d → NodeIndex m) :
    ∀ i, cubeNode d m v i ∈ Set.Ioo (0 : ℝ) 1 :=
  fun i => ruleNode_mem_unit hm (v i)

theorem cubeNode_cons (d m : ℕ) (j : NodeIndex m) (v : Fin d → NodeIndex m) :
    cubeNode (d+1) m (Fin.cons j v) = Fin.cons (ruleNode m j) (cubeNode d m v) := by
  funext i
  exact Fin.cases (by simp [cubeNode]) (fun k => by simp [cubeNode]) i

theorem cubeQuadrature_as_node_sum (d m : ℕ) (f : (Fin d → ℝ) → ℝ) :
    cubeQuadrature d m f =
      (∑ v : Fin d → NodeIndex m, f (cubeNode d m v))/(m : ℝ)^d := by
  induction d with
  | zero =>
    have h : ∀ v : Fin 0 → NodeIndex m, cubeNode 0 m v = Fin.elim0 :=
      fun _ => Subsingleton.elim _ _
    simp [cubeQuadrature, h]
  | succ d ih =>
    rw [cubeQuadrature, ih]
    simp_rw [quadrature_as_node_sum]
    rw [← Finset.sum_div, div_div, ← pow_succ']
    congr 1
    have heq := (Fin.consEquiv (fun _ : Fin (d+1) => NodeIndex m)).sum_comp
      (fun v => f (cubeNode (d+1) m v))
    have hsum : (∑ v : Fin (d+1) → NodeIndex m, f (cubeNode (d+1) m v)) =
        ∑ j : NodeIndex m, ∑ v : Fin d → NodeIndex m,
          f (Fin.cons (ruleNode m j) (cubeNode d m v)) := by
      simpa only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, cubeNode_cons] using heq.symm
    rw [hsum, Finset.sum_comm]

#print axioms cubeNode_card
#print axioms cubeNode_injective
#print axioms cubeQuadrature_as_node_sum

end SphericalRiesz.Boundary
