import Riesz.NodeCounting

/-!
# Quantitative separation of the original corrected nodes

Distinct midpoint labels differ by at least one. Each original node is
within a quarter cell of its label, so distinct nodes are more than half
a cell apart. This retains the original rule, including boundary nodes.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

theorem unscaledRuleNode_sub_gt_half {m : ℕ} (hm : 8 ≤ m)
    (i j : NodeIndex m) (hij : midpointLabel m i < midpointLabel m j) :
    1/2 < unscaledRuleNode m j-unscaledRuleNode m i := by
  have hgap : (midpointLabel m i : ℝ)+1 ≤ midpointLabel m j := by
    exact_mod_cast (Nat.succ_le_of_lt hij)
  have hi := abs_lt.mp (unscaledRuleNode_close_to_label hm i)
  have hj := abs_lt.mp (unscaledRuleNode_close_to_label hm j)
  linarith

theorem unscaledRuleNode_separated {m : ℕ} (hm : 8 ≤ m)
    (i j : NodeIndex m) (hij : i ≠ j) :
    1/2 < |unscaledRuleNode m i-unscaledRuleNode m j| := by
  have hlabel : midpointLabel m i ≠ midpointLabel m j :=
    fun h => hij (midpointLabel_injective hm h)
  rcases lt_or_gt_of_ne hlabel with h | h
  · rw [abs_sub_comm]
    exact (unscaledRuleNode_sub_gt_half hm i j h).trans_le (le_abs_self _)
  · exact (unscaledRuleNode_sub_gt_half hm j i h).trans_le (le_abs_self _)

theorem ruleNode_separated {m : ℕ} (hm : 8 ≤ m)
    (i j : NodeIndex m) (hij : i ≠ j) :
    1/(2*(m:ℝ)) < |ruleNode m i-ruleNode m j| := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := div_lt_div_of_pos_right (unscaledRuleNode_separated hm i j hij) hm0
  simpa only [ruleNode, ← sub_div, abs_div, abs_of_pos hm0, div_div] using h

theorem cubeNode_coordinate_separated (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (v w : Fin d → NodeIndex m) (hvw : v ≠ w) :
    ∃ i : Fin d, 1/(2*(m:ℝ)) < |cubeNode d m v i-cubeNode d m w i| := by
  have h : ∃ i, v i ≠ w i := by
    by_contra hn
    exact hvw (funext (fun i => by simpa using (not_exists.mp hn i)))
  obtain ⟨i, hi⟩ := h
  exact ⟨i, ruleNode_separated hm (v i) (w i) hi⟩

theorem cubeNode_norm_separated (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (v w : Fin d → NodeIndex m) (hvw : v ≠ w) :
    1/(2*(m:ℝ)) < ‖cubeNode d m v-cubeNode d m w‖ := by
  obtain ⟨i, hi⟩ := cubeNode_coordinate_separated d hm v w hvw
  exact hi.trans_le (by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (cubeNode d m v-cubeNode d m w) i)

#print axioms unscaledRuleNode_sub_gt_half
#print axioms unscaledRuleNode_separated
#print axioms ruleNode_separated
#print axioms cubeNode_coordinate_separated
#print axioms cubeNode_norm_separated

end SphericalRiesz.Boundary
