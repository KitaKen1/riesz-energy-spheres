import Riesz.Boundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Equal-weight boundary rule: the finite certificate

There are four left nodes, `m - 8` ordinary midpoint nodes, and four
reflected right nodes.  Every node has weight `1 / m`.
This file proves polynomial exactness only.  A uniform sixth-derivative
error bound, and especially singular-kernel estimates, remain separate.
-/

set_option autoImplicit false

noncomputable section

namespace SphericalRiesz.Boundary

def midpointPrimitive : Fin 6 → ℝ → ℝ := ![
  fun x => x,
  fun x => x^2/2,
  fun x => x^3/3 - x/12,
  fun x => x^4/4 - x^2/8,
  fun x => x^5/5 - x^3/6 + 7*x/240,
  fun x => x^6/6 - 5*x^4/24 + 7*x^2/96]

private theorem midpointPrimitive_step (k : Fin 6) (x : ℝ) :
    midpointPrimitive k (x + 1) - midpointPrimitive k x = (x + 1/2)^k.val := by
  fin_cases k <;> norm_num [midpointPrimitive] <;> ring

/-- Finite telescoping, rather than a general Euler–Maclaurin theorem. -/
theorem shifted_midpoint_sum (k : Fin 6) (a : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + a + 1/2)^k.val) =
      midpointPrimitive k ((n : ℝ) + a) - midpointPrimitive k a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h := midpointPrimitive_step k ((n : ℝ) + a)
    rw [show (n : ℝ) + 1 + a = ((n : ℝ) + a) + 1 by ring]
    linarith

private def pairFormula : Fin 6 → ℝ → ℝ := ![
  fun _ => 8,
  fun m => 4*m,
  fun m => 4*m^2 - (191/12)*m + 42,
  fun m => 4*m^3 - (191/8)*m^2 + 63*m,
  fun m => 4*m^4 - (191/6)*m^3 + 126*m^2 - (59527/240)*m + 777/2,
  fun m => 4*m^5 - (955/24)*m^4 + 210*m^3 - (59527/96)*m^2 + (3885/4)*m]

private def pairMonomial : Fin 6 → ℝ → ℝ → ℝ := ![
  fun _ _ => 2,
  fun m _ => m,
  fun m x => m^2 - 2*m*x + 2*x^2,
  fun m x => m^3 - 3*m^2*x + 3*m*x^2,
  fun m x => m^4 - 4*m^3*x + 6*m^2*x^2 - 4*m*x^3 + 2*x^4,
  fun m x => m^5 - 5*m^4*x + 10*m^3*x^2 - 10*m^2*x^3 + 5*m*x^4]

private theorem pairMonomial_eq (k : Fin 6) (m x : ℝ) :
    x^k.val + (m-x)^k.val = pairMonomial k m x := by
  fin_cases k <;> norm_num [pairMonomial] <;> ring

private theorem node_pair_sum (k : Fin 6) (m : ℝ) :
    (∑ i : Fin 4, ((node i)^k.val + (m-node i)^k.val)) = pairFormula k m := by
  simp_rw [pairMonomial_eq]
  obtain ⟨h1, h2, h3, h4⟩ := node_power_moments
  fin_cases k <;>
    simp [pairMonomial, pairFormula, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3, h4] <;> ring

/-- Exactly four left nodes, m-8 interior nodes, and four right nodes. -/
abbrev NodeIndex (m : ℕ) := Fin 4 ⊕ (Fin (m-8) ⊕ Fin 4)

theorem nodeIndex_card {m : ℕ} (hm : 8 ≤ m) : Fintype.card (NodeIndex m) = m := by
  simp only [NodeIndex, Fintype.card_sum, Fintype.card_fin]
  omega

def unscaledRuleNode (m : ℕ) : NodeIndex m → ℝ :=
  Sum.elim node (Sum.elim (fun j => (j : ℝ)+4+1/2) (fun i => (m : ℝ)-node i))

theorem node_between_zero_four (i : Fin 4) : 0 < node i ∧ node i < 4 := by
  have h := node_spec i
  fin_cases i <;> norm_num [lower, upper] at h ⊢ <;> constructor <;> linarith

private theorem middle_between {m : ℕ} (hm : 8 ≤ m) (j : Fin (m-8)) :
    4 < (j : ℝ)+4+1/2 ∧ (j : ℝ)+4+1/2 < (m : ℝ)-4 := by
  have hj : (j : ℕ) < m-8 := j.isLt
  have hj' : (j : ℕ)+9 ≤ m := by omega
  have hreal : (j : ℝ)+9 ≤ (m : ℝ) := by exact_mod_cast hj'
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor <;> linarith

theorem unscaledRuleNode_injective {m : ℕ} (hm : 8 ≤ m) :
    Function.Injective (unscaledRuleNode m) := by
  rw [unscaledRuleNode, Sum.elim_injective]
  refine ⟨node_injective, ?_, ?_⟩
  · rw [Sum.elim_injective]
    refine ⟨?_, ?_, ?_⟩
    · intro i j h
      apply Fin.ext
      have : (i : ℝ) = (j : ℝ) := by linarith
      exact_mod_cast this
    · intro i j h
      apply node_injective
      linarith
    · intro j i h
      have hj := (middle_between hm j).2
      have hi := (node_between_zero_four i).2
      linarith
  · intro i x h
    have hi := (node_between_zero_four i).2
    rcases x with j | j
    · have hj := (middle_between hm j).1
      change node i = (j : ℝ)+4+1/2 at h
      linarith
    · have hj := (node_between_zero_four j).2
      have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
      change node i = (m : ℝ)-node j at h
      linarith

def ruleNode (m : ℕ) (i : NodeIndex m) : ℝ := unscaledRuleNode m i / m

theorem ruleNode_injective {m : ℕ} (hm : 8 ≤ m) : Function.Injective (ruleNode m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  intro i j h
  apply unscaledRuleNode_injective hm
  exact (div_left_inj' hm0).mp h

theorem ruleNode_mem_unit {m : ℕ} (hm : 8 ≤ m) (i : NodeIndex m) :
    ruleNode m i ∈ Set.Ioo (0 : ℝ) 1 := by
  have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  unfold ruleNode
  rw [Set.mem_Ioo, div_pos_iff_of_pos_right hm0, div_lt_one hm0]
  rcases i with i | (i | i)
  · have hi := node_between_zero_four i
    change 0 < node i ∧ node i < (m : ℝ)
    constructor <;> linarith
  · have hi := middle_between hm i
    change 0 < (i : ℝ)+4+1/2 ∧ (i : ℝ)+4+1/2 < (m : ℝ)
    constructor <;> linarith
  · have hi := node_between_zero_four i
    change 0 < (m : ℝ)-node i ∧ (m : ℝ)-node i < (m : ℝ)
    constructor <;> linarith

/-- The actual positive equal-weight quadrature functional. -/
def quadrature (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((∑ i : Fin 4, f (node i / m)) +
    (∑ j ∈ Finset.range (m-8), f (((j : ℝ)+4+1/2) / m)) +
    (∑ i : Fin 4, f (((m : ℝ)-node i) / m))) / m

theorem quadrature_as_node_sum (m : ℕ) (f : ℝ → ℝ) :
    quadrature m f = (∑ i : NodeIndex m, f (ruleNode m i)) / m := by
  simp [quadrature, NodeIndex, ruleNode, unscaledRuleNode, Fintype.sum_sum_type,
    ← Fin.sum_univ_eq_sum_range, add_assoc]

theorem quadrature_add (m : ℕ) (f g : ℝ → ℝ) :
    quadrature m (fun x => f x + g x) = quadrature m f + quadrature m g := by
  simp only [quadrature, Finset.sum_add_distrib]
  ring

theorem quadrature_mul_const (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    quadrature m (fun x => c * f x) = c * quadrature m f := by
  simp only [quadrature, ← Finset.mul_sum]
  ring

theorem quadrature_finset_sum {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → ℝ → ℝ) :
    quadrature m (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, quadrature m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadrature]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [quadrature_add, ih]

private theorem unscaled_power_sum {m : ℕ} (hm : 8 ≤ m) (k : Fin 6) :
    (∑ i : Fin 4, (node i)^k.val) +
      (∑ j ∈ Finset.range (m-8), ((j : ℝ)+4+1/2)^k.val) +
      (∑ i : Fin 4, ((m : ℝ)-node i)^k.val) = (m : ℝ)^(k.val+1)/(k.val+1) := by
  rw [shifted_midpoint_sum]
  have hn : ((m-8 : ℕ) : ℝ) = (m : ℝ)-8 := by
    rw [Nat.cast_sub hm]; norm_num
  have hp := node_pair_sum k (m : ℝ)
  rw [Finset.sum_add_distrib] at hp
  rw [hn]
  have hcombine : (∑ i : Fin 4, (node i)^k.val) +
      (midpointPrimitive k ((m : ℝ)-8+4) - midpointPrimitive k 4) +
      (∑ i : Fin 4, ((m : ℝ)-node i)^k.val) =
      pairFormula k m + (midpointPrimitive k ((m : ℝ)-8+4) - midpointPrimitive k 4) := by
    linarith
  rw [hcombine]
  fin_cases k <;> norm_num [midpointPrimitive, pairFormula] <;> ring

/-- Exact integration of every monomial of degree at most five, for every m ≥ 8. -/
theorem quadrature_monomial {m : ℕ} (hm : 8 ≤ m) (k : Fin 6) :
    quadrature m (fun x => x^k.val) = 1 / (k.val+1 : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold quadrature
  simp only [div_pow, ← Finset.sum_div]
  rw [← add_div, ← add_div, unscaled_power_sum hm]
  rw [pow_succ]
  field_simp

/-- The value agrees with the ordinary integral on [0,1]. -/
theorem quadrature_monomial_integral {m : ℕ} (hm : 8 ≤ m) (k : Fin 6) :
    quadrature m (fun x => x^k.val) = ∫ x in (0 : ℝ)..1, x^k.val := by
  rw [quadrature_monomial hm, integral_pow]
  simp

/-- Every polynomial written with six coefficients is integrated exactly. -/
theorem quadrature_degree_five {m : ℕ} (hm : 8 ≤ m) (a : Fin 6 → ℝ) :
    quadrature m (fun x => ∑ k : Fin 6, a k * x^k.val) =
      ∫ x in (0 : ℝ)..1, ∑ k : Fin 6, a k * x^k.val := by
  rw [quadrature_finset_sum, intervalIntegral.integral_finsetSum]
  · simp_rw [quadrature_mul_const, quadrature_monomial_integral hm,
      intervalIntegral.integral_const_mul]
  · intro k _
    exact (by fun_prop : Continuous (fun x : ℝ => a k * x^k.val)).intervalIntegrable _ _

#print axioms quadrature_monomial
#print axioms quadrature_monomial_integral
#print axioms ruleNode_injective
#print axioms ruleNode_mem_unit
#print axioms quadrature_degree_five

end SphericalRiesz.Boundary
