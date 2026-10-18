import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Exact boundary nodes for the sixth-order equal-weight rule

The four nodes are specified by rational isolating intervals and a quartic.
No numerical root approximation enters the proof.
-/

set_option autoImplicit false

noncomputable section

namespace SphericalRiesz.Boundary

def P (x : ℝ) : ℝ :=
  39813120 * x ^ 4 - 316846080 * x ^ 3 + 842745600 * x ^ 2 -
    840595488 * x + 226287557

def lower : Fin 4 → ℝ := ![418/1000, 1575/1000, 2453/1000, 3510/1000]
def upper : Fin 4 → ℝ := ![419/1000, 1576/1000, 2454/1000, 3511/1000]

theorem continuous_P : Continuous P := by unfold P; fun_prop

private theorem root_of_opposite_signs {a b : ℝ} (hab : a < b)
    (hsign : (P a < 0 ∧ 0 < P b) ∨ (P b < 0 ∧ 0 < P a)) :
    ∃ x, a < x ∧ x < b ∧ P x = 0 := by
  rcases hsign with h | h
  · obtain ⟨x, hx, hzero⟩ :=
      intermediate_value_Ioo hab.le continuous_P.continuousOn h
    exact ⟨x, hx.1, hx.2, hzero⟩
  · obtain ⟨x, hx, hzero⟩ :=
      intermediate_value_Ioo' hab.le continuous_P.continuousOn h
    exact ⟨x, hx.1, hx.2, hzero⟩

theorem node_exists (i : Fin 4) :
    ∃ x, lower i < x ∧ x < upper i ∧ P x = 0 := by
  apply root_of_opposite_signs
  · fin_cases i <;> norm_num [lower, upper]
  · fin_cases i <;> norm_num [lower, upper, P]

noncomputable def node (i : Fin 4) : ℝ := Classical.choose (node_exists i)

theorem node_spec (i : Fin 4) :
    lower i < node i ∧ node i < upper i ∧ P (node i) = 0 :=
  Classical.choose_spec (node_exists i)

theorem node_root (i : Fin 4) : P (node i) = 0 := (node_spec i).2.2

theorem node_strictMono : StrictMono node := by
  intro i j hij
  have hi := node_spec i
  have hj := node_spec j
  have hsep : upper i < lower j := by
    fin_cases i <;> fin_cases j <;> (try { norm_num at hij }) <;> norm_num [lower, upper]
  linarith

theorem node_injective : Function.Injective node := node_strictMono.injective

theorem node_close_to_midpoint (i : Fin 4) :
    |node i - ((i : ℕ) + (1/2 : ℝ))| < 1/4 := by
  have hi := node_spec i
  fin_cases i <;> norm_num [lower, upper] at hi ⊢ <;> (try rw [abs_lt]) <;> (try constructor) <;> linarith

def normalizedPolynomial : Polynomial ℝ :=
  .X ^ 4 - .C (191/24) * .X ^ 3 + .C (24385/1152) * .X ^ 2 -
    .C (8756203/414720) * .X + .C (226287557/39813120)

theorem normalizedPolynomial_eval (x : ℝ) :
    normalizedPolynomial.eval x = P x / 39813120 := by
  simp [normalizedPolynomial, P]
  ring

theorem normalizedPolynomial_node (i : Fin 4) :
    normalizedPolynomial.eval (node i) = 0 := by
  rw [normalizedPolynomial_eval, node_root]
  norm_num

private def e1 : ℝ := node 0 + node 1 + node 2 + node 3
private def e2 : ℝ := node 0 * node 1 + node 0 * node 2 + node 0 * node 3 +
  node 1 * node 2 + node 1 * node 3 + node 2 * node 3
private def e3 : ℝ := node 0 * node 1 * node 2 + node 0 * node 1 * node 3 +
  node 0 * node 2 * node 3 + node 1 * node 2 * node 3
private def e4 : ℝ := node 0 * node 1 * node 2 * node 3

private def residual : Polynomial ℝ :=
  .C (e1 - 191/24) * .X ^ 3 + .C (24385/1152 - e2) * .X ^ 2 +
    .C (e3 - 8756203/414720) * .X + .C (226287557/39813120 - e4)

private theorem residual_identity : residual = normalizedPolynomial -
    (Polynomial.X - .C (node 0)) * (Polynomial.X - .C (node 1)) *
      (Polynomial.X - .C (node 2)) * (Polynomial.X - .C (node 3)) := by
  unfold residual normalizedPolynomial e1 e2 e3 e4
  simp only [map_add, map_sub, map_mul]
  ring

private theorem residual_zero : residual = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero residual node_injective
  · intro i
    rw [residual_identity]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, normalizedPolynomial_node]
    fin_cases i <;> norm_num
  · have h : residual.natDegree ≤ 3 := by unfold residual; compute_degree
    simpa using Nat.lt_of_le_of_lt h (by norm_num : 3 < 4)

private theorem elementary_moments :
    e1 = 191/24 ∧ e2 = 24385/1152 ∧ e3 = 8756203/414720 ∧
      e4 = 226287557/39813120 := by
  have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 3) residual_zero
  have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) residual_zero
  have h3 := congrArg (fun p : Polynomial ℝ => p.coeff 1) residual_zero
  have h4 := congrArg (fun p : Polynomial ℝ => p.coeff 0) residual_zero
  simp only [residual, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Exact factorization, without quartic radicals. -/
theorem normalizedPolynomial_factor : normalizedPolynomial =
    (Polynomial.X - .C (node 0)) * (Polynomial.X - .C (node 1)) *
      (Polynomial.X - .C (node 2)) * (Polynomial.X - .C (node 3)) := by
  apply sub_eq_zero.mp
  rw [← residual_identity, residual_zero]

/-- The first four power sums determine the boundary correction certificate. -/
theorem node_power_moments :
    (∑ i : Fin 4, node i) = 191/24 ∧
    (∑ i : Fin 4, node i ^ 2) = 21 ∧
    (∑ i : Fin 4, node i ^ 3) = 59527/960 ∧
    (∑ i : Fin 4, node i ^ 4) = 777/4 := by
  obtain ⟨h1, h2, h3, h4⟩ := elementary_moments
  have hsq : node 0 ^ 2 + node 1 ^ 2 + node 2 ^ 2 + node 3 ^ 2 = e1^2 - 2*e2 := by
    unfold e1 e2; ring
  have hcub : node 0 ^ 3 + node 1 ^ 3 + node 2 ^ 3 + node 3 ^ 3 =
      e1^3 - 3*e1*e2 + 3*e3 := by unfold e1 e2 e3; ring
  have hfour : node 0 ^ 4 + node 1 ^ 4 + node 2 ^ 4 + node 3 ^ 4 =
      e1^4 - 4*e1^2*e2 + 2*e2^2 + 4*e1*e3 - 4*e4 := by
    unfold e1 e2 e3 e4; ring
  simp only [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  dsimp at *
  constructor
  · simpa only [e1, add_assoc] using h1
  constructor
  · rw [← add_assoc, ← add_assoc, hsq, h1, h2]; norm_num
  constructor
  · rw [← add_assoc, ← add_assoc, hcub, h1, h2, h3]; norm_num
  · rw [← add_assoc, ← add_assoc, hfour, h1, h2, h3, h4]; norm_num

/-- The fifth power sum is not a free parameter: it follows from the quartic. -/
theorem node_power_fifth : (∑ i : Fin 4, node i^5) = 120684538849/191102976 := by
  obtain ⟨h1, h2, h3, h4⟩ := node_power_moments
  have h (i : Fin 4) : node i^5 = (191/24)*node i^4 -
      (24385/1152)*node i^3 + (8756203/414720)*node i^2 -
      (226287557/39813120)*node i := by
    have hi := normalizedPolynomial_node i
    simp [normalizedPolynomial] at hi
    linear_combination node i * hi
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3, h4]
  norm_num

#print axioms node_exists
#print axioms node_injective
#print axioms node_close_to_midpoint
#print axioms normalizedPolynomial_factor
#print axioms node_power_moments

end SphericalRiesz.Boundary
