import E8Leech.ModularCoefficientBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A coarse exact bound for the actual weight-four q-series

For 0 <= q <= 1/400, sigma_3(n+1) <= (n+1)^4 <= 16^n.
Geometric summation gives 1 <= E4(q) <= 13/8. No floating-point
evaluation, global modular classification or coefficient oracle is needed.
The identification with Mathlib's normalized Eisenstein form is proved
separately from this elementary series estimate.
-/

noncomputable section

namespace E8Leech

open scoped BigOperators

def eisensteinFourQ (q : ℝ) : ℝ :=
  1 + 240 * ∑' n : ℕ, ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)

theorem fourth_power_succ_le_sixteen_pow (n : ℕ) : (n + 1) ^ 4 ≤ 16 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      (n + 1 + 1) ^ 4 ≤ (2 * (n + 1)) ^ 4 := by gcongr; omega
      _ = 16 * (n + 1) ^ 4 := by ring
      _ ≤ 16 * 16 ^ n := Nat.mul_le_mul_left 16 ih
      _ = 16 ^ (n + 1) := by ring

theorem sigma_three_succ_le_sixteen_pow (n : ℕ) :
    ArithmeticFunction.sigma 3 (n + 1) ≤ 16 ^ n :=
  (ArithmeticFunction.sigma_le_pow_succ 3 (n + 1)).trans
    (fourth_power_succ_le_sixteen_pow n)

theorem eisensteinFourQ_term_le_geometric {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1) ≤
      q * (16 * q) ^ n := by
  have hc : ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) ≤ (16 : ℝ) ^ n := by
    exact_mod_cast sigma_three_succ_le_sixteen_pow n
  calc
    _ ≤ (16 : ℝ) ^ n * q ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hq _)
    _ = q * (16 * q) ^ n := by rw [mul_pow, pow_succ]; ring

theorem summable_eisensteinFourQ {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    Summable (fun n : ℕ => ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)) := by
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 16 * q)
    (by linarith : 16 * q < 1)).mul_left q
  exact hg.of_nonneg_of_le (fun n => by positivity) (eisensteinFourQ_term_le_geometric hq)

theorem eisensteinFourQ_lower {q : ℝ} (hq : 0 ≤ q) : 1 ≤ eisensteinFourQ q := by
  unfold eisensteinFourQ
  have ht : 0 ≤ ∑' n : ℕ, ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1) :=
    tsum_nonneg (fun n => by positivity)
  linarith only [ht]

theorem eisensteinFourQ_upper {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    eisensteinFourQ q ≤ 13 / 8 := by
  have hden : 0 < 1 - 16 * q := by linarith only [hqsmall]
  have hratio : q / (1 - 16 * q) ≤ 1 / 384 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hqsmall]
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 16 * q)
    (by linarith : 16 * q < 1)).mul_left q
  have hsum := (summable_eisensteinFourQ hq hqsmall).tsum_le_tsum
    (eisensteinFourQ_term_le_geometric hq) hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity : 0 ≤ 16 * q)
    (by linarith : 16 * q < 1), ← div_eq_mul_inv] at hsum
  unfold eisensteinFourQ
  linarith only [hsum, hratio]

end E8Leech
