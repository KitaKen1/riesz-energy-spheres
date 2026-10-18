import E8Leech.EisensteinQBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Exact positive bounds for the Euler product and the Klein q-quotient

The actual product P(q) = prod (1-q^(n+1)) is bounded using the finite
Weierstrass inequality, then passed to its limit. On 0 < q <= 1/400,
9*q/10 <= q*P(q)^24 <= q and 1/q <= E4(q)^3/(q*P(q)^24) <= 5/q.
Actual modular-form identification is handled separately.
-/

noncomputable section

namespace E8Leech

open scoped BigOperators

def eulerQProduct (q : ℝ) : ℝ := ∏' n : ℕ, (1 - q ^ (n + 1))

def discriminantQ (q : ℝ) : ℝ := q * (eulerQProduct q) ^ 24

def kleinJQ (q : ℝ) : ℝ := (eisensteinFourQ q) ^ 3 / discriminantQ q

theorem finite_one_sub_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) :
    1 - ∑ n ∈ s, f n ≤ ∏ n ∈ s, (1 - f n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ n ∈ s, f n := Finset.sum_nonneg (fun n _ => h0 n)
    have hi := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (h1 a))
    have hcross := mul_nonneg (h0 a) hs
    nlinarith only [hi, hcross]

theorem multipliable_eulerQProduct {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
  have hs : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq hq1)
  have hm := multipliable_one_add_of_summable hs.neg.norm
  simpa only [sub_eq_add_neg] using hm

theorem eulerQProduct_lower {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    1 - q / (1 - q) ≤ eulerQProduct q := by
  have hs : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq hq1)
  have hsum : (∑' n : ℕ, q ^ (n + 1)) = q / (1 - q) := by
    simp_rw [pow_succ, mul_comm (q ^ _) q]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]
  apply le_hasProd_of_le_prod (multipliable_eulerQProduct hq hq1).hasProd
  intro s
  have hfinite := finite_one_sub_sum_le_product s (fun n => q ^ (n + 1))
    (fun n => pow_nonneg hq _) (fun n => pow_le_one₀ hq hq1.le)
  have hsum_le := hs.sum_le_tsum s (fun n _ => pow_nonneg hq _)
  rw [hsum] at hsum_le
  linarith only [hfinite, hsum_le]

theorem eulerQProduct_upper {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    eulerQProduct q ≤ 1 := by
  apply (multipliable_eulerQProduct hq hq1).tprod_le_of_prod_le
  intro s
  exact Finset.prod_le_one₀
    (fun n _ => sub_nonneg.mpr (pow_le_one₀ hq hq1.le))
    (fun n _ => by linarith only [pow_nonneg hq (n + 1)])

theorem eulerQProduct_small_lower {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    398 / 399 ≤ eulerQProduct q := by
  have hden : 0 < 1 - q := by linarith only [hqsmall]
  have hr : q / (1 - q) ≤ 1 / 399 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hqsmall]
  have hp := eulerQProduct_lower hq (by linarith only [hqsmall])
  linarith only [hp, hr]

theorem discriminantQ_lower {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    9 / 10 * q ≤ discriminantQ q := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 398 / 399)
    (eulerQProduct_small_lower hq hqsmall) 24
  have hnum : (9 / 10 : ℝ) ≤ (398 / 399 : ℝ) ^ 24 := by norm_num
  unfold discriminantQ
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hnum.trans hp) hq

theorem discriminantQ_upper {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    discriminantQ q ≤ q := by
  have hlow := eulerQProduct_small_lower hq hqsmall
  have hu := eulerQProduct_upper hq (by linarith only [hqsmall])
  have hp : (eulerQProduct q) ^ 24 ≤ 1 := pow_le_one₀ (by linarith only [hlow]) hu
  simpa [discriminantQ] using mul_le_mul_of_nonneg_left hp hq

theorem discriminantQ_pos {q : ℝ} (hq : 0 < q) (hqsmall : q ≤ 1 / 400) :
    0 < discriminantQ q :=
  lt_of_lt_of_le (mul_pos (by norm_num) hq) (discriminantQ_lower hq.le hqsmall)

theorem kleinJQ_lower {q : ℝ} (hq : 0 < q) (hqsmall : q ≤ 1 / 400) :
    1 / q ≤ kleinJQ q := by
  have hpow : (1 : ℝ) ≤ (eisensteinFourQ q) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (eisensteinFourQ_lower hq.le) 3
  unfold kleinJQ
  apply (div_le_div_iff₀ hq (discriminantQ_pos hq hqsmall)).mpr
  calc
    1 * discriminantQ q ≤ q := by simpa using discriminantQ_upper hq.le hqsmall
    _ ≤ (eisensteinFourQ q) ^ 3 * q := by simpa using mul_le_mul_of_nonneg_right hpow hq.le

theorem kleinJQ_upper {q : ℝ} (hq : 0 < q) (hqsmall : q ≤ 1 / 400) :
    kleinJQ q ≤ 5 / q := by
  have hp := pow_le_pow_left₀ (by linarith [eisensteinFourQ_lower hq.le] :
      0 ≤ eisensteinFourQ q) (eisensteinFourQ_upper hq.le hqsmall) 3
  have hc : (eisensteinFourQ q) ^ 3 ≤ 9 / 2 := by norm_num at hp; linarith only [hp]
  have hmul := mul_le_mul_of_nonneg_right hc hq.le
  have hd := discriminantQ_lower hq.le hqsmall
  unfold kleinJQ
  apply (div_le_div_iff₀ (discriminantQ_pos hq hqsmall) hq).mpr
  nlinarith only [hmul, hd]

end E8Leech
