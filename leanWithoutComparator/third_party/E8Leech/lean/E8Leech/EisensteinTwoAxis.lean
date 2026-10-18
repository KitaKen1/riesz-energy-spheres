import E8Leech.EisensteinSixSigns
import E8Leech.EisensteinQBounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# `E₂` on the imaginary axis and the positivity of `E₂E₄ − E₆`

`E₂(iy) = 1 − 24 Σ σ₁(n) qⁿ` with `q = e^{−2πy}`. With the existing real q-series for `E₄` and
`E₆`, crude geometric tail bounds give `E₂E₄ − E₆ ≥ 700 q` for `q ≤ 1/400` (`y ≥ 1`). This is the
slope `(πy/6)(E₂E₄ − E₆)(iy) > 0` of `𝒦̂(iy, it)` as `t → ∞`.
-/

noncomputable section

namespace E8Leech

open scoped BigOperators

def eisensteinTwoQ (q : ℝ) : ℝ :=
  1 - 24 * ∑' n : ℕ, ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)

theorem square_succ_le_four_pow (n : ℕ) : (n + 1) ^ 2 ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := by gcongr; omega
      _ = 4 * (n + 1) ^ 2 := by ring
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n + 1) := by ring

theorem sigma_one_succ_le_four_pow (n : ℕ) : ArithmeticFunction.sigma 1 (n + 1) ≤ 4 ^ n :=
  (ArithmeticFunction.sigma_le_pow_succ 1 (n + 1)).trans (square_succ_le_four_pow n)

theorem eisensteinTwoQ_term_le_geometric {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℝ) * q ^ (n + 1) ≤ q * (4 * q) ^ n := by
  have hc : ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by
    exact_mod_cast sigma_one_succ_le_four_pow n
  calc _ ≤ (4 : ℝ) ^ n * q ^ (n + 1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hq _)
    _ = q * (4 * q) ^ n := by rw [mul_pow, pow_succ]; ring

/-- A divisor-sum series `Σ σ_k(n+1) q^{n+1}` lies in `[q, q/(1 − bq)]`. -/
theorem tsum_sigma_bounds {f : ℕ → ℝ} {q b : ℝ} (hq : 0 ≤ q) (hb : 0 ≤ b) (hbq : b * q < 1)
    (hf0 : f 0 = q) (hfnn : ∀ n, 0 ≤ f n) (hfle : ∀ n, f n ≤ q * (b * q) ^ n) :
    q ≤ ∑' n, f n ∧ ∑' n, f n ≤ q / (1 - b * q) := by
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ b * q) hbq).mul_left q
  have hs : Summable f := hg.of_nonneg_of_le hfnn hfle
  refine ⟨?_, ?_⟩
  · rw [← hf0]
    exact hs.le_tsum 0 fun j _ => hfnn j
  · have h := hs.tsum_le_tsum hfle hg
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hbq, ← div_eq_mul_inv] at h
    exact h

/-- `E₂E₄ − E₆ ≥ 700 q` for `0 ≤ q ≤ 1/400`. -/
theorem eisenstein_two_four_six_lower {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    700 * q ≤ eisensteinTwoQ q * eisensteinFourQ q - eisensteinSixQ q := by
  obtain ⟨hA1, hA2⟩ := tsum_sigma_bounds (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)) (b := 4) hq (by norm_num)
    (by linarith) (by simp) (fun n => by positivity)
    (eisensteinTwoQ_term_le_geometric hq)
  obtain ⟨hB1, hB2⟩ := tsum_sigma_bounds (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)) (b := 16) hq (by norm_num)
    (by linarith) (by simp) (fun n => by positivity)
    (eisensteinFourQ_term_le_geometric hq)
  obtain ⟨hC1, -⟩ := tsum_sigma_bounds (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)) (b := 64) hq (by norm_num)
    (by linarith) (by simp) (fun n => by positivity)
    (eisensteinSixQ_term_le_geometric hq)
  unfold eisensteinTwoQ eisensteinFourQ eisensteinSixQ
  set A := ∑' n : ℕ, ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)
  set B := ∑' n : ℕ, ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)
  set C := ∑' n : ℕ, ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)
  have hA : A ≤ q * (100 / 99) := hA2.trans (by
    rw [div_le_iff₀ (by linarith)]; nlinarith)
  have hB : B ≤ q * (25 / 24) := hB2.trans (by
    rw [div_le_iff₀ (by linarith)]; nlinarith)
  have hA0 : 0 ≤ A := hq.trans hA1
  have hB0 : 0 ≤ B := hq.trans hB1
  have hAB : A * B ≤ (q * (100 / 99)) * (q * (25 / 24)) :=
    mul_le_mul hA hB hB0 (by positivity)
  have hq2 : q * q ≤ q * (1 / 400) := mul_le_mul_of_nonneg_left hqsmall hq
  nlinarith

theorem eisensteinTwo_imaginary_eq_q {y : ℝ} (hy : 0 < y) :
    EisensteinSeries.E2 (UpperHalfPlane.ofComplex (Complex.I * y)) =
      (eisensteinTwoQ (imaginaryNome y) : ℂ) := by
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  have hq := complex_qParam_imaginary hy
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one] at hq ⊢
  rw [hq]
  unfold eisensteinTwoQ
  push_cast
  rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℂ) * (imaginaryNome y : ℂ) ^ n)]

end E8Leech
