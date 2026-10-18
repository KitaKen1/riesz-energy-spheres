import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Kernel-checkable rational bounds for `exp (−y)`

`expNegLo y k n ≤ exp (−y) ≤ expNegHi y k n` for rational `0 ≤ y ≤ 2^k`. The bounds use the
Taylor polynomial of degree `< n` of `exp` at `−y/2^k` (`Real.exp_bound`) and then raise to the
power `2^k`. The functions are computable, so the bounds of every box endpoint can be produced by
`decide` inside the certificate of (6.4)(1).
-/

namespace E8Leech

/-- The Taylor polynomial `Σ_{i<n} xⁱ/i!`. -/
def expTaylor (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)

/-- The error bound of `Real.exp_bound`. -/
def expErr (x : ℚ) (n : ℕ) : ℚ := |x| ^ n * ((n.succ : ℚ) / ((n.factorial : ℚ) * n))

theorem abs_exp_sub_expTaylor_le {x : ℚ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.exp x - expTaylor x n| ≤ expErr x n := by
  have h := Real.exp_bound (x := (x : ℝ)) (by exact_mod_cast hx) hn
  have e1 : ((expTaylor x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ i / (i.factorial : ℝ) := by
    simp [expTaylor]
  have e2 : ((expErr x n : ℚ) : ℝ) =
      |(x : ℝ)| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
    simp [expErr]
  rw [e1, e2]
  exact h

/-- Lower bound of `exp (−y)`. -/
def expNegLo (y : ℚ) (k n : ℕ) : ℚ :=
  max 0 (expTaylor (-y / 2 ^ k) n - expErr (-y / 2 ^ k) n) ^ (2 ^ k)

/-- Upper bound of `exp (−y)`. -/
def expNegHi (y : ℚ) (k n : ℕ) : ℚ :=
  (expTaylor (-y / 2 ^ k) n + expErr (-y / 2 ^ k) n) ^ (2 ^ k)

theorem exp_neg_eq_pow (y : ℝ) (k : ℕ) :
    Real.exp (-y) = Real.exp (-y / 2 ^ k) ^ (2 ^ k) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem expNeg_bounds {y : ℚ} (hy : 0 ≤ y) {k n : ℕ} (hk : y ≤ 2 ^ k) (hn : 0 < n) :
    (expNegLo y k n : ℝ) ≤ Real.exp (-(y : ℝ)) ∧ Real.exp (-(y : ℝ)) ≤ expNegHi y k n := by
  set x : ℚ := -y / 2 ^ k with hxdef
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hx : |x| ≤ 1 := by
    rw [hxdef, abs_div, abs_neg, abs_of_nonneg hy, abs_of_pos h2k]
    exact (div_le_one h2k).mpr hk
  have hb := abs_exp_sub_expTaylor_le hx hn
  rw [abs_le] at hb
  have hxr : ((x : ℚ) : ℝ) = -(y : ℝ) / 2 ^ k := by rw [hxdef]; push_cast; ring
  rw [hxr] at hb
  have hexp := exp_neg_eq_pow (y : ℝ) k
  constructor
  · rw [hexp, expNegLo]
    push_cast
    apply pow_le_pow_left₀ (le_max_left _ _)
    rw [← hxdef]
    exact max_le (Real.exp_pos _).le (by linarith [hb.1])
  · rw [hexp, expNegHi]
    push_cast
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [← hxdef]
    linarith [hb.2]

end E8Leech
