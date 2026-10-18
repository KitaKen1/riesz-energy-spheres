import E8Leech.EulerProductBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified separation of the actual Klein q-quotient on two imaginary intervals

Only coarse rational bounds on pi and exp(1) are used. The interval [1,2]
has J <= 8000000, while [3,4] has J >= 10000000. The resulting explicit
gap avoids global modular-orbit classification.
The identification with actual modular forms is a separate checked module.
-/

noncomputable section

namespace E8Leech

open Set

def imaginaryNome (y : ℝ) : ℝ := Real.exp (-2 * Real.pi * y)

theorem imaginaryNome_pos (y : ℝ) : 0 < imaginaryNome y := Real.exp_pos _

theorem imaginaryNome_reciprocal (y : ℝ) :
    1 / imaginaryNome y = Real.exp (2 * Real.pi * y) := by
  simp [imaginaryNome, Real.exp_neg]

theorem imaginaryNome_small {y : ℝ} (hy : 1 ≤ y) : imaginaryNome y ≤ 1 / 400 := by
  have hpow : (400 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    calc
      _ ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.exp 1) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 6
  have he6 : (Real.exp 1) ^ 6 = Real.exp 6 := by
    simp
  rw [he6] at hpow
  have hexp : (400 : ℝ) ≤ Real.exp (2 * Real.pi * y) :=
    hpow.trans (Real.exp_le_exp.mpr (by nlinarith only [hy, Real.pi_gt_three]))
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 400) hexp
  simpa only [imaginaryNome, show -2 * Real.pi * y = -(2 * Real.pi * y) by ring,
    Real.exp_neg, one_div] using hinv

theorem kleinJQ_imaginary_block_upper {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 2) :
    kleinJQ (imaginaryNome v) ≤ 8000000 := by
  have hj := kleinJQ_upper (imaginaryNome_pos v) (imaginaryNome_small hv.1)
  have harg : 2 * Real.pi * v ≤ 13 := by nlinarith only [hv.1, hv.2, Real.pi_lt_d2]
  have hpow : (Real.exp 1) ^ 13 ≤ (3 : ℝ) ^ 13 :=
    pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 13
  have he13 : (Real.exp 1) ^ 13 = Real.exp 13 := by
    simp
  rw [he13] at hpow
  have he := (Real.exp_le_exp.mpr harg).trans hpow
  rw [show 5 / imaginaryNome v = 5 * (1 / imaginaryNome v) by ring,
    imaginaryNome_reciprocal] at hj
  norm_num at he
  linarith only [hj, he]

theorem kleinJQ_imaginary_dual_lower {y : ℝ} (hy : 3 ≤ y) :
    10000000 ≤ kleinJQ (imaginaryNome y) := by
  have hj := kleinJQ_lower (imaginaryNome_pos y) (imaginaryNome_small (by linarith only [hy]))
  have hpow : (10000000 : ℝ) ≤ (Real.exp 1) ^ 18 := by
    calc
      _ ≤ (5 / 2 : ℝ) ^ 18 := by norm_num
      _ ≤ (Real.exp 1) ^ 18 :=
        pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 18
  have he18 : (Real.exp 1) ^ 18 = Real.exp 18 := by
    simp
  rw [he18] at hpow
  rw [imaginaryNome_reciprocal] at hj
  exact (hpow.trans (Real.exp_le_exp.mpr (by nlinarith only [hy, Real.pi_gt_three]))).trans hj

theorem kleinJQ_imaginary_rectangle_gap {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    2000000 ≤ kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v) := by
  linarith only [kleinJQ_imaginary_dual_lower hy.1, kleinJQ_imaginary_block_upper hv]

theorem kleinJQ_imaginary_rectangle_ne {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v) ≠ 0 := by
  have h := kleinJQ_imaginary_rectangle_gap hy hv
  linarith only [h]

end E8Leech
