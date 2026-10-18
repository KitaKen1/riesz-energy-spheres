import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Exact coefficient bounds used in algebraic modular-form inequalities

Independent proofs of inequalities (60) and (61) in Seewoo Lee,
arXiv:2602.10536, Appendix A. The coefficients and inequalities are mathematical
data. No Ramanujan identities, Deligne bound, or analytic-family identification
are imported as axioms. These analytic connections remain separate obligations.
-/

noncomputable section

namespace E8Leech

theorem divisor_count_power_bound (m : ℕ) (hm : 1 ≤ m) :
    ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * (m : ℝ) ^ (11 / 2 : ℝ) ≤
      (m : ℝ) ^ 7 := by
  have hcount : ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) ≤ m := by
    exact_mod_cast (by simpa only [ArithmeticFunction.sigma_zero_apply] using
      Nat.card_divisors_le_self m)
  calc
    _ ≤ (m : ℝ) * (m : ℝ) ^ (11 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    _ = (m : ℝ) ^ (13 / 2 : ℝ) := by
      rw [show (13 / 2 : ℝ) = 1 + 11 / 2 by norm_num,
        Real.rpow_add (by exact_mod_cast (show 0 < m by omega)), Real.rpow_one]
    _ ≤ (m : ℝ) ^ (7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by norm_num)
    _ = (m : ℝ) ^ 7 := by norm_cast

theorem modular_coefficient_bound_60 (m : ℕ) (hm : 3 ≤ m) :
    0 < (2520 : ℝ) / 3 * m ^ 9 -
      18224 / 21 * ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) *
        m ^ (11 / 2 : ℝ) + 12 / 7 * m ^ 10 := by
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpoly : 0 < (840 : ℝ) * m ^ 9 - 18224 / 21 * m ^ 7 + 12 / 7 * m ^ 10 := by
    have hid : (840 : ℝ) * m ^ 9 - 18224 / 21 * m ^ 7 + 12 / 7 * m ^ 10 =
        (m ^ 7 / 21) * (36 * m ^ 3 + 17640 * m ^ 2 - 18224) := by ring
    rw [hid]
    have hp : 0 < (36 : ℝ) * m ^ 3 + 17640 * m ^ 2 - 18224 := by nlinarith
    exact mul_pos (by positivity) hp
  have hb := divisor_count_power_bound m (by omega)
  nlinarith

theorem two_rpow_eleven_halves_lt_46 : (2 : ℝ) ^ (11 / 2 : ℝ) < 46 := by
  have hsquare : ((2 : ℝ) ^ (11 / 2 : ℝ)) ^ 2 = 2048 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (11 / 2 : ℝ)]

theorem two_rpow_seven_halves_mul_ge_four_mul (k : ℕ) (hk : 1 ≤ k) :
    4 * (k : ℝ) ≤ (2 : ℝ) ^ ((7 : ℝ) * k / 2) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (k.lt_two_pow_self.le)
  have he : (k : ℝ) + 2 ≤ (7 : ℝ) * k / 2 := by linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hmono
  norm_num at hmono
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans
    (by simpa only [mul_comm] using hmono)

theorem modular_coefficient_bound_61 (k : ℕ) (hk : 1 ≤ k) :
    0 < (2560 : ℝ) / 3 * (2 : ℝ) ^ (9 * k) - 40 / 3 * (2 : ℝ) ^ (2 * k) -
      17 / 21 * (((k : ℝ) + 2) * (2 : ℝ) ^ ((11 : ℝ) / 2 * ((k : ℝ) + 1)) +
        1048 * ((k : ℝ) + 1) * (2 : ℝ) ^ ((11 : ℝ) / 2 * k)) := by
  let q := (2 : ℝ) ^ ((7 : ℝ) * k / 2)
  let a := (2 : ℝ) ^ (11 / 2 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqk : 4 * (k : ℝ) ≤ q := two_rpow_seven_halves_mul_ge_four_mul k hk
  have ha : a < 46 := two_rpow_eleven_halves_lt_46
  have hc : 17 / 21 * (((k : ℝ) + 2) * a + 1048 * ((k : ℝ) + 1)) < 1812 * k := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 2)
      (by linarith : 0 < 46 - a)]
  have hi : 0 < (2560 : ℝ) / 3 * q ^ 2 - 40 / 3 -
      17 / 21 * (((k : ℝ) + 2) * a + 1048 * ((k : ℝ) + 1)) * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqk) hq.le,
      mul_pos (sub_pos.mpr hc) hq, sq_nonneg (q - 4)]
  have hp : (2 : ℝ) ^ (9 * k) = (2 : ℝ) ^ (2 * k) * q ^ 2 := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have he1 : (2 : ℝ) ^ ((11 : ℝ) / 2 * ((k : ℝ) + 1)) =
      (2 : ℝ) ^ (2 * k) * a * q := by
    dsimp [a, q]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have he2 : (2 : ℝ) ^ ((11 : ℝ) / 2 * k) = (2 : ℝ) ^ (2 * k) * q := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hp, he1, he2]
  have hid : (2560 : ℝ) / 3 * ((2 : ℝ) ^ (2 * k) * q ^ 2) -
      40 / 3 * (2 : ℝ) ^ (2 * k) -
      17 / 21 * (((k : ℝ) + 2) * ((2 : ℝ) ^ (2 * k) * a * q) +
        1048 * ((k : ℝ) + 1) * ((2 : ℝ) ^ (2 * k) * q)) =
      (2 : ℝ) ^ (2 * k) * ((2560 : ℝ) / 3 * q ^ 2 - 40 / 3 -
        17 / 21 * (((k : ℝ) + 2) * a + 1048 * ((k : ℝ) + 1)) * q) := by ring
  rw [hid]
  exact mul_pos (by positivity) hi

end E8Leech
