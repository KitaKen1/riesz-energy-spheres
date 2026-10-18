import E8Leech.KleinModularIdentification
import E8Leech.GaussianParameterNormalization

/-!
# Actual weight-six Eisenstein signs without differentiation or zero classification

The S-fixed point gives E6(i) = 0. The positive sigma_5 coefficients then make
the real q-series strictly decreasing in q, hence E6(iy) is nonnegative for
y >= 1 and strictly positive for y > 1. A coarse geometric coefficient bound
also gives E6(iy) >= 99/100 for y >= 3.

These are signs of the actual pinned modular form. They do not certify the
two-variable CKMRV numerator, kernel signs or the unconditional target.
-/

set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 3

noncomputable section

namespace E8Leech

open Set
open scoped BigOperators MatrixGroups

def eisensteinSixQ (q : ℝ) : ℝ :=
  1 - 504 * ∑' n : ℕ, ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)

theorem sixth_power_succ_le_sixtyFour_pow (n : ℕ) : (n + 1) ^ 6 ≤ 64 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      (n + 1 + 1) ^ 6 ≤ (2 * (n + 1)) ^ 6 := by gcongr; omega
      _ = 64 * (n + 1) ^ 6 := by ring
      _ ≤ 64 * 64 ^ n := Nat.mul_le_mul_left 64 ih
      _ = 64 ^ (n + 1) := by ring

theorem sigma_five_succ_le_sixtyFour_pow (n : ℕ) :
    ArithmeticFunction.sigma 5 (n + 1) ≤ 64 ^ n :=
  (ArithmeticFunction.sigma_le_pow_succ 5 (n + 1)).trans
    (sixth_power_succ_le_sixtyFour_pow n)

theorem eisensteinSixQ_term_le_geometric {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1) ≤
      q * (64 * q) ^ n := by
  have hc : ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) ≤ (64 : ℝ) ^ n := by
    exact_mod_cast sigma_five_succ_le_sixtyFour_pow n
  calc
    _ ≤ (64 : ℝ) ^ n * q ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hq _)
    _ = q * (64 * q) ^ n := by rw [mul_pow, pow_succ]; ring

theorem summable_eisensteinSixQ {q : ℝ} (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 400) :
    Summable (fun n : ℕ => ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1)) := by
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 64 * q)
    (by linarith : 64 * q < 1)).mul_left q
  exact hg.of_nonneg_of_le (fun n => by positivity) (eisensteinSixQ_term_le_geometric hq)

theorem eisensteinSixQ_upper {q : ℝ} (hq : 0 ≤ q) : eisensteinSixQ q ≤ 1 := by
  have hs : 0 ≤ ∑' n : ℕ, ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℝ) * q ^ (n + 1) :=
    tsum_nonneg (fun n => by positivity)
  unfold eisensteinSixQ
  linarith only [hs]

theorem eisensteinSixQ_antitone {q q' : ℝ}
    (hq : 0 ≤ q) (hqq' : q ≤ q') (hsmall : q' ≤ 1 / 400) :
    eisensteinSixQ q' ≤ eisensteinSixQ q := by
  have hs := (summable_eisensteinSixQ hq (hqq'.trans hsmall)).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqq' (n + 1))
      (Nat.cast_nonneg _)) (summable_eisensteinSixQ (hq.trans hqq') hsmall)
  unfold eisensteinSixQ
  linarith only [hs]

theorem eisensteinSixQ_strict_antitone {q q' : ℝ}
    (hq : 0 ≤ q) (hqq' : q < q') (hsmall : q' ≤ 1 / 400) :
    eisensteinSixQ q' < eisensteinSixQ q := by
  have hs := Summable.tsum_lt_tsum
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqq'.le (n + 1))
      (Nat.cast_nonneg (ArithmeticFunction.sigma 5 (n + 1))))
    (show ((ArithmeticFunction.sigma 5 (0 + 1) : ℕ) : ℝ) * q ^ (0 + 1) <
      ((ArithmeticFunction.sigma 5 (0 + 1) : ℕ) : ℝ) * q' ^ (0 + 1) by simpa using hqq')
    (summable_eisensteinSixQ hq (hqq'.le.trans hsmall))
    (summable_eisensteinSixQ (hq.trans hqq'.le) hsmall)
  unfold eisensteinSixQ
  linarith only [hs]

theorem eisensteinSixQ_tiny_lower {q : ℝ} (hq : 0 ≤ q) (hsmall : q ≤ 1 / 64000000) :
    99 / 100 ≤ eisensteinSixQ q := by
  have hden : 0 < 1 - 64 * q := by linarith only [hsmall]
  have hratio : q / (1 - 64 * q) ≤ 1 / 50400 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hsmall]
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 64 * q)
    (by linarith : 64 * q < 1)).mul_left q
  have hs := (summable_eisensteinSixQ hq (by linarith only [hsmall])).tsum_le_tsum
    (eisensteinSixQ_term_le_geometric hq) hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity : 0 ≤ 64 * q)
    (by linarith : 64 * q < 1), ← div_eq_mul_inv] at hs
  unfold eisensteinSixQ
  linarith only [hs, hratio]

theorem eisensteinSix_imaginary_eq_q {y : ℝ} (hy : 0 < y) :
    ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y)) =
      (eisensteinSixQ (imaginaryNome y) : ℂ) := by
  have h := EisensteinSeries.q_expansion_bernoulli (by norm_num : 3 ≤ 6)
    (by norm_num : Even 6) (UpperHalfPlane.ofComplex (Complex.I * y))
  have hq : Complex.exp (2 * Real.pi * Complex.I *
      (UpperHalfPlane.ofComplex (Complex.I * y) : ℂ)) = (imaginaryNome y : ℂ) := by
    simpa [Function.Periodic.qParam] using complex_qParam_imaginary hy
  rw [hq, show bernoulli 6 = 1 / 42 by decide +kernel] at h
  simp_rw [zpow_natCast] at h
  norm_num at h
  change ModularForm.E (by norm_num : 3 ≤ 6)
    (UpperHalfPlane.ofComplex (Complex.I * y)) = _
  rw [h]
  unfold eisensteinSixQ
  push_cast
  rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 5 n : ℕ) : ℂ) * (imaginaryNome y : ℂ) ^ n)]

theorem eisensteinSix_at_I_eq_zero : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have hS : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [UpperHalfPlane.modular_S_smul]
    apply UpperHalfPlane.ext
    change (-Complex.I)⁻¹ = Complex.I
    simp
  have hmem : (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' ModularForm.E₆ hmem UpperHalfPlane.I
  have hden : UpperHalfPlane.denom (ModularGroup.S : GL (Fin 2) ℝ) UpperHalfPlane.I =
      Complex.I := by
    rw [ModularGroup.denom_S]
    rfl
  change ModularForm.E₆ (ModularGroup.S • UpperHalfPlane.I) = _ at h
  rw [hS, hden] at h
  norm_num [zpow_natCast, pow_succ, Complex.I_sq] at h
  linear_combination (1 / 2 : ℂ) * h

theorem eisensteinSixQ_nome_one_eq_zero : eisensteinSixQ (imaginaryNome 1) = 0 := by
  have hz : UpperHalfPlane.ofComplex (Complex.I * (1 : ℝ)) = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    change (UpperHalfPlane.ofComplex (Complex.I * (1 : ℝ)) : ℂ) = Complex.I
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp)]
    simp
  have h := eisensteinSix_imaginary_eq_q (by norm_num : (0 : ℝ) < 1)
  rw [hz, eisensteinSix_at_I_eq_zero] at h
  exact_mod_cast h.symm

theorem imaginaryNome_antitone : Antitone imaginaryNome := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hxy (by nlinarith only [Real.pi_pos])

theorem imaginaryNome_strict_antitone : StrictAnti imaginaryNome := by
  intro x y hxy
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_neg_left hxy (by nlinarith only [Real.pi_pos])

theorem imaginaryNome_dual_tiny {y : ℝ} (hy : 3 ≤ y) :
    imaginaryNome y ≤ 1 / 64000000 := by
  have he : imaginaryNome 3 = imaginaryNome 1 ^ 3 := by
    unfold imaginaryNome
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp := pow_le_pow_left₀ (imaginaryNome_pos 1).le
    (imaginaryNome_small (by norm_num : (1 : ℝ) ≤ 1)) 3
  calc
    imaginaryNome y ≤ imaginaryNome 3 := imaginaryNome_antitone hy
    _ = imaginaryNome 1 ^ 3 := he
    _ ≤ (1 / 400 : ℝ) ^ 3 := hp
    _ = 1 / 64000000 := by norm_num

theorem eisensteinSix_imaginary_im_eq_zero {y : ℝ} (hy : 0 < y) :
    (ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y))).im = 0 := by
  rw [eisensteinSix_imaginary_eq_q hy, Complex.ofReal_im]

theorem eisensteinSix_imaginary_re_nonneg {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ (ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y))).re := by
  have h := eisensteinSixQ_antitone (imaginaryNome_pos y).le
    (imaginaryNome_antitone hy) (imaginaryNome_small (by norm_num : (1 : ℝ) ≤ 1))
  rw [eisensteinSixQ_nome_one_eq_zero] at h
  simpa only [eisensteinSix_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re] using h

theorem eisensteinSix_imaginary_re_pos {y : ℝ} (hy : 1 < y) :
    0 < (ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y))).re := by
  have h := eisensteinSixQ_strict_antitone (imaginaryNome_pos y).le
    (imaginaryNome_strict_antitone hy) (imaginaryNome_small (by norm_num : (1 : ℝ) ≤ 1))
  rw [eisensteinSixQ_nome_one_eq_zero] at h
  simpa only [eisensteinSix_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re] using h

theorem eisensteinSix_imaginary_re_upper {y : ℝ} (hy : 0 < y) :
    (ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y))).re ≤ 1 := by
  rw [eisensteinSix_imaginary_eq_q hy, Complex.ofReal_re]
  exact eisensteinSixQ_upper (imaginaryNome_pos y).le

theorem eisensteinSix_imaginary_dual_re_lower {y : ℝ} (hy : 3 ≤ y) :
    99 / 100 ≤ (ModularForm.E₆ (UpperHalfPlane.ofComplex (Complex.I * y))).re := by
  rw [eisensteinSix_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re]
  exact eisensteinSixQ_tiny_lower (imaginaryNome_pos y).le (imaginaryNome_dual_tiny hy)

theorem eisensteinSix_gaussian_dual_re_lower {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) :
    99 / 100 ≤ (ModularForm.E₆
      (UpperHalfPlane.ofComplex (Complex.I * ((Real.pi / α : ℝ) : ℂ)))).re :=
  eisensteinSix_imaginary_dual_re_lower (gaussian_dual_compact_interval hα).1

end E8Leech
