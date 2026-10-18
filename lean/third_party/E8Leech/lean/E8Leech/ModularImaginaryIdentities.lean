import E8Leech.EisensteinSixSigns
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Actual modular identities and global imaginary-axis positivity

Reuse the pinned graded-ring theorem, rather than reconstruct Ramanujan's
identities or differentiate q-series. The product for Delta is an even
power times a positive nome; its known nonvanishing upgrades nonnegativity
to strict positivity for every positive height, without a small-nome bound.
These statements do not establish the two-variable CKMRV kernel sign.
-/

set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 3

noncomputable section

namespace E8Leech

open Set

theorem eisensteinFour_imaginary_im_eq_zero {y : ℝ} (hy : 0 < y) :
    (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).im = 0 := by
  rw [eisensteinFour_imaginary_eq_q hy, Complex.ofReal_im]

theorem eisensteinFour_imaginary_re_lower {y : ℝ} (hy : 0 < y) :
    1 ≤ (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).re := by
  rw [eisensteinFour_imaginary_eq_q hy, Complex.ofReal_re]
  exact eisensteinFourQ_lower (imaginaryNome_pos y).le

theorem discriminant_imaginary_im_eq_zero {y : ℝ} (hy : 0 < y) :
    (ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * y))).im = 0 := by
  rw [discriminant_imaginary_eq_q hy, Complex.ofReal_im]

theorem discriminantQ_nome_pos {y : ℝ} (hy : 0 < y) :
    0 < discriminantQ (imaginaryNome y) := by
  have hd : discriminantQ (imaginaryNome y) ≠ 0 := by
    intro hzero
    apply ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex (Complex.I * y))
    rw [discriminant_imaginary_eq_q hy, hzero, Complex.ofReal_zero]
  have hn : 0 ≤ discriminantQ (imaginaryNome y) := by
    unfold discriminantQ
    exact mul_nonneg (imaginaryNome_pos y).le (by positivity)
  exact lt_of_le_of_ne hn (Ne.symm hd)

theorem discriminant_imaginary_re_pos {y : ℝ} (hy : 0 < y) :
    0 < (ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * y))).re := by
  rw [discriminant_imaginary_eq_q hy, Complex.ofReal_re]
  exact discriminantQ_nome_pos hy

theorem eisenstein_cubic_square_discriminant (z : UpperHalfPlane) :
    ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2 = 1728 * ModularForm.discriminant z := by
  linear_combination -1728 * ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z

theorem kleinModularJ_sub_1728 (z : UpperHalfPlane) :
    kleinModularJ z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z := by
  unfold kleinModularJ
  apply (eq_div_iff (ModularForm.discriminant_ne_zero z)).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero z)]
  linear_combination eisenstein_cubic_square_discriminant z

theorem eisensteinQ_nome_cubic_square_discriminant {y : ℝ} (hy : 0 < y) :
    eisensteinFourQ (imaginaryNome y) ^ 3 - eisensteinSixQ (imaginaryNome y) ^ 2 =
      1728 * discriminantQ (imaginaryNome y) := by
  have h := eisenstein_cubic_square_discriminant (UpperHalfPlane.ofComplex (Complex.I * y))
  rw [eisensteinFour_imaginary_eq_q hy, eisensteinSix_imaginary_eq_q hy,
    discriminant_imaginary_eq_q hy] at h
  exact_mod_cast h

theorem kleinJQ_nome_sub_1728 {y : ℝ} (hy : 0 < y) :
    kleinJQ (imaginaryNome y) - 1728 =
      eisensteinSixQ (imaginaryNome y) ^ 2 / discriminantQ (imaginaryNome y) := by
  unfold kleinJQ
  apply (eq_div_iff (ne_of_gt (discriminantQ_nome_pos hy))).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt (discriminantQ_nome_pos hy))]
  linear_combination eisensteinQ_nome_cubic_square_discriminant hy

theorem kleinImaginaryJ_re_ge_1728 {y : ℝ} (hy : 0 < y) :
    1728 ≤ (kleinImaginaryJ y).re := by
  rw [kleinImaginaryJ_eq_q hy, Complex.ofReal_re]
  have h := div_nonneg (sq_nonneg (eisensteinSixQ (imaginaryNome y)))
    (discriminantQ_nome_pos hy).le
  rw [← kleinJQ_nome_sub_1728 hy] at h
  linarith only [h]

theorem kleinImaginaryJ_re_gt_1728 {y : ℝ} (hy : 1 < y) :
    1728 < (kleinImaginaryJ y).re := by
  have hE := eisensteinSix_imaginary_re_pos hy
  rw [eisensteinSix_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re] at hE
  have h := div_pos (sq_pos_of_pos hE) (discriminantQ_nome_pos (by linarith only [hy]))
  rw [← kleinJQ_nome_sub_1728 (by linarith only [hy])] at h
  rw [kleinImaginaryJ_eq_q (by linarith only [hy]), Complex.ofReal_re]
  linarith only [h]

theorem kleinImaginaryJ_at_one_eq_1728 : kleinImaginaryJ 1 = 1728 := by
  have h := kleinJQ_nome_sub_1728 (by norm_num : (0 : ℝ) < 1)
  rw [eisensteinSixQ_nome_one_eq_zero] at h
  norm_num at h
  rw [kleinImaginaryJ_eq_q (by norm_num : (0 : ℝ) < 1)]
  have hr : kleinJQ (imaginaryNome 1) = 1728 := by linarith only [h]
  exact_mod_cast hr

end E8Leech
