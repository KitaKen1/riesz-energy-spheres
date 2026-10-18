import E8Leech.KleinImaginaryQ
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Identification with actual pinned modular forms and the CKMRV denominator

J = E4^3 / Delta uses Mathlib's normalized level-one Eisenstein form and
its actual discriminant eta^24. On the positive imaginary axis we identify
both with the checked real q-series and product, then prove the fixed
rectangle denominator is positive with a common explicit gap.

This does not construct the two-variable CKMRV numerator or its sign.
-/

set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 3

noncomputable section

namespace E8Leech

open Set
open scoped BigOperators

def kleinModularJ (z : UpperHalfPlane) : ℂ :=
  (ModularForm.E₄ z) ^ 3 / ModularForm.discriminant z

def kleinImaginaryJ (y : ℝ) : ℂ :=
  kleinModularJ (UpperHalfPlane.ofComplex (Complex.I * y))

theorem continuous_kleinModularJ : Continuous kleinModularJ := by
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  exact ((ModularFormClass.continuous ModularForm.E₄).pow 3).div hD
    ModularForm.discriminant_ne_zero

theorem continuousOn_kleinImaginaryJ : ContinuousOn kleinImaginaryJ (Ioi (0 : ℝ)) :=
  continuous_kleinModularJ.comp_continuousOn UpperHalfPlane.continuousOn_ofComplex_I_mul

theorem complex_qParam_imaginary {y : ℝ} (hy : 0 < y) :
    Function.Periodic.qParam 1 (UpperHalfPlane.ofComplex (Complex.I * y)) =
      (imaginaryNome y : ℂ) := by
  have him : 0 < (Complex.I * (y : ℂ)).im := by simpa using hy
  unfold imaginaryNome
  rw [Function.Periodic.qParam, UpperHalfPlane.ofComplex_apply_of_im_pos him,
    Complex.ofReal_exp]
  simp only [Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring_nf; simp [Complex.I_sq]

theorem eisensteinFour_imaginary_eq_q {y : ℝ} (hy : 0 < y) :
    ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y)) =
      (eisensteinFourQ (imaginaryNome y) : ℂ) := by
  have h := EisensteinSeries.q_expansion_bernoulli (by norm_num : 3 ≤ 4)
    (by norm_num : Even 4) (UpperHalfPlane.ofComplex (Complex.I * y))
  have hq : Complex.exp (2 * Real.pi * Complex.I *
      (UpperHalfPlane.ofComplex (Complex.I * y) : ℂ)) = (imaginaryNome y : ℂ) := by
    simpa [Function.Periodic.qParam] using complex_qParam_imaginary hy
  rw [hq, bernoulli_eq_bernoulli'_of_ne_one (by decide : 4 ≠ 1), bernoulli'_four] at h
  simp_rw [zpow_natCast] at h
  norm_num at h
  change ModularForm.E (by norm_num : 3 ≤ 4)
    (UpperHalfPlane.ofComplex (Complex.I * y)) = _
  rw [h]
  unfold eisensteinFourQ
  push_cast
  rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    ((ArithmeticFunction.sigma 3 n : ℕ) : ℂ) * (imaginaryNome y : ℂ) ^ n)]

theorem discriminant_imaginary_eq_q {y : ℝ} (hy : 0 < y) :
    ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * y)) =
      (discriminantQ (imaginaryNome y) : ℂ) := by
  have hq0 := (imaginaryNome_pos y).le
  have hq1 : imaginaryNome y < 1 := by
    unfold imaginaryNome
    apply Real.exp_lt_one_iff.mpr
    have hp : 0 < 2 * Real.pi * y := mul_pos (mul_pos (by norm_num) Real.pi_pos) hy
    linarith only [hp]
  have hp := multipliable_eulerQProduct hq0 hq1
  have hcast := (hp.pow 24).map_tprod Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  rw [hp.tprod_pow 24] at hcast
  change (((∏' n : ℕ, (1 - imaginaryNome y ^ (n + 1))) ^ 24 : ℝ) : ℂ) =
    ∏' n : ℕ, (((1 - imaginaryNome y ^ (n + 1)) ^ 24 : ℝ) : ℂ) at hcast
  push_cast at hcast
  rw [ModularForm.discriminant_eq_q_prod, complex_qParam_imaginary hy]
  unfold discriminantQ eulerQProduct
  push_cast
  rw [hcast]
  have heta : (fun n : ℕ =>
      (1 - ModularForm.eta_q n (UpperHalfPlane.ofComplex (Complex.I * y))) ^ 24) =
      (fun n : ℕ => (1 - (imaginaryNome y : ℂ) ^ (n + 1)) ^ 24) := by
    funext n
    exact congrArg (fun w : ℂ => (1 - w ^ (n + 1)) ^ 24) (complex_qParam_imaginary hy)
  rw [heta]

theorem kleinImaginaryJ_eq_q {y : ℝ} (hy : 0 < y) :
    kleinImaginaryJ y = (kleinJQ (imaginaryNome y) : ℂ) := by
  unfold kleinImaginaryJ kleinModularJ kleinJQ
  rw [eisensteinFour_imaginary_eq_q hy, discriminant_imaginary_eq_q hy]
  push_cast
  rfl

theorem kleinImaginaryJ_rectangle_real_gap {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    2000000 ≤ (kleinImaginaryJ y - kleinImaginaryJ v).re := by
  rw [kleinImaginaryJ_eq_q (by linarith only [hy.1]),
    kleinImaginaryJ_eq_q (by linarith only [hv.1]), Complex.sub_re]
  simp only [Complex.ofReal_re]
  exact kleinJQ_imaginary_rectangle_gap hy hv

theorem kleinImaginaryJ_rectangle_difference_ne_zero {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    kleinImaginaryJ y - kleinImaginaryJ v ≠ 0 := by
  intro h
  have hg := kleinImaginaryJ_rectangle_real_gap hy hv
  rw [h, Complex.zero_re] at hg
  norm_num at hg

end E8Leech
