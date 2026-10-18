import E8Leech.KleinModularIdentification
import E8Leech.GaussianParameterNormalization

/-!
# A positive uniform bound for the common CKMRV modular denominator

The base denominator Delta(iy) Delta(iv) (j(iy)-j(iv)) on
[3,4] x [1,2] is bounded away from zero by 1620000 exp(-12 pi).
For the dimension-24 coefficient matrices the common denominator has one
additional Delta(iv) factor; it has a separately checked lower bound below.
This proves a pole-free block and reciprocal norm bounds.
It does not construct or certify the CKMRV numerators or kernel signs.
-/

noncomputable section
namespace E8Leech
open Set

def ckmrvImaginaryDenominator (p : ℝ × ℝ) : ℂ :=
  ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * p.1)) *
  ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * p.2)) *
  (kleinImaginaryJ p.1 - kleinImaginaryJ p.2)

def ckmrvDenominatorBlockLower : ℝ := 1620000 * Real.exp (-12 * Real.pi)

theorem ckmrvDenominatorBlockLower_pos : 0 < ckmrvDenominatorBlockLower :=
  mul_pos (by norm_num) (Real.exp_pos _)

theorem discriminantQ_imaginary_interval_lower {y U : ℝ}
    (hy : 1 ≤ y) (hU : y ≤ U) :
    9 / 10 * Real.exp (-2 * Real.pi * U) ≤ discriminantQ (imaginaryNome y) := by
  have hn : Real.exp (-2 * Real.pi * U) ≤ imaginaryNome y := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hU (by nlinarith only [Real.pi_pos])
  exact (mul_le_mul_of_nonneg_left hn (by norm_num)).trans
    (discriminantQ_lower (imaginaryNome_pos y).le (imaginaryNome_small hy))

theorem discriminant_imaginary_norm_eq {y : ℝ} (hy : 1 ≤ y) :
    ‖ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * y))‖ =
      discriminantQ (imaginaryNome y) := by
  rw [discriminant_imaginary_eq_q (by linarith only [hy])]
  exact Complex.norm_of_nonneg
    (discriminantQ_pos (imaginaryNome_pos y) (imaginaryNome_small hy)).le

theorem ckmrvImaginaryDenominator_block_norm_lower {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvDenominatorBlockLower ≤ ‖ckmrvImaginaryDenominator (y, v)‖ := by
  have hdy := discriminantQ_imaginary_interval_lower
    (by linarith only [hy.1] : 1 ≤ y) hy.2
  have hdv := discriminantQ_imaginary_interval_lower hv.1 hv.2
  have hdyl : 0 ≤ 9 / 10 * Real.exp (-2 * Real.pi * 4) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hdvl : 0 ≤ 9 / 10 * Real.exp (-2 * Real.pi * 2) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hj : (2000000 : ℝ) ≤ ‖kleinImaginaryJ y - kleinImaginaryJ v‖ :=
    (kleinImaginaryJ_rectangle_real_gap hy hv).trans (Complex.re_le_norm _)
  unfold ckmrvImaginaryDenominator
  rw [norm_mul, norm_mul, discriminant_imaginary_norm_eq (by linarith only [hy.1]),
    discriminant_imaginary_norm_eq hv.1]
  have hp := mul_le_mul hdy hdv hdvl
    (discriminantQ_pos (imaginaryNome_pos y) (imaginaryNome_small (by linarith only [hy.1]))).le
  have hh := mul_le_mul hp hj (by norm_num : (0 : ℝ) ≤ 2000000)
    (mul_nonneg
      (discriminantQ_pos (imaginaryNome_pos y) (imaginaryNome_small (by linarith only [hy.1]))).le
      (discriminantQ_pos (imaginaryNome_pos v) (imaginaryNome_small hv.1)).le)
  have he : Real.exp (-2 * Real.pi * 4) * Real.exp (-2 * Real.pi * 2) =
      Real.exp (-12 * Real.pi) := by rw [← Real.exp_add]; congr 1; ring
  have hc : (9 / 10 * Real.exp (-2 * Real.pi * 4)) *
      (9 / 10 * Real.exp (-2 * Real.pi * 2)) * 2000000 = ckmrvDenominatorBlockLower := by
    unfold ckmrvDenominatorBlockLower
    calc
      _ = 1620000 * (Real.exp (-2 * Real.pi * 4) * Real.exp (-2 * Real.pi * 2)) := by ring
      _ = _ := by rw [he]
  exact hc ▸ hh

theorem ckmrvImaginaryDenominator_block_ne_zero {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvImaginaryDenominator (y, v) ≠ 0 := by
  exact norm_pos_iff.mp (ckmrvDenominatorBlockLower_pos.trans_le
    (ckmrvImaginaryDenominator_block_norm_lower hy hv))

theorem ckmrvImaginaryDenominator_block_inverse_norm_upper {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ‖(ckmrvImaginaryDenominator (y, v))⁻¹‖ ≤ ckmrvDenominatorBlockLower⁻¹ := by
  rw [norm_inv]
  have hb := ckmrvImaginaryDenominator_block_norm_lower hy hv
  exact (inv_le_inv₀ (ckmrvDenominatorBlockLower_pos.trans_le hb)
    ckmrvDenominatorBlockLower_pos).mpr hb

theorem continuousOn_ckmrvImaginaryDenominator_positive :
    ContinuousOn ckmrvImaginaryDenominator (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  have hDi := hD.comp_continuousOn UpperHalfPlane.continuousOn_ofComplex_I_mul
  have hf : ContinuousOn (Prod.fst : ℝ × ℝ → ℝ) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    continuous_fst.continuousOn
  have hs : ContinuousOn (Prod.snd : ℝ × ℝ → ℝ) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    continuous_snd.continuousOn
  exact ((hDi.comp hf (fun _ h => h.1)).mul
    (hDi.comp hs (fun _ h => h.2))).mul
    ((continuousOn_kleinImaginaryJ.comp hf (fun _ h => h.1)).sub
      (continuousOn_kleinImaginaryJ.comp hs (fun _ h => h.2)))

theorem continuousOn_ckmrvImaginaryDenominator_block :
    ContinuousOn ckmrvImaginaryDenominator (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) := by
  apply continuousOn_ckmrvImaginaryDenominator_positive.mono
  intro p hp
  change 0 < p.1 ∧ 0 < p.2
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hp.1.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp.2.1⟩

theorem continuousOn_ckmrvImaginaryDenominator_block_inverse :
    ContinuousOn (fun p => (ckmrvImaginaryDenominator p)⁻¹)
      (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) :=
  continuousOn_ckmrvImaginaryDenominator_block.inv₀
    (fun _p hp => ckmrvImaginaryDenominator_block_ne_zero hp.1 hp.2)

theorem ckmrvGaussianDenominator_block_norm_lower {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvDenominatorBlockLower ≤ ‖ckmrvImaginaryDenominator (Real.pi / α, v)‖ :=
  ckmrvImaginaryDenominator_block_norm_lower (gaussian_dual_compact_interval hα) hv

theorem ckmrvGaussianDenominator_block_ne_zero {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvImaginaryDenominator (Real.pi / α, v) ≠ 0 :=
  ckmrvImaginaryDenominator_block_ne_zero (gaussian_dual_compact_interval hα) hv

/-- The actual common denominator is real on the positive imaginary axes. -/
theorem ckmrvImaginaryDenominator_eq_real {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    ckmrvImaginaryDenominator (y, v) =
      ((discriminantQ (imaginaryNome y) * discriminantQ (imaginaryNome v) *
        (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) : ℝ) : ℂ) := by
  unfold ckmrvImaginaryDenominator
  rw [discriminant_imaginary_eq_q hy, discriminant_imaginary_eq_q hv,
    kleinImaginaryJ_eq_q hy, kleinImaginaryJ_eq_q hv]
  push_cast
  rfl

theorem ckmrvImaginaryDenominator_im_eq_zero {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    (ckmrvImaginaryDenominator (y, v)).im = 0 := by
  rw [ckmrvImaginaryDenominator_eq_real hy hv, Complex.ofReal_im]

theorem ckmrvImaginaryDenominator_block_re_pos {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    0 < (ckmrvImaginaryDenominator (y, v)).re := by
  rw [ckmrvImaginaryDenominator_eq_real (by linarith only [hy.1])
    (by linarith only [hv.1]), Complex.ofReal_re]
  exact mul_pos
    (mul_pos
      (discriminantQ_pos (imaginaryNome_pos y) (imaginaryNome_small (by linarith only [hy.1])))
      (discriminantQ_pos (imaginaryNome_pos v) (imaginaryNome_small hv.1)))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2000000)
      (kleinJQ_imaginary_rectangle_gap hy hv))

theorem ckmrvImaginaryDenominator_block_norm_eq_re {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ‖ckmrvImaginaryDenominator (y, v)‖ = (ckmrvImaginaryDenominator (y, v)).re := by
  have hp := (ckmrvImaginaryDenominator_block_re_pos hy hv).le
  rw [ckmrvImaginaryDenominator_eq_real (by linarith only [hy.1])
    (by linarith only [hv.1]), Complex.ofReal_re] at hp ⊢
  exact Complex.norm_of_nonneg hp

theorem ckmrvImaginaryDenominator_block_re_lower {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvDenominatorBlockLower ≤ (ckmrvImaginaryDenominator (y, v)).re := by
  rw [← ckmrvImaginaryDenominator_block_norm_eq_re hy hv]
  exact ckmrvImaginaryDenominator_block_norm_lower hy hv

theorem ckmrvImaginaryDenominator_block_inverse_re_pos {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    0 < ((ckmrvImaginaryDenominator (y, v))⁻¹).re := by
  have hp := ckmrvImaginaryDenominator_block_re_pos hy hv
  rw [ckmrvImaginaryDenominator_eq_real (by linarith only [hy.1])
    (by linarith only [hv.1]), Complex.ofReal_re] at hp
  rw [ckmrvImaginaryDenominator_eq_real (by linarith only [hy.1])
    (by linarith only [hv.1]), ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr hp

theorem ckmrvGaussianDenominator_block_re_lower {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvDenominatorBlockLower ≤ (ckmrvImaginaryDenominator (Real.pi / α, v)).re :=
  ckmrvImaginaryDenominator_block_re_lower (gaussian_dual_compact_interval hα) hv

/-- The common denominator of the dimension-24 matrices in CKMRV Section 4.4. -/
def ckmrvLeechImaginaryDenominator (p : ℝ × ℝ) : ℂ :=
  ckmrvImaginaryDenominator p *
    ModularForm.discriminant (UpperHalfPlane.ofComplex (Complex.I * p.2))

def ckmrvLeechDenominatorBlockLower : ℝ := 1458000 * Real.exp (-16 * Real.pi)

theorem ckmrvLeechDenominatorBlockLower_pos : 0 < ckmrvLeechDenominatorBlockLower :=
  mul_pos (by norm_num) (Real.exp_pos _)

theorem ckmrvLeechImaginaryDenominator_eq_real {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    ckmrvLeechImaginaryDenominator (y, v) =
      ((discriminantQ (imaginaryNome y) * discriminantQ (imaginaryNome v) ^ 2 *
        (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) : ℝ) : ℂ) := by
  unfold ckmrvLeechImaginaryDenominator
  rw [ckmrvImaginaryDenominator_eq_real hy hv, discriminant_imaginary_eq_q hv]
  push_cast
  ring

theorem ckmrvLeechImaginaryDenominator_block_re_lower {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvLeechDenominatorBlockLower ≤ (ckmrvLeechImaginaryDenominator (y, v)).re := by
  have hb := ckmrvImaginaryDenominator_block_re_lower hy hv
  have hd := discriminantQ_imaginary_interval_lower hv.1 hv.2
  have hm := mul_le_mul hb hd
    (by positivity : 0 ≤ 9 / 10 * Real.exp (-2 * Real.pi * 2))
    (ckmrvImaginaryDenominator_block_re_pos hy hv).le
  have hc : ckmrvDenominatorBlockLower * (9 / 10 * Real.exp (-2 * Real.pi * 2)) =
      ckmrvLeechDenominatorBlockLower := by
    unfold ckmrvDenominatorBlockLower ckmrvLeechDenominatorBlockLower
    calc
      _ = 1458000 * (Real.exp (-12 * Real.pi) * Real.exp (-2 * Real.pi * 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [hc] at hm
  unfold ckmrvLeechImaginaryDenominator
  rw [discriminant_imaginary_eq_q (by linarith only [hv.1]), Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact hm

theorem ckmrvLeechImaginaryDenominator_block_re_pos {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    0 < (ckmrvLeechImaginaryDenominator (y, v)).re :=
  ckmrvLeechDenominatorBlockLower_pos.trans_le
    (ckmrvLeechImaginaryDenominator_block_re_lower hy hv)

theorem ckmrvLeechImaginaryDenominator_block_ne_zero {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvLeechImaginaryDenominator (y, v) ≠ 0 := by
  intro h
  have hp := ckmrvLeechImaginaryDenominator_block_re_pos hy hv
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem ckmrvLeechImaginaryDenominator_block_inverse_norm_upper {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    ‖(ckmrvLeechImaginaryDenominator (y, v))⁻¹‖ ≤
      ckmrvLeechDenominatorBlockLower⁻¹ := by
  rw [norm_inv]
  have hb := (ckmrvLeechImaginaryDenominator_block_re_lower hy hv).trans
    (Complex.re_le_norm _)
  exact (inv_le_inv₀ (ckmrvLeechDenominatorBlockLower_pos.trans_le hb)
    ckmrvLeechDenominatorBlockLower_pos).mpr hb

theorem ckmrvGaussianLeechDenominator_block_re_lower {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    ckmrvLeechDenominatorBlockLower ≤
      (ckmrvLeechImaginaryDenominator (Real.pi / α, v)).re :=
  ckmrvLeechImaginaryDenominator_block_re_lower (gaussian_dual_compact_interval hα) hv

end E8Leech
