import E8Leech.ModularImaginaryIdentities
import E8Leech.CKMRVCoreMatrices

/-!
# A certified quadratic block in the published CKMRV residue formula

CKMRV arXiv:1902.05438v3, section 4.4, gives the minus residue as
I/(6912*pi^2*Delta) times the three-by-three matrix defined below.
We check its lower two-by-two block using actual pinned E4, E6 and Delta.
The analytic assertion that the two-variable kernel has this residue is
not proved here. The full three-by-three matrix has a negative first entry;
positivity of the lower block does not prove positivity of the full kernel.

Use the known answer det/trace for coercivity. The residual is a sum of two
squares, so no eigenvalue theory, zero classification or interval oracle is
needed. Compactness makes the bound uniform on every positive height interval.
-/

set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 3

noncomputable section

namespace E8Leech
open Set
open scoped Matrix BigOperators

/-- The coefficient matrix; the scalar analytic residue prefactor is excluded. -/
def ckmrvMinusResidueMatrix (z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-3456 * ModularForm.discriminant z, 0, 0;
     0, ModularForm.E₄ z ^ 2, -ModularForm.E₆ z;
     0, -ModularForm.E₆ z, ModularForm.E₄ z]

def ckmrvMinusResidueBlock (z : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ModularForm.E₄ z ^ 2, -ModularForm.E₆ z;
     -ModularForm.E₆ z, ModularForm.E₄ z]

def ckmrvMinusResidueQuadratic (y x w : ℝ) : ℝ :=
  let z := UpperHalfPlane.ofComplex (Complex.I * y)
  (ModularForm.E₄ z).re ^ 2 * x ^ 2 -
    2 * (ModularForm.E₆ z).re * x * w + (ModularForm.E₄ z).re * w ^ 2

def ckmrvMinusResidueCoercivity (y : ℝ) : ℝ :=
  let z := UpperHalfPlane.ofComplex (Complex.I * y)
  1728 * (ModularForm.discriminant z).re /
    ((ModularForm.E₄ z).re ^ 2 + (ModularForm.E₄ z).re)

theorem ckmrvMinusResidueMatrix_lower_block (z : UpperHalfPlane) (i j : Fin 2) :
    ckmrvMinusResidueMatrix z i.succ j.succ = ckmrvMinusResidueBlock z i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ckmrvMinusResidueBlock_det (z : UpperHalfPlane) :
    (ckmrvMinusResidueBlock z).det = 1728 * ModularForm.discriminant z := by
  rw [Matrix.det_fin_two]
  simpa [ckmrvMinusResidueBlock, pow_succ] using eisenstein_cubic_square_discriminant z

theorem ckmrvMinusResidueMatrix_first_entry_re_neg {y : ℝ} (hy : 0 < y) :
    (ckmrvMinusResidueMatrix (UpperHalfPlane.ofComplex (Complex.I * y)) 0 0).re < 0 := by
  have hD := discriminant_imaginary_re_pos hy
  change ((-3456 : ℂ) * ModularForm.discriminant _).re < 0
  simp only [Complex.mul_re]
  norm_num
  linarith only [hD]

theorem ckmrvMinusResidueQuadratic_eq_q {y : ℝ} (hy : 0 < y) (x w : ℝ) :
    ckmrvMinusResidueQuadratic y x w =
      eisensteinFourQ (imaginaryNome y) ^ 2 * x ^ 2 -
      2 * eisensteinSixQ (imaginaryNome y) * x * w +
      eisensteinFourQ (imaginaryNome y) * w ^ 2 := by
  simp only [ckmrvMinusResidueQuadratic, eisensteinFour_imaginary_eq_q hy,
    eisensteinSix_imaginary_eq_q hy, Complex.ofReal_re]

theorem ckmrvMinusResidueQuadratic_eq_block {y : ℝ} (hy : 0 < y) (v : Fin 2 → ℝ) :
    ckmrvMinusResidueQuadratic y (v 0) (v 1) =
      (∑ i : Fin 2, ∑ j : Fin 2, (v i : ℂ) *
        ckmrvMinusResidueBlock (UpperHalfPlane.ofComplex (Complex.I * y)) i j *
          (v j : ℂ)).re := by
  rw [ckmrvMinusResidueQuadratic_eq_q hy]
  simp [ckmrvMinusResidueBlock, Fin.sum_univ_two, eisensteinFour_imaginary_eq_q hy,
    eisensteinSix_imaginary_eq_q hy, Complex.mul_re, pow_two]
  ring

theorem ckmrvMinusResidueQuadratic_complete_square {y : ℝ} (hy : 0 < y) (x w : ℝ) :
    ckmrvMinusResidueQuadratic y x w =
      eisensteinFourQ (imaginaryNome y) *
        (w - eisensteinSixQ (imaginaryNome y) / eisensteinFourQ (imaginaryNome y) * x) ^ 2 +
      (1728 * discriminantQ (imaginaryNome y) / eisensteinFourQ (imaginaryNome y)) * x ^ 2 := by
  have hA : eisensteinFourQ (imaginaryNome y) ≠ 0 := by
    have := eisensteinFourQ_lower (imaginaryNome_pos y).le
    linarith
  rw [ckmrvMinusResidueQuadratic_eq_q hy]
  rw [← eisensteinQ_nome_cubic_square_discriminant hy]
  field_simp [hA]
  ring

theorem ckmrvMinusResidueCoercivity_eq_q {y : ℝ} (hy : 0 < y) :
    ckmrvMinusResidueCoercivity y = 1728 * discriminantQ (imaginaryNome y) /
      (eisensteinFourQ (imaginaryNome y) ^ 2 + eisensteinFourQ (imaginaryNome y)) := by
  simp only [ckmrvMinusResidueCoercivity, eisensteinFour_imaginary_eq_q hy,
    discriminant_imaginary_eq_q hy, Complex.ofReal_re]

theorem ckmrvMinusResidueCoercivity_pos {y : ℝ} (hy : 0 < y) :
    0 < ckmrvMinusResidueCoercivity y := by
  rw [ckmrvMinusResidueCoercivity_eq_q hy]
  have hA := eisensteinFourQ_lower (imaginaryNome_pos y).le
  exact div_pos (mul_pos (by norm_num) (discriminantQ_nome_pos hy))
    (by nlinarith only [sq_nonneg (eisensteinFourQ (imaginaryNome y)), hA])

theorem ckmrvMinusResidueQuadratic_coercive {y : ℝ} (hy : 0 < y) (x w : ℝ) :
    ckmrvMinusResidueCoercivity y * (x ^ 2 + w ^ 2) ≤
      ckmrvMinusResidueQuadratic y x w := by
  rw [ckmrvMinusResidueCoercivity_eq_q hy, ckmrvMinusResidueQuadratic_eq_q hy]
  let A := eisensteinFourQ (imaginaryNome y)
  let B := eisensteinSixQ (imaginaryNome y)
  let D := discriminantQ (imaginaryNome y)
  have hA : 1 ≤ A := eisensteinFourQ_lower (imaginaryNome_pos y).le
  have hT : 0 < A ^ 2 + A := by nlinarith only [sq_nonneg A, hA]
  have hdet : A ^ 3 - B ^ 2 = 1728 * D := eisensteinQ_nome_cubic_square_discriminant hy
  change 1728 * D / (A ^ 2 + A) * (x ^ 2 + w ^ 2) ≤
    A ^ 2 * x ^ 2 - 2 * B * x * w + A * w ^ 2
  rw [div_mul_eq_mul_div, div_le_iff₀ hT]
  have hs : (A ^ 2 * x - B * w) ^ 2 + (A * w - B * x) ^ 2 =
      (A ^ 2 * x ^ 2 - 2 * B * x * w + A * w ^ 2) * (A ^ 2 + A) -
        1728 * D * (x ^ 2 + w ^ 2) := by
    rw [← hdet]
    ring
  nlinarith only [hs, sq_nonneg (A ^ 2 * x - B * w), sq_nonneg (A * w - B * x)]

theorem ckmrvMinusResidueQuadratic_nonneg {y : ℝ} (hy : 0 < y) (x w : ℝ) :
    0 ≤ ckmrvMinusResidueQuadratic y x w :=
  (mul_nonneg (ckmrvMinusResidueCoercivity_pos hy).le
    (add_nonneg (sq_nonneg x) (sq_nonneg w))).trans
    (ckmrvMinusResidueQuadratic_coercive hy x w)

theorem ckmrvMinusResidueQuadratic_pos {y : ℝ} (hy : 0 < y) {x w : ℝ}
    (hxw : x ≠ 0 ∨ w ≠ 0) : 0 < ckmrvMinusResidueQuadratic y x w := by
  have hs : 0 < x ^ 2 + w ^ 2 := by
    rcases hxw with hx | hw
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg w)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hw)
  exact (mul_pos (ckmrvMinusResidueCoercivity_pos hy) hs).trans_le
    (ckmrvMinusResidueQuadratic_coercive hy x w)

theorem ckmrvMinusResidueQuadratic_eq_zero_iff {y : ℝ} (hy : 0 < y) (x w : ℝ) :
    ckmrvMinusResidueQuadratic y x w = 0 ↔ x = 0 ∧ w = 0 := by
  constructor
  · intro hzero
    by_contra hn
    have hp := ckmrvMinusResidueQuadratic_pos hy (by tauto : x ≠ 0 ∨ w ≠ 0)
    linarith only [hp, hzero]
  · rintro ⟨rfl, rfl⟩
    simp [ckmrvMinusResidueQuadratic]

theorem continuousOn_ckmrvMinusResidueCoercivity :
    ContinuousOn ckmrvMinusResidueCoercivity (Ioi (0 : ℝ)) := by
  have hA : ContinuousOn (fun y : ℝ =>
      (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).re) (Ioi 0) :=
    Complex.continuous_re.comp_continuousOn
      ((ModularFormClass.continuous ModularForm.E₄).comp_continuousOn
        UpperHalfPlane.continuousOn_ofComplex_I_mul)
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  have hDi := Complex.continuous_re.comp_continuousOn
    (hD.comp_continuousOn UpperHalfPlane.continuousOn_ofComplex_I_mul)
  apply ((continuousOn_const.mul hDi).div (hA.pow 2 |>.add hA) ?_)
  intro y hy
  change (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).re ^ 2 +
    (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).re ≠ 0
  have hE := eisensteinFour_imaginary_re_lower hy
  exact ne_of_gt (by
    nlinarith only [hE, sq_nonneg (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * y))).re])

theorem exists_uniform_ckmrvMinusResidueQuadratic_lower {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ Icc a b, ∀ x w : ℝ,
      c * (x ^ 2 + w ^ 2) ≤ ckmrvMinusResidueQuadratic y x w := by
  have hcont := continuousOn_ckmrvMinusResidueCoercivity.mono
    (show Icc a b ⊆ Ioi (0 : ℝ) from fun _ hy => ha.trans_le hy.1)
  obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
  refine ⟨ckmrvMinusResidueCoercivity y0,
    ckmrvMinusResidueCoercivity_pos (ha.trans_le hy0.1), ?_⟩
  intro y hy x w
  exact (mul_le_mul_of_nonneg_right (hmin hy)
    (add_nonneg (sq_nonneg x) (sq_nonneg w))).trans
    (ckmrvMinusResidueQuadratic_coercive (ha.trans_le hy.1) x w)

end E8Leech
