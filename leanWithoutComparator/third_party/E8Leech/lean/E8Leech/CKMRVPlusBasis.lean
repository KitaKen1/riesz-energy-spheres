import E8Leech.CKMRVActualDerivatives

/-!
# Actual plus bases and finite residue cancellation

The phi/tilde-phi formulas are CKMRV arXiv:1902.05438v3, Propositions
4.4/4.7. The tilde formula is identified with actual E2 slash S. Integer
translation and the published residue matrix reduce to finite polynomial
algebra; no classification of annihilator spaces or modular orbits is used.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open UpperHalfPlane Filter Function
open scoped Manifold Topology MatrixGroups ModularForm Matrix BigOperators

def ckmrvTranslate (n : ℤ) (z : UpperHalfPlane) : UpperHalfPlane :=
  ofComplex ((z : ℂ) + n)

theorem ckmrvTranslate_coe (n : ℤ) (z : UpperHalfPlane) :
    (ckmrvTranslate n z : ℂ) = (z : ℂ) + n := by
  exact congrArg UpperHalfPlane.coe (ofComplex_apply_of_im_pos (by
    simpa only [Complex.add_im, Complex.intCast_im, add_zero]
      using z.coe_im_pos))

theorem eisensteinTwo_translate (n : ℤ) (z : UpperHalfPlane) :
    EisensteinSeries.E2 (ckmrvTranslate n z) = EisensteinSeries.E2 z := by
  simpa [ckmrvTranslate, mul_one, Function.comp_def, ofComplex_apply] using
    eisensteinTwo_periodic_comp_ofComplex.int_mul n (z : ℂ)

theorem levelOne_translate {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (n : ℤ) (z : UpperHalfPlane) : f (ckmrvTranslate n z) = f z := by
  simpa [ckmrvTranslate, mul_one, Function.comp_def, ofComplex_apply] using
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL).int_mul n
      (z : ℂ)

theorem discriminant_translate (n : ℤ) (z : UpperHalfPlane) :
    ModularForm.discriminant (ckmrvTranslate n z) = ModularForm.discriminant z := by
  exact levelOne_translate (CuspForm.discriminant : ModularForm 𝒮ℒ 12) n z

theorem ckmrvModularFactor_translate (n : ℤ) (z : UpperHalfPlane) (i : Fin 9) :
    ckmrvModularFactor (ckmrvTranslate n z) i = ckmrvModularFactor z i := by
  simp_rw [ckmrvModularFactor_eq_products]
  rw [levelOne_translate ModularForm.E₄, levelOne_translate ModularForm.E₆,
    discriminant_translate]

theorem kleinModularJ_translate (n : ℤ) (z : UpperHalfPlane) :
    kleinModularJ (ckmrvTranslate n z) = kleinModularJ z := by
  simp only [kleinModularJ, levelOne_translate, discriminant_translate]

theorem ckmrvEightPlusCoefficientMatrix_translate_left (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvEightPlusCoefficientMatrix (ckmrvTranslate n τ) z =
      ckmrvEightPlusCoefficientMatrix τ z := by
  simp only [ckmrvEightPlusCoefficientMatrix, ckmrvModularCoreMatrix, kleinModularJ_translate,
    ckmrvModularFactor_translate]

theorem ckmrvLeechPlusCoefficientMatrix_translate_left (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvLeechPlusCoefficientMatrix (ckmrvTranslate n τ) z =
      ckmrvLeechPlusCoefficientMatrix τ z := by
  simp only [ckmrvLeechPlusCoefficientMatrix, ckmrvModularCoreMatrix, kleinModularJ_translate,
    ckmrvModularFactor_translate]

/-- Ordered by weights -2, 0, 2, with the actual E2. -/
def ckmrvPhiBasis (z : UpperHalfPlane) : Fin 3 → ℂ :=
  ![(z : ℂ), (z : ℂ) * EisensteinSeries.E2 z - 3 * Complex.I / (Real.pi : ℂ),
    (z : ℂ) * EisensteinSeries.E2 z ^ 2 -
      6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 z]

/-- Polynomial form of z^2, z^2 (E2 slash S), z^2 (E2 slash S)^2. -/
def ckmrvTildePhiBasis (z : UpperHalfPlane) : Fin 3 → ℂ :=
  ![(z : ℂ) ^ 2,
    (z : ℂ) ^ 2 * EisensteinSeries.E2 z - 6 * Complex.I / (Real.pi : ℂ) * (z : ℂ),
    (z : ℂ) ^ 2 * EisensteinSeries.E2 z ^ 2 -
      12 * Complex.I / (Real.pi : ℂ) * (z : ℂ) * EisensteinSeries.E2 z -
        36 / (Real.pi : ℂ) ^ 2]

theorem eisensteinTwo_slash_S_explicit (z : UpperHalfPlane) :
    (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularGroup.S) z =
      EisensteinSeries.E2 z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, EisensteinSeries.D2_S, riemannZeta_two] at h
  rw [h]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp, z.ne_zero]

theorem ckmrvTildePhiBasis_eq_slash (z : UpperHalfPlane) :
    ckmrvTildePhiBasis z =
      ![(z : ℂ) ^ 2, (z : ℂ) ^ 2 * (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularGroup.S) z,
        (z : ℂ) ^ 2 * ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularGroup.S) z) ^ 2] := by
  rw [eisensteinTwo_slash_S_explicit]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  ext i
  fin_cases i
  · rfl
  · change (z : ℂ) ^ 2 * EisensteinSeries.E2 z -
      6 * Complex.I / (Real.pi : ℂ) * (z : ℂ) =
      (z : ℂ) ^ 2 * (EisensteinSeries.E2 z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))
    field_simp [hp, z.ne_zero]
  · change (z : ℂ) ^ 2 * EisensteinSeries.E2 z ^ 2 -
      12 * Complex.I / (Real.pi : ℂ) * (z : ℂ) * EisensteinSeries.E2 z -
        36 / (Real.pi : ℂ) ^ 2 =
      (z : ℂ) ^ 2 * (EisensteinSeries.E2 z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))) ^ 2
    field_simp [hp, z.ne_zero]
    ring_nf
    simp [Complex.I_sq]
    ring

theorem mdifferentiable_ckmrvPhiBasis (i : Fin 3) :
    MDiff (fun z : UpperHalfPlane => ckmrvPhiBasis z i) := by
  fin_cases i
  · exact mdifferentiable_coe
  · exact (mdifferentiable_coe.mul E2_mdifferentiable).sub mdifferentiable_const
  · exact (mdifferentiable_coe.mul (E2_mdifferentiable.pow 2)).sub
      (mdifferentiable_const.mul E2_mdifferentiable)

theorem mdifferentiable_ckmrvTildePhiBasis (i : Fin 3) :
    MDiff (fun z : UpperHalfPlane => ckmrvTildePhiBasis z i) := by
  fin_cases i
  · exact mdifferentiable_coe.pow 2
  · exact ((mdifferentiable_coe.pow 2).mul E2_mdifferentiable).sub
      (mdifferentiable_const.mul mdifferentiable_coe)
  · exact (((mdifferentiable_coe.pow 2).mul (E2_mdifferentiable.pow 2)).sub
      ((mdifferentiable_const.mul mdifferentiable_coe).mul E2_mdifferentiable)).sub
        mdifferentiable_const

theorem ckmrvPhiBasis_translate (n : ℤ) (z : UpperHalfPlane) :
    ckmrvPhiBasis (ckmrvTranslate n z) =
      ![(z : ℂ) + n, ((z : ℂ) + n) * EisensteinSeries.E2 z - 3 * Complex.I / (Real.pi : ℂ),
        ((z : ℂ) + n) * EisensteinSeries.E2 z ^ 2 -
          6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 z] := by
  simp only [ckmrvPhiBasis, ckmrvTranslate_coe, eisensteinTwo_translate]

theorem ckmrvPlusResidue_contract_translate (n : ℤ) (z : UpperHalfPlane) :
    ckmrvCoreContraction (ckmrvPhiBasis (ckmrvTranslate n z))
      (ckmrvTildePhiBasis z) ckmrvPlusResidueMatrix = -36 * n / (Real.pi : ℂ) ^ 2 := by
  rw [ckmrvPhiBasis_translate]
  simp only [ckmrvCoreContraction, ckmrvTildePhiBasis, ckmrvPlusResidueMatrix,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    ]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem ckmrvPlusResidue_contract_self (z : UpperHalfPlane) :
    ckmrvCoreContraction (ckmrvPhiBasis z) (ckmrvTildePhiBasis z)
      ckmrvPlusResidueMatrix = 0 := by
  simpa [ckmrvTranslate] using ckmrvPlusResidue_contract_translate 0 z

end E8Leech
