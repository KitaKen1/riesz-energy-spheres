import E8Leech.CKMRVRegularCoefficients
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic actual coefficient entries along holomorphic paths

Use the original four formulas, including the regular part of the Leech-plus
core. Lean's reciprocal is totalized at zero; meromorphy is a punctured-local
property, not a declaration that these assigned values remove poles.
No explicit derivative of j, pole order, residue or phi/psi correspondence
is assumed or proved here.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open scoped Manifold Matrix

theorem analyticAt_of_upperHalfPlane_mdifferentiable {f : UpperHalfPlane → ℂ}
    (hf : MDiff f) (ζ : UpperHalfPlane) :
    AnalyticAt ℂ (fun w => f (UpperHalfPlane.ofComplex w)) (ζ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds ζ.im_pos)

theorem mdifferentiable_ckmrvModularFactor (k : Fin 9) :
    MDiff (fun z : UpperHalfPlane => ckmrvModularFactor z k) := by
  have hA := ModularFormClass.holo ModularForm.E₄
  have hB := ModularFormClass.holo ModularForm.E₆
  have hD := mdifferentiable_modularDiscriminant
  simp_rw [ckmrvModularFactor_eq_products]
  fin_cases k
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z * ModularForm.E₆ z / ModularForm.discriminant z : ℂ))
    exact (hA.mul hB).div hD ModularForm.discriminant_ne_zero
  · change MDiff (fun z : UpperHalfPlane => (1 : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z / ModularForm.discriminant z : ℂ))
    exact ((hA.pow 2).mul hB).div hD ModularForm.discriminant_ne_zero
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z : ℂ))
    exact hA
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₆ z : ℂ))
    exact hB
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z ^ 2 : ℂ))
    exact hA.pow 2
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z * ModularForm.E₆ z : ℂ))
    exact hA.mul hB
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.discriminant z : ℂ))
    exact hD
  · change MDiff (fun z : UpperHalfPlane => (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z : ℂ))
    exact (hA.pow 2).mul hB

theorem meromorphicAt_ckmrvEightPlusCore_entry (g : ℂ → ℂ) {x : ℂ}
    (hg : MeromorphicAt g x) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvEightPlusCore (g w) i j) x := by
  fin_cases i <;> fin_cases j
  · change MeromorphicAt (fun w => (g w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-2 * g w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-2 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop

theorem meromorphicAt_ckmrvEightMinusCore_entry (J : ℂ → ℂ) {x : ℂ}
    (hJ : MeromorphicAt J x) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvEightMinusCore (J w) i j) x := by
  fin_cases i <;> fin_cases j
  · change MeromorphicAt (fun w => (-2 * 1728 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-1 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1728 - J w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (J w : ℂ)) x
    fun_prop

theorem meromorphicAt_ckmrvLeechPlusCore_entry (J g : ℂ → ℂ) {x : ℂ}
    (hJ : MeromorphicAt J x) (hg : MeromorphicAt g x) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvLeechPlusCore (J w) (g w) i j) x := by
  fin_cases i <;> fin_cases j
  · change MeromorphicAt (fun w => (6 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1728 / g w - 6 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-12 * J w + 5 * 1728 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-2 * 1728 / g w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (12 * J w - 7 * 1728 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1728 / g w + 6 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-6 : ℂ)) x
    fun_prop

theorem meromorphicAt_ckmrvLeechMinusCore_entry (J g : ℂ → ℂ) {x : ℂ}
    (hJ : MeromorphicAt J x) (hg : MeromorphicAt g x) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvLeechMinusCore (J w) (g w) i j) x := by
  fin_cases i <;> fin_cases j
  · change MeromorphicAt (fun w => (-2 * 1728 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-2 * 1728 * g w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (J w + 2 * g w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (-1 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (0 : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1728 - 2 * g w - J w : ℂ)) x
    fun_prop
  · change MeromorphicAt (fun w => (1 : ℂ)) x
    fun_prop

theorem meromorphicAt_ckmrvEightPlusCoefficientMatrix_entry_comp
    (τ z : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ) (hz : MDiff z)
    (ζ : UpperHalfPlane) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvEightPlusCoefficientMatrix
      (τ (UpperHalfPlane.ofComplex w)) (z (UpperHalfPlane.ofComplex w)) i j) (ζ : ℂ) := by
  have hFτ (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hτ) ζ).meromorphicAt
  have hFz (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hz) ζ).meromorphicAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_modularDiscriminant.comp hz) ζ).meromorphicAt
  have hJτ := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hτ) ζ).meromorphicAt
  have hJz := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hz) ζ).meromorphicAt
  have hcore := meromorphicAt_ckmrvEightPlusCore_entry _ (hJτ.fun_sub hJz) i j
  simp only [ckmrvEightPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix_apply]
  change MeromorphicAt (fun w => (ckmrvPlusScale * ModularForm.discriminant (z (UpperHalfPlane.ofComplex w)) * (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))))⁻¹ *
    (ckmrvModularFactor (τ (UpperHalfPlane.ofComplex w)) (![4, 3, 2] i) *
      ckmrvEightPlusCore (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))) i j *
      ckmrvModularFactor (z (UpperHalfPlane.ofComplex w)) (![7, 6, 5] j))) (ζ : ℂ)
  exact ((((MeromorphicAt.const ckmrvPlusScale (ζ : ℂ)).fun_mul hD).fun_mul (hJτ.fun_sub hJz)).fun_inv).fun_mul
    (((hFτ _).fun_mul hcore).fun_mul (hFz _))

theorem meromorphicAt_ckmrvEightMinusCoefficientMatrix_entry_comp
    (τ z : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ) (hz : MDiff z)
    (ζ : UpperHalfPlane) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvEightMinusCoefficientMatrix
      (τ (UpperHalfPlane.ofComplex w)) (z (UpperHalfPlane.ofComplex w)) i j) (ζ : ℂ) := by
  have hFτ (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hτ) ζ).meromorphicAt
  have hFz (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hz) ζ).meromorphicAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_modularDiscriminant.comp hz) ζ).meromorphicAt
  have hJτ := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hτ) ζ).meromorphicAt
  have hJz := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hz) ζ).meromorphicAt
  have hcore := meromorphicAt_ckmrvEightMinusCore_entry _ hJτ i j
  simp only [ckmrvEightMinusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix_apply]
  change MeromorphicAt (fun w => (ckmrvMinusScale * ModularForm.discriminant (z (UpperHalfPlane.ofComplex w)) * (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))))⁻¹ *
    (ckmrvModularFactor (τ (UpperHalfPlane.ofComplex w)) (![3, 2, 1] i) *
      ckmrvEightMinusCore (kleinModularJ (τ (UpperHalfPlane.ofComplex w))) i j *
      ckmrvModularFactor (z (UpperHalfPlane.ofComplex w)) (![6, 5, 4] j))) (ζ : ℂ)
  exact ((((MeromorphicAt.const ckmrvMinusScale (ζ : ℂ)).fun_mul hD).fun_mul (hJτ.fun_sub hJz)).fun_inv).fun_mul
    (((hFτ _).fun_mul hcore).fun_mul (hFz _))

theorem meromorphicAt_ckmrvLeechPlusCoefficientMatrix_entry_comp
    (τ z : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ) (hz : MDiff z)
    (ζ : UpperHalfPlane) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvLeechPlusCoefficientMatrix
      (τ (UpperHalfPlane.ofComplex w)) (z (UpperHalfPlane.ofComplex w)) i j) (ζ : ℂ) := by
  have hFτ (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hτ) ζ).meromorphicAt
  have hFz (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hz) ζ).meromorphicAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_modularDiscriminant.comp hz) ζ).meromorphicAt
  have hJτ := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hτ) ζ).meromorphicAt
  have hJz := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hz) ζ).meromorphicAt
  have hcore := meromorphicAt_ckmrvLeechPlusCore_entry _ _ hJτ (hJτ.fun_sub hJz) i j
  simp only [ckmrvLeechPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix_apply]
  change MeromorphicAt (fun w => (1728 * ckmrvPlusScale * ModularForm.discriminant (z (UpperHalfPlane.ofComplex w)))⁻¹ *
    (ckmrvModularFactor (τ (UpperHalfPlane.ofComplex w)) (![8, 7, 6] i) *
      ckmrvLeechPlusCore (kleinModularJ (τ (UpperHalfPlane.ofComplex w))) (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))) i j *
      ckmrvModularFactor (z (UpperHalfPlane.ofComplex w)) (![3, 2, 1] j))) (ζ : ℂ)
  exact (((MeromorphicAt.const (1728 * ckmrvPlusScale) (ζ : ℂ)).fun_mul hD).fun_inv).fun_mul
    (((hFτ _).fun_mul hcore).fun_mul (hFz _))

theorem meromorphicAt_ckmrvLeechMinusCoefficientMatrix_entry_comp
    (τ z : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ) (hz : MDiff z)
    (ζ : UpperHalfPlane) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvLeechMinusCoefficientMatrix
      (τ (UpperHalfPlane.ofComplex w)) (z (UpperHalfPlane.ofComplex w)) i j) (ζ : ℂ) := by
  have hFτ (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hτ) ζ).meromorphicAt
  have hFz (k : Fin 9) := (analyticAt_of_upperHalfPlane_mdifferentiable
    ((mdifferentiable_ckmrvModularFactor k).comp hz) ζ).meromorphicAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_modularDiscriminant.comp hz) ζ).meromorphicAt
  have hJτ := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hτ) ζ).meromorphicAt
  have hJz := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_kleinModularJ.comp hz) ζ).meromorphicAt
  have hcore := meromorphicAt_ckmrvLeechMinusCore_entry _ _ hJτ (hJτ.fun_sub hJz) i j
  simp only [ckmrvLeechMinusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix_apply]
  change MeromorphicAt (fun w => (ckmrvMinusScale * ModularForm.discriminant (z (UpperHalfPlane.ofComplex w)) * (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))))⁻¹ *
    (ckmrvModularFactor (τ (UpperHalfPlane.ofComplex w)) (![7, 6, 5] i) *
      ckmrvLeechMinusCore (kleinModularJ (τ (UpperHalfPlane.ofComplex w))) (kleinModularJ (τ (UpperHalfPlane.ofComplex w)) - kleinModularJ (z (UpperHalfPlane.ofComplex w))) i j *
      ckmrvModularFactor (z (UpperHalfPlane.ofComplex w)) (![2, 1, 0] j))) (ζ : ℂ)
  exact ((((MeromorphicAt.const ckmrvMinusScale (ζ : ℂ)).fun_mul hD).fun_mul (hJτ.fun_sub hJz)).fun_inv).fun_mul
    (((hFτ _).fun_mul hcore).fun_mul (hFz _))

theorem meromorphicAt_ckmrvCoefficientFamily_entry_comp
    (τ z : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ) (hz : MDiff z)
    (ζ : UpperHalfPlane) (k : Fin 4) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvCoefficientFamily k
      (τ (UpperHalfPlane.ofComplex w)) (z (UpperHalfPlane.ofComplex w)) i j) (ζ : ℂ) := by
  fin_cases k
  · exact meromorphicAt_ckmrvEightPlusCoefficientMatrix_entry_comp τ z hτ hz ζ i j
  · exact meromorphicAt_ckmrvEightMinusCoefficientMatrix_entry_comp τ z hτ hz ζ i j
  · exact meromorphicAt_ckmrvLeechPlusCoefficientMatrix_entry_comp τ z hτ hz ζ i j
  · exact meromorphicAt_ckmrvLeechMinusCoefficientMatrix_entry_comp τ z hτ hz ζ i j

theorem meromorphicAt_ckmrvCoefficientFamily_entry_left
    (τ z : UpperHalfPlane) (k : Fin 4) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvCoefficientFamily k
      (UpperHalfPlane.ofComplex w) z i j) (τ : ℂ) :=
  meromorphicAt_ckmrvCoefficientFamily_entry_comp id (fun _ => z)
    mdifferentiable_id mdifferentiable_const τ k i j

theorem meromorphicAt_ckmrvCoefficientFamily_entry_right
    (τ z : UpperHalfPlane) (k : Fin 4) (i j : Fin 3) :
    MeromorphicAt (fun w => ckmrvCoefficientFamily k
      τ (UpperHalfPlane.ofComplex w) i j) (z : ℂ) :=
  meromorphicAt_ckmrvCoefficientFamily_entry_comp (fun _ => τ) id
    mdifferentiable_const mdifferentiable_id z k i j

end E8Leech
