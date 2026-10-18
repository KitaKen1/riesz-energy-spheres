import Riesz.E8ThetaTransform
import Riesz.E8QExpansion
import Riesz.WeightFour

/-!
The actual E8 theta is a genuine level-one weight-four modular form.
Its already checked constant coefficient 1 determines the entire form.
No lattice shell enumeration or regularized sum is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open UpperHalfPlane ModularForm ModularGroup
open scoped MatrixGroups ArithmeticFunction.sigma Manifold
namespace SphericalRiesz

theorem e8ThetaUpper_slash_S : e8ThetaUpper ∣[(4 : ℤ)] S = e8ThetaUpper := by
  funext τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]
  have hs : e8ThetaUpper (S • τ) = (τ : ℂ)^4 * e8ThetaUpper τ := by
    unfold e8ThetaUpper
    rw [UpperHalfPlane.modular_S_smul]
    simpa only [UpperHalfPlane.coe_mk, inv_neg, div_eq_mul_inv, neg_one_mul] using
      e8Theta_transform_S τ.im_pos
  rw [hs]
  have hτ0 : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp [zpow_neg, hτ0, mul_assoc, mul_comm]

theorem e8ThetaUpper_slash_T : e8ThetaUpper ∣[(4 : ℤ)] T = e8ThetaUpper := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]
    norm_num [ModularGroup.T]
  rw [hd]
  simp only [one_zpow, mul_one]
  unfold e8ThetaUpper
  rw [UpperHalfPlane.modular_T_smul]
  simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm] using e8Theta_add_one τ

theorem e8ThetaUpper_slash_all (γ : SL(2, ℤ)) :
    e8ThetaUpper ∣[(4 : ℤ)] γ = e8ThetaUpper :=
  SlashInvariantForm.slash_action_generators_SL2Z e8ThetaUpper_slash_S e8ThetaUpper_slash_T γ

def e8ThetaModularForm : ModularForm 𝒮ℒ 4 where
  toFun := e8ThetaUpper
  slash_action_eq' γ hγ := by
    obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hγ
    exact e8ThetaUpper_slash_all δ
  holo' := e8ThetaUpper_mdifferentiable
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    rw [e8ThetaUpper_slash_all γ]
    exact e8Theta_bounded_atImInfty

@[simp] theorem e8ThetaModularForm_apply (τ : ℍ) :
    e8ThetaModularForm τ = e8ThetaUpper τ := rfl

theorem e8ThetaModularForm_qExpansion_zero :
    (qExpansion 1 e8ThetaModularForm).coeff 0 = 1 := e8ThetaUpper_qExpansion_zero

theorem e8ThetaModularForm_eq_E4 : e8ThetaModularForm = E₄ :=
  weightFour_eq_E4 e8ThetaModularForm e8ThetaModularForm_qExpansion_zero

theorem e8ThetaUpper_positive_coeff (n : ℕ) (hn : n ≠ 0) :
    (qExpansion 1 e8ThetaUpper).coeff n = 240 * (ArithmeticFunction.sigma 3 n : ℂ) :=
  weightFour_positive_coeff e8ThetaModularForm e8ThetaModularForm_qExpansion_zero n hn

theorem e8Theta_eq_E4 (τ : ℍ) : e8Theta τ = E₄ τ :=
  congrArg (fun f : ModularForm 𝒮ℒ 4 => f τ) e8ThetaModularForm_eq_E4

#print axioms e8ThetaUpper_slash_S
#print axioms e8ThetaUpper_slash_T
#print axioms e8ThetaUpper_slash_all
#print axioms e8ThetaModularForm_apply
#print axioms e8ThetaModularForm_qExpansion_zero
#print axioms e8ThetaModularForm_eq_E4
#print axioms e8ThetaUpper_positive_coeff
#print axioms e8Theta_eq_E4
end SphericalRiesz
