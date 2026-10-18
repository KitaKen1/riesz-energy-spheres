import Riesz.FCLeechQExpansion24
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
The actual Leech theta is a genuine level-one weight-four modular form.
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

theorem leechThetaUpper_slash_S : leechThetaUpper ∣[(12 : ℤ)] S = leechThetaUpper := by
  funext τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]
  have hs : leechThetaUpper (S • τ) = (τ : ℂ)^12 * leechThetaUpper τ := by
    unfold leechThetaUpper
    rw [UpperHalfPlane.modular_S_smul]
    simpa only [UpperHalfPlane.coe_mk, inv_neg, div_eq_mul_inv, neg_one_mul] using
      leechTheta_transform_S τ.im_pos
  rw [hs]
  have hτ0 : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp [zpow_neg, hτ0, mul_assoc, mul_comm]

theorem leechThetaUpper_slash_T : leechThetaUpper ∣[(12 : ℤ)] T = leechThetaUpper := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]
    norm_num [ModularGroup.T]
  rw [hd]
  simp only [one_zpow, mul_one]
  unfold leechThetaUpper
  rw [UpperHalfPlane.modular_T_smul]
  simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm] using leechTheta_add_one τ

theorem leechThetaUpper_slash_all (γ : SL(2, ℤ)) :
    leechThetaUpper ∣[(12 : ℤ)] γ = leechThetaUpper :=
  SlashInvariantForm.slash_action_generators_SL2Z leechThetaUpper_slash_S leechThetaUpper_slash_T γ

def leechThetaModularForm : ModularForm 𝒮ℒ 12 where
  toFun := leechThetaUpper
  slash_action_eq' γ hγ := by
    obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hγ
    exact leechThetaUpper_slash_all δ
  holo' := leechThetaUpper_mdifferentiable
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    rw [leechThetaUpper_slash_all γ]
    exact leechTheta_bounded_atImInfty

@[simp] theorem leechThetaModularForm_apply (τ : ℍ) :
    leechThetaModularForm τ = leechThetaUpper τ := rfl

theorem leechThetaModularForm_qExpansion_zero :
    (qExpansion 1 leechThetaModularForm).coeff 0 = 1 := leechThetaUpper_qExpansion_zero


end SphericalRiesz
