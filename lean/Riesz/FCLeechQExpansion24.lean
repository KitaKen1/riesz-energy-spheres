import Riesz.FCLeechThetaAnalytic24
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The actual Leech theta q-expansion and its constant coefficient

Periodicity, holomorphy and the actual cusp limit already suffice for this
q-expansion connection. The S law and a modular-form structure are not needed
for the constant coefficient proof and are not assumed here.
-/

set_option autoImplicit false
noncomputable section
open UpperHalfPlane Filter Function
open scoped Topology Manifold
namespace SphericalRiesz

def leechThetaUpper (τ : ℍ) : ℂ := leechTheta τ

theorem leechThetaUpper_mdifferentiable : MDiff leechThetaUpper := by
  intro τ
  exact ((leechTheta_differentiableOn τ τ.im_pos).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)).mdifferentiableAt.comp τ
    (UpperHalfPlane.mdifferentiable_coe τ)

theorem leechThetaUpper_periodic : Periodic (leechThetaUpper ∘ ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  change leechTheta ((1 : ℝ) +ᵥ τ : ℍ) = leechTheta τ
  simpa [UpperHalfPlane.coe_vadd, add_comm] using leechTheta_add_one τ

theorem leechThetaUpper_cusp_analytic : AnalyticAt ℂ (cuspFunction 1 leechThetaUpper) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num) leechThetaUpper_periodic
    leechThetaUpper_mdifferentiable leechTheta_bounded_atImInfty

theorem leechThetaUpper_valueAtInfty : valueAtInfty leechThetaUpper = 1 :=
  leechTheta_tendsto_atImInfty.limUnder_eq

theorem leechThetaUpper_cusp_zero : cuspFunction 1 leechThetaUpper 0 = 1 := by
  rw [UpperHalfPlane.cuspFunction_apply_zero (by norm_num)
    leechThetaUpper_cusp_analytic leechThetaUpper_periodic, leechThetaUpper_valueAtInfty]

theorem leechThetaUpper_qExpansion_zero : (qExpansion 1 leechThetaUpper).coeff 0 = 1 := by
  rw [UpperHalfPlane.qExpansion_coeff_zero (by norm_num)
    leechThetaUpper_cusp_analytic leechThetaUpper_periodic, leechThetaUpper_valueAtInfty]

theorem leechThetaUpper_qExpansion_hasSum (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 leechThetaUpper).coeff m •
      Periodic.qParam 1 τ ^ m) (leechThetaUpper τ) :=
  UpperHalfPlane.hasSum_qExpansion (by norm_num) leechThetaUpper_periodic
    leechThetaUpper_mdifferentiable leechTheta_bounded_atImInfty τ

#print axioms leechThetaUpper_mdifferentiable
#print axioms leechThetaUpper_periodic
#print axioms leechThetaUpper_cusp_analytic
#print axioms leechThetaUpper_valueAtInfty
#print axioms leechThetaUpper_cusp_zero
#print axioms leechThetaUpper_qExpansion_zero
#print axioms leechThetaUpper_qExpansion_hasSum

end SphericalRiesz
