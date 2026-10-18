import Riesz.E8ThetaAnalytic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The actual E8 theta q-expansion and its constant coefficient

Periodicity, holomorphy and the actual cusp limit already suffice for this
q-expansion connection. The S law and a modular-form structure are not needed
for the constant coefficient proof and are not assumed here.
-/

set_option autoImplicit false
noncomputable section
open UpperHalfPlane Filter Function
open scoped Topology Manifold
namespace SphericalRiesz

def e8ThetaUpper (τ : ℍ) : ℂ := e8Theta τ

theorem e8ThetaUpper_mdifferentiable : MDiff e8ThetaUpper := by
  intro τ
  exact ((e8Theta_differentiableOn τ τ.im_pos).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)).mdifferentiableAt.comp τ
    (UpperHalfPlane.mdifferentiable_coe τ)

theorem e8ThetaUpper_periodic : Periodic (e8ThetaUpper ∘ ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  change e8Theta ((1 : ℝ) +ᵥ τ : ℍ) = e8Theta τ
  simpa [UpperHalfPlane.coe_vadd, add_comm] using e8Theta_add_one τ

theorem e8ThetaUpper_cusp_analytic : AnalyticAt ℂ (cuspFunction 1 e8ThetaUpper) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num) e8ThetaUpper_periodic
    e8ThetaUpper_mdifferentiable e8Theta_bounded_atImInfty

theorem e8ThetaUpper_valueAtInfty : valueAtInfty e8ThetaUpper = 1 :=
  e8Theta_tendsto_atImInfty.limUnder_eq

theorem e8ThetaUpper_cusp_zero : cuspFunction 1 e8ThetaUpper 0 = 1 := by
  rw [UpperHalfPlane.cuspFunction_apply_zero (by norm_num)
    e8ThetaUpper_cusp_analytic e8ThetaUpper_periodic, e8ThetaUpper_valueAtInfty]

theorem e8ThetaUpper_qExpansion_zero : (qExpansion 1 e8ThetaUpper).coeff 0 = 1 := by
  rw [UpperHalfPlane.qExpansion_coeff_zero (by norm_num)
    e8ThetaUpper_cusp_analytic e8ThetaUpper_periodic, e8ThetaUpper_valueAtInfty]

theorem e8ThetaUpper_qExpansion_hasSum (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 e8ThetaUpper).coeff m •
      Periodic.qParam 1 τ ^ m) (e8ThetaUpper τ) :=
  UpperHalfPlane.hasSum_qExpansion (by norm_num) e8ThetaUpper_periodic
    e8ThetaUpper_mdifferentiable e8Theta_bounded_atImInfty τ

#print axioms e8ThetaUpper_mdifferentiable
#print axioms e8ThetaUpper_periodic
#print axioms e8ThetaUpper_cusp_analytic
#print axioms e8ThetaUpper_valueAtInfty
#print axioms e8ThetaUpper_cusp_zero
#print axioms e8ThetaUpper_qExpansion_zero
#print axioms e8ThetaUpper_qExpansion_hasSum

end SphericalRiesz
