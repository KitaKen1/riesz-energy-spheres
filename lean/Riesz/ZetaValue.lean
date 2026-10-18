import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic

/-!
# The zeta value expected in the E8 regularized constant

This is the scalar calculation only. Identifying the actual lattice
regularization with this analytically continued zeta product is not proved.
-/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

theorem riemannZeta_neg_one_value : riemannZeta (-1) = (-1/12 : ℂ) := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [show bernoulli 2 = 1/6 by decide +kernel] at h ⊢
  exact h

theorem e8_zeta_product_at_two :
    60 * riemannZeta 2 * riemannZeta (-1) = -5*(Real.pi : ℂ)^2/6 := by
  rw [riemannZeta_two, riemannZeta_neg_one_value]
  ring

#print axioms riemannZeta_neg_one_value
#print axioms e8_zeta_product_at_two

end SphericalRiesz
