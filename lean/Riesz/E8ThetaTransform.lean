import Riesz.E8ThetaSchwartz
import Riesz.E8Covolume
import Riesz.E8Dual
import Riesz.PoissonLattice

/-! Gaussian Poisson inversion for the unchanged actual E8 theta sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped FourierTransform RealInnerProductSpace
namespace SphericalRiesz

theorem e8Theta_transform_S {τ : ℂ} (hτ : 0 < τ.im) :
    e8Theta (-1/τ) = τ^4 * e8Theta τ := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simpa [h] using hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let f := e8ThetaSchwartzKernel (-1/τ) hS
  have hp := SchwartzMap.poissonSummation_lattice (L := e8Lattice) f 0
  have hd : SchwartzMap.dualLattice e8Lattice = e8Lattice := e8Lattice_selfDual
  rw [hd] at hp
  have hf : (fun x : E8Ambient => f x) = e8ThetaKernel (-1/τ) :=
    e8ThetaSchwartzKernel_eq (-1/τ) hS
  have hp' : (∑' x : e8Lattice, e8ThetaKernel (-1/τ) x) =
      ∑' x : e8Lattice, 𝓕 (e8ThetaKernel (-1/τ)) x := by
    simpa [e8Lattice_covolume, hf] using hp
  rw [e8Theta_lattice_tsum, e8Theta_lattice_tsum]
  change (∑' x : e8Lattice, e8ThetaKernel (-1/τ) x) =
    τ^4 * ∑' x : e8Lattice, e8ThetaKernel τ x
  rw [hp']
  simp_rw [e8ThetaKernel_fourier_S hτ]
  exact tsum_mul_left

#print axioms e8Theta_transform_S
end SphericalRiesz
