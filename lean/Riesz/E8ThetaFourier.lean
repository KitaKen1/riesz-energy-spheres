import Riesz.E8ThetaSummable
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Fourier inversion input for the actual rank-eight theta Gaussian

Use the existing multidimensional Gaussian transform. In dimension eight its
complex exponent is the integer 4, so no square-root branch calculation or
new radial Schwartz construction is needed for this Fourier identity.
Poisson summation itself remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace SphericalRiesz

def e8ThetaKernel (τ : ℂ) (x : E8Ambient) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖x‖^2 : ℝ)*τ)

theorem e8ThetaKernel_lattice (τ : ℂ) (x : e8Lattice) :
    e8ThetaKernel τ x = e8LatticeThetaTerm τ x := rfl

theorem e8ThetaKernel_gaussian (τ : ℂ) : e8ThetaKernel τ =
    fun x : E8Ambient => Complex.exp
      (-((Real.pi : ℂ)*(-Complex.I*τ))*(‖x‖ : ℂ)^2) := by
  funext x
  unfold e8ThetaKernel
  congr 1
  push_cast
  ring

theorem e8ThetaKernel_contDiff (τ : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (e8ThetaKernel τ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : E8Ambient => ((‖x‖^2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)
  exact (contDiff_const.mul h |>.mul contDiff_const).cexp

theorem e8ThetaKernel_integrable {τ : ℂ} (hτ : 0 < τ.im) :
    Integrable (e8ThetaKernel τ) := by
  have hb : 0 < ((Real.pi : ℂ)*(-Complex.I*τ)).re := by
    simpa using mul_pos Real.pi_pos hτ
  rw [e8ThetaKernel_gaussian]
  simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E8Ambient) hb 0 0

theorem e8ThetaKernel_fourier_S {τ : ℂ} (hτ : 0 < τ.im) (w : E8Ambient) :
    𝓕 (e8ThetaKernel (-1/τ)) w = τ^4 * e8ThetaKernel τ w := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simpa [h] using hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let b : ℂ := (Real.pi : ℂ)*(-Complex.I*(-1/τ))
  have hb : 0 < b.re := by
    simpa [b] using mul_pos Real.pi_pos hS
  have hπ : (Real.pi : ℂ)/b = τ/Complex.I := by
    dsimp [b]
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((Real.pi : ℂ)/b)^((Module.finrank ℝ E8Ambient : ℂ)/2) = τ^4 := by
    rw [hπ]
    norm_num [finrank_euclideanSpace_fin, div_pow, mul_pow, Complex.I_pow_four]
  have he : -(Real.pi : ℂ)^2*(‖w‖ : ℂ)^2/b =
      (Real.pi : ℂ)*Complex.I*(‖w‖^2 : ℝ)*τ := by
    dsimp [b]
    push_cast
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  rw [e8ThetaKernel_gaussian]
  change 𝓕 (fun x : E8Ambient => Complex.exp (-b*(‖x‖ : ℂ)^2)) w = _
  rw [fourier_gaussian_innerProductSpace hb w, hc, he]
  rfl

#print axioms e8ThetaKernel_lattice
#print axioms e8ThetaKernel_gaussian
#print axioms e8ThetaKernel_contDiff
#print axioms e8ThetaKernel_integrable
#print axioms e8ThetaKernel_fourier_S

end SphericalRiesz
