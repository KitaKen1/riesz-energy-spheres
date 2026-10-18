import FCDefinitions
import Riesz.E8ThetaModular
import Riesz.E8Regularized
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
open UpperHalfPlane ModularForm EisensteinSeries
open scoped ArithmeticFunction.sigma MatrixGroups
namespace RieszSphereFC

def divisorSeries (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (∑ a ∈ Nat.divisors (n + 1), (a : ℝ) ^ k) *
    Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)

def imaginaryPoint (t : ℝ) (ht : 0 < t) : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using ht⟩

theorem eisenstein_imaginary {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    {t : ℝ} (ht : 0 < t) :
    E hk (imaginaryPoint t ht) =
      1 - (2 * (k : ℂ) / (bernoulli k : ℂ)) * (divisorSeries (k - 1) t : ℂ) := by
  rw [q_expansion_bernoulli hk hk2]
  congr 2
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  change (∑' n : ℕ, (ArithmeticFunction.sigma (k - 1) (n + 1) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (imaginaryPoint t ht : ℂ)) ^ ((n + 1 : ℕ) : ℤ)) = _
  unfold divisorSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  have he : Complex.exp (2 * Real.pi * Complex.I * (imaginaryPoint t ht : ℂ)) ^
      ((n + 1 : ℕ) : ℤ) = (Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t) : ℂ) := by
    rw [zpow_natCast, ← Complex.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    dsimp [imaginaryPoint]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [he, Complex.ofReal_mul]
  congr 1
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  rfl

theorem E4_imaginary {t : ℝ} (ht : 0 < t) :
    E₄ (imaginaryPoint t ht) = ((1 + 240 * divisorSeries 3 t : ℝ) : ℂ) := by
  have h := eisenstein_imaginary (k := 4) (by norm_num) ⟨2, rfl⟩ ht
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel] at h
  push_cast
  convert h using 1 <;> ring

theorem E6_imaginary {t : ℝ} (ht : 0 < t) :
    E₆ (imaginaryPoint t ht) = ((1 - 504 * divisorSeries 5 t : ℝ) : ℂ) := by
  have h := eisenstein_imaginary (k := 6) (by norm_num) ⟨3, rfl⟩ ht
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel] at h
  push_cast
  convert h using 1 <;> ring

theorem latticeTheta_eight_complex_eq {t : ℝ} (ht : 0 < t) :
    (latticeTheta 8 t : ℂ) = SphericalRiesz.e8ThetaImag t := by
  rw [SphericalRiesz.e8ThetaImag]
  have h := SphericalRiesz.e8Theta_eq_E4 (imaginaryPoint t ht)
  change SphericalRiesz.e8Theta ((t : ℂ) * Complex.I) = _ at h
  rw [h, E4_imaginary ht]
  rfl

end RieszSphereFC
