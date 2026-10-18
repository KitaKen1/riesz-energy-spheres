import Riesz.SphereGaussianBackground8
import Riesz.FiniteBackground

/-! Actual common lower bound for the Gaussian Mellin/Fatou integrand.
Its future integrable majorant still requires the sphere background decay. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SphericalRiesz

theorem sphereGaussianPair8_diagonal_lower {N : ℕ} (t : ℝ) (X : Configuration N) :
    (N:ℝ) ≤ ∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j) := by
  have h := gaussian_diagonal_lower t (fun i : Fin N => (X i:Ambient9))
  simpa only [kernelPair, one_mul, mul_one, Fintype.card_fin,
    sphereGaussianKernel8_eq_ambient] using h

theorem sphereGaussianPair8_background_lower {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : Configuration N) :
    (N:ℝ)^2*sphereGaussianBackground8 t ≤ ∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j) := by
  have h := sphereGaussianDefect8_nonneg ht (N:ℝ) X
  rw [sphereGaussianDefect8_charge_N ht] at h
  exact sub_nonneg.mp h

theorem sphereGaussianCentered8_common_lower_of_bound {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 ≤ t) (X : Configuration N) (C : ℝ)
    (hbackground : (N:ℝ)*sphereGaussianBackground8 t ≤ C) :
    -min 1 C ≤
      (∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground8 t - 1 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hpair := sphereGaussianPair8_background_lower ht X
  have hdiag := sphereGaussianPair8_diagonal_lower t X
  apply background_subtracted_common_lower
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hNR).mpr
    nlinarith [hpair]
  · exact (le_div_iff₀ hNR).mpr (by simpa using hdiag)
  · exact hbackground

theorem sphereGaussianCentered8_common_lower {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (X : Configuration N) :
    -min 1 ((N:ℝ)*sphereGaussianBackground8 t) ≤
      (∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground8 t - 1 :=
  sphereGaussianCentered8_common_lower_of_bound hN ht X _ le_rfl

end SphericalRiesz
