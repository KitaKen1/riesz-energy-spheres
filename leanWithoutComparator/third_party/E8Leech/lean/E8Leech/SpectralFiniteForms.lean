import E8Leech.RealPairCellLimits
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Nonnegative spectral density gives nonnegative finite quadratic forms

The positive exponent is Mathlib's inverse Fourier convention. A finite
weighted difference-kernel form is the integral of the density times a squared
finite character sum. This supplies the easy inverse-Fourier direction without
an abstract Bochner representation, general LCA duality or a new moment axiom.
It does not supply the sharp stationary zero-frequency lower bound.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ComplexConjugate
open scoped ENNReal Classical RealInnerProductSpace FourierTransform

def spectralPhase {d : ℕ} (ξ x : Ambient d) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)

@[simp] theorem spectralPhase_zero {d : ℕ} (ξ : Ambient d) : spectralPhase ξ 0 = 1 := by
  simp [spectralPhase]

theorem spectralPhase_sub {d : ℕ} (ξ x y : Ambient d) :
    spectralPhase ξ (x - y) = spectralPhase ξ x * conj (spectralPhase ξ y) := by
  unfold spectralPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

@[simp] theorem spectralPhase_norm {d : ℕ} (ξ x : Ambient d) : ‖spectralPhase ξ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (2 * Real.pi * inner ℝ ξ x)

theorem continuous_spectralPhase_frequency {d : ℕ} (x : Ambient d) :
    Continuous (fun ξ => spectralPhase ξ x) := by
  unfold spectralPhase
  fun_prop

theorem continuous_spectralPhase_point {d : ℕ} (ξ : Ambient d) :
    Continuous (spectralPhase ξ) := by
  unfold spectralPhase
  fun_prop

theorem integrable_spectral_term {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) (x : Ambient d) :
    Integrable (fun ξ => (g ξ : ℂ) * spectralPhase ξ x) ν :=
  hg.ofReal.mul_bdd (continuous_spectralPhase_frequency x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => (spectralPhase_norm ξ x).le)

def inverseSpectralKernel {d : ℕ} (ν : Measure (Ambient d)) (g : Ambient d → ℝ)
    (x : Ambient d) : ℂ :=
  ∫ ξ, (g ξ : ℂ) * spectralPhase ξ x ∂ν

/-- The convention bridge uses the actual pinned Mathlib inverse transform. -/
theorem inverseSpectralKernel_eq_fourierInv {d : ℕ} (g : Ambient d → ℝ) (x : Ambient d) :
    inverseSpectralKernel volume g x = 𝓕⁻ (fun ξ => (g ξ : ℂ)) x := by
  rw [Real.fourierInv_eq']
  simp only [inverseSpectralKernel, spectralPhase, smul_eq_mul, mul_comm]

theorem continuous_inverseSpectralKernel {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) : Continuous (inverseSpectralKernel ν g) := by
  unfold inverseSpectralKernel
  apply continuous_of_dominated (bound := fun ξ => ‖g ξ‖)
  · intro x
    exact (integrable_spectral_term ν g hg x).aestronglyMeasurable
  · intro x
    filter_upwards with ξ
    simp only [norm_mul, spectralPhase_norm, mul_one, Complex.norm_real, le_refl]
  · exact hg.norm
  · filter_upwards with ξ
    exact continuous_const.mul (continuous_spectralPhase_point ξ)

@[simp] theorem inverseSpectralKernel_zero {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) : inverseSpectralKernel ν g 0 = (∫ ξ, g ξ ∂ν : ℝ) := by
  simp only [inverseSpectralKernel, spectralPhase_zero, mul_one]
  exact integral_complex_ofReal

/-- Finite algebra, before performing any integral. -/
theorem finite_spectral_square_identity {d : ℕ} {ι : Type*} (S : Finset ι)
    (x : ι → Ambient d) (coeff : ι → ℂ) (ξ : Ambient d) :
    (∑ i ∈ S, ∑ j ∈ S, coeff i * conj (coeff j) * spectralPhase ξ (x i - x j)) =
      (Complex.normSq (∑ i ∈ S, coeff i * spectralPhase ξ (x i)) : ℂ) := by
  calc
    _ = (∑ i ∈ S, coeff i * spectralPhase ξ (x i)) *
        (∑ j ∈ S, conj (coeff j * spectralPhase ξ (x j))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [spectralPhase_sub, map_mul]
      ring
    _ = _ := by rw [← map_sum, Complex.mul_conj]

/-- Each term is integrable, so the finite interchange is genuine. -/
theorem finite_spectral_quadratic_eq_integral_normSq {d : ℕ} {ι : Type*}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (S : Finset ι) (x : ι → Ambient d) (coeff : ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S, coeff i * conj (coeff j) * inverseSpectralKernel ν g (x i - x j)) =
      (∫ ξ, g ξ * Complex.normSq (∑ i ∈ S, coeff i * spectralPhase ξ (x i)) ∂ν : ℝ) := by
  have hint (i j : ι) : Integrable (fun ξ =>
      coeff i * conj (coeff j) * ((g ξ : ℂ) * spectralPhase ξ (x i - x j))) ν :=
    (integrable_spectral_term ν g hg _).const_mul _
  have hsum : (∫ ξ, ∑ i ∈ S, ∑ j ∈ S,
      coeff i * conj (coeff j) * ((g ξ : ℂ) * spectralPhase ξ (x i - x j)) ∂ν) =
      ∑ i ∈ S, ∑ j ∈ S, coeff i * conj (coeff j) * inverseSpectralKernel ν g (x i - x j) := by
    rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ => hint i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum S (fun j _ => hint i j)]
    simp only [integral_const_mul, inverseSpectralKernel]
  calc
    _ = ∫ ξ, ∑ i ∈ S, ∑ j ∈ S,
        coeff i * conj (coeff j) * ((g ξ : ℂ) * spectralPhase ξ (x i - x j)) ∂ν := hsum.symm
    _ = ∫ ξ, (g ξ : ℂ) *
        (Complex.normSq (∑ i ∈ S, coeff i * spectralPhase ξ (x i)) : ℂ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← finite_spectral_square_identity S x coeff ξ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [← Complex.ofReal_mul, integral_complex_ofReal]

theorem finite_spectral_quadratic_re_nonneg {d : ℕ} {ι : Type*}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) (S : Finset ι)
    (x : ι → Ambient d) (coeff : ι → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S,
      coeff i * conj (coeff j) * inverseSpectralKernel ν g (x i - x j)).re := by
  rw [finite_spectral_quadratic_eq_integral_normSq ν g hg S x coeff]
  simp only [Complex.ofReal_re]
  apply integral_nonneg_of_ae
  filter_upwards [hgnonneg] with ξ hξ
  exact mul_nonneg hξ (Complex.normSq_nonneg _)

end E8Leech
