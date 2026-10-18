import E8Leech.GaussianParameterNormalization
import Riesz.RadialSchwartz
import SpherePacking.ForMathlib.ExpBounds

/-!
# The Gaussian `e^{−α|x|²}` as a Schwartz map

Built from the radial profile `s ↦ e^{−αs}` with Sphere-Packing-Lean's `RadialSchwartz` bridge.
With `fourier_gaussianKernel_eight_normalized` this gives the Gaussian part of the CKMRV
certificate functions `f = e^{−α|·|²} + 4 sin²(π|·|²/2) ∫ 𝒦 e^{−π|·|²t}`.
-/

noncomputable section

namespace E8Leech

open scoped FourierTransform ContDiff SchwartzMap

/-- The radial profile `s ↦ e^{−αs}`. -/
def gaussianProfile (α : ℝ) (s : ℝ) : ℂ := (Real.exp (-α * s) : ℂ)

theorem contDiff_gaussianProfile (α : ℝ) : ContDiff ℝ ∞ (gaussianProfile α) :=
  Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => Real.exp (-α * s))

theorem gaussianProfile_decay {α : ℝ} (hα : 0 < α) :
    ∀ k n : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianProfile α) x‖ ≤ C := by
  intro k n
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul k hα
  refine ⟨|α| ^ n * C, fun x hx => ?_⟩
  have hcomp : gaussianProfile α = Complex.ofRealLI ∘ fun s => Real.exp (-α * s) := rfl
  have h1 : ‖iteratedFDeriv ℝ n (gaussianProfile α) x‖ =
      ‖iteratedFDeriv ℝ n (fun s => Real.exp (-α * s)) x‖ := by
    rw [hcomp]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => Real.exp (-α * s)).contDiffAt
      (by exact_mod_cast le_top)
  have h2 : ‖iteratedFDeriv ℝ n (fun s => Real.exp (-α * s)) x‖ =
      ‖(-α) ^ n * Real.exp (-α * x)‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg hx, h1, h2]
  calc x ^ k * ‖(-α) ^ n * Real.exp (-α * x)‖
      = |α| ^ n * (x ^ k * Real.exp (-α * x)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (Real.exp_pos _)]
        ring
    _ ≤ |α| ^ n * C := mul_le_mul_of_nonneg_left (hC x hx) (by positivity)

/-- The Gaussian `x ↦ e^{−α|x|²}` as a Schwartz map. -/
def gaussianSchwartz {d : ℕ} {α : ℝ} (hα : 0 < α) : 𝓢(Ambient d, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg (gaussianProfile α)
    (contDiff_gaussianProfile α) (gaussianProfile_decay hα)

theorem gaussianSchwartz_apply {d : ℕ} {α : ℝ} (hα : 0 < α) (x : Ambient d) :
    gaussianSchwartz hα x = (gaussianKernel α x : ℂ) := by
  rw [gaussianSchwartz, RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg_apply]
  rfl

theorem fourier_gaussianSchwartz_eight {α : ℝ} (hα : 0 < α) (ξ : Ambient 8) :
    𝓕 (⇑(gaussianSchwartz (d := 8) hα)) ξ =
      (((Real.pi / α) ^ 4 : ℝ) : ℂ) * (gaussianKernel (Real.pi ^ 2 / α) ξ : ℂ) := by
  have h : (⇑(gaussianSchwartz (d := 8) hα)) = fun x : Ambient 8 => (gaussianKernel α x : ℂ) :=
    funext (gaussianSchwartz_apply hα)
  rw [h, fourier_gaussianKernel_eight_normalized hα]

theorem fourier_gaussianSchwartz_twentyFour {α : ℝ} (hα : 0 < α) (ξ : Ambient 24) :
    𝓕 (⇑(gaussianSchwartz (d := 24) hα)) ξ =
      (((Real.pi / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (Real.pi ^ 2 / α) ξ : ℂ) := by
  have h : (⇑(gaussianSchwartz (d := 24) hα)) = fun x : Ambient 24 => (gaussianKernel α x : ℂ) :=
    funext (gaussianSchwartz_apply hα)
  rw [h, fourier_gaussianKernel_twentyFour_normalized hα]

end E8Leech
