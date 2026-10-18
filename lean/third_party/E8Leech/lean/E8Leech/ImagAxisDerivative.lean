import SpherePacking.ModularForms.ThetaDerivIdentities
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# Derivatives along the imaginary axis from the normalized derivative

For a holomorphic function `F` on the upper half-plane, `d/dt F(it) = −2π (D F)(it)` with the
normalized derivative `D = (2πi)⁻¹ d/dz`. Ramanujan's identity for `E₂` and the Serre derivative
identities of `H₂ = θ₂⁴`, `H₄ = θ₄⁴` (ported from the sphere packing project) give

`D E₂ = (E₂² − E₄)/12`, `D H₂ = H₂ (E₂ + H₂ + 2H₄)/6`, `D H₄ = H₄ (E₂ − 2H₂ − H₄)/6`.

* `hasDerivAt_ofComplex_I_mul`: the derivative along the axis.
* `E₂_eq_E2`: the `E₂` of the sphere packing project is the `E2` of Mathlib.
* `D_E₂_apply`, `D_H₂_apply`, `D_H₄_apply`: the three identities pointwise.
* `hasDerivAt_E₂_axis`, `hasDerivAt_H₂_axis`, `hasDerivAt_H₄_axis`: the derivatives in `t`.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real Manifold

/-- `d/dt F(it) = −2π (D F)(it)` for a holomorphic function `F` on the upper half-plane. -/
theorem hasDerivAt_ofComplex_I_mul {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => F (ofComplex (I * x))) (-(2 * π) * D F (ofComplex (I * t))) t := by
  have him : 0 < (I * (t : ℂ)).im := by simpa using ht
  have hz : ((ofComplex (I * t) : ℍ) : ℂ) = I * t := by
    rw [ofComplex_apply_of_im_pos him]
  have hc : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hd : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ((ofComplex (I * t) : ℍ) : ℂ))
      ((ofComplex (I * t) : ℍ) : ℂ) :=
    (MDifferentiableAt_DifferentiableAt (hF (ofComplex (I * t)))).hasDerivAt
  have hD : deriv (F ∘ ofComplex) ((ofComplex (I * t) : ℍ) : ℂ) =
      2 * π * I * D F (ofComplex (I * t)) := by
    simp only [D]
    rw [mul_inv_cancel_left₀ hc]
  rw [hD, hz] at hd
  have h := hd.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul I)
  have h3 : HasDerivAt (fun x : ℝ => F (ofComplex (I * x)))
      (2 * π * I * D F (ofComplex (I * t)) * (I * 1)) t := h.comp_ofReal
  have hval : 2 * (π : ℂ) * I * D F (ofComplex (I * t)) * (I * 1) =
      -(2 * π) * D F (ofComplex (I * t)) := by
    linear_combination (2 * (π : ℂ) * D F (ofComplex (I * t))) * I_sq
  rw [hval] at h3
  exact h3

/-- The two normalizations of `E₂` agree: both have the expansion `1 − 24 Σ σ₁(n) qⁿ`. -/
theorem E₂_eq_E2 (z : ℍ) : E₂ z = EisensteinSeries.E2 z := by
  have hr := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  rw [E₂_eq, EisensteinSeries.E2_eq_tsum_cexp, ← tsum_pow_div_one_sub_eq_tsum_sigma hr 1]
  refine congrArg (fun s : ℂ => 1 - 24 * s) (tsum_congr fun n => ?_)
  have h : cexp (2 * π * I * n * z) = cexp (2 * π * I * z) ^ (n : ℕ) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [h, pow_one]

/-- Ramanujan's identity `D E₂ = (E₂² − E₄)/12`, pointwise. -/
theorem D_E₂_apply (z : ℍ) : D E₂ z = 12⁻¹ * (E₂ z * E₂ z - E₄ z) :=
  congrFun ramanujan_E₂ z

/-- `D H₂ = H₂ (E₂ + H₂ + 2H₄)/6`, pointwise. -/
theorem D_H₂_apply (z : ℍ) : D H₂ z = 6⁻¹ * (H₂ z * (E₂ z + H₂ z + 2 * H₄ z)) := by
  have h : D H₂ z - 2 * 12⁻¹ * E₂ z * H₂ z = (1 / 6 : ℂ) * (H₂ z * (H₂ z + 2 * H₄ z)) :=
    congrFun serre_D_two_H₂ z
  linear_combination h

/-- `D H₄ = H₄ (E₂ − 2H₂ − H₄)/6`, pointwise. -/
theorem D_H₄_apply (z : ℍ) : D H₄ z = 6⁻¹ * (H₄ z * (E₂ z - 2 * H₂ z - H₄ z)) := by
  have h : D H₄ z - 2 * 12⁻¹ * E₂ z * H₄ z = (-1 / 6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)) :=
    congrFun serre_D_two_H₄ z
  linear_combination h

/-- `d/dt E₂(it) = −(π/6)(E₂² − E₄)`. -/
theorem hasDerivAt_E₂_axis {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => E₂ (ofComplex (I * x)))
      (-(2 * π) * (12⁻¹ * (E₂ (ofComplex (I * t)) * E₂ (ofComplex (I * t)) -
        E₄ (ofComplex (I * t))))) t := by
  have h := hasDerivAt_ofComplex_I_mul E₂_holo' ht
  rw [D_E₂_apply] at h
  exact h

/-- `d/dt H₂(it) = −(π/3) H₂ (E₂ + H₂ + 2H₄)`. -/
theorem hasDerivAt_H₂_axis {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => H₂ (ofComplex (I * x)))
      (-(2 * π) * (6⁻¹ * (H₂ (ofComplex (I * t)) *
        (E₂ (ofComplex (I * t)) + H₂ (ofComplex (I * t)) + 2 * H₄ (ofComplex (I * t)))))) t := by
  have h := hasDerivAt_ofComplex_I_mul mdifferentiable_H₂ ht
  rw [D_H₂_apply] at h
  exact h

/-- `d/dt H₄(it) = −(π/3) H₄ (E₂ − 2H₂ − H₄)`. -/
theorem hasDerivAt_H₄_axis {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => H₄ (ofComplex (I * x)))
      (-(2 * π) * (6⁻¹ * (H₄ (ofComplex (I * t)) *
        (E₂ (ofComplex (I * t)) - 2 * H₂ (ofComplex (I * t)) - H₄ (ofComplex (I * t)))))) t := by
  have h := hasDerivAt_ofComplex_I_mul mdifferentiable_H₄ ht
  rw [D_H₄_apply] at h
  exact h

/-- The real part of a complex-valued function of a real variable with a real derivative. -/
theorem hasDerivAt_re_of_ofReal {f : ℝ → ℂ} {r t : ℝ} (h : HasDerivAt f (r : ℂ) t) :
    HasDerivAt (fun x => (f x).re) r t := by
  have h2 := reCLM.hasFDerivAt.comp_hasDerivAt t h
  simpa only [Function.comp_def, reCLM_apply, ofReal_re] using h2

end E8Leech
