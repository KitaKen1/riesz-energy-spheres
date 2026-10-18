import E8Leech.CKMRVFourier
import E8Leech.LeechAxisRadialProfile

/-!
# The Fourier transform of the Leech profile functions

The Schwartz function `φ(x) = P_s(π|x|²)` of `LeechAxisRadialProfile` is, for a cut `p > 0`,
`φ = φ_A + φ_B` with

`φ_A(x) = 4 sin²(π|x|²/2) ∫₀^∞ g°(t) e^{−π|x|²t} dt`, `g° = K_s` on `(0, p]`, `K_s − f` on `(p, ∞)`,
`φ_B(x) = sinc²((b − 2π)/2) e^{−(b − 2π)p} (A + (B + pA)(b − 2π))`, `b = π|x|²`,

where `f(t) = e^{2πt}(A t + B)` is the growing part of the cusp profile
(`leechAxis_radialProfile_truncated`). The kernel `g°` is integrable against `t⁻¹²`, so the Fourier
transform of `φ_A` is a `t`-integral of Fourier transforms of Gaussians as in dimension eight
(`fourier_sin_sq_laplace_meas`, the statement of `fourier_sin_sq_laplace` for a measurable kernel),
and `φ_B` is a superposition of the complex Gaussians `e^{−π(p − is)|x|²}`, `s ∈ [−1, 1]`.

* `fourier_sin_sq_laplace_meas`: the Fubini lemma for a measurable kernel.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ## Fubini for a measurable kernel -/

/-- The Fubini lemma for a measurable kernel `g`, with the integrability of the `t`-integrand. -/
theorem fourier_sin_sq_laplace_meas_full [Nontrivial V] {g : ℝ → ℂ} {φ : V → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hint : IntegrableOn (fun t : ℝ => ‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2))
      (Ioi 0))
    (hφ : ∀ v : V, v ≠ 0 → φ v = ((4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ))
    (w : V) :
    IntegrableOn (fun t : ℝ => g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖))
        (Ioi 0) ∧
    𝓕 φ w = ∫ t in Ioi 0, g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) := by
  -- `φ` is the `t`-integral of `g · sinSqGauss` off `0`
  have hae : φ =ᵐ[volume] fun v => ∫ t in Ioi 0, g t * sinSqGauss t ‖v‖ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : V))] with v hv0
    have hv : v ≠ 0 := fun h => hv0 (Set.mem_singleton_iff.mpr h)
    rw [hφ v hv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [sinSqGauss_eq]
    ring
  set F : ℝ → V → ℂ := fubiniIntegrand g w with hFdef
  -- facts for fixed `t > 0`
  have hGint : ∀ t : ℝ, 0 < t → Integrable (fun v : V => sinSqGauss t ‖v‖) := by
    intro t ht
    have hre : ∀ c : ℂ, c.re = t → 0 < ((π : ℂ) * c).re := fun c hc => by
      rw [Complex.re_ofReal_mul, hc]
      exact mul_pos Real.pi_pos ht
    exact (((integrable_gaussian_norm_sq (V := V) (hre _ (Complex.ofReal_re t))).const_mul 2).sub
      (integrable_gaussian_norm_sq (V := V) (hre ((t : ℂ) - I) (by simp)))).sub
      (integrable_gaussian_norm_sq (V := V) (hre ((t : ℂ) + I) (by simp)))
  have hnormF : ∀ t : ℝ, ∀ v : V, ‖F t v‖ = ‖g t‖ * ‖sinSqGauss t ‖v‖‖ := by
    intro t v
    simp only [hFdef, fubiniIntegrand, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hFint : ∀ t : ℝ, 0 < t → Integrable (fun v : V => F t v) := by
    intro t ht
    have h1 := continuous_sinSqGauss_norm (V := V) t
    have h2 : Continuous fun v : V => ⟪v, w⟫ := continuous_id.inner continuous_const
    have hc : Continuous fun v : V => F t v := by
      simp only [hFdef, fubiniIntegrand]
      fun_prop
    exact ((hGint t ht).norm.const_mul ‖g t‖).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun v => le_of_eq (hnormF t v))
  have hinner : ∀ t : ℝ, 0 < t → ∫ v, F t v = g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) := by
    intro t ht
    rw [← fourier_sinSqGauss ht w, Real.fourier_eq', ← integral_const_mul]
    congr 1
    ext v
    simp only [hFdef, fubiniIntegrand, smul_eq_mul]
    ring
  have hbound : ∀ t : ℝ, 0 < t → ∫ v, ‖F t v‖ ≤
      4 * (‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) := by
    intro t ht
    have hb : 0 < π * t := mul_pos Real.pi_pos ht
    have hreal : Integrable (fun v : V => Real.exp (-(π * t) * ‖v‖ ^ 2)) := by
      have h := integrable_gaussian_norm_sq (V := V) (b := ((π * t : ℝ) : ℂ)) (by simpa using hb)
      have e : (fun v : V => cexp (-((π * t : ℝ) : ℂ) * ‖v‖ ^ 2)) =
          fun v => ((Real.exp (-(π * t) * ‖v‖ ^ 2) : ℝ) : ℂ) := by
        ext v
        simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
      rw [e] at h
      exact h.re
    calc ∫ v, ‖F t v‖ ≤ ∫ v, ‖g t‖ * (4 * Real.exp (-(π * t) * ‖v‖ ^ 2)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
            ((hreal.const_mul 4).const_mul _) (Eventually.of_forall fun v => ?_)
          show ‖F t v‖ ≤ ‖g t‖ * (4 * Real.exp (-(π * t) * ‖v‖ ^ 2))
          rw [hnormF]
          exact mul_le_mul_of_nonneg_left (norm_sinSqGauss_le t ‖v‖) (norm_nonneg _)
      _ = 4 * (‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) := by
          rw [integral_const_mul, integral_const_mul,
            GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
          ring
  -- Fubini
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure V)) := by
    have h1 := continuous_sinSqGauss_prod (V := V)
    have h2 : AEStronglyMeasurable (fun p : ℝ × V => g p.1)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure V)) :=
      hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h3 : Continuous fun p : ℝ × V => ⟪p.2, w⟫ := continuous_snd.inner continuous_const
    have h4 : Continuous fun p : ℝ × V => cexp (((-2 * π * ⟪p.2, w⟫ : ℝ) : ℂ) * I) := by
      fun_prop
    exact h4.aestronglyMeasurable.mul (h2.mul h1.aestronglyMeasurable)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure V)) := by
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hFint t ht)
    · refine Integrable.mono' (hint.const_mul 4) hmeas.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      exact hbound t ht
  refine ⟨hprod.integral_prod_left.congr
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hinner t ht)), ?_⟩
  rw [Real.fourier_congr_ae hae w, Real.fourier_eq']
  calc ∫ v, cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) •
        (fun v => ∫ t in Ioi 0, g t * sinSqGauss t ‖v‖) v
      = ∫ v, ∫ t in Ioi 0, F t v := by
        congr 1
        ext v
        simp only [smul_eq_mul, hFdef, fubiniIntegrand]
        rw [← integral_const_mul]
    _ = ∫ t in Ioi 0, ∫ v, F t v := (integral_integral_swap hprod).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht => hinner t ht

/-- **The Fourier transform of `4 sin²(π|v|²/2) ∫₀^∞ g(t) e^{−π|v|²t} dt` is a `t`-integral of
Fourier transforms of Gaussians**, for a measurable kernel `g`. -/
theorem fourier_sin_sq_laplace_meas [Nontrivial V] {g : ℝ → ℂ} {φ : V → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hint : IntegrableOn (fun t : ℝ => ‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2))
      (Ioi 0))
    (hφ : ∀ v : V, v ≠ 0 → φ v = ((4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ))
    (w : V) :
    𝓕 φ w = ∫ t in Ioi 0, g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) :=
  (fourier_sin_sq_laplace_meas_full hg hint hφ w).2

/-! ## The explicit term as a superposition of exponentials -/

/-- `∫₀¹ 2(1 − s) cos(es) ds = sinc²(e/2)`. -/
theorem integral_two_mul_one_sub_mul_cos (e : ℝ) :
    ∫ s in (0 : ℝ)..1, 2 * (1 - s) * Real.cos (e * s) = Real.sinc (e / 2) ^ 2 := by
  by_cases he : e = 0
  · subst he
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => 2 * s - s ^ 2)
        (2 * (1 - s) * Real.cos (0 * s)) s := by
      intro s _
      have h := ((hasDerivAt_id' s).const_mul 2).sub ((hasDerivAt_id' s).pow 2)
      refine h.congr_deriv ?_
      rw [zero_mul, Real.cos_zero]
      norm_num
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  · have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s : ℝ => 2 * ((1 - s) * Real.sin (e * s) / e - Real.cos (e * s) / e ^ 2))
        (2 * (1 - s) * Real.cos (e * s)) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => Real.sin (e * s)) (Real.cos (e * s) * e) s := by
        simpa using ((hasDerivAt_id' s).const_mul e).sin
      have h2 : HasDerivAt (fun s : ℝ => Real.cos (e * s)) (-Real.sin (e * s) * e) s := by
        simpa using ((hasDerivAt_id' s).const_mul e).cos
      have h3 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id' s).const_sub 1
      have h := (((h3.mul h1).div_const e).sub (h2.div_const (e ^ 2))).const_mul 2
      refine h.congr_deriv ?_
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      Real.sinc_of_ne_zero (div_ne_zero he two_ne_zero), div_pow, Real.sin_sq_eq_half_sub]
    simp only [sub_self, zero_mul, mul_zero, Real.sin_zero, Real.cos_zero, mul_one, sub_zero,
      zero_div]
    rw [show 2 * (e / 2) = e by ring]
    field_simp
    ring

/-- `∫₀¹ 2 sin(es) ds = e sinc²(e/2)`. -/
theorem integral_two_mul_sin (e : ℝ) :
    ∫ s in (0 : ℝ)..1, 2 * Real.sin (e * s) = e * Real.sinc (e / 2) ^ 2 := by
  by_cases he : e = 0
  · subst he
    simp
  · have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s : ℝ => -(2 * Real.cos (e * s) / e)) (2 * Real.sin (e * s)) s := by
      intro s _
      have h2 : HasDerivAt (fun s : ℝ => Real.cos (e * s)) (-Real.sin (e * s) * e) s := by
        simpa using ((hasDerivAt_id' s).const_mul e).cos
      have h := (((h2.const_mul 2).div_const e)).neg
      refine h.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      Real.sinc_of_ne_zero (div_ne_zero he two_ne_zero), div_pow, Real.sin_sq_eq_half_sub]
    simp only [mul_one, mul_zero, Real.cos_zero]
    rw [show 2 * (e / 2) = e by ring]
    field_simp
    ring

/-- **The explicit term of the truncated profile as a superposition of the exponentials
`e^{−e(p ∓ is)}`, `s ∈ [0, 1]`.** -/
theorem explicit_term_superposition (A c : ℂ) (e p : ℝ) :
    ((Real.sinc (e / 2) ^ 2 * Real.exp (-e * p) : ℝ) : ℂ) * (A + c * (e : ℂ)) =
      ∫ s in (0 : ℝ)..1,
        ((A * ((1 - s : ℝ) : ℂ) - I * c) * cexp (-(e : ℂ) * ((p : ℂ) - (s : ℂ) * I)) +
          (A * ((1 - s : ℝ) : ℂ) + I * c) * cexp (-(e : ℂ) * ((p : ℂ) + (s : ℂ) * I))) := by
  have hpt : ∀ s : ℝ,
      (A * ((1 - s : ℝ) : ℂ) - I * c) * cexp (-(e : ℂ) * ((p : ℂ) - (s : ℂ) * I)) +
        (A * ((1 - s : ℝ) : ℂ) + I * c) * cexp (-(e : ℂ) * ((p : ℂ) + (s : ℂ) * I)) =
      ((Real.exp (-e * p) : ℝ) : ℂ) * (A * ((2 * (1 - s) * Real.cos (e * s) : ℝ) : ℂ) +
        c * ((2 * Real.sin (e * s) : ℝ) : ℂ)) := by
    intro s
    have h1 : cexp (-(e : ℂ) * ((p : ℂ) - (s : ℂ) * I)) =
        ((Real.exp (-e * p) : ℝ) : ℂ) *
          (((Real.cos (e * s) : ℝ) : ℂ) + ((Real.sin (e * s) : ℝ) : ℂ) * I) := by
      rw [show -(e : ℂ) * ((p : ℂ) - (s : ℂ) * I) = ((-e * p : ℝ) : ℂ) + ((e * s : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h2 : cexp (-(e : ℂ) * ((p : ℂ) + (s : ℂ) * I)) =
        ((Real.exp (-e * p) : ℝ) : ℂ) *
          (((Real.cos (e * s) : ℝ) : ℂ) - ((Real.sin (e * s) : ℝ) : ℂ) * I) := by
      rw [show -(e : ℂ) * ((p : ℂ) + (s : ℂ) * I) = ((-e * p : ℝ) : ℂ) + ((-(e * s) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [h1, h2]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
    linear_combination (-(2 * c * ((Real.sin (e * s) : ℝ) : ℂ) * ((Real.exp (-e * p) : ℝ) : ℂ))) *
      Complex.I_sq
  rw [intervalIntegral.integral_congr (fun s _ => hpt s), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((Continuous.intervalIntegrable (by fun_prop) _ _))
      ((Continuous.intervalIntegrable (by fun_prop) _ _)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_two_mul_one_sub_mul_cos, integral_two_mul_sin]
  push_cast
  ring

/-! ## The Fourier transform of the explicit term -/

/-- The explicit term of the truncated profile:
`sinc²((b − 2π)/2) e^{−(b − 2π)p} (A + (B + pA)(b − 2π))`. -/
def explicitProfileTerm (A B : ℂ) (p b : ℝ) : ℂ :=
  ((Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * p) : ℝ) : ℂ) *
    (A + (B + p * A) * ((b - 2 * π : ℝ) : ℂ))

/-- The weight of the complex Gaussian `e^{−π(p − is)|x|²}` in the explicit term. -/
def explicitWeightMinus (A B : ℂ) (p s : ℝ) : ℂ :=
  (A * ((1 - s : ℝ) : ℂ) - I * (B + p * A)) * cexp (2 * π * ((p : ℂ) - (s : ℂ) * I))

/-- The weight of the complex Gaussian `e^{−π(p + is)|x|²}` in the explicit term. -/
def explicitWeightPlus (A B : ℂ) (p s : ℝ) : ℂ :=
  (A * ((1 - s : ℝ) : ℂ) + I * (B + p * A)) * cexp (2 * π * ((p : ℂ) + (s : ℂ) * I))

/-- The explicit term at `b = πr²` is a superposition of the complex Gaussians
`e^{−π(p ∓ is)r²}`, `s ∈ [0, 1]`. -/
theorem explicitProfileTerm_eq_integral (A B : ℂ) (p r : ℝ) :
    explicitProfileTerm A B p (π * r ^ 2) =
      ∫ s in (0 : ℝ)..1,
        (explicitWeightMinus A B p s * cexp (-(π * ((p : ℂ) - (s : ℂ) * I)) * (r : ℂ) ^ 2) +
          explicitWeightPlus A B p s * cexp (-(π * ((p : ℂ) + (s : ℂ) * I)) * (r : ℂ) ^ 2)) := by
  rw [explicitProfileTerm, explicit_term_superposition A (B + p * A) (π * r ^ 2 - 2 * π) p]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hM : cexp (-((π * r ^ 2 - 2 * π : ℝ) : ℂ) * ((p : ℂ) - (s : ℂ) * I)) =
      cexp (2 * π * ((p : ℂ) - (s : ℂ) * I)) *
        cexp (-(π * ((p : ℂ) - (s : ℂ) * I)) * (r : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hP : cexp (-((π * r ^ 2 - 2 * π : ℝ) : ℂ) * ((p : ℂ) + (s : ℂ) * I)) =
      cexp (2 * π * ((p : ℂ) + (s : ℂ) * I)) *
        cexp (-(π * ((p : ℂ) + (s : ℂ) * I)) * (r : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [explicitWeightMinus, explicitWeightPlus]
  rw [hM, hP]
  ring

theorem norm_explicitWeightMinus_le (A B : ℂ) (p s : ℝ) :
    ‖explicitWeightMinus A B p s‖ ≤ (‖A‖ * (1 + |s|) + ‖B + p * A‖) * Real.exp (2 * π * p) := by
  have h1 : ‖cexp (2 * π * ((p : ℂ) - (s : ℂ) * I))‖ = Real.exp (2 * π * p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖A * ((1 - s : ℝ) : ℂ) - I * (B + p * A)‖ ≤ ‖A‖ * (1 + |s|) + ‖B + p * A‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : |1 - s| ≤ 1 + |s| := (abs_sub _ _).trans (by simp)
    exact add_le_add (mul_le_mul_of_nonneg_left h3 (norm_nonneg A)) le_rfl
  rw [explicitWeightMinus, norm_mul, h1]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

theorem norm_explicitWeightPlus_le (A B : ℂ) (p s : ℝ) :
    ‖explicitWeightPlus A B p s‖ ≤ (‖A‖ * (1 + |s|) + ‖B + p * A‖) * Real.exp (2 * π * p) := by
  have h1 : ‖cexp (2 * π * ((p : ℂ) + (s : ℂ) * I))‖ = Real.exp (2 * π * p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖A * ((1 - s : ℝ) : ℂ) + I * (B + p * A)‖ ≤ ‖A‖ * (1 + |s|) + ‖B + p * A‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : |1 - s| ≤ 1 + |s| := (abs_sub _ _).trans (by simp)
    exact add_le_add (mul_le_mul_of_nonneg_left h3 (norm_nonneg A)) le_rfl
  rw [explicitWeightPlus, norm_mul, h1]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

theorem norm_cexp_gauss (a : ℂ) (r : ℝ) :
    ‖cexp (-(π * a) * (r : ℂ) ^ 2)‖ = Real.exp (-(π * a.re) * r ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have h : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.re_mul_ofReal]
  simp

/-- **The Fourier transform of the explicit term** is the same superposition of the Fourier
transforms of the complex Gaussians. -/
theorem fourier_explicitProfileTerm (A B : ℂ) {p : ℝ} (hp : 0 < p) (w : V) :
    𝓕 (fun v : V => explicitProfileTerm A B p (π * ‖v‖ ^ 2)) w =
      ∫ s in (0 : ℝ)..1,
        (explicitWeightMinus A B p s *
            gaussHat (Module.finrank ℝ V) ((p : ℂ) - (s : ℂ) * I) ‖w‖ +
          explicitWeightPlus A B p s *
            gaussHat (Module.finrank ℝ V) ((p : ℂ) + (s : ℂ) * I) ‖w‖) := by
  set F : ℝ → V → ℂ := fun s v => cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) *
    (explicitWeightMinus A B p s * cexp (-(π * ((p : ℂ) - (s : ℂ) * I)) * (‖v‖ : ℂ) ^ 2) +
      explicitWeightPlus A B p s * cexp (-(π * ((p : ℂ) + (s : ℂ) * I)) * (‖v‖ : ℂ) ^ 2))
    with hF
  have hreM : ∀ s : ℝ, ((p : ℂ) - (s : ℂ) * I).re = p := fun s => by simp
  have hreP : ∀ s : ℝ, ((p : ℂ) + (s : ℂ) * I).re = p := fun s => by simp
  have hinnerC : Continuous fun v : V => ⟪v, w⟫ := continuous_id.inner continuous_const
  -- one complex Gaussian
  have hi : ∀ c : ℂ, c.re = p → Integrable (fun v : V =>
      cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) * cexp (-(π * c) * (‖v‖ : ℂ) ^ 2)) := by
    intro c hc
    have hb : 0 < ((π : ℂ) * c).re := by
      rw [Complex.re_ofReal_mul, hc]
      exact mul_pos Real.pi_pos hp
    have hcont : Continuous fun v : V =>
        cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) * cexp (-(π * c) * (‖v‖ : ℂ) ^ 2) := by
      fun_prop
    refine (integrable_gaussian_norm_sq (V := V) hb).norm.mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hFou : ∀ c : ℂ, c.re = p → ∫ v : V,
      cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) * cexp (-(π * c) * (‖v‖ : ℂ) ^ 2) =
        gaussHat (Module.finrank ℝ V) c ‖w‖ := fun c hc => by
    rw [← fourier_gauss (by rw [hc]; exact hp) w, Real.fourier_eq']
    rfl
  have hinner : ∀ s : ℝ, ∫ v, F s v =
      explicitWeightMinus A B p s * gaussHat (Module.finrank ℝ V) ((p : ℂ) - (s : ℂ) * I) ‖w‖ +
        explicitWeightPlus A B p s *
          gaussHat (Module.finrank ℝ V) ((p : ℂ) + (s : ℂ) * I) ‖w‖ := by
    intro s
    rw [← hFou _ (hreM s), ← hFou _ (hreP s), ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hi _ (hreM s)).const_mul _) ((hi _ (hreP s)).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF]
    ring
  -- the Gaussian bound
  have hreal : Integrable (fun v : V => Real.exp (-(π * p) * ‖v‖ ^ 2)) := by
    have hb : 0 < π * p := mul_pos Real.pi_pos hp
    have h := integrable_gaussian_norm_sq (V := V) (b := ((π * p : ℝ) : ℂ)) (by simpa using hb)
    have e : (fun v : V => cexp (-((π * p : ℝ) : ℂ) * ‖v‖ ^ 2)) =
        fun v => ((Real.exp (-(π * p) * ‖v‖ ^ 2) : ℝ) : ℂ) := by
      ext v
      simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
    rw [e] at h
    exact h.re
  have hnorm : ∀ s : ℝ, ∀ v : V, ‖F s v‖ ≤
      2 * ((‖A‖ * (1 + |s|) + ‖B + p * A‖) * Real.exp (2 * π * p)) *
        Real.exp (-(π * p) * ‖v‖ ^ 2) := by
    intro s v
    simp only [hF]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_cexp_gauss, norm_cexp_gauss, hreM, hreP]
    have h1 := norm_explicitWeightMinus_le A B p s
    have h2 := norm_explicitWeightPlus_le A B p s
    have h3 := (Real.exp_pos (-(π * p) * ‖v‖ ^ 2)).le
    nlinarith [mul_le_mul_of_nonneg_right h1 h3, mul_le_mul_of_nonneg_right h2 h3]
  -- Fubini
  have hcontF : Continuous (Function.uncurry F) := by
    have h3 : Continuous fun q : ℝ × V => ⟪q.2, w⟫ := continuous_snd.inner continuous_const
    have h4 : Continuous fun q : ℝ × V => (‖q.2‖ : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd.norm
    simp only [hF, explicitWeightMinus, explicitWeightPlus]
    fun_prop
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure V)) := by
    have hc : Integrable (fun s : ℝ =>
        2 * ((‖A‖ * (1 + |s|) + ‖B + p * A‖) * Real.exp (2 * π * p)))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    exact (Integrable.mul_prod hc hreal).mono' hcontF.aestronglyMeasurable
      (Eventually.of_forall fun q => hnorm q.1 q.2)
  rw [Real.fourier_eq', intervalIntegral.integral_of_le zero_le_one]
  calc ∫ v, cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) •
        (fun v : V => explicitProfileTerm A B p (π * ‖v‖ ^ 2)) v
      = ∫ v, ∫ s in Ioc (0 : ℝ) 1, F s v := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        show cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) • explicitProfileTerm A B p (π * ‖v‖ ^ 2) =
          ∫ s in Ioc (0 : ℝ) 1, F s v
        rw [explicitProfileTerm_eq_integral, intervalIntegral.integral_of_le zero_le_one,
          smul_eq_mul, ← integral_const_mul]
    _ = ∫ s in Ioc (0 : ℝ) 1, ∫ v, F s v := (integral_integral_swap hprod).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioc fun s _ => hinner s

/-! ## Integrability of the explicit term -/

theorem integrable_rexp_neg_mul_norm_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : V => Real.exp (-c * ‖v‖ ^ 2)) := by
  have h := integrable_gaussian_norm_sq (V := V) (b := (c : ℂ)) (by simpa using hc)
  have e : (fun v : V => cexp (-(c : ℂ) * ‖v‖ ^ 2)) =
      fun v => ((Real.exp (-c * ‖v‖ ^ 2) : ℝ) : ℂ) := by
    ext v
    simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
  rw [e] at h
  exact h.re

theorem norm_explicitIntegrand_le (A B : ℂ) (p s r : ℝ) :
    ‖explicitWeightMinus A B p s * cexp (-(π * ((p : ℂ) - (s : ℂ) * I)) * (r : ℂ) ^ 2) +
        explicitWeightPlus A B p s * cexp (-(π * ((p : ℂ) + (s : ℂ) * I)) * (r : ℂ) ^ 2)‖ ≤
      2 * ((‖A‖ * (1 + |s|) + ‖B + p * A‖) * Real.exp (2 * π * p)) *
        Real.exp (-(π * p) * r ^ 2) := by
  have hreM : ((p : ℂ) - (s : ℂ) * I).re = p := by simp
  have hreP : ((p : ℂ) + (s : ℂ) * I).re = p := by simp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_cexp_gauss, norm_cexp_gauss, hreM, hreP]
  have h1 := norm_explicitWeightMinus_le A B p s
  have h2 := norm_explicitWeightPlus_le A B p s
  have h3 := (Real.exp_pos (-(π * p) * r ^ 2)).le
  nlinarith [mul_le_mul_of_nonneg_right h1 h3, mul_le_mul_of_nonneg_right h2 h3]

theorem norm_explicitProfileTerm_le (A B : ℂ) (p r : ℝ) :
    ‖explicitProfileTerm A B p (π * r ^ 2)‖ ≤
      2 * ((‖A‖ * 2 + ‖B + p * A‖) * Real.exp (2 * π * p)) * Real.exp (-(π * p) * r ^ 2) := by
  rw [explicitProfileTerm_eq_integral]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_).trans_eq
    (by rw [sub_zero, abs_one, mul_one])
  rw [uIoc_of_le zero_le_one] at hs
  refine (norm_explicitIntegrand_le A B p s r).trans ?_
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have h3 := (Real.exp_pos (-(π * p) * r ^ 2)).le
  have h4 := (Real.exp_pos (2 * π * p)).le
  have h5 : ‖A‖ * (1 + |s|) ≤ ‖A‖ * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg A)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) h4) zero_le_two) h3

theorem continuous_explicitProfileTerm (A B : ℂ) (p : ℝ) :
    Continuous (explicitProfileTerm A B p) := by
  have h1 : Continuous fun b : ℝ => Real.sinc ((b - 2 * π) / 2) :=
    Real.continuous_sinc.comp (by fun_prop)
  unfold explicitProfileTerm
  fun_prop

theorem integrable_explicitProfileTerm (A B : ℂ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun v : V => explicitProfileTerm A B p (π * ‖v‖ ^ 2)) := by
  have hreal : Integrable (fun v : V => Real.exp (-(π * p) * ‖v‖ ^ 2)) :=
    integrable_rexp_neg_mul_norm_sq (mul_pos Real.pi_pos hp)
  exact (hreal.const_mul (2 * ((‖A‖ * 2 + ‖B + p * A‖) * Real.exp (2 * π * p)))).mono'
    ((continuous_explicitProfileTerm A B p).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun v => norm_explicitProfileTerm_le A B p ‖v‖)

/-- Additivity of the Fourier transform on integrable functions. -/
theorem fourier_add_of_integrable {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) (w : V) :
    𝓕 (fun v => f v + g v) w = 𝓕 f w + 𝓕 g w := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq,
    ← integral_add ((Real.fourierIntegral_convergent_iff w).mpr hf)
      ((Real.fourierIntegral_convergent_iff w).mpr hg)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_add]

/-! ## Cutting a kernel -/

/-- A kernel with a part `f` removed beyond the cut `p`. -/
def truncAt (g f : ℝ → ℂ) (p t : ℝ) : ℂ := g t - (Ioi p).indicator f t

theorem truncAt_of_le (g f : ℝ → ℂ) {p t : ℝ} (h : t ≤ p) : truncAt g f p t = g t := by
  rw [truncAt, indicator_of_notMem (notMem_Ioi.mpr h), sub_zero]

theorem truncAt_of_lt (g f : ℝ → ℂ) {p t : ℝ} (h : p < t) : truncAt g f p t = g t - f t := by
  rw [truncAt, indicator_of_mem (mem_Ioi.mpr h)]

/-- `t ↦ g(min t p)`: equal to `g` on `(0, p]`, continuous on `(0, ∞)` and bounded at `∞`. -/
theorem exists_cut_at {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) {p : ℝ} (hp : 0 < p) :
    ∃ g₁ : ℝ → ℂ, ContinuousOn g₁ (Ioi 0) ∧ (∀ t, t ≤ p → g₁ t = g t) ∧
      g =ᶠ[𝓝[>] (0 : ℝ)] g₁ ∧ g₁ =O[atTop] fun t => t * Real.exp (0 * t) := by
  refine ⟨fun t => g (min t p),
    hg.comp (continuous_id.min continuous_const).continuousOn fun t ht => lt_min ht hp,
    fun t ht => by simp only [min_eq_left ht], ?_, ?_⟩
  · have hmem : Iio p ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp)
    filter_upwards [hmem] with t ht
    simp only [min_eq_left (le_of_lt (mem_Iio.mp ht))]
  · refine IsBigO.of_bound ‖g p‖ ?_
    filter_upwards [eventually_ge_atTop (max p 1)] with t ht
    have htp : p ≤ t := (le_max_left _ _).trans ht
    have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
    simp only [min_eq_right htp, zero_mul, Real.exp_zero, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (g p)]

/-- `‖g(t)‖ t^{−n}` (`n ≥ 3`) is integrable on `(0, p]` when `g = O(e^{−π/t})` at `0`. -/
theorem integrableOn_Ioc_norm_mul_inv_pow {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t)) {n : ℕ} (hn : 3 ≤ n) {p : ℝ}
    (hp : 0 < p) : IntegrableOn (fun t : ℝ => ‖g t‖ * (t ^ n)⁻¹) (Ioc 0 p) := by
  obtain ⟨g₁, hc, heq, hev, hinf⟩ := exists_cut_at hg hp
  refine ((integrableOn_norm_mul_inv_pow hc (hg0.congr' hev EventuallyEq.rfl) hinf hn).mono_set
    Ioc_subset_Ioi_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp only [heq t ht.2]

/-- `g(t) e^{−bt}` (`b > 0`) is integrable on `(0, p]` when `g` is bounded at `0`. -/
theorem integrableOn_Ioc_mul_exp {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg01 : g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ)) {b p : ℝ} (hb : 0 < b) (hp : 0 < p) :
    IntegrableOn (fun t => g t * (Real.exp (-b * t) : ℂ)) (Ioc 0 p) := by
  obtain ⟨g₁, hc, heq, hev, hinf⟩ := exists_cut_at hg hp
  refine ((integrableOn_Ioi_mul_exp_of_isBigO hb hc (hg01.congr' hev EventuallyEq.rfl) hinf).mono_set
    Ioc_subset_Ioi_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp only [heq t ht.2]

/-- `‖h(t)‖ t^{−n}` (`n ≥ 3`) is integrable on `(p, ∞)`, `p > 0`, when `h = O(t)` at `∞`. -/
theorem integrableOn_Ioi_norm_mul_inv_pow {h : ℝ → ℂ} (hh : ContinuousOn h (Ioi 0))
    (hinf : h =O[atTop] fun t => t * Real.exp (0 * t)) {n : ℕ} (hn : 3 ≤ n) {p : ℝ}
    (hp : 0 < p) : IntegrableOn (fun t : ℝ => ‖h t‖ * (t ^ n)⁻¹) (Ioi p) := by
  have hcont : ContinuousOn (fun t : ℝ => ‖h t‖ * (t ^ n)⁻¹) (Ioi 0) :=
    hh.norm.mul ((continuousOn_pow n).inv₀ fun t ht => pow_ne_zero n (ne_of_gt ht))
  have hcontp : ContinuousOn (fun t : ℝ => ‖h t‖ * (t ^ n)⁻¹) (Ici p) :=
    hcont.mono fun t ht => mem_Ioi.mpr (lt_of_lt_of_le hp (mem_Ici.mp ht))
  refine (integrableOn_Ici_iff_integrableAtFilter_atTop.mpr
    ⟨?_, hcontp.locallyIntegrableOn measurableSet_Ici⟩).mono_set Ioi_subset_Ici_self
  have hO : (fun t : ℝ => ‖h t‖ * (t ^ n)⁻¹) =O[atTop] fun t : ℝ => t ^ (-2 : ℝ) := by
    obtain ⟨M, hMpos, hM⟩ := hinf.exists_pos
    refine IsBigO.of_bound M ?_
    filter_upwards [hM.bound, eventually_ge_atTop 1] with t ht ht1
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have htne : t ≠ 0 := htpos.ne'
    rw [zero_mul, Real.exp_zero, mul_one, Real.norm_eq_abs, abs_of_pos htpos] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖h t‖ * (t ^ n)⁻¹),
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
    have h3 : t * (t ^ 3)⁻¹ = (t ^ 2)⁻¹ := by
      rw [show t ^ 3 = t * t ^ 2 by ring, mul_inv, ← mul_assoc, mul_inv_cancel₀ htne, one_mul]
    have h2 : t * (t ^ n)⁻¹ ≤ t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg htpos.le, Real.rpow_two, ← h3]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (pow_pos htpos 3) (pow_le_pow_right₀ ht1 hn)) htpos.le
    calc ‖h t‖ * (t ^ n)⁻¹ ≤ M * t * (t ^ n)⁻¹ :=
          mul_le_mul_of_nonneg_right ht (by positivity)
      _ = M * (t * (t ^ n)⁻¹) := by ring
      _ ≤ M * t ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left h2 hMpos.le
  exact hO.integrableAtFilter
    ⟨Ioi 0, Ioi_mem_atTop 0, hcont.aestronglyMeasurable measurableSet_Ioi⟩
    (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))

end E8Leech
