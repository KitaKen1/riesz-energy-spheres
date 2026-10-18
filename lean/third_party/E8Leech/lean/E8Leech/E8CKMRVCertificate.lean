import E8Leech.E8GaussianCertificate
import E8Leech.GaussianSchwartz
import E8Leech.CKMRVCombinedKernels
import E8Leech.CKMRVSchwartz

/-!
# The E8 Gaussian certificate from the CKMRV data (Lemma 6.2 wiring)

For `α > 0` put `y = α/π`. The certificate function is `f = e^{−α|·|²} + φ`, where `φ` is the
Schwartz function of `4 sin²(π|x|²/2) ∫₀^∞ 𝒦(iy, it) e^{−π|x|²t} dt` (`CKMRVSchwartz`). Three
analytic inputs remain:
* the combined kernels are real on the imaginary axis;
* `𝒦̂ ≥ 0` on the imaginary axis (CKMRV (6.4)(1), computer-assisted);
* the Fourier identity (**): `φ̂ + 𝓕(e^{−α|·|²}) = 4 sin²(π|ξ|²/2) ∫₀^∞ 𝒦̂(iy, it) e^{−π|ξ|²t} dt`.
From these, `f` is a Gaussian certificate for `E8`. The minorant sign comes from
`𝒦(iy, it) = −y^{−4} 𝒦̂(i/y, it)`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open scoped FourierTransform Real SchwartzMap

/-- **The E8 Gaussian certificate from the CKMRV data.** -/
theorem e8_gaussianSchwartzCertificate_of_ckmrv {α : ℝ} (hα : 0 < α)
    (hreal : ∀ q t : ℝ, 0 < q → 0 < t →
      (ckmrvEightKernel (imagPt q) (imagPt t)).im = 0 ∧
        (ckmrvEightHatKernel (imagPt q) (imagPt t)).im = 0)
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → 0 ≤ (ckmrvEightHatKernel (imagPt q) (imagPt t)).re)
    (φ : 𝓢(Ambient 8, ℂ))
    (hφ : ∀ x : Ambient 8, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
        (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ))
    (hF : ∀ ξ : Ambient 8, ξ ≠ 0 →
      𝓕 (⇑φ) ξ + (((π / α) ^ 4 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
        ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, ckmrvEightHatKernel (imagPt (α / π)) (imagPt t) *
            (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ)) :
    GaussianSchwartzCertificate e8Set α (gaussianSchwartz hα + φ) := by
  set y := α / π with hydef
  have hy0 : 0 < y := div_pos hα Real.pi_pos
  set J : Ambient 8 → ℝ := fun v => ∫ t in Ioi 0,
    (ckmrvEightKernel (imagPt y) (imagPt t)).re * Real.exp (-(π * ‖v‖ ^ 2) * t) with hJdef
  set Jhat : Ambient 8 → ℝ := fun ξ => ∫ t in Ioi 0,
    (ckmrvEightHatKernel (imagPt y) (imagPt t)).re * Real.exp (-(π * ‖ξ‖ ^ 2) * t) with hJhatdef
  have hKint : ∀ v : Ambient 8, ∫ t in Ioi 0, ckmrvEightKernel (imagPt y) (imagPt t) *
      (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ) = (J v : ℂ) := by
    intro v
    simp only [hJdef]
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have him := (hreal y t hy0 ht).1
    conv_lhs => rw [← Complex.re_add_im (ckmrvEightKernel (imagPt y) (imagPt t)), him]
    push_cast
    ring
  have hKhat : ∀ ξ : Ambient 8, ∫ t in Ioi 0, ckmrvEightHatKernel (imagPt y) (imagPt t) *
      (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ) = (Jhat ξ : ℂ) := by
    intro ξ
    simp only [hJhatdef]
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have him := (hreal y t hy0 ht).2
    conv_lhs => rw [← Complex.re_add_im (ckmrvEightHatKernel (imagPt y) (imagPt t)), him]
    push_cast
    ring
  have hJ : ∀ v : Ambient 8, v ≠ 0 → J v ≤ 0 := by
    intro v _
    refine setIntegral_nonpos measurableSet_Ioi fun t ht => ?_
    have hre : (ckmrvEightKernel (imagPt y) (imagPt t)).re =
        -(y ^ 4)⁻¹ * (ckmrvEightHatKernel (imagPt y⁻¹) (imagPt t)).re := by
      rw [ckmrvEightKernel_imagPt hy0,
        show -((y : ℂ) ^ 4)⁻¹ = ((-(y ^ 4)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have hp := hpos y⁻¹ t (inv_pos.mpr hy0) ht
    have hy4 : 0 < (y ^ 4)⁻¹ := by positivity
    have h1 : -(y ^ 4)⁻¹ * (ckmrvEightHatKernel (imagPt y⁻¹) (imagPt t)).re ≤ 0 := by nlinarith
    rw [hre]
    exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.exp_pos _).le
  have hJhat : ∀ ξ : Ambient 8, ξ ≠ 0 → 0 ≤ Jhat ξ := fun ξ _ =>
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (hpos y t hy0 ht) (Real.exp_pos _).le
  have hcoe : (⇑(gaussianSchwartz (d := 8) hα + φ) : Ambient 8 → ℂ) =
      fun v => gaussianSchwartz (d := 8) hα v + φ v := by
    funext v
    rfl
  have hf : ∀ v : Ambient 8, v ≠ 0 → (gaussianSchwartz (d := 8) hα + φ) v =
      ((gaussianKernel α v + 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * J v : ℝ) : ℂ) := by
    intro v hv
    rw [show (gaussianSchwartz (d := 8) hα + φ) v = gaussianSchwartz (d := 8) hα v + φ v from rfl,
      gaussianSchwartz_apply, hφ v hv, hKint v]
    push_cast
    ring
  have hfhat : ∀ ξ : Ambient 8, ξ ≠ 0 → 𝓕 (⇑(gaussianSchwartz (d := 8) hα + φ)) ξ =
      ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 * Jhat ξ : ℝ) : ℂ) := by
    intro ξ hξ
    have hadd : 𝓕 (⇑(gaussianSchwartz (d := 8) hα + φ)) ξ =
        𝓕 (⇑(gaussianSchwartz (d := 8) hα)) ξ + 𝓕 (⇑φ) ξ := by
      rw [hcoe]
      simp only [Real.fourier_eq]
      rw [← integral_add ((Real.fourierIntegral_convergent_iff ξ).mpr
          (gaussianSchwartz (d := 8) hα).integrable)
          ((Real.fourierIntegral_convergent_iff ξ).mpr φ.integrable)]
      congr 1
      ext v
      rw [smul_add]
    rw [hadd, fourier_gaussianSchwartz_eight hα, add_comm, hF ξ hξ, hKhat ξ]
    push_cast
    ring
  exact e8_gaussianSchwartzCertificate_of_sin_sq (gaussianSchwartz (d := 8) hα + φ) hα J Jhat hf hJ hfhat
    hJhat

/-- The Schwartz function of `4 sin²(π|x|²/2) ∫₀^∞ 𝒦(iβ, it) e^{−π|x|²t} dt` on the axis (`β ≠ 1`),
`𝒦 = (K₊ + K₋)/2`. -/
theorem exists_schwartz_ckmrvEightKernel_axis (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, x ≠ 0 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨φp, hφp⟩ := exists_schwartz_ckmrvEightPlus_axis F hβ hβ1
  obtain ⟨φm, hφm⟩ := exists_schwartz_ckmrvEightMinus_axis F hβ hβ1
  refine ⟨(1 / 2 : ℂ) • (φp + φm), fun x hx => ?_⟩
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hip := integrableOn_ckmrvEightPlusKernel_laplace_imagAxis hβ hβ1 hr
  have him := integrableOn_ckmrvEightMinusKernel_laplace_imagAxis hβ hβ1 hr
  have hsum : ∫ t in Ioi 0, ckmrvEightKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) = (1 / 2 : ℂ) *
        ((∫ t in Ioi 0, ckmrvEightPlusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) +
        ∫ t in Ioi 0, ckmrvEightMinusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) := by
    rw [← integral_add hip him, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [ckmrvEightKernel]
    ring
  rw [show ((1 / 2 : ℂ) • (φp + φm)) x = (1 / 2 : ℂ) * (φp x + φm x) from rfl, hφp x hx,
    hφm x hx, hsum]
  ring

/-- **E8 certificates from the CKMRV kernel facts.** For `α > 0`, `α ≠ π`, there is a Schwartz
function `φ` (the `𝒦`-part on the axis) such that the identity (**) for `φ` makes
`e^{−α|·|²} + φ` a Gaussian certificate for `E8`, given realness and (6.4)(1). -/
theorem e8_exists_gaussianSchwartzCertificate_of_ckmrv {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hreal : ∀ q t : ℝ, 0 < q → 0 < t →
      (ckmrvEightKernel (imagPt q) (imagPt t)).im = 0 ∧
        (ckmrvEightHatKernel (imagPt q) (imagPt t)).im = 0)
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → 0 ≤ (ckmrvEightHatKernel (imagPt q) (imagPt t)).re) :
    ∃ φ : 𝓢(Ambient 8, ℂ),
      (∀ x : Ambient 8, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) ∧
      ((∀ ξ : Ambient 8, ξ ≠ 0 →
        𝓕 (⇑φ) ξ + (((π / α) ^ 4 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
          ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
            ∫ t in Ioi 0, ckmrvEightHatKernel (imagPt (α / π)) (imagPt t) *
              (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ)) →
        GaussianSchwartzCertificate e8Set α (gaussianSchwartz hα + φ)) := by
  have hβ : 0 < α / π := div_pos hα Real.pi_pos
  have hβ1 : α / π ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)
  obtain ⟨φ, hφ⟩ := exists_schwartz_ckmrvEightKernel_axis (Ambient 8) hβ hβ1
  exact ⟨φ, hφ, fun hF => e8_gaussianSchwartzCertificate_of_ckmrv hα hreal hpos φ hφ hF⟩

end E8Leech
