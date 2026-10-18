import E8Leech.LeechContourAssembly
import E8Leech.LeechCuspShift
import E8Leech.CKMRVContourFinal

/-!
# The contour identity in dimension 24

For `τ = iy` (`y ≠ 1`), `ρ = r² > 2`, `γ(a) = a⁻¹² e^{−πρ/a}`, `f(t) = e^{2πt}(A t + B)` the growing
part of `𝒦⁽²⁴⁾(iy, it)` and `P_{±1}` its pull-backs to the cusps `±1`
(`leech_contour_identity`):

`∫₀^∞ (𝒦 − f)(t) (2γ(t) − γ(t − i) − γ(t + i)) dt + y⁻¹² e^{−πρ/y}
    − (e^{−iπρ} ∫₀^∞ P₁(is) e^{−πρs} ds + e^{iπρ} ∫₀^∞ P₋₁(is) e^{−πρs} ds)
  = 4 sin²(πρ/2) ∫₀^∞ 𝒦̂(iy, it) e^{−πρt} dt`.

The proof is the proof of `ckmrv_contour_identity` (dimension eight) with `𝒦 − f` on the `x`-side
and `(𝒦̂ − P_{±1}) E` on the two triangles; the cusp parts leave their integrals along the imaginary
axis. By `cusp_shift_sum` these are the terms that the Fourier transform of the truncated profile
contains (`fourier_leechAxisRadialProfile`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm FourierTransform

/-- `(𝒦 − f)(t)`: the kernel `𝒦⁽²⁴⁾(iy, it)` minus the growing part of its cusp profile. -/
def leechKmf (y t : ℝ) : ℂ :=
  ckmrvLeechKernel (imagPt y) (imagPt t) -
    growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t

theorem leechKmf_gaussHat_sub_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    leechKmf y t * gaussHat 24 ((t : ℂ) - I) r =
      -I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (leechPlusF y (r ^ 2) (vPath t) * vPath' t) :=
  leech_kernel_gaussHat_sub_I y r ht

theorem leechKmf_gaussHat_add_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    leechKmf y t * gaussHat 24 ((t : ℂ) + I) r =
      -I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * (leechMinusF y (r ^ 2) (uPath t) * uPath' t) :=
  leech_kernel_gaussHat_add_I y r ht

theorem leechKmf_gaussHat_inv (y r : ℝ) {s : ℝ} (hs : 0 < s) :
    |(-(s ^ 2)⁻¹ : ℝ)| • (leechKmf y s⁻¹ * gaussHat 24 ((s⁻¹ : ℝ) : ℂ) r) =
      leechHatF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
          leechPlusF y (r ^ 2) (1 + I * s) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * leechMinusF y (r ^ 2) (I * s - 1)) / 2 :=
  leech_kernel_gaussHat_inv y r hs

/-! ## The identity -/

/-- **The contour identity in dimension 24** (`τ = iy`, `ρ = r² > 2`). -/
theorem leech_contour_identity {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => leechKmf y t *
        (2 * gaussHat 24 t r - gaussHat 24 (t - I) r - gaussHat 24 (t + I) r)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), leechKmf y t *
          (2 * gaussHat 24 t r - gaussHat 24 (t - I) r - gaussHat 24 (t + I) r)) +
        ((y⁻¹ ^ 12 : ℝ) : ℂ) * (Real.exp (-(π / y) * r ^ 2) : ℂ) -
        (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
            (∫ s in Ioi (0 : ℝ), cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s) * gaussE (r ^ 2) (I * s)) +
          cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
            ∫ s in Ioi (0 : ℝ), cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s) * gaussE (r ^ 2) (I * s)) =
      ((4 * Real.sin (π * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ckmrvLeechHatKernel (imagPt y) (imagPt t) *
          (Real.exp (-(π * r ^ 2) * t) : ℂ) := by
  have hρ : 0 < r ^ 2 := by linarith
  obtain ⟨Gp, hGpF, hGpc, ⟨Cp, hCp⟩, hCauchyP⟩ := exists_leechGPlus_cauchy hy hy1 hr
  obtain ⟨Gm, hGmF, hGmc, ⟨Cm, hCm⟩, hCauchyM⟩ := exists_leechGMinus_cauchy hy hy1 hr
  -- principal parts on the imaginary axis
  have hqp : 0 < (sigmaC y + 1).im := by
    rw [Complex.add_im, im_sigmaC hy, Complex.one_im, add_zero]; exact inv_pos.mpr hy
  have hqm : 0 < (sigmaC y - 1).im := by
    rw [Complex.sub_im, im_sigmaC hy, Complex.one_im, sub_zero]; exact inv_pos.mpr hy
  have hqpr : |(sigmaC y + 1).re| = 1 := by
    rw [Complex.add_re, re_sigmaC hy, Complex.one_re, zero_add, abs_one]
  have hqmr : |(sigmaC y - 1).re| = 1 := by
    rw [Complex.sub_re, re_sigmaC hy, Complex.one_re, zero_sub, abs_neg, abs_one]
  have ikp := integrableOn_principalK_imag hqp hqpr
  have ikm := integrableOn_principalK_imag hqm hqmr
  have iJp := integrableOn_principalK_imag (q := I * y + 1) (by simpa using hy) (by simp)
  have iJm := integrableOn_principalK_imag (q := I * y - 1) (by simpa using hy) (by simp)
  -- the corrected functions on the lines
  have iGp1 : IntegrableOn (fun t : ℝ => Gp (1 + I * t)) (Ioi 0) := integrableOn_line_one hGpc hCp
  have iGp0 : IntegrableOn (fun t : ℝ => Gp (I * t)) (Ioi 0) := integrableOn_line_zero hGpc hCp
  have iGm0 : IntegrableOn (fun t : ℝ => Gm (I * t)) (Ioi 0) :=
    (integrableOn_line_one hGmc hCm).congr_fun (fun t _ => by simp only [add_sub_cancel_left])
      measurableSet_Ioi
  have iGm1 : IntegrableOn (fun t : ℝ => Gm (I * t - 1)) (Ioi 0) :=
    integrableOn_line_zero hGmc hCm
  -- finitely many exceptional points
  have aeP0 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (I * t) = leechFPlus y (r ^ 2) (I * t) :=
    ae_eq_of_eq_off_finset injective_I_mul (specialPlus y) hGpF
  have aeP1 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (1 + I * t) = leechFPlus y (r ^ 2) (1 + I * t) :=
    ae_eq_of_eq_off_finset injective_one_add_I_mul (specialPlus y) hGpF
  have aeM0 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (I * t) = leechFMinus y (r ^ 2) (I * t) :=
    ae_eq_of_eq_off_finset injective_I_mul (specialMinus y) hGmF
  have aeM1 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (I * t - 1) = leechFMinus y (r ^ 2) (I * t - 1) :=
    ae_eq_of_eq_off_finset injective_I_mul_sub_one (specialMinus y) hGmF
  have aeV : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (vPath t) = leechFPlus y (r ^ 2) (vPath t) :=
    ae_eq_of_eq_off_finset injective_vPath (specialPlus y) hGpF
  have aeU : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (uPath t) = leechFMinus y (r ^ 2) (uPath t) :=
    ae_eq_of_eq_off_finset injective_uPath (specialMinus y) hGmF
  -- `f` on `L₀`
  have iZ1 := integrableOn_cuspPartPlus_imag (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (ρ := r ^ 2) hρ
  have iZm1 := integrableOn_cuspPartMinus_imag (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (ρ := r ^ 2) hρ
  have iP0 : IntegrableOn (fun t : ℝ => Gp (I * t) +
      leechCPlus y (r ^ 2) * principalK (sigmaC y + 1) (I * t)) (Ioi 0) :=
    Integrable.add iGp0 (Integrable.const_mul ikp (leechCPlus y (r ^ 2)))
  have iM0 : IntegrableOn (fun t : ℝ => Gm (I * t) +
      leechCMinus y (r ^ 2) * principalK (sigmaC y - 1) (I * t)) (Ioi 0) :=
    Integrable.add iGm0 (Integrable.const_mul ikm (leechCMinus y (r ^ 2)))
  have iF0 : IntegrableOn (fun t : ℝ => leechHatF y (r ^ 2) (I * t)) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iP0 iZ1) ?_
    filter_upwards [aeP0] with t ht
    simp only [Pi.add_apply]
    rw [ht, leechFPlus, leechPlusF_eq]
    ring
  have e7 : (∫ t in Ioi (0 : ℝ), leechHatF y (r ^ 2) (I * t)) =
      (∫ t in Ioi (0 : ℝ), Gp (I * t)) +
        leechCPlus y (r ^ 2) * (∫ t in Ioi (0 : ℝ), principalK (sigmaC y + 1) (I * t)) +
        ∫ s in Ioi (0 : ℝ), cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s) * gaussE (r ^ 2) (I * s) := by
    rw [← integral_const_mul, ← integral_add iGp0 (Integrable.const_mul ikp (leechCPlus y (r ^ 2))),
      ← integral_add iP0 iZ1]
    refine integral_congr_ae ?_
    filter_upwards [aeP0] with t ht
    rw [ht, leechFPlus, leechPlusF_eq]
    ring
  have e8 : (∫ t in Ioi (0 : ℝ), leechHatF y (r ^ 2) (I * t)) =
      (∫ t in Ioi (0 : ℝ), Gm (I * t)) +
        leechCMinus y (r ^ 2) * (∫ t in Ioi (0 : ℝ), principalK (sigmaC y - 1) (I * t)) +
        ∫ s in Ioi (0 : ℝ), cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s) * gaussE (r ^ 2) (I * s) := by
    rw [← integral_const_mul, ← integral_add iGm0 (Integrable.const_mul ikm (leechCMinus y (r ^ 2))),
      ← integral_add iM0 iZm1]
    refine integral_congr_ae ?_
    filter_upwards [aeM0] with t ht
    rw [ht, leechFMinus, leechMinusF_eq]
    ring
  -- Cauchy on both triangles
  have e5 : (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) =
      I * (∫ t in Ioi (0 : ℝ), Gp (1 + I * t)) - I * ∫ t in Ioi (0 : ℝ), Gp (I * t) := by
    rw [← hCauchyP, integral_const_mul, integral_const_mul]
  have e6 : (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ) =
      I * (∫ t in Ioi (0 : ℝ), Gm (I * t)) - I * ∫ t in Ioi (0 : ℝ), Gm (I * t - 1) := by
    rw [← hCauchyM, integral_const_mul, integral_const_mul]
  -- the semicircles in the `t`-parametrization
  have hSG := semicircle_conv_v Gp
  have hSH := semicircle_conv_u Gm
  have iGv : IntegrableOn (fun t : ℝ => Gp (vPath t) * vPath' t) (Ioi 0) :=
    hSG.1.mp (integrableOn_semicircleIntegrand hGpc hCp)
  have iGu : IntegrableOn (fun t : ℝ => Gm (uPath t) * uPath' t) (Ioi 0) :=
    hSH.1.mp (integrableOn_semicircleIntegrand hGmc hCm)
  have eSG : (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) =
      -∫ t in Ioi (0 : ℝ), Gp (vPath t) * vPath' t := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo, hSG.2]
  have eSH : (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ) =
      ∫ t in Ioi (0 : ℝ), Gm (uPath t) * uPath' t := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo, hSH.2]
  have hmv := principalK_sigma_vPath hy
  have hmu := principalK_sigma_uPath hy
  have efv : (∫ t in Ioi (0 : ℝ), leechPlusF y (r ^ 2) (vPath t) * vPath' t) =
      (∫ t in Ioi (0 : ℝ), Gp (vPath t) * vPath' t) +
        leechCPlus y (r ^ 2) * (I * ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add iGv
      (Integrable.const_mul (Integrable.const_mul iJm I) (leechCPlus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeV] with t ht
    rw [← hmv t, ht, leechFPlus]
    ring
  have efu : (∫ t in Ioi (0 : ℝ), leechMinusF y (r ^ 2) (uPath t) * uPath' t) =
      (∫ t in Ioi (0 : ℝ), Gm (uPath t) * uPath' t) +
        leechCMinus y (r ^ 2) * (I * ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add iGu
      (Integrable.const_mul (Integrable.const_mul iJp I) (leechCMinus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeU] with t ht
    rw [← hmu t, ht, leechFMinus]
    ring
  have ifv : IntegrableOn (fun t : ℝ => leechPlusF y (r ^ 2) (vPath t) * vPath' t) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iGv
      (Integrable.const_mul (Integrable.const_mul iJm I) (leechCPlus y (r ^ 2)))) ?_
    filter_upwards [aeV] with t ht
    simp only [Pi.add_apply]
    rw [← hmv t, ht, leechFPlus]
    ring
  have ifu : IntegrableOn (fun t : ℝ => leechMinusF y (r ^ 2) (uPath t) * uPath' t) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iGu
      (Integrable.const_mul (Integrable.const_mul iJp I) (leechCMinus y (r ^ 2)))) ?_
    filter_upwards [aeU] with t ht
    simp only [Pi.add_apply]
    rw [← hmu t, ht, leechFMinus]
    ring
  -- the `t ∓ i` terms
  have eT2 : (∫ t in Ioi (0 : ℝ), leechKmf y t *
      gaussHat 24 ((t : ℂ) - I) r) = -I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        ∫ t in Ioi (0 : ℝ), leechPlusF y (r ^ 2) (vPath t) * vPath' t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => leechKmf_gaussHat_sub_I y r ht
  have eT3 : (∫ t in Ioi (0 : ℝ), leechKmf y t *
      gaussHat 24 ((t : ℂ) + I) r) = -I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        ∫ t in Ioi (0 : ℝ), leechMinusF y (r ^ 2) (uPath t) * uPath' t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => leechKmf_gaussHat_add_I y r ht
  have iT2 : IntegrableOn (fun t : ℝ => leechKmf y t *
      gaussHat 24 ((t : ℂ) - I) r) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul ifv (-I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ)))))
      (fun t ht => (leechKmf_gaussHat_sub_I y r ht).symm) measurableSet_Ioi
  have iT3 : IntegrableOn (fun t : ℝ => leechKmf y t *
      gaussHat 24 ((t : ℂ) + I) r) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul ifu (-I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ))))
      (fun t ht => (leechKmf_gaussHat_add_I y r ht).symm) measurableSet_Ioi
  have e3 : (∫ t in Ioi (0 : ℝ), leechKmf y t *
      gaussHat 24 ((t : ℂ) - I) r) =
      I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) +
        cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * leechCPlus y (r ^ 2) *
          ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t) := by
    rw [eT2, efv]
    linear_combination (-I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ)))) * eSG -
      (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * leechCPlus y (r ^ 2) *
        ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) * Complex.I_sq
  have e4 : (∫ t in Ioi (0 : ℝ), leechKmf y t *
      gaussHat 24 ((t : ℂ) + I) r) =
      -(I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
          (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ)) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * leechCMinus y (r ^ 2) *
          ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t) := by
    rw [eT3, efu]
    linear_combination (I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ))) * eSH -
      (cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * leechCMinus y (r ^ 2) *
        ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) * Complex.I_sq
  -- the `2t⁻⁴e^{−πρ/t}` term
  have e11 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * leechCMinus y (r ^ 2) =
      -(cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * leechCPlus y (r ^ 2)) := by
    simp only [leechCPlus, leechCMinus, gaussE_add, gaussE_sub_one, gaussE_one]
    ring
  have hk1 : ∀ s : ℝ, principalK (sigmaC y + 1) (1 + I * s) =
      principalK (sigmaC y - 1) (I * s - 1) := fun s => by
    rw [add_comm (1 : ℂ) (I * s)]; exact principalK_add_one_eq _ _
  have aeT1 : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      leechHatF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        leechPlusF y (r ^ 2) (1 + I * s) + cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        leechMinusF y (r ^ 2) (I * s - 1)) / 2 =
      leechHatF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * Gp (1 + I * s) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * Gm (I * s - 1)) / 2 := by
    filter_upwards [aeP1, aeM1] with s h1 h2
    rw [h1, h2, leechFPlus, leechFMinus]
    linear_combination (-(cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * leechCPlus y (r ^ 2)) / 2) * hk1 s +
      (-(principalK (sigmaC y - 1) (I * s - 1)) / 2) * e11
  have hinvd : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(s ^ 2)⁻¹) (Ioi 0) s :=
    fun s hs => (hasDerivAt_inv (ne_of_gt hs)).hasDerivWithinAt
  have hinvinj : InjOn (fun s : ℝ => s⁻¹) (Ioi 0) := inv_injective.injOn
  have hinvimg : (fun s : ℝ => s⁻¹) '' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨s, hs, hsx⟩ => hsx ▸ inv_pos.mpr hs, fun hx => ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩⟩
  have hT1i := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hinvd hinvinj
    (fun t : ℝ => leechKmf y t * gaussHat 24 (t : ℂ) r)
  have hT1e := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hinvd hinvinj
    (fun t : ℝ => leechKmf y t * gaussHat 24 (t : ℂ) r)
  rw [hinvimg] at hT1i hT1e
  have hpt : EqOn (fun s : ℝ => |(-(s ^ 2)⁻¹ : ℝ)| •
      (leechKmf y s⁻¹ * gaussHat 24 ((s⁻¹ : ℝ) : ℂ) r))
      (fun s : ℝ => leechHatF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        leechPlusF y (r ^ 2) (1 + I * s) + cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        leechMinusF y (r ^ 2) (I * s - 1)) / 2) (Ioi 0) :=
    fun s hs => leechKmf_gaussHat_inv y r hs
  have iA : IntegrableOn (fun s : ℝ => (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * Gp (1 + I * s) +
      cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * Gm (I * s - 1)) / 2) (Ioi 0) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul iGp1 _)
      (Integrable.const_mul iGm1 _)) 2
  have iT1 : IntegrableOn (fun t : ℝ => leechKmf y t *
      gaussHat 24 (t : ℂ) r) (Ioi 0) := by
    refine hT1i.mpr (IntegrableOn.congr_fun ?_ (fun s hs => (hpt hs).symm) measurableSet_Ioi)
    refine Integrable.congr (Integrable.sub iF0 iA) ?_
    filter_upwards [aeT1] with s hs
    simp only [Pi.sub_apply]
    exact hs.symm
  have eT1 : 2 * (∫ t in Ioi (0 : ℝ), leechKmf y t *
      gaussHat 24 (t : ℂ) r) =
      2 * (∫ t in Ioi (0 : ℝ), leechHatF y (r ^ 2) (I * t)) -
        cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (∫ t in Ioi (0 : ℝ), Gp (1 + I * t)) -
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * ∫ t in Ioi (0 : ℝ), Gm (I * t - 1) := by
    rw [hT1e, setIntegral_congr_fun measurableSet_Ioi hpt, integral_congr_ae aeT1,
      integral_sub iF0 iA, integral_div, integral_add (Integrable.const_mul iGp1 _)
        (Integrable.const_mul iGm1 _), integral_const_mul, integral_const_mul]
    ring
  have e1 : (∫ t in Ioi (0 : ℝ), leechKmf y t *
        (2 * gaussHat 24 t r - gaussHat 24 (t - I) r - gaussHat 24 (t + I) r)) =
      2 * (∫ t in Ioi (0 : ℝ), leechKmf y t * gaussHat 24 (t : ℂ) r) -
        (∫ t in Ioi (0 : ℝ), leechKmf y t *
          gaussHat 24 ((t : ℂ) - I) r) -
        ∫ t in Ioi (0 : ℝ), leechKmf y t * gaussHat 24 ((t : ℂ) + I) r := by
    have iT12 : IntegrableOn (fun t : ℝ =>
        2 * (leechKmf y t * gaussHat 24 (t : ℂ) r) -
          leechKmf y t * gaussHat 24 ((t : ℂ) - I) r) (Ioi 0) :=
      Integrable.sub (Integrable.const_mul iT1 2) iT2
    rw [← integral_const_mul, ← integral_sub (Integrable.const_mul iT1 2) iT2,
      ← integral_sub iT12 iT3]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  -- the explicit principal parts: `Q' = −2π`
  have e9 : (∫ t in Ioi (0 : ℝ), principalK (sigmaC y + 1) (I * t)) -
      (∫ t in Ioi (0 : ℝ), principalK (sigmaC y - 1) (I * t)) =
        -4 * ((Real.arctan y⁻¹ : ℝ) : ℂ) := by
    rw [← integral_sub ikp ikm, sigmaC_eq hy, integral_principalK_sub_imag]
    simp
  have e10 : (∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) -
      (∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) = -4 * ((Real.arctan y : ℝ) : ℂ) := by
    rw [← integral_sub iJp iJm, integral_principalK_sub_imag]
    simp
  have e13 : ((Real.arctan y⁻¹ : ℝ) : ℂ) + ((Real.arctan y : ℝ) : ℂ) = π / 2 := by
    rw [Real.arctan_inv_of_pos hy]; push_cast; ring
  -- the Gaussian
  have hI4 : I ^ 12 = (1 : ℂ) := I_pow_twelve
  have hpm2 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hπ2 : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hσ4 : sigmaC y ^ 12 = ((y⁻¹ ^ 12 : ℝ) : ℂ) := by
    rw [sigmaC_eq hy, mul_pow, hI4, one_mul]; norm_cast
  have hEσ : gaussE (r ^ 2) (sigmaC y) = ((Real.exp (-(π / y) * r ^ 2) : ℝ) : ℂ) := by
    rw [sigmaC_eq hy, gaussE_I_mul, Complex.ofReal_exp]; congr 1; push_cast; ring
  have e14 : cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * leechCPlus y (r ^ 2) * (2 * π) =
      ((y⁻¹ ^ 12 : ℝ) : ℂ) * (Real.exp (-(π / y) * r ^ 2) : ℂ) := by
    rw [leechCPlus, gaussE_add, gaussE_one,
      show ∀ A B c e : ℂ, e * (A / c * B) * c = (A / c * c) * (B * e) from
        fun _ _ _ _ => by ring, div_mul_cancel₀ _ hπ2, hσ4, hEσ]
    linear_combination (((y⁻¹ ^ 12 : ℝ) : ℂ) * ((Real.exp (-(π / y) * r ^ 2) : ℝ) : ℂ)) * hpm2
  -- the right-hand side
  have hsin : ((4 * Real.sin (π * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) =
      2 - cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) - cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) := by
    have h1 : Real.sin (π * r ^ 2 / 2) ^ 2 = 1 / 2 - Real.cos (π * r ^ 2) / 2 := by
      rw [Real.sin_sq_eq_half_sub, show 2 * (π * r ^ 2 / 2) = π * r ^ 2 by ring]
    have h2 := Complex.two_cos ((π * r ^ 2 : ℝ) : ℂ)
    have h3 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) = cexp (((π * r ^ 2 : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have h4 : cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) = cexp (-((π * r ^ 2 : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have h5 : ((4 * (1 / 2 - Real.cos (π * r ^ 2) / 2) : ℝ) : ℂ) =
        2 - 2 * Complex.cos ((π * r ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos]; push_cast; ring
    rw [h1, h3, h4, h5]
    linear_combination -h2
  have hF0eq : (∫ t in Ioi (0 : ℝ), ckmrvLeechHatKernel (imagPt y) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) = ∫ t in Ioi (0 : ℝ), leechHatF y (r ^ 2) (I * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [leechHatF]
    rw [rightC_I_mul _ _ ht, gaussE_I_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have iΓ : IntegrableOn (fun t : ℝ => leechKmf y t *
      (2 * gaussHat 24 t r - gaussHat 24 (t - I) r - gaussHat 24 (t + I) r)) (Ioi 0) := by
    have i12 : IntegrableOn (fun t : ℝ => 2 * (leechKmf y t * gaussHat 24 (t : ℂ) r) -
        leechKmf y t * gaussHat 24 ((t : ℂ) - I) r) (Ioi 0) :=
      Integrable.sub (Integrable.const_mul iT1 2) iT2
    have i123 : IntegrableOn (fun t : ℝ => 2 * (leechKmf y t * gaussHat 24 (t : ℂ) r) -
        leechKmf y t * gaussHat 24 ((t : ℂ) - I) r -
        leechKmf y t * gaussHat 24 ((t : ℂ) + I) r) (Ioi 0) := Integrable.sub i12 iT3
    refine i123.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show 2 * (leechKmf y t * gaussHat 24 (t : ℂ) r) - leechKmf y t * gaussHat 24 ((t : ℂ) - I) r -
      leechKmf y t * gaussHat 24 ((t : ℂ) + I) r = leechKmf y t *
        (2 * gaussHat 24 t r - gaussHat 24 (t - I) r - gaussHat 24 (t + I) r)
    ring
  refine ⟨iΓ, ?_⟩
  rw [hsin, hF0eq]
  exact leech_contour_algebra e1 eT1 e3 e4 e5 e6 e7 e8 e9 e10 rfl e11 e13 e14

end E8Leech
