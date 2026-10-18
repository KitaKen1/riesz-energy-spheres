import E8Leech.LeechHatProfileSign
import E8Leech.LeechGaussianCertificate
import E8Leech.GaussianSchwartz

/-!
# The Leech Gaussian certificate from the CKMRV data (Lemma 6.2 wiring)

For `α > 0`, `α ≠ π`, put `y = α/π`. The certificate function is `f = e^{−α|·|²} + φ`, where `φ` is
the Schwartz function `x ↦ P_𝒦,y(π|x|²)` of `LeechAxisRadialProfile`
(for `|x|² > 2`: `4 sin²(π|x|²/2) ∫₀^∞ 𝒦(iy, it) e^{−π|x|²t} dt`). Two inputs are hypotheses of
this file and are *not* proved in it:

* `LeechKernelInequalities`: the kernel inequalities of CKMRV (6.4) in dimension 24;
* `LeechFourierIdentity α φ`: the identity (**) in dimension 24, for all radii,
  `φ̂(ξ) + 𝓕(e^{−α|·|²})(ξ) = P_𝒦̂,y(π|ξ|²)` for `ξ ≠ 0`
  (for `|ξ|² > 2` the right side is `4 sin²(π|ξ|²/2) ∫₀^∞ 𝒦̂(iy, it) e^{−π|ξ|²t} dt`).

From them `f` is a Gaussian certificate for the Leech lattice
(`leech_gaussianSchwartzCertificate_of_ckmrv`). The realness of the kernels and of their cusp
coefficients on the axis is proved (`LeechKernelReal`), and the minorant side is reduced to the
Fourier side by `𝒦(iy, ·) = −y^{−12} 𝒦̂(i/y, ·)` (`leechProfile_re_nonpos`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open scoped FourierTransform Real SchwartzMap

/-- The identity (**) in dimension 24 for the Schwartz function `φ` of the `𝒦`-profile at
`y = α/π`: `φ̂ + 𝓕(e^{−α|·|²})` is the `𝒦̂`-profile, at every `ξ ≠ 0`. -/
def LeechFourierIdentity (α : ℝ) (φ : 𝓢(Ambient 24, ℂ)) : Prop :=
  ∀ ξ : Ambient 24, ξ ≠ 0 →
    𝓕 (⇑φ) ξ + (((π / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
      leechAxisRadialProfile (-1) (α / π) (π * ‖ξ‖ ^ 2)

/-- **The Leech Gaussian certificate from the CKMRV data.** -/
theorem leech_gaussianSchwartzCertificate_of_ckmrv {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (H : LeechKernelInequalities) (φ : 𝓢(Ambient 24, ℂ))
    (hφ : ∀ x : Ambient 24, φ x = leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2))
    (hF : LeechFourierIdentity α φ) :
    GaussianSchwartzCertificate leechSet α (gaussianSchwartz hα + φ) := by
  have hπ := Real.pi_pos
  set y := α / π with hydef
  have hy : 0 < y := div_pos hα hπ
  have hy1 : y ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hπ.ne').mp h)
  have hb : ∀ v : Ambient 24, v ≠ 0 → 0 < π * ‖v‖ ^ 2 := fun v hv =>
    mul_pos hπ (pow_pos (norm_pos_iff.mpr hv) 2)
  have hbig : ∀ v : Ambient 24, 2 < ‖v‖ ^ 2 → 2 * π < π * ‖v‖ ^ 2 := fun v hv => by nlinarith
  have hne : ∀ v : Ambient 24, 2 < ‖v‖ ^ 2 → v ≠ 0 := fun v hv h => by
    rw [h, norm_zero] at hv
    norm_num at hv
  -- the two sides for all nonzero arguments
  have hfv : ∀ v : Ambient 24, (gaussianSchwartz (d := 24) hα + φ) v =
      (gaussianKernel α v : ℂ) + leechAxisRadialProfile 1 y (π * ‖v‖ ^ 2) := fun v => by
    rw [show (gaussianSchwartz (d := 24) hα + φ) v = gaussianSchwartz (d := 24) hα v + φ v from rfl,
      gaussianSchwartz_apply, hφ v]
  have hcoe : (⇑(gaussianSchwartz (d := 24) hα + φ) : Ambient 24 → ℂ) =
      fun v => gaussianSchwartz (d := 24) hα v + φ v := by
    funext v
    rfl
  have hfhat : ∀ ξ : Ambient 24, ξ ≠ 0 → 𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ =
      leechAxisRadialProfile (-1) y (π * ‖ξ‖ ^ 2) := by
    intro ξ hξ
    have hadd : 𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ =
        𝓕 (⇑(gaussianSchwartz (d := 24) hα)) ξ + 𝓕 (⇑φ) ξ := by
      rw [hcoe]
      simp only [Real.fourier_eq]
      rw [← integral_add ((Real.fourierIntegral_convergent_iff ξ).mpr
          (gaussianSchwartz (d := 24) hα).integrable)
          ((Real.fourierIntegral_convergent_iff ξ).mpr φ.integrable)]
      congr 1
      ext v
      rw [smul_add]
    rw [hadd, fourier_gaussianSchwartz_twentyFour hα, add_comm, hF ξ hξ]
  -- the Laplace forms for `|v|² > 2`
  have hlap : ∀ (s : ℂ), s.im = 0 → ∀ v : Ambient 24, 2 < ‖v‖ ^ 2 →
      leechAxisRadialProfile s y (π * ‖v‖ ^ 2) =
        ((4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * ∫ t in Ioi 0,
          (leechAxisKernel s y t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)).re : ℝ) : ℂ) := by
    intro s hs v hv
    rw [leechAxisRadialProfile_eq_laplace s hy hy1 (hbig v hv),
      setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
        rw [Complex.im_mul_ofReal, leechAxisKernel_im hs hy ht, zero_mul]]
    push_cast
    ring
  refine leech_gaussianSchwartzCertificate_of_large_sin_sq (gaussianSchwartz hα + φ) hα
    (fun v => ∫ t in Ioi 0, (leechAxisKernel 1 y t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)).re)
    (fun ξ => ∫ t in Ioi 0, (leechAxisKernel (-1) y t * (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ)).re)
    ?_ ?_ ?_ ?_ ?_
  · intro v hv
    show (gaussianSchwartz (d := 24) hα + φ) v = ((gaussianKernel α v +
      4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * ∫ t in Ioi 0,
        (leechAxisKernel 1 y t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)).re : ℝ) : ℂ)
    rw [hfv v, hlap 1 (by simp) v hv, ← Complex.ofReal_add]
  · intro ξ hξ
    show 𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ = ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 *
      ∫ t in Ioi 0, (leechAxisKernel (-1) y t * (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ)).re : ℝ) : ℂ)
    rw [hfhat ξ (hne ξ hξ), hlap (-1) im_neg_one ξ hξ]
  · intro v hv
    rw [hfv v, Complex.add_re, Complex.ofReal_re]
    linarith [leechProfile_re_nonpos H hy hy1 (hb v hv)]
  · -- realness of the Fourier transform, at `0` by continuity
    have hcont : Continuous (𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ))) := by
      rw [← SchwartzMap.fourier_coe]
      exact (𝓕 (gaussianSchwartz (d := 24) hα + φ)).continuous
    have hcl : IsClosed {ξ : Ambient 24 | (𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp hcont) continuous_const
    have hsub : ({0}ᶜ : Set (Ambient 24)) ⊆
        {ξ | (𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ).im = 0} := by
      intro ξ hξ
      show (𝓕 (⇑(gaussianSchwartz (d := 24) hα + φ)) ξ).im = 0
      rw [hfhat ξ hξ]
      exact leechAxisRadialProfile_im im_neg_one hy _
    have h := hcl.closure_subset_iff.mpr hsub
    have : Nonempty (Fin 24) := ⟨0⟩
    rw [(dense_compl_singleton (0 : Ambient 24)).closure_eq] at h
    exact fun ξ => h (Set.mem_univ ξ)
  · intro ξ hξ
    rw [hfhat ξ hξ]
    exact leechHatProfile_re_nonneg H hy hy1 (hb ξ hξ)

/-- **Leech certificates from the CKMRV kernel facts.** For `α > 0`, `α ≠ π`, there is a Schwartz
function `φ` (the `𝒦`-profile at `τ = iα/π`) such that the identity (**) for `φ` makes
`e^{−α|·|²} + φ` a Gaussian certificate for the Leech lattice, given the kernel inequalities. -/
theorem leech_exists_gaussianSchwartzCertificate_of_ckmrv {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (H : LeechKernelInequalities) :
    ∃ φ : 𝓢(Ambient 24, ℂ),
      (∀ x : Ambient 24, φ x = leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2)) ∧
      (LeechFourierIdentity α φ →
        GaussianSchwartzCertificate leechSet α (gaussianSchwartz hα + φ)) := by
  have hβ : 0 < α / π := div_pos hα Real.pi_pos
  have hβ1 : α / π ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)
  obtain ⟨φ, hφ, -⟩ := exists_schwartz_leechAxisRadialProfile (Ambient 24) 1 hβ hβ1
  exact ⟨φ, hφ, fun hF => leech_gaussianSchwartzCertificate_of_ckmrv hα hαπ H φ hφ hF⟩

end E8Leech
