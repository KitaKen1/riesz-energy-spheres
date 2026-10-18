import E8Leech.FourierCompactSupport
import E8Leech.LeechSlackProfile

/-!
# The Leech Fourier identities for all radii from the identities outside the ball

`LeechFourierIdentityLarge α φ` is the identity (**) in dimension 24 for `|ξ|² > 2` only, where the
right side is `4 sin²(π|ξ|²/2) ∫₀^∞ 𝒦̂ e^{−π|ξ|²t} dt`. If it holds for every `α`, then (**) holds
for all radii (`leechFourierIdentities_of_large`), without an analytic continuation in the radius:

with `y = α/π`, `ψ` the Schwartz function of the `𝒦̂`-profile and `G` the Gaussian `e^{−α|·|²}`,
the Schwartz function `h = 𝓕(φ + G) − ψ` vanishes for `|ξ|² > 2` by the hypothesis at `α`. Its
Fourier transform is `(φ + G)(−·) − 𝓕ψ`, and the hypothesis at `π²/α` (that is, at `1/y`), applied
to `−y¹² ψ`, which is the `𝒦`-profile at `1/y` by `𝒦(iy, ·) = −y⁻¹² 𝒦̂(i/y, ·)`, gives
`𝓕ψ = φ + G` for `|x|² > 2`. So `h` and `𝓕h` vanish outside a ball and `h = 0`
(`schwartz_eq_zero_of_compact_supports`).

The hypothesis is proved in `LeechFourierIdentityProof` (`leechFourierIdentityLarge`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open scoped FourierTransform Real SchwartzMap

/-- The identity (**) in dimension 24 outside the ball `|ξ|² ≤ 2`. -/
def LeechFourierIdentityLarge (α : ℝ) (φ : 𝓢(Ambient 24, ℂ)) : Prop :=
  ∀ ξ : Ambient 24, 2 < ‖ξ‖ ^ 2 →
    𝓕 (⇑φ) ξ + (((π / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
      leechAxisRadialProfile (-1) (α / π) (π * ‖ξ‖ ^ 2)

/-- The Fourier transform of the Fourier transform of a Schwartz function is its reflection. -/
theorem schwartz_fourier_fourier_apply (f : 𝓢(Ambient 24, ℂ)) (x : Ambient 24) :
    𝓕 (⇑(𝓕 f : 𝓢(Ambient 24, ℂ))) x = f (-x) := by
  have h : 𝓕⁻ (𝓕 f : 𝓢(Ambient 24, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h2 : (𝓕⁻ (𝓕 f : 𝓢(Ambient 24, ℂ)) : 𝓢(Ambient 24, ℂ)) (-x) = f (-x) := by rw [h]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at h2
  exact h2

/-- **The Leech Fourier identities for all radii from the identities outside the ball
`|ξ|² ≤ 2`.** -/
theorem leechFourierIdentities_of_large
    (h : ∀ α : ℝ, 0 < α → α ≠ π → ∀ φ : 𝓢(Ambient 24, ℂ),
      (∀ x : Ambient 24, φ x = leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2)) →
        LeechFourierIdentityLarge α φ) : LeechFourierIdentities := by
  intro α hα hαπ φ hφ ξ _
  have hπ := Real.pi_pos
  have hy : 0 < α / π := div_pos hα hπ
  have hy1 : α / π ≠ 1 := fun h1 => hαπ ((div_eq_one_iff_eq hπ.ne').mp h1)
  have hyc : ((α / π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hyi : 0 < (α / π)⁻¹ := inv_pos.mpr hy
  have hyi1 : (α / π)⁻¹ ≠ 1 := fun h1 => hy1 (inv_eq_one.mp h1)
  -- the Schwartz function of the hat profile and the Gaussian
  obtain ⟨ψ, hψ, -⟩ := exists_schwartz_leechAxisRadialProfile (Ambient 24) (-1) hy hy1
  have hFadd : ∀ ζ : Ambient 24, (𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) ζ =
      𝓕 (⇑φ) ζ + (((π / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ζ : ℂ) := by
    intro ζ
    rw [FourierAdd.fourier_add]
    show (𝓕 φ : 𝓢(Ambient 24, ℂ)) ζ + (𝓕 (gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) ζ = _
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, fourier_gaussianSchwartz_twentyFour hα]
  -- the Fourier transform of `ψ` outside the ball, from the hypothesis at `π²/α`
  have hα' : 0 < π ^ 2 / α := by positivity
  have hα'π : π ^ 2 / α ≠ π := by
    intro h1
    rw [div_eq_iff hα.ne'] at h1
    exact hαπ (mul_left_cancel₀ hπ.ne' (by rw [← h1, sq])).symm
  have hinv : π ^ 2 / α / π = (α / π)⁻¹ := by
    rw [inv_div]
    field_simp
  have hφ' : ∀ x : Ambient 24, ((-((α / π : ℝ) : ℂ) ^ 12) • ψ) x =
      leechAxisRadialProfile 1 (π ^ 2 / α / π) (π * ‖x‖ ^ 2) := by
    intro x
    rw [hinv, leechAxisRadialProfile_one_eq hyi hyi1, inv_inv,
      show ((-((α / π : ℝ) : ℂ) ^ 12) • ψ) x = -((α / π : ℝ) : ℂ) ^ 12 * ψ x from rfl, hψ x]
    congr 1
    push_cast
    rw [inv_pow, inv_inv]
  have hψhat : ∀ x : Ambient 24, 2 < ‖x‖ ^ 2 →
      𝓕 (⇑ψ) x = φ x + (gaussianKernel α x : ℂ) := by
    intro x hx
    have hL := h (π ^ 2 / α) hα' hα'π _ hφ' x hx
    have hsmul : 𝓕 (⇑((-((α / π : ℝ) : ℂ) ^ 12) • ψ)) x = -((α / π : ℝ) : ℂ) ^ 12 * 𝓕 (⇑ψ) x := by
      rw [← SchwartzMap.fourier_coe, FourierSMul.fourier_smul, ← SchwartzMap.fourier_coe]
      rfl
    have e1 : π / (π ^ 2 / α) = α / π := by
      field_simp
    have e2 : π ^ 2 / (π ^ 2 / α) = α := by
      field_simp
    have hprof : leechAxisRadialProfile (-1) (π ^ 2 / α / π) (π * ‖x‖ ^ 2) =
        -((α / π : ℝ) : ℂ) ^ 12 * φ x := by
      rw [hinv, hφ x, leechAxisRadialProfile_one_eq hy hy1]
      field_simp
    rw [hsmul, e1, e2, hprof] at hL
    have hy12 : ((α / π : ℝ) : ℂ) ^ 12 ≠ 0 := pow_ne_zero 12 hyc
    have hL' : ((α / π : ℝ) : ℂ) ^ 12 * (𝓕 (⇑ψ) x - (φ x + (gaussianKernel α x : ℂ))) = 0 := by
      push_cast at hL ⊢
      linear_combination -hL
    have := (mul_eq_zero.mp hL').resolve_left hy12
    exact sub_eq_zero.mp this
  -- the difference and its Fourier transform vanish outside a ball
  have hzero : (𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) - ψ = 0 := by
    refine schwartz_eq_zero_of_compact_supports _ (R := 2) (fun v hv => ?_) (fun w hw => ?_)
    · have hv2 : 2 < ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
      show (𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) v - ψ v = 0
      rw [hFadd v, hψ v, h α hα hαπ φ hφ v hv2, sub_self]
    · have hw2 : 2 < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      have e : 𝓕 (⇑((𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) - ψ)) w =
          𝓕 (⇑(𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ))) w - 𝓕 (⇑ψ) w := by
        rw [← SchwartzMap.fourier_coe,
          show (𝓕 ((𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) - ψ) :
            𝓢(Ambient 24, ℂ)) = 𝓕 (𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) -
              𝓕 ψ from map_sub (SchwartzMap.fourierTransformCLM ℂ) _ _]
        rfl
      rw [e, schwartz_fourier_fourier_apply, hψhat w hw2]
      show φ (-w) + gaussianSchwartz (d := 24) hα (-w) - (φ w + (gaussianKernel α w : ℂ)) = 0
      rw [hφ (-w), hφ w, gaussianSchwartz_apply, norm_neg, gaussianKernel, gaussianKernel, norm_neg]
      ring
  have hpt := congrArg (fun f : 𝓢(Ambient 24, ℂ) => f ξ) hzero
  have hpt' : (𝓕 (φ + gaussianSchwartz (d := 24) hα) : 𝓢(Ambient 24, ℂ)) ξ - ψ ξ = 0 := hpt
  rw [hFadd ξ, hψ ξ] at hpt'
  exact sub_eq_zero.mp hpt'

end E8Leech
