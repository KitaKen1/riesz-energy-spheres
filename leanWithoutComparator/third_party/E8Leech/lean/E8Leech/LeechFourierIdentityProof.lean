import E8Leech.LeechContourFinal
import E8Leech.LeechFourierAxis
import E8Leech.LeechFourierReduction

/-!
# The Fourier identities (**) of the Leech certificate

For `y = α/π ≠ 1` and `φ(x) = P_{𝒦,y}(π|x|²)`, the identity
`𝓕φ(ξ) + y⁻¹² e^{−π|ξ|²/y} = P_{𝒦̂,y}(π|ξ|²)` holds for `|ξ|² > 2` (`leechFourierIdentityLarge`):

* the Fourier transform of the truncated profile (`fourier_leechAxisRadialProfile`, cut `p = 1`) is
  `∫₀^∞ (𝒦 − f) Γ + ∫₀¹ f Γ + (explicit term)`;
* `∫₀¹ f Γ + (explicit term)` is minus the two integrals of the cusp parts along the imaginary
  axis (`cusp_shift_sum`);
* the contour identity (`leech_contour_identity`) gives the Laplace transform of `𝒦̂`, which is the
  profile for `π|ξ|² > 2π` (`leechAxisRadialProfile_eq_laplace`).

Hence the identities hold for all radii (`leechFourierIdentities`, by
`leechFourierIdentities_of_large`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real FourierTransform SchwartzMap

/-- On `(0, p]` the truncated kernel is `(𝒦 − f) + f`. -/
theorem leechAxisTruncKernel_one_of_le {y p t : ℝ} (ht : t ≤ p) :
    leechAxisTruncKernel 1 y p t =
      leechKmf y t + growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t := by
  rw [leechAxisTruncKernel, truncAt_of_le _ _ ht, leechAxisKernel_one, leechKmf]
  ring

/-- On `(p, ∞)` the truncated kernel is `𝒦 − f`. -/
theorem leechAxisTruncKernel_one_of_lt {y p t : ℝ} (ht : p < t) :
    leechAxisTruncKernel 1 y p t = leechKmf y t := by
  rw [leechAxisTruncKernel, truncAt_of_lt _ _ ht, leechAxisKernel_one, leechKmf, leechAxisGrowth,
    growthC_ofReal]

/-- **The Fourier identity (**) of the Leech certificate outside the ball `|ξ|² ≤ 2`.** -/
theorem leechFourierIdentityLarge {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (φ : 𝓢(Ambient 24, ℂ))
    (hφ : ∀ x : Ambient 24, φ x = leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2)) :
    LeechFourierIdentityLarge α φ := by
  intro ξ hξ
  have hπ := Real.pi_pos
  have hy : 0 < α / π := div_pos hα hπ
  have hy1 : α / π ≠ 1 := div_pi_ne_one hαπ
  have hr0 : ‖ξ‖ ≠ 0 := by
    intro h
    rw [h] at hξ
    norm_num at hξ
  have hd : Module.finrank ℝ (Ambient 24) = 24 := by simp [Ambient]
  obtain ⟨hXint, hX⟩ := fourier_leechAxisRadialProfile hd 1 hy hy1 φ hφ (p := 1) one_pos ξ
  obtain ⟨hCIint, hCI⟩ := leech_contour_identity hy hy1 (r := ‖ξ‖) hξ
  have hEX := cusp_shift_sum (leechAxisCusp 1 (α / π) 0) (leechAxisCusp 1 (α / π) 1)
    (r := ‖ξ‖) (p := 1) hr0 one_pos
  -- the truncated kernel against `Γ`
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hIoc : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun t ht => ht.1
  have hIoi : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have ifΓ : IntegrableOn (fun x : ℝ =>
      growthC (leechAxisCusp 1 (α / π) 0) (leechAxisCusp 1 (α / π) 1) x *
        (2 * gaussHat 24 x ‖ξ‖ - gaussHat 24 (x - I) ‖ξ‖ - gaussHat 24 (x + I) ‖ξ‖)) (Ioc 0 1) := by
    have hdiff : IntegrableOn (fun t : ℝ => leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) -
        leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖)) (Ioc 0 1) :=
      (hXint.mono_set hIoc).sub (hCIint.mono_set hIoc)
    refine hdiff.congr_fun (fun t ht => ?_) measurableSet_Ioc
    show leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) -
        leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) = _
    rw [leechAxisTruncKernel_one_of_le ht.2]
    ring
  have hsplit : ∫ t in Ioi (0 : ℝ), leechAxisTruncKernel 1 (α / π) 1 t *
        (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) =
      (∫ t in Ioi (0 : ℝ), leechKmf (α / π) t *
        (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖)) +
      ∫ x in Ioc (0 : ℝ) 1, growthC (leechAxisCusp 1 (α / π) 0) (leechAxisCusp 1 (α / π) 1) x *
        (2 * gaussHat 24 x ‖ξ‖ - gaussHat 24 (x - I) ‖ξ‖ - gaussHat 24 (x + I) ‖ξ‖) := by
    have h1 : ∫ t in Ioi (0 : ℝ), leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) =
        (∫ t in Ioc (0 : ℝ) 1, leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖)) +
        ∫ t in Ioi (1 : ℝ), leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) := by
      rw [hu]
      exact setIntegral_union hdisj measurableSet_Ioi (hXint.mono_set hIoc) (hXint.mono_set hIoi)
    have h2 : ∫ t in Ioi (0 : ℝ), leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) =
        (∫ t in Ioc (0 : ℝ) 1, leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖)) +
        ∫ t in Ioi (1 : ℝ), leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) := by
      rw [hu]
      exact setIntegral_union hdisj measurableSet_Ioi (hCIint.mono_set hIoc)
        (hCIint.mono_set hIoi)
    have h3 : ∫ t in Ioc (0 : ℝ) 1, leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) =
        (∫ t in Ioc (0 : ℝ) 1, leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖)) +
        ∫ x in Ioc (0 : ℝ) 1,
          growthC (leechAxisCusp 1 (α / π) 0) (leechAxisCusp 1 (α / π) 1) x *
            (2 * gaussHat 24 x ‖ξ‖ - gaussHat 24 (x - I) ‖ξ‖ - gaussHat 24 (x + I) ‖ξ‖) := by
      rw [← integral_add (hCIint.mono_set hIoc) ifΓ]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [leechAxisTruncKernel_one_of_le ht.2]
      ring
    have h4 : ∫ t in Ioi (1 : ℝ), leechAxisTruncKernel 1 (α / π) 1 t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) =
        ∫ t in Ioi (1 : ℝ), leechKmf (α / π) t *
          (2 * gaussHat 24 t ‖ξ‖ - gaussHat 24 (t - I) ‖ξ‖ - gaussHat 24 (t + I) ‖ξ‖) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [leechAxisTruncKernel_one_of_lt ht]
    rw [h1, h2, h3, h4]
    ring
  -- the right side
  have hR : leechAxisRadialProfile (-1) (α / π) (π * ‖ξ‖ ^ 2) =
      ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ckmrvLeechHatKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ) := by
    rw [leechAxisRadialProfile_eq_laplace (-1) hy hy1 (by nlinarith : 2 * π < π * ‖ξ‖ ^ 2)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [leechAxisKernel_neg_one]
  -- the Gaussian
  have hY : (((π / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
      (((α / π)⁻¹ ^ 12 : ℝ) : ℂ) * (Real.exp (-(π / (α / π)) * ‖ξ‖ ^ 2) : ℂ) := by
    have hg1 : (α / π)⁻¹ = π / α := inv_div α π
    have hg2 : π / (α / π) = π ^ 2 / α := by rw [div_div_eq_mul_div, sq]
    rw [hg1, hg2, gaussianKernel]
  rw [hX, hsplit, hY, hR, ← hCI]
  linear_combination -hEX

/-- **The Fourier identities (**) of the Leech certificate**, for all radii. -/
theorem leechFourierIdentities : LeechFourierIdentities :=
  leechFourierIdentities_of_large fun _ hα hαπ φ hφ => leechFourierIdentityLarge hα hαπ φ hφ

end E8Leech
