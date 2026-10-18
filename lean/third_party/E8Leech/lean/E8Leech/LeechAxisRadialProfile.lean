import E8Leech.LeechKernelReal
import E8Leech.CuspProfileUnique

/-!
# The radial profile of the Leech kernels on the axis, in terms of the kernels

`leechAxisRadialProfile s β b` is the radial profile of `K_s = (K₊ + s K₋)/2` at `τ = iβ`, written
with the kernel itself (its junk values at the two removable points `t = β, 1/β` do not affect the
integrals). `s = 1` is `𝒦⁽²⁴⁾`, `s = −1` is `𝒦̂⁽²⁴⁾`.

* `exists_schwartz_leechAxisRadialProfile`: the Schwartz function `x ↦ P_s(π|x|²)`.
* `leechAxisRadialProfile_eq_laplace`: for `b > 2π`, `P_s(b) = 4 sin²(b/2) ∫₀^∞ K_s e^{−bt} dt`.
* `leechAxisRadialProfile_truncated`: the truncated form for every `b > 0` and cut `p ≥ 0`.
* `leechAxisCusp_one_eq`, `leechAxisRadialProfile_one_eq`: from `𝒦(iy, ·) = −y^{−12} 𝒦̂(i/y, ·)`
  and the uniqueness of cusp profiles, the cusp coefficients and the profiles satisfy the same
  relation. This is `e^{−α|x|²} − f(x) = y^{−12} F̃(i/y, x)` of CKMRV Lemma 6.2, for all radii.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real

/-- Integrals over a set of two functions that agree off two points are equal. -/
theorem setIntegral_congr_off_two {f g : ℝ → ℂ} {p q : ℝ} (S : Set ℝ)
    (h : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x) : ∫ t in S, g t = ∫ t in S, f t := by
  refine integral_congr_ae ?_
  have hfin : volume ({p, q} : Set ℝ) = 0 := (Set.toFinite {p, q}).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({p, q} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  filter_upwards [ae_restrict_of_ae hae] with x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  exact h x hx.1 hx.2

/-- The radial profile of `(K₊ + s K₋)/2 (iβ, ·)`, in terms of the kernel. -/
def leechAxisRadialProfile (s : ℂ) (β b : ℝ) : ℂ :=
  radialProfile (fun t => leechAxisKernel s β t - leechAxisProfile s β t)
    (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3)
    (2 * π) b

/-- The profile of a continuous representative is the profile of the kernel. -/
theorem radialProfile_eq_leechAxisRadialProfile (s : ℂ) {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = leechAxisKernel s β x) (b : ℝ) :
    radialProfile (fun t => g t - leechAxisProfile s β t)
      (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3)
      (2 * π) b = leechAxisRadialProfile s β b := by
  have h : ∫ t in Ioi 0, (g t - leechAxisProfile s β t) * (Real.exp (-b * t) : ℂ) =
      ∫ t in Ioi 0, (leechAxisKernel s β t - leechAxisProfile s β t) *
        (Real.exp (-b * t) : ℂ) :=
    setIntegral_congr_off_two (p := β) (q := β⁻¹) (Ioi 0) fun x h1 h2 => by rw [hgK x h1 h2]
  show ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
      (∫ t in Ioi 0, (g t - leechAxisProfile s β t) * (Real.exp (-b * t) : ℂ)) +
        cuspProfileSinc (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
          (leechAxisCusp s β 3) (2 * π) b =
    ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
      (∫ t in Ioi 0, (leechAxisKernel s β t - leechAxisProfile s β t) *
        (Real.exp (-b * t) : ℂ)) +
        cuspProfileSinc (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
          (leechAxisCusp s β 3) (2 * π) b
  rw [h]

section Schwartz

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The Schwartz function `x ↦ P_s(π|x|²)`.** For `|x|² > 2` it is
`4 sin²(π|x|²/2) ∫₀^∞ K_s(iβ, it) e^{−π|x|²t} dt`. -/
theorem exists_schwartz_leechAxisRadialProfile (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, (∀ x : F, φ x = leechAxisRadialProfile s β (π * ‖x‖ ^ 2)) ∧
      ∀ x : F, 2 < ‖x‖ ^ 2 →
        φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, leechAxisKernel s β t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, φ, -, hgK, -, -, hprof, hφ⟩ := exists_schwartz_leechAxis F s hβ hβ1
  exact ⟨φ, fun x => by rw [hprof x, radialProfile_eq_leechAxisRadialProfile s hgK], hφ⟩

end Schwartz

/-- **The truncated form of the Leech profile, in terms of the kernel.** -/
theorem leechAxisRadialProfile_truncated (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {b p : ℝ}
    (hb : 0 < b) (hp : 0 ≤ p) :
    leechAxisRadialProfile s β b =
      ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
        ((∫ t in Ioc 0 p, leechAxisKernel s β t * (Real.exp (-b * t) : ℂ)) +
          ∫ t in Ioi p, (leechAxisKernel s β t -
            (leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
              leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ)) +
        ((Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * p) : ℝ) : ℂ) *
          (leechAxisCusp s β 0 + (leechAxisCusp s β 1 + p * leechAxisCusp s β 0) *
            ((b - 2 * π : ℝ) : ℂ)) := by
  obtain ⟨g, hg, hgK, -, hg01, -, hsub⟩ := exists_leechAxis s hβ hβ1
  rw [← radialProfile_eq_leechAxisRadialProfile s hgK,
    leechAxis_radialProfile_truncated s hg hg01 hsub hb hp]
  have h1 : ∫ t in Ioc 0 p, g t * (Real.exp (-b * t) : ℂ) =
      ∫ t in Ioc 0 p, leechAxisKernel s β t * (Real.exp (-b * t) : ℂ) :=
    setIntegral_congr_off_two (p := β) (q := β⁻¹) (Ioc 0 p) fun x h1 h2 => by rw [hgK x h1 h2]
  have h2 : ∫ t in Ioi p, (g t - (leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
        leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ) =
      ∫ t in Ioi p, (leechAxisKernel s β t -
        (leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
          leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ) :=
    setIntegral_congr_off_two (p := β) (q := β⁻¹) (Ioi p) fun x h1 h2 => by rw [hgK x h1 h2]
  rw [h1, h2]

/-- **For `b > 2π` the profile is the Laplace transform of the kernel times `4 sin²(b/2)`.** -/
theorem leechAxisRadialProfile_eq_laplace (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {b : ℝ}
    (hb : 2 * π < b) :
    leechAxisRadialProfile s β b = ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, leechAxisKernel s β t * (Real.exp (-b * t) : ℂ) := by
  obtain ⟨g, hg, hgK, -, hg01, -, hsub⟩ := exists_leechAxis s hβ hβ1
  have hπ := Real.pi_pos
  have hsplit := integral_eq_sub_cuspProfile (b := b) hg hg01
    (show (fun t => g t - cuspProfile (leechAxisCusp s β 0) (leechAxisCusp s β 1)
      (leechAxisCusp s β 2) (leechAxisCusp s β 3) (2 * π) t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t) from hsub)
    (by linarith) (by positivity) hb
  rw [← radialProfile_eq_leechAxisRadialProfile s hgK,
    show (fun t => g t - leechAxisProfile s β t) = fun t => g t - cuspProfile
      (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3)
      (2 * π) t from rfl,
    radialProfile_eq hsplit sin_two_pi_div_two (by linarith : b ≠ 0) (by linarith : b - 2 * π ≠ 0)]
  have h : ∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ) =
      ∫ t in Ioi 0, leechAxisKernel s β t * (Real.exp (-b * t) : ℂ) :=
    setIntegral_congr_off_two (p := β) (q := β⁻¹) (Ioi 0) fun x h1 h2 => by rw [hgK x h1 h2]
  rw [h]

/-! ## The relation between `𝒦(iy, ·)` and `𝒦̂(i/y, ·)` -/

theorem cuspProfile_smul (l A B C D : ℂ) (c t : ℝ) :
    cuspProfile (l * A) (l * B) (l * C) (l * D) c t = l * cuspProfile A B C D c t := by
  simp only [cuspProfile]
  ring

/-- `K₁(iy, it) = −y^{−12} K₋₁(i/y, it)`. -/
theorem leechAxisKernel_one_eq {y : ℝ} (hy : 0 < y) (t : ℝ) :
    leechAxisKernel 1 y t = -((y : ℂ) ^ 12)⁻¹ * leechAxisKernel (-1) y⁻¹ t := by
  rw [leechAxisKernel_one, leechAxisKernel_neg_one, ckmrvLeechKernel_imagPt hy]

/-- **The cusp coefficients of `𝒦(iy, ·)` are `−y^{−12}` times those of `𝒦̂(i/y, ·)`.** -/
theorem leechAxisCusp_one_eq {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (k : Fin 4) :
    leechAxisCusp 1 y k = -((y : ℂ) ^ 12)⁻¹ * leechAxisCusp (-1) y⁻¹ k := by
  have hy' : 0 < y⁻¹ := inv_pos.mpr hy
  have hy1' : y⁻¹ ≠ 1 := fun h => hy1 (inv_eq_one.mp h)
  obtain ⟨g₁, -, hg₁K, -, -, -, hsub₁⟩ := exists_leechAxis 1 hy hy1
  obtain ⟨g₂, -, hg₂K, -, -, -, hsub₂⟩ := exists_leechAxis (-1) hy' hy1'
  set l : ℂ := -((y : ℂ) ^ 12)⁻¹ with hl
  have hev : ∀ᶠ t in atTop, g₁ t = l * g₂ t := by
    filter_upwards [eventually_gt_atTop (max y y⁻¹)] with t ht
    have h1 : t ≠ y := ne_of_gt (lt_of_le_of_lt (le_max_left _ _) ht)
    have h2 : t ≠ y⁻¹ := ne_of_gt (lt_of_le_of_lt (le_max_right _ _) ht)
    rw [hg₁K t h1 h2, hg₂K t h2 (by rwa [inv_inv]), leechAxisKernel_one_eq hy]
  have hsub₂' : (fun t => g₁ t - cuspProfile (l * leechAxisCusp (-1) y⁻¹ 0)
      (l * leechAxisCusp (-1) y⁻¹ 1) (l * leechAxisCusp (-1) y⁻¹ 2)
      (l * leechAxisCusp (-1) y⁻¹ 3) (2 * π) t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t) := by
    refine (hsub₂.const_mul_left l).congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with t ht
    rw [ht, cuspProfile_smul, leechAxisProfile]
    ring
  have hπ := Real.pi_pos
  obtain ⟨h0, h1, h2, h3⟩ := cuspProfile_unique (by linarith : -π + π / 4 < 0)
    (by positivity : (0 : ℝ) < 2 * π)
    (show (fun t => g₁ t - cuspProfile (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
      (leechAxisCusp 1 y 2) (leechAxisCusp 1 y 3) (2 * π) t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t) from hsub₁) hsub₂'
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **`P_𝒦,y(b) = −y^{−12} P_𝒦̂,1/y(b)`** for every `b`: Lemma 6.2's relation between the
minorant side and the Fourier side, for all radii. -/
theorem leechAxisRadialProfile_one_eq {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (b : ℝ) :
    leechAxisRadialProfile 1 y b = -((y : ℂ) ^ 12)⁻¹ * leechAxisRadialProfile (-1) y⁻¹ b := by
  have hc := leechAxisCusp_one_eq hy hy1
  have hint : ∫ t in Ioi 0, (leechAxisKernel 1 y t - leechAxisProfile 1 y t) *
      (Real.exp (-b * t) : ℂ) = -((y : ℂ) ^ 12)⁻¹ *
        ∫ t in Ioi 0, (leechAxisKernel (-1) y⁻¹ t - leechAxisProfile (-1) y⁻¹ t) *
          (Real.exp (-b * t) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [leechAxisProfile, hc, cuspProfile_smul, leechAxisKernel_one_eq hy]
    ring
  simp only [leechAxisRadialProfile, radialProfile, cuspProfileSinc, hint, hc]
  ring

end E8Leech
