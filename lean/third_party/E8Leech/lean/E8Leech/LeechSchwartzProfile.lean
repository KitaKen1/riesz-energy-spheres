import E8Leech.CKMRVSchwartz
import E8Leech.CKMRVCombinedKernels
import E8Leech.TruncatedRadialProfile

/-!
# The radial profile of the Leech kernel transforms, for all radii

In dimension 24 the transform `4 sin²(π|x|²/2) ∫₀^∞ K(iβ, it) e^{−π|x|²t} dt` converges for
`|x|² > 2` only. `CKMRVSchwartz` continues it to a Schwartz function by subtracting the cusp
profile `A t e^{2πt} + B e^{2πt} + C t + D` of the kernel, but states the result for `|x|² > 2`.
The sign conditions for `|x|² ≤ 2` (CKMRV (6.4)(2), (3)) need the continued formula itself.

* `exists_schwartz_of_cusp_split_profile`: the assembly of `CKMRVSchwartz`, also returning
  `φ(x) = radialProfile (g − cuspProfile) (π|x|²)` for all `x`.
* `leechAxisCusp s β`: the cusp coefficients of `(K₊ + s K₋)/2` at `τ = iβ`; `s = 1` is `𝒦`,
  `s = −1` is `𝒦̂`.
* `exists_leechAxis`: a continuous function on `(0, ∞)` equal to `(K₊ + s K₋)/2 (iβ, i·)` off the
  two removable points, with its bounds and the (5.3)/(5.4) split.
* `exists_schwartz_leechAxis`: the Schwartz function of the transform with its profile.
* `leechAxis_radialProfile_truncated`: the profile in the truncated form of
  `TruncatedRadialProfile`, for every `b > 0`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ContDiff

/-! ## The assembly, with the profile -/

section Assembly

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The assembly `exists_schwartz_of_cusp_split`, with the value of the Schwartz function at
every point: it is the radial profile at `π|x|²`. -/
theorem exists_schwartz_of_cusp_split_profile {g : ℝ → ℂ} {A B C D : ℂ} {a c a' S₁ : ℝ}
    (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (ha' : a' < -(π / 2))
    (hsmooth : ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile A B C D c t) *
      (Real.exp (-b * t) : ℂ)) (Ioi a'))
    (hc : Real.sin (c / 2) = 0) (hS₁ : 0 ≤ S₁) (hcS : c ≤ π * S₁)
    (hsplit : ∀ b : ℝ, π * S₁ < b → ∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile A B C D c t) * (Real.exp (-b * t) : ℂ)) +
        cuspProfileLaplace A B C D c b) :
    ∃ φ : SchwartzMap F ℂ,
      (∀ x : F, φ x = radialProfile (fun t => g t - cuspProfile A B C D c t) A B C D c
        (π * ‖x‖ ^ 2)) ∧
      ∀ x : F, S₁ < ‖x‖ ^ 2 →
        φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  have hπ := Real.pi_pos
  set prof : ℝ → ℂ := fun s => radialProfile (fun t => g t - cuspProfile A B C D c t) A B C D c
    (π * s) with hprof
  have hsmooth' : ContDiffOn ℝ ∞ prof (Ioi (a' / π)) := by
    refine (contDiffOn_radialProfile hsmooth).comp (contDiff_const.mul contDiff_id).contDiffOn
      fun s hs => ?_
    show a' < π * s
    have h : a' / π < s := hs
    rw [div_lt_iff₀ hπ] at h
    linarith
  have ha'' : a' / π < -1 / 2 := by
    rw [div_lt_iff₀ hπ]
    linarith
  have heq : ∀ s : ℝ, S₁ < s → prof s = ((4 * Real.sin (π * s / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ) := by
    intro s hs
    have hb : π * S₁ < π * s := mul_lt_mul_of_pos_left hs hπ
    have hb0 : 0 < π * s := lt_of_le_of_lt (mul_nonneg hπ.le hS₁) hb
    have hbc : 0 < π * s - c := by linarith
    exact radialProfile_eq (hsplit _ hb) hc hb0.ne' hbc.ne'
  have hdecay := decay_of_eventually_eq_sin_sq hg hg0 hginf heq
  have happly := RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg_apply
    (F := F) prof (contDiff_cutoffC_mul_of_contDiffOn_Ioi ha'' hsmooth')
    (schwartz_bounds_of_decay (by linarith) hsmooth' hdecay)
  refine ⟨RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg (F := F)
    prof (contDiff_cutoffC_mul_of_contDiffOn_Ioi ha'' hsmooth')
    (schwartz_bounds_of_decay (by linarith) hsmooth' hdecay), fun x => happly x, fun x hx => ?_⟩
  rw [happly x, heq _ hx]

end Assembly

/-! ## The cusp profile is linear in its coefficients -/

theorem cuspProfile_combo (s : ℂ) (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : ℂ) (c t : ℝ) :
    cuspProfile ((A₁ + s * A₂) / 2) ((B₁ + s * B₂) / 2) ((C₁ + s * C₂) / 2) ((D₁ + s * D₂) / 2) c t =
      (cuspProfile A₁ B₁ C₁ D₁ c t + s * cuspProfile A₂ B₂ C₂ D₂ c t) / 2 := by
  simp only [cuspProfile]
  ring

theorem isBigO_half_combo {l : Filter ℝ} {f g : ℝ → ℂ} {w : ℝ → ℝ} (s : ℂ)
    (hf : f =O[l] w) (hg : g =O[l] w) : (fun t => (f t + s * g t) / 2) =O[l] w := by
  have h := (hf.add (hg.const_mul_left s)).const_mul_left (1 / 2 : ℂ)
  refine h.congr_left fun t => ?_
  ring

/-! ## The cusp coefficients of the Leech kernels on the axis -/

/-- Cusp coefficients `(A, B, C, D)` of `K₋⁽²⁴⁾(τ, ·)`:
`K₋(τ, it) = A t e^{2πt} + B e^{2πt} + C t + D + O(t e^{−πt})`. -/
def leechMinusCusp (τ : ℍ) : Fin 4 → ℂ :=
  ![ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant τ)),
    ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant τ) +
      (leechMinusBeta τ + leechMinusAlpha τ)),
    ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant τ *
      (720 - kleinModularJ τ))),
    ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant τ *
      (720 - kleinModularJ τ)) +
      ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) - leechMinusNZeroC τ))]

/-- Cusp coefficients `(A, B, C, D)` of `K₊⁽²⁴⁾(τ, ·)`. -/
def leechPlusCusp (τ : ℍ) : Fin 4 → ℂ :=
  ![(1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a τ),
    (1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a τ,
    (1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c τ),
    (1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c τ]

/-- Cusp coefficients of `(K₊ + s K₋)/2` at `τ = iβ`. For `s = 1` this is `𝒦⁽²⁴⁾`, for `s = −1`
it is `𝒦̂⁽²⁴⁾`. -/
def leechAxisCusp (s : ℂ) (β : ℝ) (k : Fin 4) : ℂ :=
  (leechPlusCusp (imagPt β) k + s * leechMinusCusp (imagPt β) k) / 2

/-- The cusp profile of `(K₊ + s K₋)/2` at `τ = iβ`. -/
def leechAxisProfile (s : ℂ) (β t : ℝ) : ℂ :=
  cuspProfile (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
    (leechAxisCusp s β 3) (2 * π) t

/-- The kernel `(K₊ + s K₋)/2` on the axis. -/
def leechAxisKernel (s : ℂ) (β t : ℝ) : ℂ :=
  (ckmrvLeechPlusKernel (imagPt β) (imagPt t) + s * ckmrvLeechMinusKernel (imagPt β) (imagPt t)) / 2

theorem leechAxisKernel_one (β t : ℝ) :
    leechAxisKernel 1 β t = ckmrvLeechKernel (imagPt β) (imagPt t) := by
  simp [leechAxisKernel, ckmrvLeechKernel]

theorem leechAxisKernel_neg_one (β t : ℝ) :
    leechAxisKernel (-1) β t = ckmrvLeechHatKernel (imagPt β) (imagPt t) := by
  simp only [leechAxisKernel, ckmrvLeechHatKernel]
  ring

/-- **The Leech kernels on the axis.** For `β ≠ 1` there is a continuous function on `(0, ∞)` equal
to `(K₊ + s K₋)/2 (iβ, it)` off the removable points `t = β, 1/β`, of size `O(e^{−π/t})` at `0` and
`O(t e^{2πt})` at `∞`, whose difference with the cusp profile is `O(t e^{−3πt/4})` at `∞`. -/
theorem exists_leechAxis (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧
      (∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = leechAxisKernel s β x) ∧
      g =O[𝓝[>] (0 : ℝ)] (fun t => Real.exp (-π / t)) ∧
      g =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) ∧
      g =O[atTop] (fun t => t * Real.exp (2 * π * t)) ∧
      (fun t => g t - leechAxisProfile s β t) =O[atTop] fun t => t * Real.exp ((-π + π / 4) * t) := by
  obtain ⟨gp, hgp, hgpK⟩ := exists_ckmrvLeechPlus_axis hβ hβ1
  obtain ⟨gm, hgm, hgmK⟩ := exists_ckmrvLeechMinus_axis hβ hβ1
  refine ⟨fun t => (gp t + s * gm t) / 2, (hgp.add (continuousOn_const.mul hgm)).div_const 2,
    fun x h1 h2 => by simp only [leechAxisKernel, hgpK x h1 h2, hgmK x h1 h2], ?_, ?_, ?_, ?_⟩
  · exact isBigO_half_combo s (isBigO_leechPlusAxis_zero hβ hgpK)
      (isBigO_leechMinusAxis_zero hβ hgmK)
  · exact isBigO_half_combo s (isBigO_leechPlusAxis_zero_one hβ hgpK)
      (isBigO_leechMinusAxis_zero_one hβ hgmK)
  · exact isBigO_half_combo s (isBigO_leechPlusAxis_atTop hgpK) (isBigO_leechMinusAxis_atTop hgmK)
  · have hm : (fun t => gm t - cuspProfile (leechMinusCusp (imagPt β) 0)
        (leechMinusCusp (imagPt β) 1) (leechMinusCusp (imagPt β) 2)
        (leechMinusCusp (imagPt β) 3) (2 * π) t) =O[atTop]
          fun t => t * Real.exp ((-π + π / 4) * t) := by
      refine (isBigO_leechMinusAxis_sub_G hgmK).trans (IsBigO.of_bound 1 ?_)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [one_mul, Real.norm_of_nonneg (mul_nonneg ht (Real.exp_pos _).le),
        Real.norm_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ht
      nlinarith [Real.pi_pos]
    have hp : (fun t => gp t - cuspProfile (leechPlusCusp (imagPt β) 0)
        (leechPlusCusp (imagPt β) 1) (leechPlusCusp (imagPt β) 2)
        (leechPlusCusp (imagPt β) 3) (2 * π) t) =O[atTop]
          fun t => t * Real.exp ((-π + π / 4) * t) := isBigO_leechPlusAxis_sub_G hgpK
    refine (isBigO_half_combo s hp hm).congr_left fun t => ?_
    simp only [leechAxisProfile, leechAxisCusp, cuspProfile_combo]
    ring

/-! ## The Schwartz function of the transform, with its profile -/

section Schwartz

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The transform of `(K₊ + s K₋)/2 (iβ, ·)` is Schwartz, with its profile for all radii.**
For `|x|² > 2` it is `4 sin²(π|x|²/2) ∫₀^∞ (K₊ + s K₋)/2 (iβ, it) e^{−π|x|²t} dt`. -/
theorem exists_schwartz_leechAxis (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ (g : ℝ → ℂ) (φ : SchwartzMap F ℂ), ContinuousOn g (Ioi 0) ∧
      (∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = leechAxisKernel s β x) ∧
      g =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) ∧
      ((fun t => g t - leechAxisProfile s β t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t)) ∧
      (∀ x : F, φ x = radialProfile (fun t => g t - leechAxisProfile s β t)
        (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3)
        (2 * π) (π * ‖x‖ ^ 2)) ∧
      ∀ x : F, 2 < ‖x‖ ^ 2 →
        φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, leechAxisKernel s β t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, hg, hgK, hg0, hg01, hginf, hsub⟩ := exists_leechAxis s hβ hβ1
  have hsub' : (fun t => g t - cuspProfile (leechAxisCusp s β 0) (leechAxisCusp s β 1)
      (leechAxisCusp s β 2) (leechAxisCusp s β 3) (2 * π) t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t) := hsub
  have hsmooth : ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile (leechAxisCusp s β 0)
      (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3) (2 * π) t) *
        (Real.exp (-b * t) : ℂ)) (Ioi (-π + π / 4)) :=
    contDiffOn_laplace (hg.sub (continuous_cuspProfile _ _ _ _ (2 * π)).continuousOn)
      (hg01.sub (((continuous_cuspProfile _ _ _ _ (2 * π)).tendsto 0).mono_left
        nhdsWithin_le_nhds |>.isBigO_one ℝ)) hsub'
  obtain ⟨φ, hφprof, hφ⟩ := exists_schwartz_of_cusp_split_profile F hg hg0 hginf
    (by linarith [Real.pi_pos] : -π + π / 4 < -(π / 2)) hsmooth sin_two_pi_div_two zero_le_two
    (by linarith [Real.pi_pos] : 2 * π ≤ π * 2)
    (fun b hb => integral_eq_sub_cuspProfile hg hg01 hsub' (by linarith [Real.pi_pos])
      (by positivity) (by linarith))
  exact ⟨g, φ, hg, hgK, hg01, hsub, hφprof,
    fun x hx => by rw [hφ x hx, setIntegral_eq_of_eq_off_two hgK]⟩

end Schwartz

/-- **The truncated form of the Leech profile**, for every `b > 0` and every cut `p ≥ 0`. With
`A, B` the coefficients of `t e^{2πt}` and `e^{2πt}`, the profile is
`4 sin²(b/2) [∫₀^p g e^{−bt} + ∫_p^∞ (g − A t e^{2πt} − B e^{2πt}) e^{−bt}]
  + sinc²((b − 2π)/2) e^{−(b − 2π)p} (A + (B + pA)(b − 2π))`. -/
theorem leechAxis_radialProfile_truncated (s : ℂ) {β : ℝ} {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0)) (hg01 : g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hsub : (fun t => g t - leechAxisProfile s β t) =O[atTop]
      fun t => t * Real.exp ((-π + π / 4) * t)) {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    radialProfile (fun t => g t - leechAxisProfile s β t)
        (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2) (leechAxisCusp s β 3)
        (2 * π) b =
      ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
        ((∫ t in Ioc 0 p, g t * (Real.exp (-b * t) : ℂ)) +
          ∫ t in Ioi p, (g t - (leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
            leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ)) +
        ((Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * p) : ℝ) : ℂ) *
          (leechAxisCusp s β 0 + (leechAxisCusp s β 1 + p * leechAxisCusp s β 0) *
            ((b - 2 * π : ℝ) : ℂ)) :=
  radialProfile_truncated hg hg01 hsub (by linarith [Real.pi_pos]) hb sin_two_pi_div_two hp

end E8Leech
