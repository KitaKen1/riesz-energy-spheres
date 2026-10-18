import E8Leech.CKMRVLaplaceSmooth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The radial profiles of the CKMRV generating functions are smooth (P4d-5c)

In (5.1) the kernel integral is multiplied by `4 sin²(b/2)` (`b = πr²`). With (5.3)/(5.4)
(`CKMRVLaplaceFull`) the product becomes

  `P(b) = 4 sin²(b/2) ∫₀^∞ (K − G)(τ, it) e^{−bt} dt + 4 sin²(b/2) Ĝ(b)`,

and `4 sin²(b/2) Ĝ(b)` is a combination of `sinc(b/2)²`, `b·sinc(b/2)²` and, for the Leech
lattice, the same functions of `b − 2π` (`sin²(b/2) = sin²((b − 2π)/2)`). `sinc` is `C^∞`
(it is `dslope sin 0`, analytic at `0`), so `P` is `C^∞` on `b > −π` (`b > −π/2` for the Leech
plus kernel), and `P(b) = 4 sin²(b/2) ∫₀^∞ K(τ, it) e^{−bt} dt` on the range of (5.1).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ContDiff

theorem contDiff_sinc : ContDiff ℝ ∞ Real.sinc := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨p, hp⟩ := (Real.analyticAt_sin (x := 0))
    have h := hp.has_fpower_series_dslope_fslope
    rw [← Real.sinc_eq_dslope] at h
    exact h.analyticAt.contDiffAt
  · have heq : Real.sinc =ᶠ[𝓝 x] fun y => Real.sin y / y := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy using Real.sinc_of_ne_zero hy
    exact ((Real.contDiff_sin.contDiffAt).div contDiffAt_id hx).congr_of_eventuallyEq heq

/-- `4 sin²(b/2) / (b − c)² = sinc((b − c)/2)²` when `c ∈ 2πℤ`; here `c = 0` or `c = 2π`. -/
theorem four_sin_sq_div_sq {b c : ℝ} (hc : Real.sin (c / 2) = 0) (hb : b - c ≠ 0) :
    4 * Real.sin (b / 2) ^ 2 / (b - c) ^ 2 = Real.sinc ((b - c) / 2) ^ 2 := by
  have hcos : Real.cos (c / 2) ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq (c / 2)]
  have hs : Real.sin (b / 2) ^ 2 = Real.sin ((b - c) / 2) ^ 2 := by
    rw [show (b - c) / 2 = b / 2 - c / 2 by ring, Real.sin_sub, hc]
    simp only [mul_zero, sub_zero, mul_pow, hcos, mul_one]
  rw [Real.sinc_of_ne_zero (by intro h; apply hb; linarith), hs, div_pow]
  field_simp
  ring

/-- The `sinc`-form of `4 sin²(b/2) Ĝ(b)`. -/
def cuspProfileSinc (A B C D : ℂ) (c b : ℝ) : ℂ :=
  (A + B * ((b - c : ℝ) : ℂ)) * (Real.sinc ((b - c) / 2) ^ 2 : ℝ) +
    (C + D * (b : ℂ)) * (Real.sinc (b / 2) ^ 2 : ℝ)

theorem contDiff_cuspProfileSinc (A B C D : ℂ) (c : ℝ) :
    ContDiff ℝ ∞ (cuspProfileSinc A B C D c) := by
  have hs := contDiff_sinc
  unfold cuspProfileSinc
  have h1 : ContDiff ℝ ∞ fun b : ℝ => ((Real.sinc ((b - c) / 2) ^ 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((hs.comp ((contDiff_id.sub contDiff_const).div_const 2)).pow 2)
  have h2 : ContDiff ℝ ∞ fun b : ℝ => ((Real.sinc (b / 2) ^ 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((hs.comp (contDiff_id.div_const 2)).pow 2)
  have h3 : ContDiff ℝ ∞ fun b : ℝ => ((b - c : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)
  have h4 : ContDiff ℝ ∞ fun b : ℝ => (b : ℂ) := Complex.ofRealCLM.contDiff
  exact ((contDiff_const.add (contDiff_const.mul h3)).mul h1).add
    ((contDiff_const.add (contDiff_const.mul h4)).mul h2)

theorem four_sin_sq_mul_cuspProfileLaplace (A B C D : ℂ) {c b : ℝ}
    (hc : Real.sin (c / 2) = 0) (hb0 : b ≠ 0) (hbc : b - c ≠ 0) :
    (4 * Real.sin (b / 2) ^ 2 : ℝ) * cuspProfileLaplace A B C D c b =
      cuspProfileSinc A B C D c b := by
  have h1 := four_sin_sq_div_sq hc hbc
  have h2 := four_sin_sq_div_sq (c := 0) (by simp) (by simpa using hb0)
  simp only [sub_zero] at h2
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
  have hbc' : (b : ℂ) - c ≠ 0 := by exact_mod_cast hbc
  rw [cuspProfileLaplace, cuspProfileSinc, ← h1, ← h2]
  push_cast
  field_simp
  ring

/-! ## The profiles -/

/-- The radial profile `P(b) = 4 sin²(b/2) ∫(K − G) e^{−bt} + 4 sin²(b/2) Ĝ(b)`, written with
`sinc` so that it is visibly smooth. -/
def radialProfile (g : ℝ → ℂ) (A B C D : ℂ) (c b : ℝ) : ℂ :=
  (4 * Real.sin (b / 2) ^ 2 : ℝ) * (∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ)) +
    cuspProfileSinc A B C D c b

theorem contDiffOn_radialProfile {g : ℝ → ℂ} {A B C D : ℂ} {a c : ℝ}
    (hg : ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ)) (Ioi a)) :
    ContDiffOn ℝ ∞ (radialProfile g A B C D c) (Ioi a) := by
  have hsin : ContDiff ℝ ∞ fun b : ℝ => ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
      ((Real.contDiff_sin.comp (contDiff_id.div_const 2)).pow 2))
  exact (hsin.contDiffOn.mul hg).add (contDiff_cuspProfileSinc A B C D c).contDiffOn

/-- On the range of (5.1) the profile is `4 sin²(b/2) ∫ K e^{−bt}`. -/
theorem radialProfile_eq {k g : ℝ → ℂ} {A B C D : ℂ} {c b : ℝ}
    (hsplit : ∫ t in Ioi 0, k t * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ)) + cuspProfileLaplace A B C D c b)
    (hc : Real.sin (c / 2) = 0) (hb0 : b ≠ 0) (hbc : b - c ≠ 0) :
    radialProfile g A B C D c b =
      (4 * Real.sin (b / 2) ^ 2 : ℝ) * ∫ t in Ioi 0, k t * (Real.exp (-b * t) : ℂ) := by
  rw [radialProfile, hsplit, mul_add, four_sin_sq_mul_cuspProfileLaplace A B C D hc hb0 hbc]

theorem sin_two_pi_div_two : Real.sin (2 * π / 2) = 0 := by
  rw [show 2 * π / 2 = π by ring, Real.sin_pi]


/-! ## `d = 8`, minus kernel -/

/-- The radial profile of `K₋⁽⁸⁾` at `τ`. -/
def ckmrvEightMinusProfile (τ : ℍ) : ℝ → ℂ :=
  radialProfile (fun t => ckmrvEightMinusKernel τ (imagPt t) - ckmrvEightMinusG τ (imagPt t)) 0 0
    (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 τ)
    (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 τ * (4 * Real.log 2) +
      eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ)) 0

theorem contDiffOn_ckmrvEightMinusProfile {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ContDiffOn ℝ ∞ (ckmrvEightMinusProfile τ) (Ioi (-π)) :=
  contDiffOn_radialProfile (contDiffOn_ckmrvEightMinus_sub_G_laplace hτ)

theorem ckmrvEightMinusProfile_eq {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ} (hb : 0 < b) :
    ckmrvEightMinusProfile τ b = (4 * Real.sin (b / 2) ^ 2 : ℝ) *
      ∫ t in Ioi 0, ckmrvEightMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) :=
  radialProfile_eq (integral_ckmrvEightMinusKernel_eq_sub_G hτ hb) (by simp) hb.ne'
    (by simpa using hb.ne')

end E8Leech
