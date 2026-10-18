import E8Leech.RayHomotopyCauchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cauchy's theorem on the ideal triangle `(0, 1, ∞)`

Known answer first: sweep the triangle by rays from the center `1/2` of its lower side, the
semicircle `|z − 1/2| = 1/2`. In the angle `θ` the outer side is the vertical line `Re z = 1`
(`r = 1/(2 cos θ)`), then a horizontal cut at height `H` (`r = H / sin θ`), then the line
`Re z = 0` (`r = −1/(2 cos θ)`). `ray_cauchy` on the three angular pieces, the cancellation of the
two inner rays, and the limits `θ₀ → 0` (the cusps `1` and `0`) and `H → ∞` give

  `∫₀^∞ i g(1 + it) dt − ∫₀^∞ i g(it) dt = ∫₀^π (i/2) e^{iθ} g(1/2 + e^{iθ}/2) dθ`

for `g` holomorphic on the open triangle, continuous on its closure in the upper half-plane and
`O((1 + Im z)⁻²)` there.
-/

noncomputable section

namespace E8Leech

open Complex Set MeasureTheory intervalIntegral Filter Topology
open scoped Real Interval

/-- The open ideal triangle `(0, 1, ∞)`. -/
def idealTriangle : Set ℂ := {z | 0 < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 / 2 < ‖z - 1 / 2‖}

/-- Its closure in the upper half-plane (the cusps `0, 1` removed). -/
def idealTriangleCl : Set ℂ := {z | 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 / 2 ≤ ‖z - 1 / 2‖}

/-- The triangle cut off at height `η`. -/
def idealTriangleAbove (η : ℝ) : Set ℂ :=
  {z | η < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 / 2 < ‖z - 1 / 2‖}

/-- Radial profiles, seen from the center `1/2`. -/
def rSemi : ℝ → ℝ := fun _ => 1 / 2
def rRight : ℝ → ℝ := fun θ => 1 / (2 * Real.cos θ)
def rTop (H : ℝ) : ℝ → ℝ := fun θ => H / Real.sin θ
def rLeft : ℝ → ℝ := fun θ => -1 / (2 * Real.cos θ)

/-- The integrand of `g dz` on the semicircle in the angle parametrization. -/
def semicircleIntegrand (g : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (I / 2 * cexp (θ * I)) * g (1 / 2 + cexp (θ * I) / 2)

theorem isOpen_idealTriangleAbove (η : ℝ) : IsOpen (idealTriangleAbove η) := by
  have h1 : IsOpen {z : ℂ | η < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h3 : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have h4 : IsOpen {z : ℂ | 1 / 2 < ‖z - 1 / 2‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  exact h1.inter (h2.inter (h3.inter h4))

theorem idealTriangleAbove_subset {η : ℝ} (hη : 0 ≤ η) :
    idealTriangleAbove η ⊆ idealTriangle := fun _ hz =>
  ⟨hη.trans_lt hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩

theorem closure_idealTriangleAbove_subset {η : ℝ} (hη : 0 < η) :
    closure (idealTriangleAbove η) ⊆ idealTriangleCl := by
  have hclosed : IsClosed {z : ℂ | η ≤ z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 / 2 ≤ ‖z - 1 / 2‖} := by
    have h1 : IsClosed {z : ℂ | η ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have h2 : IsClosed {z : ℂ | 0 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h3 : IsClosed {z : ℂ | z.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
    have h4 : IsClosed {z : ℂ | 1 / 2 ≤ ‖z - 1 / 2‖} :=
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
    exact h1.inter (h2.inter (h3.inter h4))
  have hsub : idealTriangleAbove η ⊆
      {z : ℂ | η ≤ z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 / 2 ≤ ‖z - 1 / 2‖} := fun z hz =>
    ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  intro z hz
  have h := closure_minimal hsub hclosed hz
  exact ⟨hη.trans_le h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Points on rays from `1/2` -/

theorem half_add_re (ρ θ : ℝ) :
    ((1 / 2 : ℂ) + (ρ : ℂ) * cexp (θ * I)).re = 1 / 2 + ρ * Real.cos θ := by
  simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem half_add_im (ρ θ : ℝ) :
    ((1 / 2 : ℂ) + (ρ : ℂ) * cexp (θ * I)).im = ρ * Real.sin θ := by
  simp [Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem norm_half_add_sub (ρ θ : ℝ) :
    ‖(1 / 2 : ℂ) + (ρ : ℂ) * cexp (θ * I) - 1 / 2‖ = |ρ| := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem half_add_mem_above {η ρ θ : ℝ} (hρ : 1 / 2 < ρ) (hc : |ρ * Real.cos θ| < 1 / 2)
    (hs : η < ρ * Real.sin θ) :
    (1 / 2 : ℂ) + (ρ : ℂ) * cexp (θ * I) ∈ idealTriangleAbove η := by
  rw [abs_lt] at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [half_add_im]; exact hs
  · rw [half_add_re]; linarith
  · rw [half_add_re]; linarith
  · rw [norm_half_add_sub, abs_of_pos (by linarith)]; exact hρ

theorem half_add_mem_cl {ρ θ : ℝ} (hρ : 1 / 2 ≤ ρ) (hc : |ρ * Real.cos θ| ≤ 1 / 2)
    (hs : 0 < ρ * Real.sin θ) :
    (1 / 2 : ℂ) + (ρ : ℂ) * cexp (θ * I) ∈ idealTriangleCl := by
  rw [abs_le] at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [half_add_im]; exact hs
  · rw [half_add_re]; linarith
  · rw [half_add_re]; linarith
  · rw [norm_half_add_sub, abs_of_pos (by linarith)]; exact hρ

theorem raySweep_half (r₁ r₂ : ℝ → ℝ) (s θ : ℝ) :
    raySweep (1 / 2) r₁ r₂ s θ =
      (1 / 2 : ℂ) + (((1 - s) * r₁ θ + s * r₂ θ : ℝ) : ℂ) * cexp (θ * I) := rfl

/-! ## The explicit sides -/

theorem cexp_mul_I_eq (θ : ℝ) : cexp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem polarCurve_rRight {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    polarCurve (1 / 2) rRight θ = 1 + I * ((Real.tan θ / 2 : ℝ) : ℂ) := by
  have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  rw [polarCurve, rRight, cexp_mul_I_eq, Real.tan_eq_sin_div_cos]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  ring

theorem polarCurve_rLeft {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    polarCurve (1 / 2) rLeft θ = I * ((-Real.tan θ / 2 : ℝ) : ℂ) := by
  have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  rw [polarCurve, rLeft, cexp_mul_I_eq, Real.tan_eq_sin_div_cos]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_neg]
  field_simp
  ring

theorem polarCurve_rTop (H : ℝ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    polarCurve (1 / 2) (rTop H) θ =
      ((1 / 2 + H * Real.cos θ / Real.sin θ : ℝ) : ℂ) + I * H := by
  have hs : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  rw [polarCurve, rTop, cexp_mul_I_eq]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_add]
  field_simp
  ring

theorem polarCurve_rSemi (θ : ℝ) :
    polarCurve (1 / 2) rSemi θ = 1 / 2 + cexp (θ * I) / 2 := by
  rw [polarCurve, rSemi]
  push_cast
  ring

theorem polarVelocity_rSemi (θ : ℝ) :
    polarVelocity rSemi (deriv rSemi) θ = I / 2 * cexp (θ * I) := by
  have h : deriv rSemi θ = 0 := by
    show deriv (fun _ : ℝ => (1 / 2 : ℝ)) θ = 0
    exact deriv_const θ _
  rw [polarVelocity, h, rSemi]
  push_cast
  ring

/-- The velocity of a polar curve agrees with that of any local reparametrization. -/
theorem polarVelocity_eq_of_eventuallyEq {c : ℂ} {r : ℝ → ℝ} {θ : ℝ} {p : ℝ → ℂ} {p' : ℂ}
    (hr : DifferentiableAt ℝ r θ) (hp : HasDerivAt p p' θ)
    (hev : polarCurve c r =ᶠ[𝓝 θ] p) : polarVelocity r (deriv r) θ = p' :=
  (hasDerivAt_polarCurve c hr.hasDerivAt).unique (hp.congr_of_eventuallyEq hev)

theorem differentiableAt_rRight {θ : ℝ} (hθ : Real.cos θ ≠ 0) : DifferentiableAt ℝ rRight θ := by
  unfold rRight
  exact (differentiableAt_const _).div (Real.differentiableAt_cos.const_mul _)
    (mul_ne_zero two_ne_zero hθ)

theorem differentiableAt_rLeft {θ : ℝ} (hθ : Real.cos θ ≠ 0) : DifferentiableAt ℝ rLeft θ := by
  unfold rLeft
  exact (differentiableAt_const _).div (Real.differentiableAt_cos.const_mul _)
    (mul_ne_zero two_ne_zero hθ)

theorem differentiableAt_rTop (H : ℝ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    DifferentiableAt ℝ (rTop H) θ := by
  unfold rTop
  exact (differentiableAt_const _).div Real.differentiableAt_sin hθ

theorem polarVelocity_rRight {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    polarVelocity rRight (deriv rRight) θ = I * ((1 / (2 * Real.cos θ ^ 2) : ℝ) : ℂ) := by
  have hp : HasDerivAt (fun θ : ℝ => 1 + I * ((Real.tan θ / 2 : ℝ) : ℂ))
      (I * ((1 / (2 * Real.cos θ ^ 2) : ℝ) : ℂ)) θ := by
    have h := ((((Real.hasDerivAt_tan hθ).div_const 2).ofReal_comp).const_mul I).const_add 1
    have e : (1 / Real.cos θ ^ 2 / 2 : ℝ) = 1 / (2 * Real.cos θ ^ 2) := by ring
    rw [e] at h
    exact h
  refine polarVelocity_eq_of_eventuallyEq (c := 1 / 2) (differentiableAt_rRight hθ) hp ?_
  filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hθ] with x hx
  exact polarCurve_rRight hx

theorem polarVelocity_rLeft {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    polarVelocity rLeft (deriv rLeft) θ = I * ((-(1 / (2 * Real.cos θ ^ 2)) : ℝ) : ℂ) := by
  have hp : HasDerivAt (fun θ : ℝ => I * ((-Real.tan θ / 2 : ℝ) : ℂ))
      (I * ((-(1 / (2 * Real.cos θ ^ 2)) : ℝ) : ℂ)) θ := by
    have h := (((Real.hasDerivAt_tan hθ).neg.div_const 2).ofReal_comp).const_mul I
    have e : (-(1 / Real.cos θ ^ 2) / 2 : ℝ) = -(1 / (2 * Real.cos θ ^ 2)) := by ring
    rw [e] at h
    exact h
  refine polarVelocity_eq_of_eventuallyEq (c := 1 / 2) (differentiableAt_rLeft hθ) hp ?_
  filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hθ] with x hx
  exact polarCurve_rLeft hx

theorem hasDerivAt_cot_part (H : ℝ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (fun θ : ℝ => 1 / 2 + H * Real.cos θ / Real.sin θ)
      (-(H / Real.sin θ ^ 2)) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul H).div (Real.hasDerivAt_sin θ) hθ
  have h2 := h.const_add (1 / 2)
  have e : (H * -Real.sin θ * Real.sin θ - H * Real.cos θ * Real.cos θ) / Real.sin θ ^ 2 =
      -(H / Real.sin θ ^ 2) := by
    rw [show H * -Real.sin θ * Real.sin θ - H * Real.cos θ * Real.cos θ =
      -H * (Real.sin θ ^ 2 + Real.cos θ ^ 2) by ring, Real.sin_sq_add_cos_sq]
    ring
  rw [e] at h2
  exact h2

theorem polarVelocity_rTop (H : ℝ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    polarVelocity (rTop H) (deriv (rTop H)) θ = ((-(H / Real.sin θ ^ 2)) : ℝ) := by
  have hp : HasDerivAt (fun θ : ℝ => ((1 / 2 + H * Real.cos θ / Real.sin θ : ℝ) : ℂ) + I * H)
      ((-(H / Real.sin θ ^ 2) : ℝ) : ℂ) θ := by
    have h := (hasDerivAt_cot_part H hθ).ofReal_comp.add_const (I * H)
    exact h
  refine polarVelocity_eq_of_eventuallyEq (c := 1 / 2) (differentiableAt_rTop H hθ) hp ?_
  filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hθ] with x hx
  exact polarCurve_rTop H hx

/-! ## Trigonometric facts on the three angular pieces -/

theorem cos_lt_one_of_mem {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : |Real.cos θ| < 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have h := Real.sin_sq_add_cos_sq θ
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (Real.cos θ + 1), sq_nonneg (Real.cos θ - 1)]

theorem cos_pos_of_piece {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

theorem sin_arctan_eq (H : ℝ) :
    Real.sin (Real.arctan (2 * H)) = 2 * H * Real.cos (Real.arctan (2 * H)) := by
  have hc := Real.cos_arctan_pos (2 * H)
  have ht := Real.tan_arctan (2 * H)
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hc.ne'] at ht
  exact ht

theorem arctan_two_mul_pos {H : ℝ} (hH : 0 < H) : 0 < Real.arctan (2 * H) :=
  Real.arctan_pos.mpr (by linarith)

/-- On `[θ₁, π − θ₁]` with `tan θ₁ = 2H` the horizontal cut stays over `[0, 1]`. -/
theorem two_mul_abs_cos_le_sin {H θ : ℝ} (hH : 0 < H) (h1 : Real.arctan (2 * H) ≤ θ)
    (h2 : θ ≤ π - Real.arctan (2 * H)) : 2 * H * |Real.cos θ| ≤ Real.sin θ := by
  set θ₁ := Real.arctan (2 * H) with hθ₁
  have hpos : 0 < θ₁ := arctan_two_mul_pos hH
  have hlt : θ₁ < π / 2 := Real.arctan_lt_pi_div_two _
  have hs₁ := sin_arctan_eq H
  rw [← hθ₁] at hs₁
  have key : ∀ φ : ℝ, θ₁ ≤ φ → φ ≤ π / 2 → 2 * H * |Real.cos φ| ≤ Real.sin φ := by
    intro φ hφ1 hφ2
    have hcφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hφ2⟩
    have hc : Real.cos φ ≤ Real.cos θ₁ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]) hφ1
    have hsn : Real.sin θ₁ ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hφ2 hφ1
    rw [abs_of_nonneg hcφ]
    nlinarith
  rcases le_total θ (π / 2) with hθ | hθ
  · exact key θ h1 hθ
  · have h := key (π - θ) (by linarith) (by linarith)
    rwa [Real.cos_pi_sub, abs_neg, Real.sin_pi_sub] at h

/-! ## The swept regions lie in the triangle -/

theorem sweep_right_mem {θ₀ θ₁ s θ : ℝ} (h0 : 0 < θ₀) (h1 : θ₁ < π / 2)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo θ₀ θ₁) :
    raySweep (1 / 2) rSemi rRight s θ ∈ idealTriangleAbove (Real.sin θ₀ / 4) := by
  rcases hs with ⟨hs0, hs1⟩
  rcases hθ with ⟨hθ0, hθ1⟩
  have hc := cos_pos_of_piece (h0.trans hθ0) (hθ1.trans h1)
  have hc1 : Real.cos θ < 1 := (abs_lt.mp (cos_lt_one_of_mem (h0.trans hθ0)
    (by linarith [Real.pi_pos]))).2
  have hsin : Real.sin θ₀ ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) hθ0.le
  have hs₀ : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [raySweep_half]
  set ρ := (1 - s) * rSemi θ + s * rRight θ with hρ
  have hρc : ρ * Real.cos θ = (1 - s) * Real.cos θ / 2 + s / 2 := by
    rw [hρ, rSemi, rRight]; field_simp
  have hρgt : 1 / 2 < ρ := by
    rw [hρ, rSemi, rRight]
    have : 1 / 2 < 1 / (2 * Real.cos θ) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
    nlinarith
  refine half_add_mem_above hρgt ?_ ?_
  · rw [hρc, abs_lt]; constructor <;> nlinarith
  · nlinarith

theorem sweep_left_mem {θ₀ θ₁ s θ : ℝ} (h0 : 0 < θ₀) (h1 : θ₁ < π / 2)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (π - θ₁) (π - θ₀)) :
    raySweep (1 / 2) rSemi rLeft s θ ∈ idealTriangleAbove (Real.sin θ₀ / 4) := by
  rcases hs with ⟨hs0, hs1⟩
  rcases hθ with ⟨hθ0, hθ1⟩
  have hc : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have hc1 : -1 < Real.cos θ := (abs_lt.mp (cos_lt_one_of_mem (by linarith [Real.pi_pos])
    (by linarith))).1
  have hsin : Real.sin θ₀ ≤ Real.sin θ := by
    rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)
  have hs₀ : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [raySweep_half]
  set ρ := (1 - s) * rSemi θ + s * rLeft θ with hρ
  have hρc : ρ * Real.cos θ = (1 - s) * Real.cos θ / 2 - s / 2 := by
    have hcne : Real.cos θ ≠ 0 := hc.ne
    rw [hρ, rSemi, rLeft]; field_simp; ring
  have hρgt : 1 / 2 < ρ := by
    rw [hρ, rSemi, rLeft]
    have : 1 / 2 < -1 / (2 * Real.cos θ) := by
      rw [lt_div_iff_of_neg (by linarith)]; linarith
    nlinarith
  refine half_add_mem_above hρgt ?_ ?_
  · rw [hρc, abs_lt]; constructor <;> nlinarith
  · nlinarith

theorem sweep_top_mem {θ₀ H s θ : ℝ} (h0 : 0 < θ₀) (hH : 1 ≤ H) (hθ₀ : θ₀ < Real.arctan (2 * H))
    (hs : s ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (Real.arctan (2 * H)) (π - Real.arctan (2 * H))) :
    raySweep (1 / 2) rSemi (rTop H) s θ ∈ idealTriangleAbove (Real.sin θ₀ / 4) := by
  rcases hs with ⟨hs0, hs1⟩
  rcases hθ with ⟨hθ0, hθ1⟩
  set θ₁ := Real.arctan (2 * H) with hθ₁
  have hθ₁lt : θ₁ < π / 2 := Real.arctan_lt_pi_div_two _
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (h0.trans (hθ₀.trans hθ0))
    (by linarith [Real.pi_pos])
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hkey := two_mul_abs_cos_le_sin (by linarith) hθ0.le hθ1.le
  have hc1 := cos_lt_one_of_mem (h0.trans (hθ₀.trans hθ0)) (by linarith [Real.pi_pos])
  have hsin : Real.sin θ₀ ≤ Real.sin θ := by
    rcases le_total θ (π / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h
        (by linarith)
    · rw [← Real.sin_pi_sub θ]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
        (by linarith)
  have hs₀ : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [raySweep_half]
  set ρ := (1 - s) * rSemi θ + s * rTop H θ with hρ
  have hHs : 1 ≤ H / Real.sin θ := by rw [le_div_iff₀ hsinpos]; nlinarith
  have hρgt : 1 / 2 < ρ := by rw [hρ, rSemi, rTop]; nlinarith
  refine half_add_mem_above hρgt ?_ ?_
  · have habs : |ρ * Real.cos θ| ≤ (1 - s) * |Real.cos θ| / 2 + s / 2 := by
      rw [hρ, rSemi, rTop, abs_mul]
      have hρnn : 0 ≤ (1 - s) * (1 / 2) + s * (H / Real.sin θ) := by positivity
      rw [abs_of_nonneg hρnn]
      have : H / Real.sin θ * |Real.cos θ| ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hsinpos]; linarith
      nlinarith [abs_nonneg (Real.cos θ)]
    have : (1 - s) * |Real.cos θ| / 2 + s / 2 < 1 / 2 := by nlinarith
    linarith
  · nlinarith

/-! ## The four sides as ordinary integrals -/

theorem continuousOn_comp_line {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl) {p : ℝ → ℂ}
    (hp : Continuous p) {T : Set ℝ} (hT : ∀ t ∈ T, p t ∈ idealTriangleCl) :
    ContinuousOn (fun t => g (p t)) T :=
  hgc.comp hp.continuousOn hT

theorem one_add_I_mul_mem {t : ℝ} (ht : 0 < t) : (1 : ℂ) + I * t ∈ idealTriangleCl := by
  refine ⟨by simpa using ht, by simp, by simp, ?_⟩
  have : (1 : ℂ) + I * t - 1 / 2 = (1 / 2 : ℝ) + (t : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]
  calc (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt ((1 / 2) ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

theorem I_mul_mem {t : ℝ} (ht : 0 < t) : I * (t : ℂ) ∈ idealTriangleCl := by
  refine ⟨by simpa using ht, by simp, by simp, ?_⟩
  have : I * (t : ℂ) - 1 / 2 = (-1 / 2 : ℝ) + (t : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]
  calc (1 / 2 : ℝ) = Real.sqrt ((-1 / 2) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]; norm_num
    _ ≤ Real.sqrt ((-1 / 2) ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

theorem top_mem {x H : ℝ} (hH : 1 ≤ H) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x : ℂ) + I * H ∈ idealTriangleCl := by
  refine ⟨by simp; linarith, by simpa using hx0, by simpa using hx1, ?_⟩
  have : (x : ℂ) + I * H - 1 / 2 = (x - 1 / 2 : ℝ) + (H : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]
  calc (1 / 2 : ℝ) ≤ Real.sqrt (H ^ 2) := by rw [Real.sqrt_sq (by linarith)]; linarith
    _ ≤ Real.sqrt ((x - 1 / 2) ^ 2 + H ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

theorem semicircle_mem {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    (1 / 2 : ℂ) + cexp (θ * I) / 2 ∈ idealTriangleCl := by
  have h := half_add_mem_cl (ρ := 1 / 2) (θ := θ) le_rfl ?_ ?_
  · convert h using 1; push_cast; ring
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := (cos_lt_one_of_mem h0 hπ).le
    linarith
  · have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
    positivity

theorem integral_right_side {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < π / 2) :
    (∫ θ in a..b, polarVelocity rRight (deriv rRight) θ * g (polarCurve (1 / 2) rRight θ)) =
      ∫ t in Real.tan a / 2..Real.tan b / 2, I * g (1 + I * t) := by
  have hcos : ∀ θ ∈ uIcc a b, Real.cos θ ≠ 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ
    exact (cos_pos_of_piece (ha.trans_le hθ.1) (hθ.2.trans_lt hb)).ne'
  have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ => Real.tan θ / 2)
      (1 / (2 * Real.cos θ ^ 2)) θ := fun θ hθ => by
    have h := (Real.hasDerivAt_tan (hcos θ hθ)).div_const 2
    have e : (1 / Real.cos θ ^ 2 / 2 : ℝ) = 1 / (2 * Real.cos θ ^ 2) := by ring
    rwa [e] at h
  have hcont : ContinuousOn (fun θ => 1 / (2 * Real.cos θ ^ 2)) (uIcc a b) :=
    continuousOn_const.div (continuousOn_const.mul (Real.continuous_cos.continuousOn.pow 2))
      fun θ hθ => mul_ne_zero two_ne_zero (pow_ne_zero 2 (hcos θ hθ))
  have himg : ∀ t ∈ (fun θ => Real.tan θ / 2) '' uIcc a b, (1 : ℂ) + I * t ∈ idealTriangleCl := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [uIcc_of_le hab] at hθ
    have hθ0 : 0 < θ := ha.trans_le hθ.1
    have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 (hθ.2.trans_lt hb)
    exact one_add_I_mul_mem (by positivity)
  have hG : ContinuousOn (fun t : ℝ => I * g (1 + I * t)) ((fun θ => Real.tan θ / 2) '' uIcc a b) :=
    continuousOn_const.mul (continuousOn_comp_line hgc (by fun_prop) himg)
  rw [← intervalIntegral.integral_deriv_smul_comp' hderiv hcont hG]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [Function.comp_apply]
  rw [polarVelocity_rRight (hcos θ hθ), polarCurve_rRight (hcos θ hθ), Complex.real_smul]
  ring

theorem integral_left_side {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl) {a b : ℝ}
    (ha : π / 2 < a) (hab : a ≤ b) (hb : b < π) :
    (∫ θ in a..b, polarVelocity rLeft (deriv rLeft) θ * g (polarCurve (1 / 2) rLeft θ)) =
      ∫ t in -Real.tan a / 2..-Real.tan b / 2, I * g (I * t) := by
  have hcosneg : ∀ θ ∈ uIcc a b, Real.cos θ < 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (ha.trans_le hθ.1) (by linarith [hθ.2])
  have hcos : ∀ θ ∈ uIcc a b, Real.cos θ ≠ 0 := fun θ hθ => (hcosneg θ hθ).ne
  have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ => -Real.tan θ / 2)
      (-(1 / (2 * Real.cos θ ^ 2))) θ := fun θ hθ => by
    have h := (Real.hasDerivAt_tan (hcos θ hθ)).neg.div_const 2
    have e : (-(1 / Real.cos θ ^ 2) / 2 : ℝ) = -(1 / (2 * Real.cos θ ^ 2)) := by ring
    rwa [e] at h
  have hcont : ContinuousOn (fun θ => -(1 / (2 * Real.cos θ ^ 2))) (uIcc a b) :=
    (continuousOn_const.div (continuousOn_const.mul (Real.continuous_cos.continuousOn.pow 2))
      fun θ hθ => mul_ne_zero two_ne_zero (pow_ne_zero 2 (hcos θ hθ))).neg
  have himg : ∀ t ∈ (fun θ => -Real.tan θ / 2) '' uIcc a b, I * (t : ℂ) ∈ idealTriangleCl := by
    rintro _ ⟨θ, hθ, rfl⟩
    have ht : Real.tan θ < 0 := by
      rw [Real.tan_eq_sin_div_cos]
      rw [uIcc_of_le hab] at hθ
      have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2])
      exact div_neg_of_pos_of_neg hs (hcosneg θ (by rw [uIcc_of_le hab]; exact hθ))
    exact I_mul_mem (by linarith)
  have hG : ContinuousOn (fun t : ℝ => I * g (I * t)) ((fun θ => -Real.tan θ / 2) '' uIcc a b) :=
    continuousOn_const.mul (continuousOn_comp_line hgc (by fun_prop) himg)
  rw [← intervalIntegral.integral_deriv_smul_comp' hderiv hcont hG]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [Function.comp_apply]
  rw [polarVelocity_rLeft (hcos θ hθ), polarCurve_rLeft (hcos θ hθ), Complex.real_smul]
  ring

theorem integral_top_side {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl) {H : ℝ}
    (hH : 1 ≤ H) :
    (∫ θ in Real.arctan (2 * H)..π - Real.arctan (2 * H),
        polarVelocity (rTop H) (deriv (rTop H)) θ * g (polarCurve (1 / 2) (rTop H) θ)) =
      -∫ x in (0 : ℝ)..1, g (x + I * H) := by
  set θ₁ := Real.arctan (2 * H) with hθ₁
  have hpos : 0 < θ₁ := arctan_two_mul_pos (by linarith)
  have hlt : θ₁ < π / 2 := Real.arctan_lt_pi_div_two _
  have hle : θ₁ ≤ π - θ₁ := by linarith
  have hsin : ∀ θ ∈ uIcc θ₁ (π - θ₁), 0 < Real.sin θ := fun θ hθ => by
    rw [uIcc_of_le hle] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hderiv : ∀ θ ∈ uIcc θ₁ (π - θ₁),
      HasDerivAt (fun θ => 1 / 2 + H * Real.cos θ / Real.sin θ) (-(H / Real.sin θ ^ 2)) θ :=
    fun θ hθ => hasDerivAt_cot_part H (hsin θ hθ).ne'
  have hcont : ContinuousOn (fun θ => -(H / Real.sin θ ^ 2)) (uIcc θ₁ (π - θ₁)) :=
    (continuousOn_const.div (Real.continuous_sin.continuousOn.pow 2)
      fun θ hθ => pow_ne_zero 2 (hsin θ hθ).ne').neg
  have himg : ∀ x ∈ (fun θ => 1 / 2 + H * Real.cos θ / Real.sin θ) '' uIcc θ₁ (π - θ₁),
      (x : ℂ) + I * H ∈ idealTriangleCl := by
    rintro _ ⟨θ, hθ, rfl⟩
    have hs := hsin θ hθ
    rw [uIcc_of_le hle] at hθ
    have hk := two_mul_abs_cos_le_sin (by linarith) hθ.1 hθ.2
    have hb : |H * Real.cos θ / Real.sin θ| ≤ 1 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < H), abs_of_pos hs,
        div_le_iff₀ hs]
      linarith
    rw [abs_le] at hb
    exact top_mem hH (by linarith) (by linarith)
  have hG : ContinuousOn (fun x : ℝ => g (x + I * H))
      ((fun θ => 1 / 2 + H * Real.cos θ / Real.sin θ) '' uIcc θ₁ (π - θ₁)) :=
    continuousOn_comp_line hgc (by fun_prop) himg
  have hv1 : 1 / 2 + H * Real.cos θ₁ / Real.sin θ₁ = 1 := by
    have hs := sin_arctan_eq H
    rw [← hθ₁] at hs
    have hc : 0 < Real.cos θ₁ := Real.cos_arctan_pos _
    rw [hs]; field_simp; ring
  have hv0 : 1 / 2 + H * Real.cos (π - θ₁) / Real.sin (π - θ₁) = 0 := by
    have hs := sin_arctan_eq H
    rw [← hθ₁] at hs
    have hc : 0 < Real.cos θ₁ := Real.cos_arctan_pos _
    rw [Real.cos_pi_sub, Real.sin_pi_sub, hs]; field_simp; ring
  have h := intervalIntegral.integral_deriv_smul_comp' hderiv hcont hG
  simp only [hv1, hv0] at h
  rw [← intervalIntegral.integral_symm, ← h]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [Function.comp_apply]
  rw [polarVelocity_rTop H (hsin θ hθ).ne', polarCurve_rTop H (hsin θ hθ).ne', Complex.real_smul]

theorem integral_semicircle_side (g : ℂ → ℂ) (a b : ℝ) :
    (∫ θ in a..b, polarVelocity rSemi (deriv rSemi) θ * g (polarCurve (1 / 2) rSemi θ)) =
      ∫ θ in a..b, semicircleIntegrand g θ := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [polarVelocity_rSemi, polarCurve_rSemi, semicircleIntegrand]

/-! ## The truncated identity -/

theorem rayIntegral_congr {c : ℂ} {r₁ r₂ r₁' r₂' : ℝ → ℝ} (g : ℂ → ℂ) {θ : ℝ}
    (h₁ : r₁ θ = r₁' θ) (h₂ : r₂ θ = r₂' θ) :
    rayIntegral c r₁ r₂ g θ = rayIntegral c r₁' r₂' g θ := by
  simp only [rayIntegral, raySweep, h₁, h₂]

theorem rRight_arctan {H : ℝ} (hH : H ≠ 0) :
    rRight (Real.arctan (2 * H)) = rTop H (Real.arctan (2 * H)) := by
  have hs := sin_arctan_eq H
  have hc := Real.cos_arctan_pos (2 * H)
  simp only [rRight, rTop]
  rw [hs]
  field_simp

theorem rTop_pi_sub_arctan {H : ℝ} (hH : H ≠ 0) :
    rTop H (π - Real.arctan (2 * H)) = rLeft (π - Real.arctan (2 * H)) := by
  have hs := sin_arctan_eq H
  have hc := Real.cos_arctan_pos (2 * H)
  simp only [rTop, rLeft, Real.sin_pi_sub, Real.cos_pi_sub]
  rw [hs]
  field_simp

theorem contDiffOn_rRight {a b : ℝ} (ha : 0 < a) (hb : b < π / 2) :
    ContDiffOn ℝ 2 rRight (Icc a b) := by
  have h : ContDiffOn ℝ 2 (fun θ : ℝ => (1 : ℝ) / (2 * Real.cos θ)) (Icc a b) :=
    contDiffOn_const.div (contDiffOn_const.mul Real.contDiff_cos.contDiffOn) fun θ hθ =>
      mul_ne_zero two_ne_zero (cos_pos_of_piece (ha.trans_le hθ.1) (hθ.2.trans_lt hb)).ne'
  exact h

theorem contDiffOn_rLeft {a b : ℝ} (ha : π / 2 < a) (hb : b < π) :
    ContDiffOn ℝ 2 rLeft (Icc a b) := by
  have h : ContDiffOn ℝ 2 (fun θ : ℝ => (-1 : ℝ) / (2 * Real.cos θ)) (Icc a b) :=
    contDiffOn_const.div (contDiffOn_const.mul Real.contDiff_cos.contDiffOn) fun θ hθ =>
      mul_ne_zero two_ne_zero
        (Real.cos_neg_of_pi_div_two_lt_of_lt (ha.trans_le hθ.1)
          (by linarith [hθ.2, Real.pi_pos])).ne
  exact h

theorem contDiffOn_rTop (H : ℝ) {a b : ℝ} (ha : 0 < a) (hb : b < π) :
    ContDiffOn ℝ 2 (rTop H) (Icc a b) := by
  have h : ContDiffOn ℝ 2 (fun θ : ℝ => H / Real.sin θ) (Icc a b) :=
    contDiffOn_const.div Real.contDiff_sin.contDiffOn fun θ hθ =>
      (Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hθ.1) (hθ.2.trans_lt hb)).ne'
  exact h

theorem continuousOn_semicircleIntegrand {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl)
    {a b : ℝ} (ha : 0 < a) (hb : b < π) : ContinuousOn (semicircleIntegrand g) (Icc a b) := by
  have hp : Continuous fun θ : ℝ => (1 / 2 : ℂ) + cexp (θ * I) / 2 := by fun_prop
  have h := continuousOn_comp_line hgc hp (T := Icc a b) fun θ hθ =>
    semicircle_mem (ha.trans_le hθ.1) (hθ.2.trans_lt hb)
  exact (Continuous.continuousOn (by fun_prop)).mul h

/-- Cauchy's theorem on the triangle cut at the angle `θ₀` (both cusps) and the height `H`. -/
theorem idealTriangle_truncated {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g idealTriangle)
    (hgc : ContinuousOn g idealTriangleCl) {θ₀ H : ℝ} (hθ₀ : 0 < θ₀) (hH : 1 ≤ H)
    (hθ : θ₀ < Real.arctan (2 * H)) :
    (∫ t in Real.tan θ₀ / 2..H, I * g (1 + I * t)) - (∫ x in (0 : ℝ)..1, g (x + I * H)) -
        (∫ t in Real.tan θ₀ / 2..H, I * g (I * t)) -
        (∫ θ in θ₀..π - θ₀, semicircleIntegrand g θ) =
      rayIntegral (1 / 2) rSemi rLeft g (π - θ₀) - rayIntegral (1 / 2) rSemi rRight g θ₀ := by
  set θ₁ := Real.arctan (2 * H) with hθ₁
  have hθ₁lt : θ₁ < π / 2 := Real.arctan_lt_pi_div_two _
  have hs₀ : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθ₀ (by linarith [Real.pi_pos])
  have hη : 0 < Real.sin θ₀ / 4 := by positivity
  have hU := isOpen_idealTriangleAbove (Real.sin θ₀ / 4)
  have hgU : DifferentiableOn ℂ g (idealTriangleAbove (Real.sin θ₀ / 4)) :=
    hg.mono (idealTriangleAbove_subset hη.le)
  have hgcU : ContinuousOn g (closure (idealTriangleAbove (Real.sin θ₀ / 4))) :=
    hgc.mono (closure_idealTriangleAbove_subset hη)
  have hsemi : ∀ a b : ℝ, ContDiffOn ℝ 2 rSemi (Icc a b) := fun _ _ => contDiffOn_const
  have p1 := ray_cauchy (c := 1 / 2) hθ (hsemi _ _) (contDiffOn_rRight hθ₀ hθ₁lt) hU hgU hgcU
    fun s hs θ hθ' => sweep_right_mem hθ₀ hθ₁lt hs hθ'
  have p2 := ray_cauchy (c := 1 / 2) (a := θ₁) (b := π - θ₁) (by linarith) (hsemi _ _)
    (contDiffOn_rTop H (arctan_two_mul_pos (by linarith)) (by linarith)) hU hgU hgcU
    fun s hs θ hθ' => sweep_top_mem hθ₀ hH hθ hs hθ'
  have p3 := ray_cauchy (c := 1 / 2) (a := π - θ₁) (b := π - θ₀) (by linarith) (hsemi _ _)
    (contDiffOn_rLeft (by linarith) (by linarith)) hU hgU hgcU
    fun s hs θ hθ' => sweep_left_mem hθ₀ hθ₁lt hs hθ'
  have htan : Real.tan θ₁ / 2 = H := by rw [hθ₁, Real.tan_arctan]; ring
  rw [integral_right_side hgc hθ₀ hθ.le hθ₁lt, htan, integral_semicircle_side] at p1
  rw [integral_top_side hgc hH, integral_semicircle_side] at p2
  rw [integral_left_side hgc (by linarith) (by linarith) (by linarith [Real.pi_pos]),
    integral_semicircle_side, Real.tan_pi_sub, Real.tan_pi_sub, neg_neg, neg_neg, htan] at p3
  have j1 : rayIntegral (1 / 2) rSemi rRight g θ₁ = rayIntegral (1 / 2) rSemi (rTop H) g θ₁ :=
    rayIntegral_congr g rfl (rRight_arctan (by linarith : H ≠ 0))
  have j2 : rayIntegral (1 / 2) rSemi (rTop H) g (π - θ₁) =
      rayIntegral (1 / 2) rSemi rLeft g (π - θ₁) :=
    rayIntegral_congr g rfl (rTop_pi_sub_arctan (by linarith : H ≠ 0))
  have hint : ∀ a b : ℝ, θ₀ ≤ a → a ≤ b → b ≤ π - θ₀ →
      IntervalIntegrable (semicircleIntegrand g) volume a b := fun a b ha hab hb => by
    have hc := continuousOn_semicircleIntegrand hgc hθ₀ (by linarith : π - θ₀ < π)
    refine (hc.mono ?_).intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsum : (∫ θ in θ₀..θ₁, semicircleIntegrand g θ) +
      (∫ θ in θ₁..π - θ₁, semicircleIntegrand g θ) +
        (∫ θ in π - θ₁..π - θ₀, semicircleIntegrand g θ) =
      ∫ θ in θ₀..π - θ₀, semicircleIntegrand g θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hint _ _ le_rfl hθ.le (by linarith)) (hint _ _ hθ.le (by linarith) (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals
        (hint _ _ le_rfl (by linarith) (by linarith)) (hint _ _ (by linarith) (by linarith) le_rfl)]
  rw [intervalIntegral.integral_symm (Real.tan θ₀ / 2) H] at p3
  rw [← hsum]
  linear_combination p1 + p2 + p3 + j1 + j2

/-! ## Removing the cuts -/

theorem norm_rayIntegral_le {c : ℂ} {r₁ r₂ : ℝ → ℝ} {g : ℂ → ℂ} {θ M : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖g (raySweep c r₁ r₂ s θ)‖ ≤ M) :
    ‖rayIntegral c r₁ r₂ g θ‖ ≤ |r₂ θ - r₁ θ| * M := by
  unfold rayIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := |r₂ θ - r₁ θ| * M)
    (f := fun s => (((r₂ θ - r₁ θ : ℝ) : ℂ) * cexp (θ * I)) * g (raySweep c r₁ r₂ s θ))
    (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM s (Ioc_subset_Icc_self hs)) (abs_nonneg _))
  simpa using h

theorem sweep_right_cl {θ s : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hs : s ∈ Icc (0 : ℝ) 1) :
    raySweep (1 / 2) rSemi rRight s θ ∈ idealTriangleCl := by
  rcases hs with ⟨hs0, hs1⟩
  have hc := cos_pos_of_piece h0 h1
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsn := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [raySweep_half]
  have hρc : ((1 - s) * rSemi θ + s * rRight θ) * Real.cos θ =
      (1 - s) * Real.cos θ / 2 + s / 2 := by
    rw [rSemi, rRight]; field_simp
  have hge : 1 / 2 ≤ 1 / (2 * Real.cos θ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  refine half_add_mem_cl ?_ ?_ ?_
  · rw [rSemi, rRight]; nlinarith
  · rw [hρc, abs_le]; constructor <;> nlinarith
  · rw [rSemi, rRight]
    have : 0 < (1 - s) * (1 / 2) + s * (1 / (2 * Real.cos θ)) := by nlinarith
    positivity

theorem sweep_left_cl {θ s : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hs : s ∈ Icc (0 : ℝ) 1) :
    raySweep (1 / 2) rSemi rLeft s (π - θ) ∈ idealTriangleCl := by
  have h := sweep_right_cl h0 h1 hs
  have e : rLeft (π - θ) = rRight θ := by
    simp only [rLeft, rRight, Real.cos_pi_sub]; ring
  rw [raySweep_half] at h ⊢
  rw [e, show rSemi (π - θ) = rSemi θ from rfl]
  rcases h with ⟨him, hre0, hre1, hn⟩
  set ρ := (1 - s) * rSemi θ + s * rRight θ
  rw [half_add_im] at him
  rw [half_add_re] at hre0 hre1
  rw [norm_half_add_sub] at hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [half_add_im, Real.sin_pi_sub]; exact him
  · rw [half_add_re, Real.cos_pi_sub]; linarith
  · rw [half_add_re, Real.cos_pi_sub]; linarith
  · rw [norm_half_add_sub]; exact hn

theorem tendsto_rRight_sub : Tendsto (fun θ => rRight θ - rSemi θ) (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt (fun θ => rRight θ - rSemi θ) 0 := by
    unfold rRight rSemi
    exact ((continuousAt_const.div (continuousAt_const.mul Real.continuous_cos.continuousAt)
      (by simp)).sub continuousAt_const)
  have h0 : rRight 0 - rSemi 0 = 0 := by norm_num [rRight, rSemi]
  simpa [h0] using h.tendsto

theorem integrableOn_Ioi_of_bound {F : ℝ → ℂ} {C : ℝ} (hF : ContinuousOn F (Ioi 0))
    (hb : ∀ t : ℝ, 0 < t → ‖F t‖ ≤ C / (1 + t) ^ 2) : IntegrableOn F (Ioi 0) := by
  have hfin : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 := by rw [Module.finrank_self]; norm_num
  have hint : IntegrableOn (fun t : ℝ => C * (1 + ‖t‖) ^ (-(2 : ℝ))) (Ioi 0) :=
    ((integrable_one_add_norm (μ := (volume : Measure ℝ)) hfin).const_mul C).integrableOn
  refine hint.mono' (hF.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg ht'.le, Real.rpow_neg (by positivity), Real.rpow_two]
  calc ‖F t‖ ≤ C / (1 + t) ^ 2 := hb t ht'
    _ = C * ((1 + t) ^ 2)⁻¹ := by rw [div_eq_mul_inv]

theorem tendsto_integral_trunc {F : ℝ → ℂ} {C : ℝ} (hF : IntegrableOn F (Ioi 0))
    (hb : ∀ t : ℝ, 0 < t → ‖F t‖ ≤ C) {a b : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (ha0 : ∀ n, 0 ≤ a n) (hb' : Tendsto b atTop atTop) (hb0 : ∀ n, 0 ≤ b n) :
    Tendsto (fun n => ∫ t in a n..b n, F t) atTop (𝓝 (∫ t in Ioi 0, F t)) := by
  have hII : ∀ x : ℝ, 0 ≤ x → IntervalIntegrable F volume 0 x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr (hF.mono_set Ioc_subset_Ioi_self)
  have e : ∀ n, (∫ t in a n..b n, F t) = (∫ t in (0 : ℝ)..b n, F t) - ∫ t in (0 : ℝ)..a n, F t :=
    fun n => (intervalIntegral.integral_interval_sub_left (hII _ (hb0 n)) (hII _ (ha0 n))).symm
  simp_rw [e]
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hF hb'
  have h2 : Tendsto (fun n => ∫ t in (0 : ℝ)..a n, F t) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun n => C * |a n - 0|) atTop (𝓝 0) := by
      have := (ha.sub_const 0).abs.const_mul C
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le (ha0 n)] at ht
    exact hb t ht.1
  simpa using h1.sub h2

/-- **Cauchy's theorem on the ideal triangle `(0, 1, ∞)`.** -/
theorem idealTriangle_cauchy {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g idealTriangle)
    (hgc : ContinuousOn g idealTriangleCl) {C : ℝ}
    (hC : ∀ z ∈ idealTriangleCl, ‖g z‖ ≤ C / (1 + z.im) ^ 2) :
    (∫ t in Ioi (0 : ℝ), I * g (1 + I * t)) - (∫ t in Ioi (0 : ℝ), I * g (I * t)) =
      ∫ θ in (0 : ℝ)..π, semicircleIntegrand g θ := by
  have hC0 : 0 ≤ C := by
    have h := hC _ (one_add_I_mul_mem one_pos)
    have hpos : 0 < (1 + ((1 : ℂ) + I * (1 : ℝ)).im) ^ 2 := by norm_num
    have := (norm_nonneg _).trans h
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hpos)
  have hCb : ∀ z ∈ idealTriangleCl, ‖g z‖ ≤ C := fun z hz => by
    refine (hC z hz).trans ?_
    have : 1 ≤ (1 + z.im) ^ 2 := by nlinarith [hz.1]
    exact div_le_self hC0 this
  -- the two vertical sides
  set F₁ : ℝ → ℂ := fun t => I * g (1 + I * t) with hF₁
  set F₂ : ℝ → ℂ := fun t => I * g (I * t) with hF₂
  have hF₁c : ContinuousOn F₁ (Ioi 0) :=
    continuousOn_const.mul (continuousOn_comp_line hgc (by fun_prop) fun t ht =>
      one_add_I_mul_mem ht)
  have hF₂c : ContinuousOn F₂ (Ioi 0) :=
    continuousOn_const.mul (continuousOn_comp_line hgc (by fun_prop) fun t ht => I_mul_mem ht)
  have hF₁b : ∀ t : ℝ, 0 < t → ‖F₁ t‖ ≤ C / (1 + t) ^ 2 := fun t ht => by
    simp only [hF₁, norm_mul, Complex.norm_I, one_mul]
    simpa using hC _ (one_add_I_mul_mem ht)
  have hF₂b : ∀ t : ℝ, 0 < t → ‖F₂ t‖ ≤ C / (1 + t) ^ 2 := fun t ht => by
    simp only [hF₂, norm_mul, Complex.norm_I, one_mul]
    simpa using hC _ (I_mul_mem ht)
  have hF₁i := integrableOn_Ioi_of_bound hF₁c hF₁b
  have hF₂i := integrableOn_Ioi_of_bound hF₂c hF₂b
  have hle : ∀ t : ℝ, 0 < t → C / (1 + t) ^ 2 ≤ C := fun t ht =>
    div_le_self hC0 (by nlinarith)
  -- the parameters
  set θs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hθs
  set Hs : ℕ → ℝ := fun n => (n : ℝ) + 1 with hHs
  have hθpos : ∀ n, 0 < θs n := fun n => by simp only [hθs]; positivity
  have hθle : ∀ n, θs n ≤ 1 / 2 := fun n => by
    simp only [hθs]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [n.cast_nonneg' (α := ℝ)]
  have hHge : ∀ n, 1 ≤ Hs n := fun n => by simp only [hHs]; linarith [n.cast_nonneg' (α := ℝ)]
  have hθarc : ∀ n, θs n < Real.arctan (2 * Hs n) := fun n => by
    have h1 : Real.arctan 1 < Real.arctan (2 * Hs n) :=
      Real.arctan_strictMono (by linarith [hHge n])
    rw [Real.arctan_one] at h1
    linarith [hθle n, Real.pi_gt_three]
  have hθt : Tendsto θs atTop (𝓝 0) := by
    simp only [hθs]
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hHt : Tendsto Hs atTop atTop := by
    simp only [hHs]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have htan : Tendsto (fun n => Real.tan (θs n) / 2) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun θ => Real.sin θ / Real.cos θ) 0 :=
      Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt (by simp)
    have h := (hcont.tendsto.comp hθt).div_const 2
    simp only [Function.comp_def, Real.sin_zero, zero_div] at h
    refine h.congr fun n => ?_
    rw [Real.tan_eq_sin_div_cos]
  have htan0 : ∀ n, 0 ≤ Real.tan (θs n) / 2 := fun n =>
    div_nonneg (Real.tan_pos_of_pos_of_lt_pi_div_two (hθpos n)
      (by linarith [hθle n, Real.pi_gt_three])).le (by norm_num)
  have hA := tendsto_integral_trunc hF₁i (fun t ht => (hF₁b t ht).trans (hle t ht)) htan htan0
    hHt fun n => (zero_le_one.trans (hHge n))
  have hD := tendsto_integral_trunc hF₂i (fun t ht => (hF₂b t ht).trans (hle t ht)) htan htan0
    hHt fun n => (zero_le_one.trans (hHge n))
  -- the horizontal cut
  have hTop : Tendsto (fun n => ∫ x in (0 : ℝ)..1, g (x + I * Hs n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun n => C / (1 + Hs n) ^ 2 * |(1 : ℝ) - 0|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (1 + Hs n) ^ 2) atTop atTop :=
        tendsto_atTop_mono (fun n => by nlinarith [hHge n]) hHt
      have := (tendsto_const_nhds (x := C)).div_atTop h1
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hm := top_mem (hHge n) hx.1.le hx.2
    have := hC _ hm
    simpa using this
  -- the semicircle
  set S := semicircleIntegrand g with hS
  have hSc : ContinuousOn S (Ioo 0 π) := by
    have hp : Continuous fun θ : ℝ => (1 / 2 : ℂ) + cexp (θ * I) / 2 := by fun_prop
    have h := continuousOn_comp_line hgc hp (T := Ioo 0 π) fun θ hθ => semicircle_mem hθ.1 hθ.2
    exact (Continuous.continuousOn (by fun_prop)).mul h
  have hSb : ∀ θ ∈ Ioo (0 : ℝ) π, ‖S θ‖ ≤ C / 2 := fun θ hθ => by
    simp only [hS, semicircleIntegrand, norm_mul, norm_div, Complex.norm_I,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_ofNat]
    have := hCb _ (semicircle_mem hθ.1 hθ.2)
    linarith
  have hae : ∀ᵐ x : ℝ, x ≠ π := by
    simp [ae_iff, measure_singleton]
  have hSb' : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ π → ∀ᵐ x : ℝ, x ∈ Ι a b → ‖S x‖ ≤ C / 2 := by
    intro a b ha hab hb
    filter_upwards [hae] with x hxπ hx
    rw [uIoc_of_le hab] at hx
    exact hSb x ⟨by linarith [hx.1], lt_of_le_of_ne (by linarith [hx.2]) hxπ⟩
  have hSi : IntervalIntegrable S volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
    refine Integrable.mono' (integrable_const (C / 2)) (hSc.aestronglyMeasurable measurableSet_Ioo)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hSb x hx
  have hSi' : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ π → IntervalIntegrable S volume a b :=
    fun a b ha hab hb => hSi.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc ha hb)
  have hSemi : Tendsto (fun n => ∫ θ in θs n..π - θs n, S θ) atTop (𝓝 (∫ θ in (0 : ℝ)..π, S θ)) := by
    have e : ∀ n, (∫ θ in θs n..π - θs n, S θ) =
        (∫ θ in (0 : ℝ)..π, S θ) - (∫ θ in (0 : ℝ)..θs n, S θ) - ∫ θ in π - θs n..π, S θ := by
      intro n
      have h1 := hθle n
      have h0 := hθpos n
      have hπ := Real.pi_gt_three
      rw [← intervalIntegral.integral_add_adjacent_intervals
          (hSi' 0 (θs n) le_rfl (hθpos n).le (by linarith))
          (hSi' (θs n) π (hθpos n).le (by linarith) le_rfl),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hSi' (θs n) (π - θs n) (hθpos n).le (by linarith) (by linarith))
          (hSi' (π - θs n) π (by linarith) (by linarith) le_rfl)]
      ring
    simp_rw [e]
    have hsmall : ∀ f : ℕ → ℝ × ℝ, (∀ n, 0 ≤ (f n).1 ∧ (f n).1 ≤ (f n).2 ∧ (f n).2 ≤ π ∧
        |(f n).2 - (f n).1| = θs n) →
        Tendsto (fun n => ∫ θ in (f n).1..(f n).2, S θ) atTop (𝓝 0) := by
      intro f hf
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hlim : Tendsto (fun n => C / 2 * θs n) atTop (𝓝 0) := by
        simpa using hθt.const_mul (C / 2)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
        (hSb' _ _ (hf n).1 (hf n).2.1 (hf n).2.2.1)
      rwa [(hf n).2.2.2] at h
    have h1 := hsmall (fun n => (0, θs n)) fun n =>
      ⟨le_rfl, (hθpos n).le, by linarith [hθle n, Real.pi_gt_three],
        by simp [abs_of_pos (hθpos n)]⟩
    have h2 := hsmall (fun n => (π - θs n, π)) fun n =>
      ⟨by linarith [hθle n, Real.pi_gt_three], by linarith [hθpos n], le_rfl,
        by simp [abs_of_pos (hθpos n)]⟩
    simpa using (tendsto_const_nhds.sub h1).sub h2
  -- the two cusp rays
  have hR1 : Tendsto (fun n => rayIntegral (1 / 2) rSemi rRight g (θs n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun n => |rRight (θs n) - rSemi (θs n)| * C) atTop (𝓝 0) := by
      have := ((tendsto_rRight_sub.comp hθt).abs).mul_const C
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    exact norm_rayIntegral_le fun s hs =>
      hCb _ (sweep_right_cl (hθpos n) (by linarith [hθle n, Real.pi_gt_three]) hs)
  have hR3 : Tendsto (fun n => rayIntegral (1 / 2) rSemi rLeft g (π - θs n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun n => |rRight (θs n) - rSemi (θs n)| * C) atTop (𝓝 0) := by
      have := ((tendsto_rRight_sub.comp hθt).abs).mul_const C
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have e : rLeft (π - θs n) - rSemi (π - θs n) = rRight (θs n) - rSemi (θs n) := by
      simp only [rLeft, rRight, rSemi, Real.cos_pi_sub]; ring
    rw [← e]
    exact norm_rayIntegral_le fun s hs =>
      hCb _ (sweep_left_cl (hθpos n) (by linarith [hθle n, Real.pi_gt_three]) hs)
  -- combine
  have hid : ∀ n, (∫ t in Real.tan (θs n) / 2..Hs n, F₁ t) - (∫ x in (0 : ℝ)..1, g (x + I * Hs n)) -
      (∫ t in Real.tan (θs n) / 2..Hs n, F₂ t) - (∫ θ in θs n..π - θs n, S θ) =
      rayIntegral (1 / 2) rSemi rLeft g (π - θs n) - rayIntegral (1 / 2) rSemi rRight g (θs n) :=
    fun n => idealTriangle_truncated hg hgc (hθpos n) (hHge n) (hθarc n)
  have hL := ((hA.sub hTop).sub hD).sub hSemi
  have hR := hR3.sub hR1
  have := tendsto_nhds_unique (hL.congr hid) hR
  simp only [sub_zero, sub_self] at this
  linear_combination this


end E8Leech
