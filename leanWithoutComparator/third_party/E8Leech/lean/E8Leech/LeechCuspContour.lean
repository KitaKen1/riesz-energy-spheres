import E8Leech.CKMRVFourier
import E8Leech.IdealTriangleCauchy
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# A contour shift for the cusp parts of the Leech contour identity

`γ_ρ(a) = a⁻¹² e^{−πρ/a}` is the Fourier transform of the Gaussian `e^{−πa|x|²}` in dimension 24 at
`|ξ|² = ρ` (`gaussHat_twentyFour`). For an entire function `f`, `σ = ±i` and a cut `p > 0`, the
function `F(t) = f(t) γ_ρ(t − σ)` is holomorphic on `ℂ ∖ {σ}`. The arc `t = s/(1 − σs)`,
`s ∈ (0, ∞)`, from `0` to `σ` and the path `0 → p → p + σ → σ` lie in the disc
`B(p, √(p² + 1))`, whose boundary passes through `σ`. A primitive of `F` on the disc and the decay
of `γ_ρ(t − σ)` at `σ` between the two paths give (`cusp_contour_shift`)

`e^{−πρσ} ∫₀^∞ (1 − σs)¹⁰ f(s/(1 − σs)) e^{−πρs} ds
   = ∫₀^p f(x) γ_ρ(x − σ) dx + σ ∫₀¹ f(p + σv) γ_ρ(p + σv − σ) dv − ∫₀^p f(x + σ) γ_ρ(x) dx`.

The left side is the integral of the cusp part `P_{±1}(z) e^{πiρz}` of the Leech kernel along the
imaginary axis; the right side consists of the integrals that occur in the Fourier transform of
the truncated profile.
-/

noncomputable section

namespace E8Leech

open Complex Set MeasureTheory Filter Topology
open scoped Real Interval

/-! ## The function `γ_ρ` -/

/-- `γ_ρ(a) = a⁻¹² e^{−πρ/a}`. -/
def gaussGam (ρ : ℝ) (a : ℂ) : ℂ := (a ^ 12)⁻¹ * cexp (-(π * ρ) / a)

theorem gaussHat_twentyFour {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    gaussHat 24 a r = gaussGam (r ^ 2) a := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h24 : ((24 : ℕ) : ℂ) / 2 = ((12 : ℕ) : ℂ) := by norm_num
  rw [gaussHat, gaussGam, h24, Complex.cpow_natCast, div_mul_eq_div_div, div_self hπ, one_div,
    inv_pow]
  congr 2
  rw [div_eq_div_iff (mul_ne_zero hπ ha) ha]
  push_cast
  ring

theorem differentiableAt_gaussGam (ρ : ℝ) {a : ℂ} (ha : a ≠ 0) :
    DifferentiableAt ℂ (gaussGam ρ) a := by
  have h1 : DifferentiableAt ℂ (fun a : ℂ => (a ^ 12)⁻¹) a :=
    (differentiableAt_fun_id.pow 12).inv (pow_ne_zero 12 ha)
  have h2 : DifferentiableAt ℂ (fun a : ℂ => cexp (-(π * ρ) / a)) a :=
    ((differentiableAt_const _).div differentiableAt_fun_id ha).cexp
  exact h1.mul h2

theorem norm_gaussGam (ρ : ℝ) (a : ℂ) :
    ‖gaussGam ρ a‖ = (‖a‖ ^ 12)⁻¹ * Real.exp (-(π * ρ) * (a⁻¹).re) := by
  rw [gaussGam, norm_mul, norm_inv, norm_pow, Complex.norm_exp]
  congr 2
  rw [div_eq_mul_inv, show (-((π : ℂ) * ρ)) = ((-(π * ρ) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- `γ_ρ` is bounded on the positive reals. -/
theorem exists_bound_gaussGam_pos {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → ‖gaussGam ρ x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul 12 (mul_pos Real.pi_pos hρ)
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x⁻¹ (inv_nonneg.mpr hx.le)
  rw [norm_gaussGam, Complex.norm_real, Real.norm_of_nonneg hx.le, ← Complex.ofReal_inv,
    Complex.ofReal_re, ← inv_pow]
  exact h

/-! ## `σ = ±i` -/

section Sigma

variable {σ : ℂ}

theorem sigma_sq (hσ : σ = I ∨ σ = -I) : σ ^ 2 = -1 := by
  rcases hσ with rfl | rfl <;> simp [Complex.I_sq]

theorem sigma_ne_zero (hσ : σ = I ∨ σ = -I) : σ ≠ 0 := by
  rcases hσ with rfl | rfl <;> simp

theorem norm_sigma (hσ : σ = I ∨ σ = -I) : ‖σ‖ = 1 := by
  rcases hσ with rfl | rfl <;> simp

theorem normSq_ofReal_add_sigma_mul (hσ : σ = I ∨ σ = -I) (a b : ℝ) :
    Complex.normSq ((a : ℂ) + σ * b) = a ^ 2 + b ^ 2 := by
  rcases hσ with rfl | rfl <;> simp [Complex.normSq_apply] <;> ring

theorem re_ofReal_add_sigma_mul (hσ : σ = I ∨ σ = -I) (a b : ℝ) :
    ((a : ℂ) + σ * b).re = a := by
  rcases hσ with rfl | rfl <;> simp

theorem one_sub_sigma_mul_ne_zero (hσ : σ = I ∨ σ = -I) (s : ℝ) : (1 : ℂ) - σ * s ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rcases hσ with rfl | rfl <;> simp at this

theorem normSq_one_sub_sigma_mul (hσ : σ = I ∨ σ = -I) (s : ℝ) :
    Complex.normSq (1 - σ * s) = 1 + s ^ 2 := by
  have h := normSq_ofReal_add_sigma_mul hσ 1 (-s)
  rw [show ((1 : ℝ) : ℂ) + σ * ((-s : ℝ) : ℂ) = 1 - σ * s by push_cast; ring] at h
  rw [h]
  ring

/-- The arc from `0` to `σ`: `s/(1 − σs) = s/(s² + 1) + σ (1 − 1/(s² + 1))`. -/
theorem arc_eq (hσ : σ = I ∨ σ = -I) (s : ℝ) :
    (s : ℂ) / (1 - σ * s) =
      ((s / (s ^ 2 + 1) : ℝ) : ℂ) + σ * ((1 - 1 / (s ^ 2 + 1) : ℝ) : ℂ) := by
  have h1 := one_sub_sigma_mul_ne_zero hσ s
  have h2 : (s : ℂ) ^ 2 + 1 ≠ 0 := by
    have : (0 : ℝ) < s ^ 2 + 1 := by positivity
    exact_mod_cast this.ne'
  have hσ2 := sigma_sq hσ
  rw [div_eq_iff h1]
  push_cast
  field_simp
  linear_combination ((s : ℂ) ^ 3) * hσ2

theorem arc_sub_sigma (hσ : σ = I ∨ σ = -I) (s : ℝ) :
    (s : ℂ) / (1 - σ * s) - σ = -σ / (1 - σ * s) := by
  have h1 := one_sub_sigma_mul_ne_zero hσ s
  have hσ2 := sigma_sq hσ
  rw [div_sub' h1, div_left_inj' h1]
  linear_combination (s : ℂ) * hσ2

theorem hasDerivAt_arc (hσ : σ = I ∨ σ = -I) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) / (1 - σ * s)) (1 / (1 - σ * s) ^ 2) s := by
  have h1 := one_sub_sigma_mul_ne_zero hσ s
  have ha : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  have hb : HasDerivAt (fun s : ℝ => (1 : ℂ) - σ * s) (-σ) s := by
    simpa using (ha.const_mul σ).const_sub 1
  refine (ha.div hb h1).congr_deriv ?_
  field_simp
  ring

end Sigma

/-! ## The fundamental theorem along a path in a domain with a primitive -/

theorem integral_path_of_hasDerivAt {Φ F : ℂ → ℂ} {D : Set ℂ}
    (hΦ : ∀ z ∈ D, HasDerivAt Φ (F z) z) (hFc : ContinuousOn F D) {c c' : ℝ → ℂ} {a b : ℝ}
    (hc : ∀ s ∈ uIcc a b, HasDerivAt c (c' s) s) (hc' : ContinuousOn c' (uIcc a b))
    (hmem : ∀ s ∈ uIcc a b, c s ∈ D) :
    ∫ s in a..b, F (c s) * c' s = Φ (c b) - Φ (c a) := by
  have hderiv : ∀ s ∈ uIcc a b, HasDerivAt (fun s => Φ (c s)) (F (c s) * c' s) s := by
    intro s hs
    have h := (hΦ (c s) (hmem s hs)).scomp s (hc s hs)
    simpa [smul_eq_mul, mul_comm, Function.comp_def] using h
  have hcont : ContinuousOn (fun s => F (c s) * c' s) (uIcc a b) :=
    (hFc.comp (fun s hs => (hc s hs).continuousAt.continuousWithinAt) hmem).mul hc'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-! ## The disc `B(p, √(p² + 1))` -/

section Disc

variable {σ : ℂ} {p : ℝ}

theorem mem_shiftDisc {z : ℂ} :
    z ∈ Metric.ball (p : ℂ) (Real.sqrt (p ^ 2 + 1)) ↔ Complex.normSq (z - p) < p ^ 2 + 1 := by
  rw [Metric.mem_ball, Complex.dist_eq, Real.lt_sqrt (norm_nonneg _), Complex.sq_norm]

theorem sigma_path_mem (hσ : σ = I ∨ σ = -I) {a b : ℝ} (h : (a - p) ^ 2 + b ^ 2 < p ^ 2 + 1) :
    (a : ℂ) + σ * b ∈ Metric.ball (p : ℂ) (Real.sqrt (p ^ 2 + 1)) := by
  rw [mem_shiftDisc, show (a : ℂ) + σ * b - p = ((a - p : ℝ) : ℂ) + σ * b by push_cast; ring,
    normSq_ofReal_add_sigma_mul hσ]
  exact h

theorem sub_sigma_ne_zero_of_mem (hσ : σ = I ∨ σ = -I) {z : ℂ}
    (hz : z ∈ Metric.ball (p : ℂ) (Real.sqrt (p ^ 2 + 1))) : z - σ ≠ 0 := by
  intro h
  rw [sub_eq_zero.mp h, mem_shiftDisc,
    show σ - (p : ℂ) = ((-p : ℝ) : ℂ) + σ * ((1 : ℝ) : ℂ) by push_cast; ring,
    normSq_ofReal_add_sigma_mul hσ] at hz
  nlinarith

theorem arc_mem (hσ : σ = I ∨ σ = -I) (hp : 0 < p) {s : ℝ} (hs : 0 ≤ s) :
    (s : ℂ) / (1 - σ * s) ∈ Metric.ball (p : ℂ) (Real.sqrt (p ^ 2 + 1)) := by
  rw [arc_eq hσ s]
  refine sigma_path_mem hσ ?_
  have hq : (0 : ℝ) < s ^ 2 + 1 := by positivity
  have hx : 0 ≤ s / (s ^ 2 + 1) := div_nonneg hs hq.le
  have hv : 0 < 1 / (s ^ 2 + 1) := by positivity
  have hxv : (s / (s ^ 2 + 1)) ^ 2 + (1 / (s ^ 2 + 1)) ^ 2 = 1 / (s ^ 2 + 1) := by
    field_simp
  nlinarith [mul_nonneg hp.le hx]

end Disc

/-! ## The integrand on the arc -/

section Arc

variable {σ : ℂ}

theorem gaussGam_arc (hσ : σ = I ∨ σ = -I) (ρ s : ℝ) :
    gaussGam ρ ((s : ℂ) / (1 - σ * s) - σ) =
      (1 - σ * s) ^ 12 * cexp (-(π * ρ) * (σ + s)) := by
  have h1 := one_sub_sigma_mul_ne_zero hσ s
  have hσ0 := sigma_ne_zero hσ
  have hσ2 := sigma_sq hσ
  have hσ12 : (-σ) ^ 12 = 1 := by
    rw [show (-σ) ^ 12 = (σ ^ 2) ^ 6 by ring, hσ2]
    norm_num
  rw [arc_sub_sigma hσ, gaussGam]
  congr 1
  · rw [div_pow, inv_div, hσ12, div_one]
  · congr 1
    rw [div_div_eq_mul_div, div_eq_iff (neg_ne_zero.mpr hσ0)]
    linear_combination (-((π : ℂ) * ρ)) * hσ2

theorem cuspShift_arc_integrand (hσ : σ = I ∨ σ = -I) (f : ℂ → ℂ) (ρ s : ℝ) :
    f ((s : ℂ) / (1 - σ * s)) * gaussGam ρ ((s : ℂ) / (1 - σ * s) - σ) *
        (1 / (1 - σ * s) ^ 2) =
      cexp (-(π * ρ) * σ) *
        ((1 - σ * s) ^ 10 * f ((s : ℂ) / (1 - σ * s)) * cexp (-(π * ρ) * s)) := by
  have h1 := one_sub_sigma_mul_ne_zero hσ s
  rw [gaussGam_arc hσ, mul_add, Complex.exp_add]
  field_simp

theorem norm_cexp_neg_mul_ofReal (c s : ℝ) : ‖cexp (-((c : ℂ)) * s)‖ = Real.exp (-c * s) := by
  rw [show (-((c : ℂ)) * s) = ((-c * s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]

theorem norm_cexp_neg_mul_sigma (hσ : σ = I ∨ σ = -I) (c : ℝ) : ‖cexp (-((c : ℂ)) * σ)‖ = 1 := by
  rw [Complex.norm_exp]
  rcases hσ with rfl | rfl <;> simp

/-- The cusp part on the imaginary axis is integrable against `e^{−πρs}`. -/
theorem integrableOn_arc_integrand (hσ : σ = I ∨ σ = -I) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => (1 - σ * s) ^ 10 * f (s / (1 - σ * s)) * cexp (-(π * ρ) * s))
      (Ioi 0) := by
  obtain ⟨Bf, hBf⟩ := (isCompact_closedBall ((1 : ℝ) : ℂ)
    (Real.sqrt ((1 : ℝ) ^ 2 + 1))).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨K, hK⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul 12 (mul_pos Real.pi_pos hρ)
  have h1 : Continuous fun s : ℝ => (1 : ℂ) - σ * s := by fun_prop
  have h2 : Continuous fun s : ℝ => (s : ℂ) / (1 - σ * s) :=
    Complex.continuous_ofReal.div h1 (one_sub_sigma_mul_ne_zero hσ)
  have hcont : ContinuousOn
      (fun s : ℝ => (1 - σ * s) ^ 10 * f (s / (1 - σ * s)) * cexp (-(π * ρ) * s)) (Ioi 0) :=
    (((h1.pow 10).mul (hf.continuous.comp h2)).mul (by fun_prop)).continuousOn
  refine integrableOn_Ioi_of_bound (C := Bf * (K * Real.exp (π * ρ))) hcont fun s hs => ?_
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  have hfb : ‖f (s / (1 - σ * s))‖ ≤ Bf :=
    hBf _ (Metric.ball_subset_closedBall (arc_mem hσ one_pos hs.le))
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans hfb
  have hn : ‖(1 : ℂ) - σ * s‖ ≤ 1 + s := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_sigma hσ, one_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hexp : ‖cexp (-((π : ℂ) * ρ) * s)‖ = Real.exp (-(π * ρ) * s) := by
    have := norm_cexp_neg_mul_ofReal (π * ρ) s
    rwa [Complex.ofReal_mul] at this
  have hKs := hK (1 + s) hs1.le
  have he : Real.exp (-(π * ρ) * s) = Real.exp (-(π * ρ) * (1 + s)) * Real.exp (π * ρ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, norm_mul, norm_pow, hexp, le_div_iff₀ (pow_pos hs1 2)]
  have hpow : ‖(1 : ℂ) - σ * s‖ ^ 10 ≤ (1 + s) ^ 10 := pow_le_pow_left₀ (norm_nonneg _) hn 10
  have hE := Real.exp_pos (-(π * ρ) * s)
  calc ‖(1 : ℂ) - σ * s‖ ^ 10 * ‖f (s / (1 - σ * s))‖ * Real.exp (-(π * ρ) * s) * (1 + s) ^ 2
      ≤ (1 + s) ^ 10 * Bf * Real.exp (-(π * ρ) * s) * (1 + s) ^ 2 := by
        gcongr
    _ = Bf * ((1 + s) ^ 12 * Real.exp (-(π * ρ) * (1 + s)) * Real.exp (π * ρ)) := by
        rw [he]
        ring
    _ ≤ Bf * (K * Real.exp (π * ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKs (Real.exp_pos _).le) hBf0

end Arc

/-! ## Decay of `γ_ρ(t − σ)` between the two paths -/

section Decay

variable {σ : ℂ}

/-- On the segment from `x_S + σ` to the arc point `S/(1 − σS)` (`x_S = S/(S² + 1)`),
`|γ_ρ(t − σ)| ≤ (2S)¹² e^{−πρS}`. -/
theorem norm_gaussGam_near_sigma (hσ : σ = I ∨ σ = -I) {ρ S v : ℝ} (hρ : 0 < ρ) (hS : 1 ≤ S)
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / (S ^ 2 + 1)) :
    ‖gaussGam ρ (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ * ((-v : ℝ) : ℂ))‖ ≤
      (2 * S) ^ 12 * Real.exp (-(π * ρ) * S) := by
  have hS0 : (0 : ℝ) < S := by linarith
  have hq : (0 : ℝ) < S ^ 2 + 1 := by positivity
  set x : ℝ := S / (S ^ 2 + 1) with hx
  set u : ℂ := (x : ℂ) + σ * ((-v : ℝ) : ℂ) with hu
  have hxpos : 0 < x := div_pos hS0 hq
  have hxS : 1 / (2 * S) ≤ x := by
    rw [hx, div_le_div_iff₀ (by positivity) hq]
    nlinarith
  have hre : u.re = x := re_ofReal_add_sigma_mul hσ x (-v)
  have hnsq : Complex.normSq u = x ^ 2 + v ^ 2 := by
    rw [hu, normSq_ofReal_add_sigma_mul hσ]
    ring
  have hnu : x ≤ ‖u‖ := by
    have h := Complex.abs_re_le_norm u
    rwa [hre, abs_of_pos hxpos] at h
  -- the power
  have hpow : (‖u‖ ^ 12)⁻¹ ≤ (2 * S) ^ 12 := by
    have h1 : (2 * S)⁻¹ ≤ ‖u‖ := by
      rw [← one_div]
      exact hxS.trans hnu
    have h2 : ((2 * S) ^ 12)⁻¹ ≤ ‖u‖ ^ 12 := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) h1 12
    exact inv_le_of_inv_le₀ (by positivity) h2
  -- the exponential
  have hinv : S ≤ (u⁻¹).re := by
    rw [Complex.inv_re, hre, hnsq, le_div_iff₀ (by positivity)]
    have hvS : v ^ 2 ≤ (1 / (S ^ 2 + 1)) ^ 2 := pow_le_pow_left₀ hv0 hv 2
    have hxv : x ^ 2 + (1 / (S ^ 2 + 1)) ^ 2 = 1 / (S ^ 2 + 1) := by
      rw [hx]
      field_simp
    have hSx : S * (1 / (S ^ 2 + 1)) = x := by
      rw [hx]
      ring
    calc S * (x ^ 2 + v ^ 2) ≤ S * (x ^ 2 + (1 / (S ^ 2 + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hS0.le
      _ = x := by rw [hxv, hSx]
  have hexp : Real.exp (-(π * ρ) * (u⁻¹).re) ≤ Real.exp (-(π * ρ) * S) := by
    refine Real.exp_le_exp.mpr ?_
    have hc : 0 < π * ρ := mul_pos Real.pi_pos hρ
    nlinarith
  rw [norm_gaussGam]
  exact mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)

end Decay

/-! ## The contour shift -/

/-- **The contour shift.** For an entire function `f`, `σ = ±i`, `ρ > 0` and a cut `p > 0`:
`e^{−πρσ} ∫₀^∞ (1 − σs)¹⁰ f(s/(1 − σs)) e^{−πρs} ds
  = ∫₀^p f(x) γ(x − σ) dx + σ ∫₀¹ f(p + σv) γ(p + σv − σ) dv − ∫₀^p f(x + σ) γ(x) dx`. -/
theorem cusp_contour_shift {f : ℂ → ℂ} (hf : Differentiable ℂ f) {σ : ℂ} (hσ : σ = I ∨ σ = -I)
    {ρ p : ℝ} (hρ : 0 < ρ) (hp : 0 < p) :
    cexp (-(π * ρ) * σ) * ∫ s in Ioi (0 : ℝ),
        (1 - σ * s) ^ 10 * f (s / (1 - σ * s)) * cexp (-(π * ρ) * s) =
      (∫ x in (0 : ℝ)..p, f x * gaussGam ρ (x - σ)) +
        σ * (∫ v in (0 : ℝ)..1, f (p + σ * v) * gaussGam ρ (p + σ * v - σ)) -
        ∫ x in (0 : ℝ)..p, f (x + σ) * gaussGam ρ x := by
  set D : Set ℂ := Metric.ball (p : ℂ) (Real.sqrt (p ^ 2 + 1)) with hD
  set F : ℂ → ℂ := fun t => f t * gaussGam ρ (t - σ) with hF
  set A : ℝ → ℂ := fun s => (1 - σ * s) ^ 10 * f (s / (1 - σ * s)) * cexp (-(π * ρ) * s) with hA
  set G : ℝ → ℂ := fun x => f (x + σ) * gaussGam ρ x with hG
  have hσn := norm_sigma hσ
  -- the primitive
  have hFd : DifferentiableOn ℂ F D := fun z hz => by
    have h1 : DifferentiableAt ℂ (fun t : ℂ => gaussGam ρ (t - σ)) z :=
      (differentiableAt_gaussGam ρ (sub_sigma_ne_zero_of_mem hσ hz)).comp z
        (differentiableAt_fun_id.sub_const σ)
    exact (hf.differentiableAt.mul h1).differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := hFd.isExactOn_ball
  have hFc : ContinuousOn F D := hFd.continuousOn
  obtain ⟨Bf, hBf⟩ := (isCompact_closedBall (p : ℂ)
    (Real.sqrt (p ^ 2 + 1))).exists_bound_of_continuousOn hf.continuous.continuousOn
  have hBfD : ∀ z ∈ D, ‖f z‖ ≤ Bf := fun z hz => hBf z (Metric.ball_subset_closedBall hz)
  obtain ⟨Cγ, hCγ⟩ := exists_bound_gaussGam_pos hρ
  obtain ⟨K, hK⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul 13 (mul_pos Real.pi_pos hρ)
  have hK0 : 0 ≤ K := by simpa using hK 0 le_rfl
  have hCγ0 : 0 ≤ Cγ := (norm_nonneg _).trans (hCγ 1 one_pos)
  -- points of the paths
  have m1 : ∀ x ∈ uIcc (0 : ℝ) p, ((x : ℝ) : ℂ) ∈ D := by
    intro x hx
    rw [uIcc_of_le hp.le] at hx
    have h := sigma_path_mem hσ (p := p) (a := x) (b := 0) (by nlinarith [hx.1, hx.2])
    rwa [Complex.ofReal_zero, mul_zero, add_zero] at h
  have m2 : ∀ v ∈ uIcc (0 : ℝ) 1, (p : ℂ) + σ * v ∈ D := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    exact sigma_path_mem hσ (by nlinarith [hv.1, hv.2])
  have m3 : ∀ x : ℝ, 0 < x → x ≤ p → (x : ℂ) + σ ∈ D := by
    intro x hx0 hxp
    have h := sigma_path_mem hσ (p := p) (a := x) (b := 1) (by nlinarith)
    rwa [Complex.ofReal_one, mul_one] at h
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBfD _ (m3 p hp le_rfl))
  -- the four fixed pieces
  have hI1 : ∫ x in (0 : ℝ)..p, F x * 1 = Φ p - Φ ((0 : ℝ) : ℂ) :=
    integral_path_of_hasDerivAt hΦ hFc (c := fun x : ℝ => (x : ℂ)) (c' := fun _ => 1)
      (fun x _ => (hasDerivAt_id x).ofReal_comp) continuousOn_const m1
  have hI2 : ∫ v in (0 : ℝ)..1, F (p + σ * v) * σ =
      Φ (p + σ * ((1 : ℝ) : ℂ)) - Φ (p + σ * ((0 : ℝ) : ℂ)) :=
    integral_path_of_hasDerivAt hΦ hFc (c := fun v : ℝ => (p : ℂ) + σ * v) (c' := fun _ => σ)
      (fun v _ => by
        simpa using ((hasDerivAt_id v).ofReal_comp.const_mul σ).const_add (p : ℂ))
      continuousOn_const m2
  have hI3 : ∀ x₀ : ℝ, 0 < x₀ → x₀ ≤ p →
      ∫ x in x₀..p, F (x + σ) * 1 = Φ (p + σ) - Φ (x₀ + σ) := by
    intro x₀ hx₀ hx₀p
    refine integral_path_of_hasDerivAt hΦ hFc (c := fun x : ℝ => (x : ℂ) + σ) (c' := fun _ => 1)
      (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp.add_const σ) continuousOn_const
      fun x hx => ?_
    rw [uIcc_of_le hx₀p] at hx
    exact m3 x (lt_of_lt_of_le hx₀ hx.1) hx.2
  have hI4 : ∀ S : ℝ, 0 ≤ S →
      ∫ s in (0 : ℝ)..S, F (s / (1 - σ * s)) * (1 / (1 - σ * s) ^ 2) =
        Φ (S / (1 - σ * S)) - Φ (((0 : ℝ) : ℂ) / (1 - σ * ((0 : ℝ) : ℂ))) := by
    intro S hS
    have hc1 : Continuous fun s : ℝ => (1 : ℂ) - σ * s := by fun_prop
    refine integral_path_of_hasDerivAt hΦ hFc (c := fun s : ℝ => (s : ℂ) / (1 - σ * s))
      (c' := fun s : ℝ => 1 / (1 - σ * s) ^ 2) (fun s _ => hasDerivAt_arc hσ s)
      (continuous_const.div (hc1.pow 2) fun s =>
        pow_ne_zero 2 (one_sub_sigma_mul_ne_zero hσ s)).continuousOn fun s hs => ?_
    rw [uIcc_of_le hS] at hs
    exact arc_mem hσ hp hs.1
  -- the pieces depending on `S`
  have hI5 : ∀ S : ℝ, 1 ≤ S → S / (S ^ 2 + 1) ≤ p →
      ∫ v in (0 : ℝ)..(1 / (S ^ 2 + 1)),
          F (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * v) * (-σ) =
        Φ (S / (1 - σ * S)) - Φ (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ) := by
    intro S hS hSp
    have hq : (0 : ℝ) < S ^ 2 + 1 := by positivity
    have hvS : (0 : ℝ) ≤ 1 / (S ^ 2 + 1) := by positivity
    have hxS : 0 < S / (S ^ 2 + 1) := div_pos (by linarith) hq
    have h := integral_path_of_hasDerivAt hΦ hFc
      (c := fun v : ℝ => ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * v) (c' := fun _ => -σ)
      (a := 0) (b := 1 / (S ^ 2 + 1))
      (fun v _ => by
        simpa using ((hasDerivAt_id v).ofReal_comp.const_mul (-σ)).const_add
          (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ))
      continuousOn_const (fun v hv => by
        rw [uIcc_of_le hvS] at hv
        have hv1 : v ≤ 1 := hv.2.trans (by rw [div_le_one hq]; nlinarith)
        have h := sigma_path_mem hσ (p := p) (a := S / (S ^ 2 + 1)) (b := 1 - v)
          (by nlinarith [hv.1])
        rw [show ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * (v : ℂ) =
          ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ * ((1 - v : ℝ) : ℂ) by push_cast; ring]
        exact h)
    rw [h]
    congr 2
    · rw [arc_eq hσ S]
      push_cast
      ring
    · push_cast
      ring
  -- integrability
  have hAint : IntegrableOn A (Ioi 0) := integrableOn_arc_integrand hσ hf hρ
  have hGb : ∀ x : ℝ, 0 < x → x ≤ p → ‖G x‖ ≤ Bf * Cγ := by
    intro x hx hxp
    simp only [hG]
    rw [norm_mul]
    exact mul_le_mul (hBfD _ (m3 x hx hxp)) (hCγ x hx) (norm_nonneg _) hBf0
  have hGc : ContinuousOn G (Ioc 0 p) := by
    intro x hx
    have h1 : ContinuousAt (fun x : ℝ => f ((x : ℂ) + σ)) x :=
      (hf.continuous.comp (Complex.continuous_ofReal.add continuous_const)).continuousAt
    have h2 : ContinuousAt (fun x : ℝ => gaussGam ρ (x : ℂ)) x :=
      (differentiableAt_gaussGam ρ (Complex.ofReal_ne_zero.mpr hx.1.ne')).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    exact (h1.mul h2).continuousWithinAt
  have hGint : IntegrableOn G (Ioc 0 p) := by
    refine Integrable.mono' (integrable_const (Bf * Cγ))
      (hGc.aestronglyMeasurable measurableSet_Ioc) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun x hx => hGb x hx.1 hx.2)
  have hGii : ∀ x₀ : ℝ, 0 ≤ x₀ → x₀ ≤ p → IntervalIntegrable G volume 0 x₀ := fun x₀ h0 hx₀ =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr
      (hGint.mono_set (Ioc_subset_Ioc_right hx₀))
  -- the identity for large `S`
  set L : ℂ := (∫ x in (0 : ℝ)..p, f x * gaussGam ρ (x - σ)) +
    σ * (∫ v in (0 : ℝ)..1, f (p + σ * v) * gaussGam ρ (p + σ * v - σ)) -
    ∫ x in (0 : ℝ)..p, f (x + σ) * gaussGam ρ x with hL
  have hmain : ∀ S : ℝ, 1 ≤ S → S / (S ^ 2 + 1) ≤ p →
      cexp (-(π * ρ) * σ) * (∫ s in (0 : ℝ)..S, A s) - L =
        (∫ v in (0 : ℝ)..(1 / (S ^ 2 + 1)),
          F (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * v) * (-σ)) +
          ∫ x in (0 : ℝ)..(S / (S ^ 2 + 1)), G x := by
    intro S hS hSp
    have hq : (0 : ℝ) < S ^ 2 + 1 := by positivity
    have hxS : 0 < S / (S ^ 2 + 1) := div_pos (by linarith) hq
    have e4 : cexp (-(π * ρ) * σ) * (∫ s in (0 : ℝ)..S, A s) =
        ∫ s in (0 : ℝ)..S, F (s / (1 - σ * s)) * (1 / (1 - σ * s) ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (cuspShift_arc_integrand hσ f ρ s).symm
    have e1 : ∫ x in (0 : ℝ)..p, f x * gaussGam ρ (x - σ) = ∫ x in (0 : ℝ)..p, F x * 1 :=
      intervalIntegral.integral_congr fun x _ => by simp only [hF, mul_one]
    have e2 : σ * (∫ v in (0 : ℝ)..1, f (p + σ * v) * gaussGam ρ (p + σ * v - σ)) =
        ∫ v in (0 : ℝ)..1, F (p + σ * v) * σ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [hF]
      ring
    have e3 : ∫ x in (S / (S ^ 2 + 1))..p, F (x + σ) * 1 = ∫ x in (S / (S ^ 2 + 1))..p, G x :=
      intervalIntegral.integral_congr fun x _ => by
        simp only [hF, hG, mul_one, add_sub_cancel_right]
    have eG : ∫ x in (0 : ℝ)..p, f (x + σ) * gaussGam ρ x =
        (∫ x in (0 : ℝ)..(S / (S ^ 2 + 1)), G x) + ∫ x in (S / (S ^ 2 + 1))..p, G x := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hGii _ hxS.le hSp)]
      exact ((hGii p hp.le le_rfl).symm.trans (hGii _ hxS.le hSp)).symm
    have h0 : ((0 : ℝ) : ℂ) / (1 - σ * ((0 : ℝ) : ℂ)) = ((0 : ℝ) : ℂ) := by simp
    have hp1 : (p : ℂ) + σ * ((1 : ℝ) : ℂ) = p + σ := by simp
    have hp0 : (p : ℂ) + σ * ((0 : ℝ) : ℂ) = p := by simp
    have h4 := hI4 S (by linarith)
    have h5 := hI5 S hS hSp
    have h3 := hI3 _ hxS hSp
    rw [h0] at h4
    rw [hp1, hp0] at hI2
    rw [hL, e4, e1, e2, eG, h4, h5, hI1, hI2, ← e3, h3]
    ring
  -- the error terms
  have herr : ∀ᶠ S : ℝ in atTop, ‖cexp (-(π * ρ) * σ) * (∫ s in (0 : ℝ)..S, A s) - L‖ ≤
      (Bf * (2 ^ 12 * K) + Bf * Cγ) / S := by
    filter_upwards [eventually_ge_atTop (max 1 (1 / p))] with S hSmax
    have hS : 1 ≤ S := (le_max_left _ _).trans hSmax
    have hS0 : (0 : ℝ) < S := by linarith
    have hq : (0 : ℝ) < S ^ 2 + 1 := by positivity
    have hxS : 0 < S / (S ^ 2 + 1) := div_pos hS0 hq
    have hxS' : S / (S ^ 2 + 1) ≤ 1 / S := by
      rw [div_le_div_iff₀ hq hS0]
      nlinarith
    have hSp : S / (S ^ 2 + 1) ≤ p := by
      refine hxS'.trans ?_
      have h1 : 1 / p ≤ S := (le_max_right _ _).trans hSmax
      rw [div_le_iff₀ hp] at h1
      rw [div_le_iff₀ hS0]
      linarith
    have hvS : (0 : ℝ) ≤ 1 / (S ^ 2 + 1) := by positivity
    have hvS1 : 1 / (S ^ 2 + 1) ≤ 1 := by
      rw [div_le_one hq]
      nlinarith
    rw [hmain S hS hSp]
    refine (norm_add_le _ _).trans ?_
    have hK13 : S ^ 12 * Real.exp (-(π * ρ) * S) ≤ K / S := by
      rw [le_div_iff₀ hS0]
      have := hK S hS0.le
      calc S ^ 12 * Real.exp (-(π * ρ) * S) * S = S ^ 13 * Real.exp (-(π * ρ) * S) := by ring
        _ ≤ K := this
    have b5 : ‖∫ v in (0 : ℝ)..(1 / (S ^ 2 + 1)),
        F (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * v) * (-σ)‖ ≤ Bf * (2 ^ 12 * K) / S := by
      have hb : ∀ v ∈ Ι (0 : ℝ) (1 / (S ^ 2 + 1)),
          ‖F (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * v) * (-σ)‖ ≤ Bf * (2 ^ 12 * K) / S := by
        intro v hv
        rw [uIoc_of_le hvS] at hv
        have hv1 : v ≤ 1 := hv.2.trans hvS1
        have hmem : ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * (v : ℂ) ∈ D := by
          have h := sigma_path_mem hσ (p := p) (a := S / (S ^ 2 + 1)) (b := 1 - v)
            (by nlinarith [hv.1])
          rw [show ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * (v : ℂ) =
            ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ * ((1 - v : ℝ) : ℂ) by push_cast; ring]
          exact h
        have hγ := norm_gaussGam_near_sigma hσ hρ hS hv.1.le hv.2
        have hu : ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * (v : ℂ) - σ =
            ((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ * ((-v : ℝ) : ℂ) := by
          push_cast
          ring
        simp only [hF]
        rw [norm_mul, norm_mul, norm_neg, hσn, mul_one, hu]
        calc ‖f (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ + -σ * (v : ℂ))‖ *
              ‖gaussGam ρ (((S / (S ^ 2 + 1) : ℝ) : ℂ) + σ * ((-v : ℝ) : ℂ))‖
            ≤ Bf * ((2 * S) ^ 12 * Real.exp (-(π * ρ) * S)) :=
              mul_le_mul (hBfD _ hmem) hγ (norm_nonneg _) hBf0
          _ = Bf * (2 ^ 12 * (S ^ 12 * Real.exp (-(π * ρ) * S))) := by ring
          _ ≤ Bf * (2 ^ 12 * (K / S)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK13 (by positivity)) hBf0
          _ = Bf * (2 ^ 12 * K) / S := by ring
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
      refine h.trans ?_
      rw [sub_zero, abs_of_nonneg hvS]
      exact mul_le_of_le_one_right
        (div_nonneg (mul_nonneg hBf0 (mul_nonneg (by positivity) hK0)) hS0.le) hvS1
    have bG : ‖∫ x in (0 : ℝ)..(S / (S ^ 2 + 1)), G x‖ ≤ Bf * Cγ / S := by
      have hb : ∀ x ∈ Ι (0 : ℝ) (S / (S ^ 2 + 1)), ‖G x‖ ≤ Bf * Cγ := by
        intro x hx
        rw [uIoc_of_le hxS.le] at hx
        exact hGb x hx.1 (hx.2.trans hSp)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
      refine h.trans ?_
      rw [sub_zero, abs_of_pos hxS, div_eq_mul_one_div (Bf * Cγ) S]
      exact mul_le_mul_of_nonneg_left hxS' (mul_nonneg hBf0 hCγ0)
    calc _ ≤ Bf * (2 ^ 12 * K) / S + Bf * Cγ / S := add_le_add b5 bG
      _ = (Bf * (2 ^ 12 * K) + Bf * Cγ) / S := by ring
  -- the limit
  have hlim0 : Tendsto (fun S : ℝ => cexp (-(π * ρ) * σ) * (∫ s in (0 : ℝ)..S, A s) - L) atTop
      (𝓝 0) :=
    squeeze_zero_norm' herr (tendsto_const_nhds.div_atTop tendsto_id)
  have hlim1 : Tendsto (fun S : ℝ => cexp (-(π * ρ) * σ) * (∫ s in (0 : ℝ)..S, A s) - L) atTop
      (𝓝 (cexp (-(π * ρ) * σ) * (∫ s in Ioi (0 : ℝ), A s) - L)) :=
    ((intervalIntegral_tendsto_integral_Ioi 0 hAint tendsto_id).const_mul _).sub_const L
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim1 hlim0)

end E8Leech
