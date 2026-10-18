import E8Leech.LeechCuspContour
import E8Leech.LeechCuspParts
import E8Leech.LeechFourierProfile

/-!
# The integrals of the cusp parts along the imaginary axis

For the growing part `f(t) = e^{2πt}(A t + B)` and its pull-backs `P_{±1}` to the cusps `±1`
(`LeechCuspParts`), the two contour shifts of `LeechCuspContour` (`σ = ±i`) add up to
(`cusp_shift_sum`)

`−(e^{−iπρ} ∫₀^∞ P₁(is) e^{−πρs} ds + e^{iπρ} ∫₀^∞ P₋₁(is) e^{−πρs} ds)
   = ∫₀^p f(x) (2γ(x) − γ(x − i) − γ(x + i)) dx + ∫₀¹ (W₋(u) γ(p − iu) + W₊(u) γ(p + iu)) du`,

because `f(x + i) + f(x − i) = 2 f(x)`. The right side is what the Fourier transform of the
truncated profile contains in addition to `∫₀^∞ (𝒦 − f)(2γ(t) − γ(t − i) − γ(t + i)) dt`
(`fourier_leechAxisRadialProfile`).
-/

noncomputable section

namespace E8Leech

open Complex Set MeasureTheory Filter Topology
open scoped Real Interval

theorem integrableOn_cuspPartPlus_imag (A B : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => cuspPartPlus A B (I * s) * gaussE ρ (I * s)) (Ioi 0) := by
  have h := integrableOn_arc_integrand (σ := I) (Or.inl rfl) (differentiable_growthC A B) hρ
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [cuspPartPlus_I_mul, gaussE_I_mul]
  simp only [neg_mul]

theorem integrableOn_cuspPartMinus_imag (A B : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => cuspPartMinus A B (I * s) * gaussE ρ (I * s)) (Ioi 0) := by
  have h := integrableOn_arc_integrand (σ := -I) (Or.inr rfl) (differentiable_growthC A B) hρ
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [cuspPartMinus_I_mul, gaussE_I_mul]
  simp only [neg_mul]

/-- A continuous function times `γ_ρ` is integrable on `(0, p]`. -/
theorem integrableOn_mul_gaussGam {h : ℝ → ℂ} (hh : Continuous h) {ρ : ℝ} (hρ : 0 < ρ) (p : ℝ) :
    IntegrableOn (fun x : ℝ => h x * gaussGam ρ x) (Ioc 0 p) := by
  obtain ⟨Bh, hBh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := p)).exists_bound_of_continuousOn
    hh.continuousOn
  obtain ⟨Cγ, hCγ⟩ := exists_bound_gaussGam_pos hρ
  have hc : ContinuousOn (fun x : ℝ => h x * gaussGam ρ x) (Ioc 0 p) := by
    intro x hx
    have h2 : ContinuousAt (fun x : ℝ => gaussGam ρ (x : ℂ)) x :=
      (differentiableAt_gaussGam ρ (Complex.ofReal_ne_zero.mpr hx.1.ne')).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    exact (hh.continuousAt.mul h2).continuousWithinAt
  refine Integrable.mono' (integrable_const (Bh * Cγ)) (hc.aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_))
  have h1 := hBh x ⟨hx.1.le, hx.2⟩
  rw [norm_mul]
  exact mul_le_mul h1 (hCγ x hx.1) (norm_nonneg _) ((norm_nonneg _).trans h1)

theorem continuous_gaussGam_add (ρ : ℝ) {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun x : ℝ => gaussGam ρ ((x : ℂ) + c) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hne : (x : ℂ) + c ≠ 0 := fun h => hc (by simpa using congrArg Complex.im h)
  have hc' : Continuous fun x : ℝ => (x : ℂ) + c := Complex.continuous_ofReal.add continuous_const
  exact ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + c)
    (differentiableAt_gaussGam ρ hne).continuousAt hc'.continuousAt

theorem continuous_gaussGam_comp (ρ : ℝ) {c : ℝ → ℂ} (hc : Continuous c) (hne : ∀ v, c v ≠ 0) :
    Continuous fun v => gaussGam ρ (c v) :=
  continuous_iff_continuousAt.mpr fun v =>
    ContinuousAt.comp (f := c) (differentiableAt_gaussGam ρ (hne v)).continuousAt hc.continuousAt

/-- `−i f(p + i(1 − u)) = W₋(u)`. -/
theorem neg_I_mul_growthC (A B : ℂ) (p u : ℝ) :
    -I * growthC A B ((p : ℂ) + I * ((1 - u : ℝ) : ℂ)) = explicitWeightMinus A B p u := by
  have hexp : cexp (2 * π * ((p : ℂ) + I * ((1 - u : ℝ) : ℂ))) =
      cexp (2 * π * ((p : ℂ) - (u : ℂ) * I)) := by
    rw [show 2 * (π : ℂ) * ((p : ℂ) + I * ((1 - u : ℝ) : ℂ)) =
      2 * π * ((p : ℂ) - (u : ℂ) * I) + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [growthC, hexp, explicitWeightMinus]
  push_cast
  linear_combination (-(cexp (2 * π * ((p : ℂ) - (u : ℂ) * I)) * A * (1 - (u : ℂ)))) *
    Complex.I_sq

/-- `i f(p − i(1 − u)) = W₊(u)`. -/
theorem I_mul_growthC (A B : ℂ) (p u : ℝ) :
    I * growthC A B ((p : ℂ) + -I * ((1 - u : ℝ) : ℂ)) = explicitWeightPlus A B p u := by
  have hexp : cexp (2 * π * ((p : ℂ) + -I * ((1 - u : ℝ) : ℂ))) =
      cexp (2 * π * ((p : ℂ) + (u : ℂ) * I)) := by
    rw [show 2 * (π : ℂ) * ((p : ℂ) + -I * ((1 - u : ℝ) : ℂ)) =
      2 * π * ((p : ℂ) + (u : ℂ) * I) - 2 * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [growthC, hexp, explicitWeightPlus]
  push_cast
  linear_combination (-(cexp (2 * π * ((p : ℂ) + (u : ℂ) * I)) * A * (1 - (u : ℂ)))) *
    Complex.I_sq

/-- **The two cusp integrals along the imaginary axis** in terms of the integrals on the
`x`-side. -/
theorem cusp_shift_sum (A B : ℂ) {r p : ℝ} (hr : r ≠ 0) (hp : 0 < p) :
    -(cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
          (∫ s in Ioi (0 : ℝ), cuspPartPlus A B (I * s) * gaussE (r ^ 2) (I * s)) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
          ∫ s in Ioi (0 : ℝ), cuspPartMinus A B (I * s) * gaussE (r ^ 2) (I * s)) =
      (∫ x in Ioc (0 : ℝ) p, growthC A B x *
          (2 * gaussHat 24 x r - gaussHat 24 (x - I) r - gaussHat 24 (x + I) r)) +
        ∫ u in (0 : ℝ)..1,
          (explicitWeightMinus A B p u * gaussHat 24 ((p : ℂ) - (u : ℂ) * I) r +
            explicitWeightPlus A B p u * gaussHat 24 ((p : ℂ) + (u : ℂ) * I) r) := by
  have hρ : 0 < r ^ 2 := by positivity
  have hfd := differentiable_growthC A B
  have hfc : Continuous (growthC A B) := hfd.continuous
  have hofR : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
  have hP := cusp_contour_shift hfd (σ := I) (Or.inl rfl) hρ hp
  have hM := cusp_contour_shift hfd (σ := -I) (Or.inr rfl) hρ hp
  -- the left sides
  have eL1 : cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        (∫ s in Ioi (0 : ℝ), cuspPartPlus A B (I * s) * gaussE (r ^ 2) (I * s)) =
      cexp (-(π * ((r ^ 2 : ℝ) : ℂ)) * I) * ∫ s in Ioi (0 : ℝ),
        (1 - I * s) ^ 10 * growthC A B (s / (1 - I * s)) * cexp (-(π * ((r ^ 2 : ℝ) : ℂ)) * s) := by
    congr 1
    · congr 1
      ring
    · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [cuspPartPlus_I_mul, gaussE_I_mul]
      simp only [neg_mul]
  have eL2 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        (∫ s in Ioi (0 : ℝ), cuspPartMinus A B (I * s) * gaussE (r ^ 2) (I * s)) =
      cexp (-(π * ((r ^ 2 : ℝ) : ℂ)) * -I) * ∫ s in Ioi (0 : ℝ),
        (1 - -I * s) ^ 10 * growthC A B (s / (1 - -I * s)) *
          cexp (-(π * ((r ^ 2 : ℝ) : ℂ)) * s) := by
    congr 1
    · congr 1
      ring
    · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [cuspPartMinus_I_mul, gaussE_I_mul]
      simp only [neg_mul]
  -- integrability on `(0, p]`
  have hcm : Continuous fun x : ℝ => growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I) :=
    (hfc.comp hofR).mul (continuous_gaussGam_comp _ (hofR.sub continuous_const) fun x h => by
      simpa using congrArg Complex.im h)
  have hcp : Continuous fun x : ℝ => growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I) :=
    (hfc.comp hofR).mul (continuous_gaussGam_comp _ (hofR.add continuous_const) fun x h => by
      simpa using congrArg Complex.im h)
  have i0 : IntegrableOn (fun x : ℝ => growthC A B x * gaussGam (r ^ 2) x) (Ioc 0 p) :=
    integrableOn_mul_gaussGam (hfc.comp hofR) hρ p
  have im : IntegrableOn (fun x : ℝ => growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I))
      (Ioc 0 p) := hcm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ip : IntegrableOn (fun x : ℝ => growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I))
      (Ioc 0 p) := hcp.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ihp : IntegrableOn (fun x : ℝ => growthC A B ((x : ℂ) + I) * gaussGam (r ^ 2) x)
      (Ioc 0 p) := integrableOn_mul_gaussGam (hfc.comp (hofR.add continuous_const)) hρ p
  have ihm : IntegrableOn (fun x : ℝ => growthC A B ((x : ℂ) + -I) * gaussGam (r ^ 2) x)
      (Ioc 0 p) := integrableOn_mul_gaussGam (hfc.comp (hofR.add continuous_const)) hρ p
  -- the first integral of the right side
  have E1 : ∫ x in Ioc (0 : ℝ) p, growthC A B x *
        (2 * gaussHat 24 x r - gaussHat 24 (x - I) r - gaussHat 24 (x + I) r) =
      2 * (∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) x) -
        (∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I)) -
        ∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I) := by
    have i01 : IntegrableOn (fun x : ℝ => 2 * (growthC A B x * gaussGam (r ^ 2) x)) (Ioc 0 p) :=
      i0.const_mul 2
    have i02 : IntegrableOn (fun x : ℝ => 2 * (growthC A B x * gaussGam (r ^ 2) x) -
        growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I)) (Ioc 0 p) := i01.sub im
    have h1 : ∫ x in Ioc (0 : ℝ) p, (2 * (growthC A B x * gaussGam (r ^ 2) x) -
          growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I) -
          growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I)) =
        2 * (∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) x) -
          (∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - I)) -
          ∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I) := by
      rw [integral_sub i02 ip, integral_sub i01 im, integral_const_mul]
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
    have hm : (x : ℂ) - I ≠ 0 := fun h => by simpa using congrArg Complex.im h
    have hpp : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
    rw [gaussHat_twentyFour h0, gaussHat_twentyFour hm, gaussHat_twentyFour hpp]
    ring
  -- the horizontal sides: `f(x + i) + f(x − i) = 2 f(x)`
  have E2 : (∫ x in (0 : ℝ)..p, growthC A B ((x : ℂ) + I) * gaussGam (r ^ 2) x) +
      (∫ x in (0 : ℝ)..p, growthC A B ((x : ℂ) + -I) * gaussGam (r ^ 2) x) =
      2 * ∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) x := by
    rw [intervalIntegral.integral_of_le hp.le, intervalIntegral.integral_of_le hp.le,
      ← integral_add ihp ihm, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    have h := growthC_add_I_add_sub_I A B (x : ℂ)
    rw [sub_eq_add_neg] at h
    linear_combination gaussGam (r ^ 2) (x : ℂ) * h
  have E3 : ∫ x in (0 : ℝ)..p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) - -I) =
      ∫ x in Ioc (0 : ℝ) p, growthC A B x * gaussGam (r ^ 2) ((x : ℂ) + I) := by
    rw [intervalIntegral.integral_of_le hp.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [sub_neg_eq_add]
  -- the vertical sides
  have hre : ∀ (σ : ℂ) (v : ℝ), σ.re = 0 → (p : ℂ) + σ * v - σ ≠ 0 := fun σ v hσ h => by
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero, hσ, zero_mul, add_zero, Complex.zero_re] at h2
    exact hp.ne' h2
  have hJp : Continuous fun v : ℝ =>
      growthC A B ((p : ℂ) + I * v) * gaussGam (r ^ 2) ((p : ℂ) + I * v - I) :=
    (hfc.comp (continuous_const.add (continuous_const.mul hofR))).mul
      (continuous_gaussGam_comp _ ((continuous_const.add (continuous_const.mul hofR)).sub
        continuous_const) fun v => hre I v Complex.I_re)
  have hJm : Continuous fun v : ℝ =>
      growthC A B ((p : ℂ) + -I * v) * gaussGam (r ^ 2) ((p : ℂ) + -I * v - -I) :=
    (hfc.comp (continuous_const.add (continuous_const.mul hofR))).mul
      (continuous_gaussGam_comp _ ((continuous_const.add (continuous_const.mul hofR)).sub
        continuous_const) fun v => hre (-I) v (by simp))
  have E4 : ∫ u in (0 : ℝ)..1,
        (explicitWeightMinus A B p u * gaussHat 24 ((p : ℂ) - (u : ℂ) * I) r +
          explicitWeightPlus A B p u * gaussHat 24 ((p : ℂ) + (u : ℂ) * I) r) =
      -(I * ∫ v in (0 : ℝ)..1,
          growthC A B ((p : ℂ) + I * v) * gaussGam (r ^ 2) ((p : ℂ) + I * v - I)) -
        -I * ∫ v in (0 : ℝ)..1,
          growthC A B ((p : ℂ) + -I * v) * gaussGam (r ^ 2) ((p : ℂ) + -I * v - -I) := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => explicitWeightMinus A B p u * gaussHat 24 ((p : ℂ) - (u : ℂ) * I) r +
        explicitWeightPlus A B p u * gaussHat 24 ((p : ℂ) + (u : ℂ) * I) r) 1
    rw [sub_self, sub_zero] at hsub
    have iJ1 : IntervalIntegrable (fun v : ℝ => -(I * (growthC A B ((p : ℂ) + I * v) *
        gaussGam (r ^ 2) ((p : ℂ) + I * v - I)))) volume 0 1 :=
      ((hJp.const_mul I).neg).intervalIntegrable 0 1
    have iJ2 : IntervalIntegrable (fun v : ℝ => -I * (growthC A B ((p : ℂ) + -I * v) *
        gaussGam (r ^ 2) ((p : ℂ) + -I * v - -I))) volume 0 1 :=
      (hJm.const_mul (-I)).intervalIntegrable 0 1
    have hsplit : ∫ v in (0 : ℝ)..1,
          (-(I * (growthC A B ((p : ℂ) + I * v) * gaussGam (r ^ 2) ((p : ℂ) + I * v - I))) -
            -I * (growthC A B ((p : ℂ) + -I * v) *
              gaussGam (r ^ 2) ((p : ℂ) + -I * v - -I))) =
        -(I * ∫ v in (0 : ℝ)..1,
            growthC A B ((p : ℂ) + I * v) * gaussGam (r ^ 2) ((p : ℂ) + I * v - I)) -
          -I * ∫ v in (0 : ℝ)..1,
            growthC A B ((p : ℂ) + -I * v) * gaussGam (r ^ 2) ((p : ℂ) + -I * v - -I) := by
      rw [intervalIntegral.integral_sub iJ1 iJ2, intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hsub, ← hsplit]
    refine intervalIntegral.integral_congr fun v _ => ?_
    have hm : (p : ℂ) - ((1 - v : ℝ) : ℂ) * I ≠ 0 := fun h => by
      have h2 := congrArg Complex.re h
      simp at h2
      exact hp.ne' h2
    have hpp : (p : ℂ) + ((1 - v : ℝ) : ℂ) * I ≠ 0 := fun h => by
      have h2 := congrArg Complex.re h
      simp at h2
      exact hp.ne' h2
    have e1 := neg_I_mul_growthC A B p (1 - v)
    have e2 := I_mul_growthC A B p (1 - v)
    have c1 : (p : ℂ) + I * ((1 - (1 - v) : ℝ) : ℂ) = (p : ℂ) + I * v := by
      push_cast
      ring
    have c2 : (p : ℂ) + -I * ((1 - (1 - v) : ℝ) : ℂ) = (p : ℂ) + -I * v := by
      push_cast
      ring
    have a1 : (p : ℂ) - ((1 - v : ℝ) : ℂ) * I = (p : ℂ) + I * v - I := by
      push_cast
      ring
    have a2 : (p : ℂ) + ((1 - v : ℝ) : ℂ) * I = (p : ℂ) + -I * v - -I := by
      push_cast
      ring
    rw [c1] at e1
    rw [c2] at e2
    show explicitWeightMinus A B p (1 - v) * gaussHat 24 ((p : ℂ) - ((1 - v : ℝ) : ℂ) * I) r +
        explicitWeightPlus A B p (1 - v) * gaussHat 24 ((p : ℂ) + ((1 - v : ℝ) : ℂ) * I) r = _
    rw [gaussHat_twentyFour hm, gaussHat_twentyFour hpp, ← e1, ← e2, a1, a2]
    ring
  rw [eL1, eL2, hP, hM, E1, E4, E3, intervalIntegral.integral_of_le hp.le]
  linear_combination E2

end E8Leech
