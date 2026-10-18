import E8Leech.CKMRVRadialProfile

/-!
# The truncated form of the radial profile

Let `k` be a kernel on `(0, ∞)` with cusp profile `A t e^{ct} + B e^{ct} + C t + D` at `∞`
(`sin(c/2) = 0`; in dimension 24, `c = 2π`). The radial profile

`P(b) = 4 sin²(b/2) ∫₀^∞ (k − cuspProfile) e^{−bt} dt + (A + B(b − c)) sinc²((b − c)/2)
          + (C + D b) sinc²(b/2)`

continues `4 sin²(b/2) ∫₀^∞ k e^{−bt} dt` from `b > c` to smaller `b`. For the sign of `P` on
`0 < b ≤ c` one cuts the integral at a point `p ≥ 0` (CKMRV (6.3), `p = 1.01`): for every `b > 0`,

`P(b) = 4 sin²(b/2) [∫₀^p k e^{−bt} dt + ∫_p^∞ (k − A t e^{ct} − B e^{ct}) e^{−bt} dt]
          + sinc²((b − c)/2) e^{−(b − c)p} (A + (B + pA)(b − c))`.

The polynomial part `C t + D` of the cusp profile drops out, and the exponential part is integrated
explicitly on `[0, p]`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open scoped Real

/-! ## Two elementary integrals -/

theorem integral_Ioc_exp_neg_mul {ε p : ℝ} (hε : ε ≠ 0) (hp : 0 ≤ p) :
    ε * ∫ t in Ioc 0 p, Real.exp (-ε * t) = 1 - Real.exp (-ε * p) := by
  rw [← intervalIntegral.integral_of_le hp]
  have hd : ∀ t ∈ Set.uIcc 0 p,
      HasDerivAt (fun t => -(Real.exp (-ε * t) / ε)) (Real.exp (-ε * t)) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => -ε * t) (-ε) t := by
      simpa using (hasDerivAt_id t).const_mul (-ε)
    have h : HasDerivAt (fun t => -(Real.exp (-ε * t) / ε))
        (-(Real.exp (-ε * t) * (-ε) / ε)) t := (h0.exp.div_const ε).neg
    refine h.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-ε * t)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

theorem integral_Ioc_mul_exp_neg_mul {ε p : ℝ} (hε : ε ≠ 0) (hp : 0 ≤ p) :
    ε ^ 2 * ∫ t in Ioc 0 p, t * Real.exp (-ε * t) =
      1 - Real.exp (-ε * p) - p * ε * Real.exp (-ε * p) := by
  rw [← intervalIntegral.integral_of_le hp]
  have hd : ∀ t ∈ Set.uIcc 0 p,
      HasDerivAt (fun t => -(Real.exp (-ε * t) * (t / ε + 1 / ε ^ 2)))
        (t * Real.exp (-ε * t)) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => -ε * t) (-ε) t := by
      simpa using (hasDerivAt_id t).const_mul (-ε)
    have h2 : HasDerivAt (fun t : ℝ => t / ε + 1 / ε ^ 2) (1 / ε) t :=
      ((hasDerivAt_id t).div_const ε).add_const (1 / ε ^ 2)
    have h : HasDerivAt (fun t => -(Real.exp (-ε * t) * (t / ε + 1 / ε ^ 2)))
        (-(Real.exp (-ε * t) * (-ε) * (t / ε + 1 / ε ^ 2) + Real.exp (-ε * t) * (1 / ε))) t :=
      (h0.exp.mul h2).neg
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => t * Real.exp (-ε * t)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-! ## The truncated form -/

/-- **The truncated form of the radial profile.** -/
theorem radialProfile_truncated {k : ℝ → ℂ} {A B C D : ℂ} {a c b p : ℝ}
    (hk : ContinuousOn k (Ioi 0)) (hk0 : k =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hkinf : (fun t => k t - cuspProfile A B C D c t) =O[atTop] fun t => t * Real.exp (a * t))
    (ha : a < b) (hb : 0 < b) (hc : Real.sin (c / 2) = 0) (hp : 0 ≤ p) :
    radialProfile (fun t => k t - cuspProfile A B C D c t) A B C D c b =
      ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
        ((∫ t in Ioc 0 p, k t * (Real.exp (-b * t) : ℂ)) +
          ∫ t in Ioi p, (k t - (A * ((t : ℂ) * (Real.exp (c * t) : ℂ)) +
            B * (Real.exp (c * t) : ℂ))) * (Real.exp (-b * t) : ℂ)) +
        ((Real.sinc ((b - c) / 2) ^ 2 * Real.exp (-(b - c) * p) : ℝ) : ℂ) *
          (A + (B + p * A) * ((b - c : ℝ) : ℂ)) := by
  set w : ℝ → ℂ := fun t => (Real.exp (-b * t) : ℂ) with hw
  set E : ℝ → ℂ := fun t => A * ((t : ℂ) * (Real.exp (c * t) : ℂ)) + B * (Real.exp (c * t) : ℂ)
    with hE
  set Q : ℝ → ℂ := fun t => C * (t : ℂ) + D with hQ
  have hcusp : ∀ t, cuspProfile A B C D c t = E t + Q t := fun t => by
    simp only [cuspProfile, hE, hQ]
    ring
  -- integrability
  have isub : IntegrableOn (fun t => (k t - cuspProfile A B C D c t) * w t) (Ioi 0) :=
    integrableOn_sub_cuspProfile hk hk0 hkinf ha
  have iQ : IntegrableOn (fun t => Q t * w t) (Ioi 0) := by
    refine (integrableOn_cuspProfile 0 0 C D le_rfl hb).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [cuspProfile, hQ, hw]
  have hEcont : Continuous fun t => E t * w t := by
    simp only [hE, hw]
    fun_prop
  have iE : IntegrableOn (fun t => E t * w t) (Ioc 0 p) :=
    (hEcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIocIoi : Ioc (0 : ℝ) p ⊆ Ioi 0 := fun t ht => ht.1
  have hIoiIoi : Ioi p ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_le_of_lt hp ht
  have ik : IntegrableOn (fun t => k t * w t) (Ioc 0 p) := by
    refine (((isub.mono_set hIocIoi).add iE).add (iQ.mono_set hIocIoi)).congr_fun
      (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.add_apply, hcusp]
    ring
  have ikE : IntegrableOn (fun t => (k t - E t) * w t) (Ioi p) := by
    refine ((isub.mono_set hIoiIoi).add (iQ.mono_set hIoiIoi)).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, hcusp]
    ring
  -- the split of the subtracted integral
  have hsplit : ∫ t in Ioi 0, (k t - cuspProfile A B C D c t) * w t =
      ((∫ t in Ioc 0 p, k t * w t) + ∫ t in Ioi p, (k t - E t) * w t) -
        (∫ t in Ioc 0 p, E t * w t) - ∫ t in Ioi 0, Q t * w t := by
    have hu : Ioi (0 : ℝ) = Ioc 0 p ∪ Ioi p := (Ioc_union_Ioi_eq_Ioi hp).symm
    have hdisj : Disjoint (Ioc (0 : ℝ) p) (Ioi p) := Ioc_disjoint_Ioi le_rfl
    have h1 : ∫ t in Ioi 0, (k t - cuspProfile A B C D c t) * w t =
        (∫ t in Ioc 0 p, (k t - cuspProfile A B C D c t) * w t) +
          ∫ t in Ioi p, (k t - cuspProfile A B C D c t) * w t := by
      rw [hu]
      exact setIntegral_union hdisj measurableSet_Ioi (isub.mono_set hIocIoi)
        (isub.mono_set hIoiIoi)
    have h2 : ∫ t in Ioi 0, Q t * w t =
        (∫ t in Ioc 0 p, Q t * w t) + ∫ t in Ioi p, Q t * w t := by
      rw [hu]
      exact setIntegral_union hdisj measurableSet_Ioi (iQ.mono_set hIocIoi) (iQ.mono_set hIoiIoi)
    have h3 : ∫ t in Ioc 0 p, (k t - cuspProfile A B C D c t) * w t =
        (∫ t in Ioc 0 p, k t * w t) - (∫ t in Ioc 0 p, E t * w t) -
          ∫ t in Ioc 0 p, Q t * w t := by
      have e1 : ∫ t in Ioc 0 p, (k t * w t - E t * w t) =
          (∫ t in Ioc 0 p, k t * w t) - ∫ t in Ioc 0 p, E t * w t := integral_sub ik iE
      have ikE' : IntegrableOn (fun t => k t * w t - E t * w t) (Ioc 0 p) := ik.sub iE
      have e2 : ∫ t in Ioc 0 p, ((k t * w t - E t * w t) - Q t * w t) =
          (∫ t in Ioc 0 p, (k t * w t - E t * w t)) - ∫ t in Ioc 0 p, Q t * w t :=
        integral_sub ikE' (iQ.mono_set hIocIoi)
      rw [← e1, ← e2]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      simp only [hcusp]
      ring
    have h4 : ∫ t in Ioi p, (k t - cuspProfile A B C D c t) * w t =
        (∫ t in Ioi p, (k t - E t) * w t) - ∫ t in Ioi p, Q t * w t := by
      have e3 : ∫ t in Ioi p, ((k t - E t) * w t - Q t * w t) =
          (∫ t in Ioi p, (k t - E t) * w t) - ∫ t in Ioi p, Q t * w t :=
        integral_sub ikE (iQ.mono_set hIoiIoi)
      rw [← e3]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hcusp]
      ring
    rw [h1, h2, h3, h4]
    ring
  -- the polynomial part
  have hLQ : ((b : ℂ) ^ 2) * ∫ t in Ioi 0, Q t * w t = C + D * (b : ℂ) := by
    have h := integral_cuspProfile 0 0 C D le_rfl hb
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have h' : ∫ t in Ioi 0, Q t * w t = cuspProfileLaplace 0 0 C D 0 b := by
      rw [← h]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp [cuspProfile, hQ, hw]
    rw [h', cuspProfileLaplace]
    push_cast
    field_simp
    ring
  have hsin0 : ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) =
      ((Real.sinc (b / 2) ^ 2 : ℝ) : ℂ) * (b : ℂ) ^ 2 := by
    have h := four_sin_sq_div_sq (b := b) (c := 0) (by simp) (by simpa using hb.ne')
    simp only [sub_zero] at h
    rw [← h]
    push_cast
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
  -- names for the four numbers
  obtain ⟨X, hXdef⟩ : ∃ X : ℂ, X = (∫ t in Ioc 0 p, k t * w t) +
      ∫ t in Ioi p, (k t - E t) * w t := ⟨_, rfl⟩
  obtain ⟨IE, hIEdef⟩ : ∃ IE : ℂ, IE = ∫ t in Ioc 0 p, E t * w t := ⟨_, rfl⟩
  obtain ⟨LQ, hLQdef⟩ : ∃ LQ : ℂ, LQ = ∫ t in Ioi 0, Q t * w t := ⟨_, rfl⟩
  rw [← hXdef, ← hIEdef, ← hLQdef] at hsplit
  rw [← hLQdef] at hLQ
  show ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
        (∫ t in Ioi 0, (k t - cuspProfile A B C D c t) * w t) +
      ((A + B * ((b - c : ℝ) : ℂ)) * ((Real.sinc ((b - c) / 2) ^ 2 : ℝ) : ℂ) +
        (C + D * (b : ℂ)) * ((Real.sinc (b / 2) ^ 2 : ℝ) : ℂ)) =
    ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) *
        ((∫ t in Ioc 0 p, k t * w t) + ∫ t in Ioi p, (k t - E t) * w t) +
      ((Real.sinc ((b - c) / 2) ^ 2 * Real.exp (-(b - c) * p) : ℝ) : ℂ) *
        (A + (B + p * A) * ((b - c : ℝ) : ℂ))
  rw [← hXdef, hsplit]
  by_cases hε : b - c = 0
  · -- `b = c`: the factor `4 sin²(b/2)` vanishes
    have hbc : b = c := by linarith
    have hT0 : ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hbc, hc]
      simp
    have hbne : (b : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hb.ne')
    have hS0z : ((Real.sinc (b / 2) ^ 2 : ℝ) : ℂ) = 0 := by
      have h : ((Real.sinc (b / 2) ^ 2 : ℝ) : ℂ) * (b : ℂ) ^ 2 = 0 := by rw [← hsin0, hT0]
      exact (mul_eq_zero.mp h).resolve_right hbne
    rw [hT0, hS0z]
    simp [hε]
  · -- `b ≠ c`
    have hsin : ((4 * Real.sin (b / 2) ^ 2 : ℝ) : ℂ) =
        ((Real.sinc ((b - c) / 2) ^ 2 : ℝ) : ℂ) * ((b - c : ℝ) : ℂ) ^ 2 := by
      have h := four_sin_sq_div_sq (b := b) hc hε
      rw [← h]
      push_cast
      have hε' : ((b : ℂ) - (c : ℂ)) ≠ 0 := by exact_mod_cast hε
      field_simp
    have hIEval : ((b - c : ℝ) : ℂ) ^ 2 * IE =
        A * (1 - (Real.exp (-(b - c) * p) : ℂ)) -
          A * (p : ℂ) * ((b - c : ℝ) : ℂ) * (Real.exp (-(b - c) * p) : ℂ) +
          B * ((b - c : ℝ) : ℂ) * (1 - (Real.exp (-(b - c) * p) : ℂ)) := by
      have hpt : ∀ t : ℝ, E t * w t =
          A * ((t * Real.exp (-(b - c) * t) : ℝ) : ℂ) +
            B * ((Real.exp (-(b - c) * t) : ℝ) : ℂ) := by
        intro t
        have he : Real.exp (-(b - c) * t) = Real.exp (c * t) * Real.exp (-b * t) := by
          rw [← Real.exp_add]
          ring_nf
        simp only [hE, hw, he]
        push_cast
        ring
      have i1 : IntegrableOn (fun t : ℝ => ((t * Real.exp (-(b - c) * t) : ℝ) : ℂ)) (Ioc 0 p) :=
        ((by fun_prop : Continuous fun t : ℝ =>
          ((t * Real.exp (-(b - c) * t) : ℝ) : ℂ)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have i2 : IntegrableOn (fun t : ℝ => ((Real.exp (-(b - c) * t) : ℝ) : ℂ)) (Ioc 0 p) :=
        ((by fun_prop : Continuous fun t : ℝ =>
          ((Real.exp (-(b - c) * t) : ℝ) : ℂ)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hIE' : IE = A * ((∫ t in Ioc 0 p, t * Real.exp (-(b - c) * t) : ℝ) : ℂ) +
          B * ((∫ t in Ioc 0 p, Real.exp (-(b - c) * t) : ℝ) : ℂ) := by
        rw [hIEdef, ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
          ← integral_const_mul, ← integral_add (i1.const_mul A) (i2.const_mul B)]
        exact setIntegral_congr_fun measurableSet_Ioc fun t _ => hpt t
      have h1 := integral_Ioc_exp_neg_mul hε hp
      have h2 := integral_Ioc_mul_exp_neg_mul hε hp
      have h1c : ((b - c : ℝ) : ℂ) * ((∫ t in Ioc 0 p, Real.exp (-(b - c) * t) : ℝ) : ℂ) =
          1 - (Real.exp (-(b - c) * p) : ℂ) := by exact_mod_cast h1
      have h2c : ((b - c : ℝ) : ℂ) ^ 2 *
          ((∫ t in Ioc 0 p, t * Real.exp (-(b - c) * t) : ℝ) : ℂ) =
          1 - (Real.exp (-(b - c) * p) : ℂ) -
            (p : ℂ) * ((b - c : ℝ) : ℂ) * (Real.exp (-(b - c) * p) : ℂ) := by exact_mod_cast h2
      rw [hIE']
      linear_combination A * h2c + B * ((b - c : ℝ) : ℂ) * h1c
    push_cast at hsin hsin0 hIEval hLQ ⊢
    linear_combination (-IE) * hsin - ((Real.sinc ((b - c) / 2) : ℂ)) ^ 2 * hIEval -
      LQ * hsin0 - ((Real.sinc (b / 2) : ℂ)) ^ 2 * hLQ

end E8Leech
