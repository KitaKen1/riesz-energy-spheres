import E8Leech.CKMRVLaplaceHolomorphicLeechPlus

/-!
# The Laplace representation at all radii (CKMRV (5.3)/(5.4), P4d-5a)

`K − G = O(|z|^k e^{−π Im z})` at the cusp ((4.38)), so `∫₀^∞ (K − G)(τ, it) e^{−bt} dt`
converges for every `b > −π`, in particular at `b = 0` (radius `0`). The cusp terms are
explicit on the imaginary axis:
`G(τ, it) = A t e^{ct} + B e^{ct} + C t + D` with `c = 2π` for the Leech lattice (the `e^{−2πiz}`
terms) and `A = B = 0` for `d = 8`. Their Laplace transform is
`A/(b − c)² + B/(b − c) + C/b² + D/b`, so in the convergence range of (5.1)

  `∫ K e^{−bt} = ∫ (K − G) e^{−bt} + A/(b − c)² + B/(b − c) + C/b² + D/b`.

The right side is defined for every `b > 0` with `b ≠ c`; the poles at `b = 0` and `b = 2π`
(`r² = 0, 2`) are cancelled by `4 sin²(b/2)` in (5.1). This is the representation used for small
radii (CKMRV (5.3)/(5.4)).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real

/-! ## Elementary Laplace transforms -/

theorem integral_exp_mul_exp_Ioi {c b : ℝ} (h : c < b) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ) = ((b - c)⁻¹ : ℝ) := by
  have hr : 0 < b - c := sub_pos.mpr h
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi one_pos hr
  rw [sub_self, Real.Gamma_one, mul_one, Real.rpow_one, one_div] at hI
  rw [← hI, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Real.rpow_zero, one_mul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem integral_mul_exp_mul_exp_Ioi {c b : ℝ} (h : c < b) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) * (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ) =
      (((b - c) ^ 2)⁻¹ : ℝ) := by
  have hr : 0 < b - c := sub_pos.mpr h
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hr
  have hG : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one]
    norm_num
  rw [hG, mul_one, one_div, Real.inv_rpow hr.le] at hI
  norm_num at hI
  rw [← hI, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, ← Complex.ofReal_mul]
  ring_nf

theorem integrableOn_exp_mul_exp_Ioi {c b : ℝ} (h : c < b) :
    IntegrableOn (fun t : ℝ => (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := c) h
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (c * t) : ℂ)).continuousOn
    (((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => (Real.exp (c * t) : ℂ)) 0)
      |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ)
    (IsBigO.of_bound 1 (by
      filter_upwards [eventually_ge_atTop 1] with t ht
      rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le), one_mul]
      exact le_mul_of_one_le_left (Real.exp_pos _).le ht))

theorem integrableOn_mul_exp_mul_exp_Ioi {c b : ℝ} (h : c < b) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ))
      (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := c) h
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (Real.exp (c * t) : ℂ)).continuousOn
    (((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => (t : ℂ) *
      (Real.exp (c * t) : ℂ)) 0) |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ)
    (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        one_mul]))

/-- The cusp profile `A t e^{ct} + B e^{ct} + C t + D`. -/
def cuspProfile (A B C D : ℂ) (c t : ℝ) : ℂ :=
  A * ((t : ℂ) * (Real.exp (c * t) : ℂ)) + B * (Real.exp (c * t) : ℂ) + C * (t : ℂ) + D

/-- Its Laplace transform `A/(b − c)² + B/(b − c) + C/b² + D/b`. -/
def cuspProfileLaplace (A B C D : ℂ) (c b : ℝ) : ℂ :=
  A * (((b - c) ^ 2)⁻¹ : ℝ) + B * ((b - c)⁻¹ : ℝ) + C * ((b ^ 2)⁻¹ : ℝ) + D * (b⁻¹ : ℝ)

theorem continuous_cuspProfile (A B C D : ℂ) (c : ℝ) : Continuous (cuspProfile A B C D c) := by
  unfold cuspProfile
  fun_prop

theorem integrableOn_cuspProfile (A B C D : ℂ) {c b : ℝ} (hc : 0 ≤ c) (h : c < b) :
    IntegrableOn (fun t => cuspProfile A B C D c t * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  have h0 : (0 : ℝ) < b := lt_of_le_of_lt hc h
  have e0 : ∀ t : ℝ, (Real.exp (0 * t) : ℂ) = 1 := fun t => by simp
  have i1 := (integrableOn_mul_exp_mul_exp_Ioi h).const_mul A
  have i2 := (integrableOn_exp_mul_exp_Ioi h).const_mul B
  have i3 := (integrableOn_mul_exp_mul_exp_Ioi (c := 0) h0).const_mul C
  have i4 := (integrableOn_exp_mul_exp_Ioi (c := 0) h0).const_mul D
  refine IntegrableOn.congr_fun (((i1.add i2).add i3).add i4) (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, cuspProfile, e0]
  ring

theorem integral_cuspProfile (A B C D : ℂ) {c b : ℝ} (hc : 0 ≤ c) (h : c < b) :
    ∫ t in Ioi 0, cuspProfile A B C D c t * (Real.exp (-b * t) : ℂ) =
      cuspProfileLaplace A B C D c b := by
  have h0 : (0 : ℝ) < b := lt_of_le_of_lt hc h
  have e0 : ∀ t : ℝ, (Real.exp (0 * t) : ℂ) = 1 := fun t => by simp
  have i1 := (integrableOn_mul_exp_mul_exp_Ioi h).const_mul A
  have i2 := (integrableOn_exp_mul_exp_Ioi h).const_mul B
  have i3 := (integrableOn_mul_exp_mul_exp_Ioi (c := 0) h0).const_mul C
  have i4 := (integrableOn_exp_mul_exp_Ioi (c := 0) h0).const_mul D
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), cuspProfile A B C D c t * (Real.exp (-b * t) : ℂ) =
      A * ((t : ℂ) * (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        B * ((Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        C * ((t : ℂ) * (Real.exp (0 * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        D * ((Real.exp (0 * t) : ℂ) * (Real.exp (-b * t) : ℂ)) := fun t _ => by
    simp only [cuspProfile, e0]
    ring
  have i12 : IntegrableOn (fun t : ℝ =>
      A * ((t : ℂ) * (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        B * ((Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ))) (Ioi 0) := i1.add i2
  have i123 : IntegrableOn (fun t : ℝ =>
      A * ((t : ℂ) * (Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        B * ((Real.exp (c * t) : ℂ) * (Real.exp (-b * t) : ℂ)) +
        C * ((t : ℂ) * (Real.exp (0 * t) : ℂ) * (Real.exp (-b * t) : ℂ))) (Ioi 0) := i12.add i3
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add i123 i4,
    integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_mul_exp_mul_exp_Ioi h,
    integral_exp_mul_exp_Ioi h, integral_mul_exp_mul_exp_Ioi (c := 0) h0,
    integral_exp_mul_exp_Ioi (c := 0) h0, sub_zero]
  rfl

/-! ## A general subtraction lemma -/

/-- If `K = O(1)` near `0`, `K − G = O(t e^{a t})` at `∞`, and `G` is a cusp profile, then
`∫ (K − G) e^{−bt}` converges for all `b > a`, and `∫ K e = ∫ (K − G) e + Ĝ(b)` for `b > c`. -/
theorem integrableOn_sub_cuspProfile {k : ℝ → ℂ} {A B C D : ℂ} {a c b : ℝ}
    (hk : ContinuousOn k (Ioi 0)) (hk0 : k =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hkinf : (fun t => k t - cuspProfile A B C D c t) =O[atTop] fun t => t * Real.exp (a * t))
    (hb : a < b) :
    IntegrableOn (fun t => (k t - cuspProfile A B C D c t) * (Real.exp (-b * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO hb (hk.sub (continuous_cuspProfile A B C D c).continuousOn)
    (hk0.sub (((continuous_cuspProfile A B C D c).tendsto 0).mono_left nhdsWithin_le_nhds
      |>.isBigO_one ℝ)) hkinf

theorem integral_eq_sub_cuspProfile {k : ℝ → ℂ} {A B C D : ℂ} {a c b : ℝ}
    (hk : ContinuousOn k (Ioi 0)) (hk0 : k =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hkinf : (fun t => k t - cuspProfile A B C D c t) =O[atTop] fun t => t * Real.exp (a * t))
    (ha : a < b) (hc : 0 ≤ c) (h : c < b) :
    ∫ t in Ioi 0, k t * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (k t - cuspProfile A B C D c t) * (Real.exp (-b * t) : ℂ)) +
        cuspProfileLaplace A B C D c b := by
  have i1 := integrableOn_sub_cuspProfile hk hk0 hkinf ha
  have i2 := integrableOn_cuspProfile A B C D hc h
  rw [← integral_cuspProfile A B C D hc h, ← integral_add i1 i2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ## The cusp terms on the imaginary axis -/

theorem cuspS_imagPt {t : ℝ} (ht : 0 < t) : cuspS (imagPt t) = (Real.exp (-π * t) : ℂ) := by
  rw [cuspS, coe_imagPt ht, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (π * (t : ℂ)) * Complex.I_sq

theorem cuspS_imagPt_sq_inv {t : ℝ} (ht : 0 < t) :
    (cuspS (imagPt t) ^ 2)⁻¹ = (Real.exp (2 * π * t) : ℂ) := by
  rw [cuspS_imagPt ht, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Real.exp_nat_mul,
    ← Real.exp_neg]
  congr 2
  push_cast
  ring

theorem ckmrvEightMinusG_imagPt (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    ckmrvEightMinusG τ (imagPt t) = cuspProfile 0 0
      (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 τ)
      (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 τ * (4 * Real.log 2) +
        eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ)) 0 t := by
  rw [ckmrvEightMinusG, coe_imagPt ht, cuspProfile]
  linear_combination (-ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 τ * π * t) * Complex.I_sq

theorem ckmrvEightPlusG_imagPt (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    ckmrvEightPlusG τ (imagPt t) = cuspProfile 0 0
      (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ *
        (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))
      (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))) 0 t := by
  rw [ckmrvEightPlusG, coe_imagPt ht, cuspProfile]
  linear_combination (ckmrvPlusScale⁻¹ * 12 / (π : ℂ) *
    (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) * t) *
      Complex.I_sq

theorem ckmrvLeechMinusG_imagPt (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    ckmrvLeechMinusG τ (imagPt t) = cuspProfile
      (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant τ)))
      (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant τ) +
        (leechMinusBeta τ + leechMinusAlpha τ)))
      (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant τ *
        (720 - kleinModularJ τ))))
      (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant τ *
        (720 - kleinModularJ τ)) +
        ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) -
          leechMinusNZeroC τ))) (2 * π) t := by
  rw [ckmrvLeechMinusG, cuspS_imagPt_sq_inv ht, ckmrvEll, coe_imagPt ht, cuspProfile]
  linear_combination (ckmrvMinusScale⁻¹ * π * (t : ℂ) *
    ((Real.exp (2 * π * t) : ℂ) * (2 * 1728 * ModularForm.discriminant τ) +
      (-(2 * 1728) * ModularForm.discriminant τ * (720 - kleinModularJ τ)))) * Complex.I_sq

theorem ckmrvLeechPlusG_imagPt (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    ckmrvLeechPlusG τ (imagPt t) = cuspProfile
      ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a τ))
      ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a τ)
      ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c τ))
      ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c τ) (2 * π) t := by
  rw [ckmrvLeechPlusG, cuspS_imagPt_sq_inv ht, coe_imagPt ht, cuspProfile]
  ring

/-! ## The four kernels -/

theorem kleinModularJ_ne_imagPt_of_not_mem_jCut {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t) := fun _ ht h =>
  hτ (h ▸ kleinModularJ_imagPt_mem_jCut ht)

theorem isBigO_sub_cuspProfile_of_eventuallyEq {k g : ℝ → ℂ} {A B C D : ℂ} {c : ℝ}
    {w : ℝ → ℝ} (hg : ∀ t, 0 < t → g t = cuspProfile A B C D c t)
    (h : (fun t => k t - g t) =O[atTop] w) :
    (fun t => k t - cuspProfile A B C D c t) =O[atTop] w :=
  h.congr' (by filter_upwards [eventually_gt_atTop 0] with t ht; rw [hg t ht])
    (Eventually.of_forall fun _ => rfl)

theorem isBigO_mul_exp_neg_pi_sq {f : ℝ → ℂ}
    (hf : f =O[atTop] fun t => t ^ 2 * Real.exp (-2 * π * t)) :
    f =O[atTop] fun t => t * Real.exp (-π * t) :=
  hf.trans ((isBigO_sq_mul_exp_shift (c := -2 * π) Real.pi_pos).congr_right fun t => by
    congr 2
    ring)

/-- **(5.3), `d = 8`, minus kernel.** -/
theorem integral_ckmrvEightMinusKernel_eq_sub_G {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (ckmrvEightMinusKernel τ (imagPt t) -
        ckmrvEightMinusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace 0 0 (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 τ)
        (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 τ * (4 * Real.log 2) +
          eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ)) 0 b := by
  have hkinf : (fun t => ckmrvEightMinusKernel τ (imagPt t) - ckmrvEightMinusG τ (imagPt t))
      =O[atTop] fun t => t * Real.exp (-π * t) :=
    isBigO_comp_imagPt (w := fun x => x) (c := -π) (isBigO_ckmrvEightMinusKernel_sub_G τ)
  rw [integral_eq_sub_cuspProfile (continuousOn_ckmrvEightMinusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvEightMinusKernel_imagPt_zero τ)
      (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvEightMinusG_imagPt τ ht) hkinf)
      (by linarith [Real.pi_pos]) le_rfl hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ckmrvEightMinusG_imagPt τ ht]

/-- **(5.3), `d = 8`, minus kernel: convergence at every radius.** -/
theorem integrableOn_ckmrvEightMinusKernel_sub_G {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut)
    {b : ℝ} (hb : -π < b) :
    IntegrableOn (fun t => (ckmrvEightMinusKernel τ (imagPt t) -
      ckmrvEightMinusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  have hkinf : (fun t => ckmrvEightMinusKernel τ (imagPt t) - ckmrvEightMinusG τ (imagPt t))
      =O[atTop] fun t => t * Real.exp (-π * t) :=
    isBigO_comp_imagPt (w := fun x => x) (c := -π) (isBigO_ckmrvEightMinusKernel_sub_G τ)
  refine (integrableOn_sub_cuspProfile (continuousOn_ckmrvEightMinusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvEightMinusKernel_imagPt_zero τ)
      (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvEightMinusG_imagPt τ ht) hkinf)
      hb).congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [ckmrvEightMinusG_imagPt τ ht]

/-- **(5.3), `d = 8`, plus kernel.** -/
theorem integral_ckmrvEightPlusKernel_eq_sub_G {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (ckmrvEightPlusKernel τ (imagPt t) -
        ckmrvEightPlusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace 0 0
        (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ *
          (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))
        (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))) 0 b := by
  have hkinf : (fun t => ckmrvEightPlusKernel τ (imagPt t) - ckmrvEightPlusG τ (imagPt t))
      =O[atTop] fun t => t * Real.exp (-π * t) :=
    isBigO_mul_exp_neg_pi_sq (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -2 * π)
      (isBigO_ckmrvEightPlusKernel_sub_G τ))
  rw [integral_eq_sub_cuspProfile (continuousOn_ckmrvEightPlusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvEightPlusKernel_imagPt_zero τ)
      (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvEightPlusG_imagPt τ ht) hkinf)
      (by linarith [Real.pi_pos]) le_rfl hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ckmrvEightPlusG_imagPt τ ht]

/-- **(5.4), Leech minus kernel.** Valid for `b > 2π`; the right side is defined for all
`b > 0`, `b ≠ 2π`. -/
theorem integral_ckmrvLeechMinusKernel_eq_sub_G {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (ckmrvLeechMinusKernel τ (imagPt t) -
        ckmrvLeechMinusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace
        (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant τ)))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant τ) +
          (leechMinusBeta τ + leechMinusAlpha τ)))
        (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant τ *
          (720 - kleinModularJ τ))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant τ *
          (720 - kleinModularJ τ)) +
          ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) -
            leechMinusNZeroC τ))) (2 * π) b := by
  have hkinf : (fun t => ckmrvLeechMinusKernel τ (imagPt t) - ckmrvLeechMinusG τ (imagPt t))
      =O[atTop] fun t => t * Real.exp (-π * t) :=
    isBigO_comp_imagPt (w := fun x => x) (c := -π) (isBigO_ckmrvLeechMinusKernel_sub_G τ)
  rw [integral_eq_sub_cuspProfile (continuousOn_ckmrvLeechMinusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvLeechMinusKernel_imagPt_zero τ)
      (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvLeechMinusG_imagPt τ ht) hkinf)
      (by linarith [Real.pi_pos]) (by positivity) hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ckmrvLeechMinusG_imagPt τ ht]

/-- **(5.4), Leech plus kernel.** -/
theorem integral_ckmrvLeechPlusKernel_eq_sub_G {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (ckmrvLeechPlusKernel τ (imagPt t) -
        ckmrvLeechPlusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a τ))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a τ)
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c τ))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c τ) (2 * π) b := by
  have hkinf : (fun t => ckmrvLeechPlusKernel τ (imagPt t) - ckmrvLeechPlusG τ (imagPt t))
      =O[atTop] fun t => t * Real.exp ((-π + π / 2) * t) :=
    (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -π)
      (isBigO_ckmrvLeechPlusKernel_sub_G τ)).trans
      (isBigO_sq_mul_exp_shift (c := -π) (ε := π / 2) (by positivity))
  rw [integral_eq_sub_cuspProfile (continuousOn_ckmrvLeechPlusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvLeechPlusKernel_imagPt_zero τ)
      (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvLeechPlusG_imagPt τ ht) hkinf)
      (by linarith [Real.pi_pos]) (by positivity) hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ckmrvLeechPlusG_imagPt τ ht]

end E8Leech
