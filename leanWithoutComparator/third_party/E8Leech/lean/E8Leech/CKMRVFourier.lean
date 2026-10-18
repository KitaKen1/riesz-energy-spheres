import E8Leech.CKMRVSchwartz
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Fourier transform of the CKMRV radial functions as a `t`-integral of Gaussians (P4d-4′)

For `g` on `(0, ∞)` with `∫₀^∞ |g(t)| t^{−d/2} dt < ∞`, the radial function
`φ(v) = 4 sin²(π|v|²/2) ∫₀^∞ g(t) e^{−π|v|²t} dt` on a `d`-dimensional real inner product space
has Fourier transform
`φ̂(w) = ∫₀^∞ g(t) (2 γ(t, w) − γ(t − i, w) − γ(t + i, w)) dt`,
where `γ(a, w) = (π/(πa))^{d/2} e^{−π²|w|²/(πa)} = a^{−d/2} e^{−π|w|²/a}` is the Fourier transform
of `v ↦ e^{−πa|v|²}`.
Proof: `4 sin²(πr²/2) e^{−πr²t} = 2e^{−πr²t} − e^{−πr²(t−i)} − e^{−πr²(t+i)}`, Fubini, and Mathlib's
Fourier transform of Gaussians.

For `d = 8` the hypothesis holds for both kernels on the axis (`K(iβ, it) = O(t)` at `∞`). So the
Fourier transforms of the Schwartz functions of `CKMRVSchwartz` are such `t`-integrals. The
identity (**) then reduces to a one-variable contour shift of the `t ± i` terms (P4d-4″).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real FourierTransform RealInnerProductSpace

/-! ## The Gaussian combination -/

/-- `2e^{−πtr²} − e^{−π(t−i)r²} − e^{−π(t+i)r²}`. -/
def sinSqGauss (t r : ℝ) : ℂ :=
  2 * cexp (-(π * (t : ℂ)) * (r : ℂ) ^ 2) - cexp (-(π * ((t : ℂ) - I)) * (r : ℂ) ^ 2) -
    cexp (-(π * ((t : ℂ) + I)) * (r : ℂ) ^ 2)

theorem sinSqGauss_eq (t r : ℝ) :
    sinSqGauss t r = ((4 * Real.sin (π * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ) := by
  have h := two_sub_cexp_sub_cexp (r ^ 2)
  have e0 : ((Real.exp (-(π * r ^ 2) * t) : ℝ) : ℂ) = cexp (-(π * (t : ℂ)) * (r : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have e1 : cexp (-(π * ((t : ℂ) - I)) * (r : ℂ) ^ 2) =
      cexp (-(π * (t : ℂ)) * (r : ℂ) ^ 2) * cexp (((π * r ^ 2 : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : cexp (-(π * ((t : ℂ) + I)) * (r : ℂ) ^ 2) =
      cexp (-(π * (t : ℂ)) * (r : ℂ) ^ 2) * cexp (-((π * r ^ 2 : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [sinSqGauss, e1, e2, e0, ← h]
  ring

theorem norm_sinSqGauss_le (t r : ℝ) :
    ‖sinSqGauss t r‖ ≤ 4 * Real.exp (-(π * t) * r ^ 2) := by
  have hs : Real.sin (π * r ^ 2 / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (π * r ^ 2 / 2), sq_nonneg (Real.cos (π * r ^ 2 / 2))]
  have he : Real.exp (-(π * r ^ 2) * t) = Real.exp (-(π * t) * r ^ 2) := by
    congr 1
    ring
  rw [sinSqGauss_eq, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sin (π * r ^ 2 / 2) ^ 2),
    abs_of_pos (Real.exp_pos _), he]
  have h1 := Real.exp_pos (-(π * t) * r ^ 2)
  nlinarith

theorem continuous_sinSqGauss : Continuous fun p : ℝ × ℝ => sinSqGauss p.1 p.2 := by
  unfold sinSqGauss
  fun_prop

/-! ## Gaussians on a finite-dimensional inner product space -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_sinSqGauss_norm (t : ℝ) : Continuous fun v : V => sinSqGauss t ‖v‖ := by
  unfold sinSqGauss
  fun_prop

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_sinSqGauss_prod : Continuous fun p : ℝ × V => sinSqGauss p.1 ‖p.2‖ := by
  unfold sinSqGauss
  fun_prop

/-- The Fubini integrand `e^{−2πi⟨v,w⟩} g(t) sinSqGauss(t, |v|)`. -/
def fubiniIntegrand (g : ℝ → ℂ) (w : V) (t : ℝ) (v : V) : ℂ :=
  cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) * (g t * sinSqGauss t ‖v‖)

theorem integrable_gaussian_norm_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable (fun v : V => cexp (-b * ‖v‖ ^ 2)) := by
  simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : V)

/-- The Fourier transform of `v ↦ e^{−πa|v|²}` (`Re a > 0`) on a `d`-dimensional space,
`(π/(πa))^{d/2} e^{−π²|w|²/(πa)}`. -/
def gaussHat (d : ℕ) (a : ℂ) (r : ℝ) : ℂ :=
  ((π : ℂ) / (π * a)) ^ ((d : ℂ) / 2) * cexp (-(π : ℂ) ^ 2 * (r : ℂ) ^ 2 / (π * a))

theorem fourier_gauss {a : ℂ} (ha : 0 < a.re) (w : V) :
    𝓕 (fun v : V => cexp (-(π * a) * ‖v‖ ^ 2)) w = gaussHat (Module.finrank ℝ V) a ‖w‖ := by
  have hb : 0 < ((π : ℂ) * a).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos Real.pi_pos ha
  rw [fourier_gaussian_innerProductSpace hb]
  rfl

theorem fourier_sinSqGauss {t : ℝ} (ht : 0 < t) (w : V) :
    𝓕 (fun v : V => sinSqGauss t ‖v‖) w =
      2 * gaussHat (Module.finrank ℝ V) t ‖w‖ - gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ -
        gaussHat (Module.finrank ℝ V) (t + I) ‖w‖ := by
  have hre : ∀ c : ℂ, c.re = t → 0 < ((π : ℂ) * c).re := fun c hc => by
    rw [Complex.re_ofReal_mul, hc]
    exact mul_pos Real.pi_pos ht
  have hi : ∀ c : ℂ, c.re = t →
      Integrable (fun v : V => 𝐞 (-⟪v, w⟫) • cexp (-(π * c) * ‖v‖ ^ 2)) :=
    fun c hc => (Real.fourierIntegral_convergent_iff w).mpr
      (integrable_gaussian_norm_sq (hre c hc))
  have hF : ∀ c : ℂ, c.re = t →
      ∫ v : V, 𝐞 (-⟪v, w⟫) • cexp (-(π * c) * ‖v‖ ^ 2) =
        gaussHat (Module.finrank ℝ V) c ‖w‖ := fun c hc => by
    rw [← fourier_gauss (by rw [hc]; exact ht) w, Real.fourier_eq]
  have e1 : (t : ℂ).re = t := Complex.ofReal_re t
  have e2 : ((t : ℂ) - I).re = t := by simp
  have e3 : ((t : ℂ) + I).re = t := by simp
  have h1 : Integrable (fun v : V => 2 * (𝐞 (-⟪v, w⟫) • cexp (-(π * (t : ℂ)) * ‖v‖ ^ 2))) :=
    (hi _ e1).const_mul 2
  have h12 : Integrable (fun v : V => 2 * (𝐞 (-⟪v, w⟫) • cexp (-(π * (t : ℂ)) * ‖v‖ ^ 2)) -
      𝐞 (-⟪v, w⟫) • cexp (-(π * ((t : ℂ) - I)) * ‖v‖ ^ 2)) := h1.sub (hi _ e2)
  rw [Real.fourier_eq]
  calc ∫ v : V, 𝐞 (-⟪v, w⟫) • sinSqGauss t ‖v‖
      = ∫ v : V, (2 * (𝐞 (-⟪v, w⟫) • cexp (-(π * (t : ℂ)) * ‖v‖ ^ 2)) -
          𝐞 (-⟪v, w⟫) • cexp (-(π * ((t : ℂ) - I)) * ‖v‖ ^ 2)) -
          𝐞 (-⟪v, w⟫) • cexp (-(π * ((t : ℂ) + I)) * ‖v‖ ^ 2) := by
        congr 1
        ext v
        simp only [sinSqGauss, Circle.smul_def, smul_eq_mul]
        ring
    _ = _ := by
        rw [integral_sub h12 (hi _ e3), integral_sub h1 (hi _ e2), integral_const_mul, hF _ e1,
          hF _ e2, hF _ e3]

/-! ## Fubini -/

/-- **The Fourier transform of `4 sin²(π|v|²/2) ∫₀^∞ g(t) e^{−π|v|²t} dt` is a `t`-integral of
Fourier transforms of Gaussians.** -/
theorem fourier_sin_sq_laplace [Nontrivial V] {g : ℝ → ℂ} {φ : V → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hint : IntegrableOn (fun t : ℝ => ‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2))
      (Ioi 0))
    (hφ : ∀ v : V, v ≠ 0 → φ v = ((4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ))
    (w : V) :
    𝓕 φ w = ∫ t in Ioi 0, g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) := by
  -- `φ` is the `t`-integral of `g · sinSqGauss` off `0`
  have hae : φ =ᵐ[volume] fun v => ∫ t in Ioi 0, g t * sinSqGauss t ‖v‖ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : V))] with v hv0
    have hv : v ≠ 0 := fun h => hv0 (Set.mem_singleton_iff.mpr h)
    rw [hφ v hv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [sinSqGauss_eq]
    ring
  set F : ℝ → V → ℂ := fubiniIntegrand g w with hFdef
  -- facts for fixed `t > 0`
  have hGint : ∀ t : ℝ, 0 < t → Integrable (fun v : V => sinSqGauss t ‖v‖) := by
    intro t ht
    have hre : ∀ c : ℂ, c.re = t → 0 < ((π : ℂ) * c).re := fun c hc => by
      rw [Complex.re_ofReal_mul, hc]
      exact mul_pos Real.pi_pos ht
    exact (((integrable_gaussian_norm_sq (V := V) (hre _ (Complex.ofReal_re t))).const_mul 2).sub
      (integrable_gaussian_norm_sq (V := V) (hre ((t : ℂ) - I) (by simp)))).sub
      (integrable_gaussian_norm_sq (V := V) (hre ((t : ℂ) + I) (by simp)))
  have hnormF : ∀ t : ℝ, ∀ v : V, ‖F t v‖ = ‖g t‖ * ‖sinSqGauss t ‖v‖‖ := by
    intro t v
    simp only [hFdef, fubiniIntegrand, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hFint : ∀ t : ℝ, 0 < t → Integrable (fun v : V => F t v) := by
    intro t ht
    have h1 := continuous_sinSqGauss_norm (V := V) t
    have h2 : Continuous fun v : V => ⟪v, w⟫ := continuous_id.inner continuous_const
    have hc : Continuous fun v : V => F t v := by
      simp only [hFdef, fubiniIntegrand]
      fun_prop
    exact ((hGint t ht).norm.const_mul ‖g t‖).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun v => le_of_eq (hnormF t v))
  have hinner : ∀ t : ℝ, 0 < t → ∫ v, F t v = g t * (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ -
      gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ - gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) := by
    intro t ht
    rw [← fourier_sinSqGauss ht w, Real.fourier_eq', ← integral_const_mul]
    congr 1
    ext v
    simp only [hFdef, fubiniIntegrand, smul_eq_mul]
    ring
  have hbound : ∀ t : ℝ, 0 < t → ∫ v, ‖F t v‖ ≤
      4 * (‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) := by
    intro t ht
    have hb : 0 < π * t := mul_pos Real.pi_pos ht
    have hreal : Integrable (fun v : V => Real.exp (-(π * t) * ‖v‖ ^ 2)) := by
      have h := integrable_gaussian_norm_sq (V := V) (b := ((π * t : ℝ) : ℂ)) (by simpa using hb)
      have e : (fun v : V => cexp (-((π * t : ℝ) : ℂ) * ‖v‖ ^ 2)) =
          fun v => ((Real.exp (-(π * t) * ‖v‖ ^ 2) : ℝ) : ℂ) := by
        ext v
        simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
      rw [e] at h
      exact h.re
    calc ∫ v, ‖F t v‖ ≤ ∫ v, ‖g t‖ * (4 * Real.exp (-(π * t) * ‖v‖ ^ 2)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
            ((hreal.const_mul 4).const_mul _) (Eventually.of_forall fun v => ?_)
          show ‖F t v‖ ≤ ‖g t‖ * (4 * Real.exp (-(π * t) * ‖v‖ ^ 2))
          rw [hnormF]
          exact mul_le_mul_of_nonneg_left (norm_sinSqGauss_le t ‖v‖) (norm_nonneg _)
      _ = 4 * (‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) := by
          rw [integral_const_mul, integral_const_mul,
            GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
          ring
  -- Fubini
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure V)) := by
    have hcont : ContinuousOn (Function.uncurry F) (Ioi 0 ×ˢ univ) := by
      have h1 := continuous_sinSqGauss_prod (V := V)
      have h2 : ContinuousOn (fun p : ℝ × V => g p.1) (Ioi 0 ×ˢ univ) :=
        hg.comp continuous_fst.continuousOn fun p hp => hp.1
      have h3 : Continuous fun p : ℝ × V => ⟪p.2, w⟫ := continuous_snd.inner continuous_const
      have h4 : Continuous fun p : ℝ × V => cexp (((-2 * π * ⟪p.2, w⟫ : ℝ) : ℂ) * I) := by
        fun_prop
      have h5 := h4.continuousOn.mul (h2.mul h1.continuousOn)
      exact h5.congr fun p _ => rfl
    rw [← Measure.restrict_univ (μ := (volume : Measure V)), Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure V)) := by
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hFint t ht)
    · refine Integrable.mono' (hint.const_mul 4) hmeas.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      exact hbound t ht
  rw [Real.fourier_congr_ae hae w, Real.fourier_eq']
  calc ∫ v, cexp (((-2 * π * ⟪v, w⟫ : ℝ) : ℂ) * I) •
        (fun v => ∫ t in Ioi 0, g t * sinSqGauss t ‖v‖) v
      = ∫ v, ∫ t in Ioi 0, F t v := by
        congr 1
        ext v
        simp only [smul_eq_mul, hFdef, fubiniIntegrand]
        rw [← integral_const_mul]
    _ = ∫ t in Ioi 0, ∫ v, F t v := (integral_integral_swap hprod).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht => hinner t ht

/-! ## `d = 8` -/

/-- `‖g(t)‖ t^{−n}` (`n ≥ 3`) is integrable on `(0, ∞)` when `g = O(e^{−π/t})` at `0` and
`g = O(t)` at `∞`. -/
theorem integrableOn_norm_mul_inv_pow {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (0 * t)) {n : ℕ} (hn : 3 ≤ n) :
    IntegrableOn (fun t : ℝ => ‖g t‖ * (t ^ n)⁻¹) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => ‖g t‖ * (t ^ n)⁻¹) (Ioi 0) :=
    hg.norm.mul ((continuousOn_pow n).inv₀ fun t ht => pow_ne_zero n (ne_of_gt ht))
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- bounded near `0`
    obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul n Real.pi_pos
    obtain ⟨M, hMpos, hM⟩ := hg0.exists_pos
    have h0 : (fun t : ℝ => ((‖g t‖ * (t ^ n)⁻¹ : ℝ) : ℂ)) =O[𝓝[>] (0 : ℝ)]
        fun _ => (1 : ℝ) := by
      refine IsBigO.of_bound (M * C) ?_
      filter_upwards [hM.bound, self_mem_nhdsWithin] with t ht htpos
      have htp : (0 : ℝ) < t := htpos
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g t‖ * (t ^ n)⁻¹), norm_one, mul_one]
      have hb := hC t⁻¹ (inv_nonneg.mpr htp.le)
      calc ‖g t‖ * (t ^ n)⁻¹ ≤ M * Real.exp (-π / t) * (t ^ n)⁻¹ :=
            mul_le_mul_of_nonneg_right ht (by positivity)
        _ = M * (t⁻¹ ^ n * Real.exp (-π * t⁻¹)) := by
            rw [inv_pow, div_eq_mul_inv]
            ring
        _ ≤ M * C := mul_le_mul_of_nonneg_left hb hMpos.le
    have hc : ContinuousOn (fun t : ℝ => ((‖g t‖ * (t ^ n)⁻¹ : ℝ) : ℂ)) (Ioc 0 1) :=
      Complex.continuous_ofReal.comp_continuousOn (hcont.mono Ioc_subset_Ioi_self)
    have h : IntegrableOn (fun t : ℝ => ‖((‖g t‖ * (t ^ n)⁻¹ : ℝ) : ℂ)‖) (Ioc 0 1) :=
      (integrableOn_Ioc_of_isBigO hc h0).norm
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have htp : (0 : ℝ) < t := ht.1
    show ‖((‖g t‖ * (t ^ n)⁻¹ : ℝ) : ℂ)‖ = ‖g t‖ * (t ^ n)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · have hcont1 : ContinuousOn (fun t : ℝ => ‖g t‖ * (t ^ n)⁻¹) (Ici 1) :=
      hcont.mono fun t ht => mem_Ioi.mpr (lt_of_lt_of_le one_pos (mem_Ici.mp ht))
    refine (integrableOn_Ici_iff_integrableAtFilter_atTop.mpr
      ⟨?_, hcont1.locallyIntegrableOn measurableSet_Ici⟩).mono_set Ioi_subset_Ici_self
    have hO : (fun t : ℝ => ‖g t‖ * (t ^ n)⁻¹) =O[atTop] fun t : ℝ => t ^ (-2 : ℝ) := by
      obtain ⟨M, hMpos, hM⟩ := hginf.exists_pos
      refine IsBigO.of_bound M ?_
      filter_upwards [hM.bound, eventually_ge_atTop 1] with t ht ht1
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have htne : t ≠ 0 := htpos.ne'
      rw [zero_mul, Real.exp_zero, mul_one, Real.norm_eq_abs, abs_of_pos htpos] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g t‖ * (t ^ n)⁻¹),
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      have h3 : t * (t ^ 3)⁻¹ = (t ^ 2)⁻¹ := by
        rw [show t ^ 3 = t * t ^ 2 by ring, mul_inv, ← mul_assoc, mul_inv_cancel₀ htne, one_mul]
      have h2 : t * (t ^ n)⁻¹ ≤ t ^ (-2 : ℝ) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_two, ← h3]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (pow_pos htpos 3) (pow_le_pow_right₀ ht1 hn)) htpos.le
      calc ‖g t‖ * (t ^ n)⁻¹ ≤ M * t * (t ^ n)⁻¹ :=
            mul_le_mul_of_nonneg_right ht (by positivity)
        _ = M * (t * (t ^ n)⁻¹) := by ring
        _ ≤ M * t ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left h2 hMpos.le
    exact hO.integrableAtFilter
      ⟨Ioi 0, Ioi_mem_atTop 0, hcont.aestronglyMeasurable measurableSet_Ioi⟩
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))

/-- `d = 8` assembly: a kernel on the axis with the `g`-extension data. -/
theorem fourier_of_axis_eight [Nontrivial V] (hd : Module.finrank ℝ V = 8) {g K : ℝ → ℂ}
    {β : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (0 * t))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = K x) {φ : V → ℂ}
    (hφ : ∀ x : V, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, K t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) (w : V) :
    𝓕 φ w = ∫ t in Ioi 0, K t *
      (2 * gaussHat 8 t ‖w‖ - gaussHat 8 (t - I) ‖w‖ - gaussHat 8 (t + I) ‖w‖) := by
  have hφg : ∀ x : V, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := fun x hx => by
    rw [hφ x hx, setIntegral_eq_of_eq_off_two hgK]
  have hint := integrableOn_norm_mul_inv_pow hg hg0 hginf (n := 4) (by norm_num)
  have hint' : IntegrableOn
      (fun t : ℝ => ‖g t‖ * (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) (Ioi 0) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [hd, show ((8 : ℕ) : ℝ) / 2 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_mul_cancel_left₀ Real.pi_ne_zero, inv_pow]
  rw [fourier_sin_sq_laplace hg hint' hφg w, hd, setIntegral_eq_of_eq_off_two hgK]

/-- **The Fourier transform of the `d = 8` minus-kernel Schwartz function on the axis** is the
`t`-integral of `K₋(iβ, it)` against Fourier transforms of Gaussians. -/
theorem fourier_ckmrvEightMinus_axis [Nontrivial V] (hd : Module.finrank ℝ V = 8) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap V ℂ, (∀ x : V, x ≠ 0 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightMinusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) ∧
      ∀ w : V, 𝓕 (⇑φ) w = ∫ t in Ioi 0, ckmrvEightMinusKernel (imagPt β) (imagPt t) *
        (2 * gaussHat 8 t ‖w‖ - gaussHat 8 (t - I) ‖w‖ - gaussHat 8 (t + I) ‖w‖) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvEightMinus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_ckmrvEightMinus_axis V hβ hβ1
  exact ⟨φ, hφ, fourier_of_axis_eight hd hg (isBigO_eightMinusAxis_zero hβ hgK)
    (isBigO_eightMinusAxis_atTop hgK) hgK hφ⟩

/-- **The Fourier transform of the `d = 8` plus-kernel Schwartz function on the axis.** -/
theorem fourier_ckmrvEightPlus_axis [Nontrivial V] (hd : Module.finrank ℝ V = 8) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap V ℂ, (∀ x : V, x ≠ 0 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightPlusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) ∧
      ∀ w : V, 𝓕 (⇑φ) w = ∫ t in Ioi 0, ckmrvEightPlusKernel (imagPt β) (imagPt t) *
        (2 * gaussHat 8 t ‖w‖ - gaussHat 8 (t - I) ‖w‖ - gaussHat 8 (t + I) ‖w‖) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvEightPlus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_ckmrvEightPlus_axis V hβ hβ1
  exact ⟨φ, hφ, fourier_of_axis_eight hd hg (isBigO_eightPlusAxis_zero hβ hgK)
    (isBigO_eightPlusAxis_atTop hgK) hgK hφ⟩

end E8Leech
