import Riesz.CubeEnvelopeQuadrature
import Riesz.GaussianCompositionSixth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! One-dimensional Gaussian bounds for the sixth-order rule.

For `φ(t) = e^{-β(t-b)²}` on `[0,1]`: the integral is at most `min(1, √(π/β))`, at least
`e⁻¹ min(1/2, 1/√γ)` for a center `b ∈ [0,1]`, and the rule average is at most `1` and at most
`C/√β` as long as `β ≤ m²` (the sixth-order `L¹` error of the bump is then of the same size). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The one-dimensional Gaussian profile. -/
def gauss1 (β b t : ℝ) : ℝ := Real.exp (-(β*(t-b)^2))

theorem gauss1_nonneg (β b t : ℝ) : 0 ≤ gauss1 β b t := (Real.exp_pos _).le

theorem gauss1_le_one {β : ℝ} (hβ : 0 ≤ β) (b t : ℝ) : gauss1 β b t ≤ 1 := by
  unfold gauss1
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ β*(t-b)^2 := by positivity
  linarith

theorem continuous_gauss1 (β b : ℝ) : Continuous (gauss1 β b) := by
  unfold gauss1
  fun_prop

theorem gauss1_integral_le_one {β : ℝ} (hβ : 0 ≤ β) (b : ℝ) :
    (∫ t in (0:ℝ)..1, gauss1 β b t) ≤ 1 := by
  calc (∫ t in (0:ℝ)..1, gauss1 β b t) ≤ ∫ t in (0:ℝ)..1, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_gauss1 β b).intervalIntegrable _ _) intervalIntegrable_const
        intro t _
        exact gauss1_le_one hβ b t
    _ = 1 := by simp

theorem gauss1_integral_le_sqrt {β : ℝ} (hβ : 0 < β) (b : ℝ) :
    (∫ t in (0:ℝ)..1, gauss1 β b t) ≤ Real.sqrt (Real.pi/β) := by
  have hint : Integrable (fun t : ℝ => gauss1 β b t) := by
    have h := (integrable_exp_neg_mul_sq hβ).comp_sub_right b
    simpa only [gauss1, neg_mul] using h
  have hfull : (∫ t : ℝ, gauss1 β b t) = Real.sqrt (Real.pi/β) := by
    have h2 := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => Real.exp (-β*t^2)) b
    simp only [gauss1, neg_mul] at h2 ⊢
    rw [h2]
    simpa only [neg_mul] using integral_gaussian β
  rw [intervalIntegral.integral_of_le (by norm_num), ← hfull]
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => gauss1_nonneg β b t)

/-- A Gaussian centered in `[0,1]` keeps a fixed fraction of its width inside `[0,1]`. -/
theorem gauss1_integral_ge {γ b : ℝ} (hγ : 0 < γ) (hb : b ∈ Icc (0:ℝ) 1) :
    Real.exp (-1)*min (1/2) (1/Real.sqrt γ) ≤ ∫ t in (0:ℝ)..1, gauss1 γ b t := by
  set h := min (1/2:ℝ) (1/Real.sqrt γ) with hhdef
  have hh0 : 0 < h := lt_min (by norm_num) (by positivity)
  have hh2 : h ≤ 1/2 := min_le_left _ _
  have hhs : h ≤ 1/Real.sqrt γ := min_le_right _ _
  have hsq : γ*h^2 ≤ 1 := by
    have hs : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
    have h1 : h*Real.sqrt γ ≤ 1 := by
      rw [le_div_iff₀ hs] at hhs
      exact hhs
    have h2 : (h*Real.sqrt γ)^2 ≤ 1 := by nlinarith [mul_pos hh0 hs]
    calc γ*h^2 = (h*Real.sqrt γ)^2 := by rw [mul_pow, Real.sq_sqrt hγ.le]; ring
      _ ≤ 1 := h2
  -- the integrand is at least `e⁻¹` on an interval of length `h` inside `[0,1]`
  have hlow : ∀ t, |t-b| ≤ h → Real.exp (-1) ≤ gauss1 γ b t := by
    intro t ht
    unfold gauss1
    apply Real.exp_le_exp.mpr
    have : (t-b)^2 ≤ h^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ht 2
    nlinarith
  have hcont := continuous_gauss1 γ b
  obtain ⟨c, hc0, hc1, hcb⟩ : ∃ c, 0 ≤ c ∧ c+h ≤ 1 ∧ ∀ t ∈ Icc c (c+h), |t-b| ≤ h := by
    by_cases hb2 : b ≤ 1/2
    · refine ⟨b, hb.1, by linarith, ?_⟩
      intro t ht
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    · refine ⟨b-h, by linarith [hb.2], by linarith [hb.2], ?_⟩
      intro t ht
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hsub : (∫ t in c..c+h, gauss1 γ b t) ≤ ∫ t in (0:ℝ)..1, gauss1 γ b t := by
    apply intervalIntegral.integral_mono_interval hc0 (by linarith) hc1
      (Filter.Eventually.of_forall fun t => gauss1_nonneg γ b t)
      (hcont.intervalIntegrable (μ := volume) _ _)
  have hlo : h*Real.exp (-1) ≤ ∫ t in c..c+h, gauss1 γ b t := by
    have := intervalIntegral.integral_mono_on (a := c) (b := c+h) (by linarith)
      (intervalIntegrable_const (c := Real.exp (-1))) (hcont.intervalIntegrable (μ := volume) _ _)
      (fun t ht => hlow t (hcb t ht))
    simpa [mul_comm] using this
  calc Real.exp (-1)*h = h*Real.exp (-1) := mul_comm _ _
    _ ≤ _ := hlo.trans hsub

theorem gauss1_quadrature_le_one {m : ℕ} (hm : 8 ≤ m) {β : ℝ} (hβ : 0 ≤ β) (b : ℝ) :
    quadrature m (gauss1 β b) ≤ 1 := by
  have h := quadrature_mono hm (f := gauss1 β b) (g := fun _ => (1:ℝ))
    (fun t _ => gauss1_le_one hβ b t)
  rwa [quadrature_const hm] at h

/-- Sixth derivative of the one-dimensional profile. -/
theorem gauss1_sixth_le {β : ℝ} (hβ : 0 ≤ β) (b t : ℝ) :
    ‖iteratedFDeriv ℝ 6 (gauss1 β b) t‖ ≤
      (720*729*26000000)*(1+β^3)*gauss1 (β/2) b t := by
  have hF : ContDiffAt ℝ 6 (fun s : ℝ => s-b) t := by fun_prop
  have hderiv : deriv (fun s : ℝ => s-b) = fun _ => 1 := by
    funext s
    simp
  have hFL : ∀ j, 1 ≤ j → j ≤ 6 → ‖iteratedFDeriv ℝ j (fun s : ℝ => s-b) t‖ ≤ 1 := by
    intro j hj _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
    rw [iteratedDeriv_succ', hderiv, iteratedDeriv_const]
    split_ifs <;> simp
  have h := norm_iteratedFDeriv_six_exp_neg_mul_norm_sq_le hF le_rfl hFL hβ
  have heq : (fun y : ℝ => Real.exp (-(β*‖y-b‖^2))) = gauss1 β b := by
    funext y
    simp [gauss1, Real.norm_eq_abs, sq_abs]
  rw [heq] at h
  have he : Real.exp (-(β*‖t-b‖^2/2)) = gauss1 (β/2) b t := by
    simp only [gauss1, Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [he] at h
  simpa only [one_pow, mul_one] using h

/-- The rule average of a Gaussian of width at least the node spacing. -/
theorem gauss1_quadrature_le {m : ℕ} (hm : 8 ≤ m) {β : ℝ} (hβ : 0 < β)
    (hβm : β ≤ (m:ℝ)^2) (b : ℝ) :
    quadrature m (gauss1 β b) ≤
      (Real.sqrt Real.pi+128*(720*729*26000000)*Real.sqrt (2*Real.pi))/Real.sqrt β := by
  set K : ℝ := 720*729*26000000 with hK
  have hcd : ContDiffOn ℝ 6 (gauss1 β b) (Icc (0:ℝ) 1) := by
    apply ContDiff.contDiffOn
    unfold gauss1
    fun_prop
  have hl1 := quadrature_sixth_order_l1_bound_on hm hcd
  have hu : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |iteratedDerivWithin 6 (gauss1 β b) (Icc (0:ℝ) 1) t| ≤
      K*(1+β^3)*gauss1 (β/2) b t := by
    intro t ht
    have hca : ContDiffAt ℝ 6 (gauss1 β b) t := by
      unfold gauss1
      fun_prop
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hca ht, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact gauss1_sixth_le hβ.le b t
  have hβ2 : 0 < β/2 := by positivity
  have hint : (∫ t in (0:ℝ)..1, |iteratedDerivWithin 6 (gauss1 β b) (Icc (0:ℝ) 1) t|) ≤
      K*(1+β^3)*Real.sqrt (2*Real.pi/β) := by
    have hcont : ContinuousOn (fun t => |iteratedDerivWithin 6 (gauss1 β b) (Icc (0:ℝ) 1) t|)
        (Icc (0:ℝ) 1) :=
      (hcd.continuousOn_iteratedDerivWithin (by norm_num) hu).abs
    calc _ ≤ ∫ t in (0:ℝ)..1, K*(1+β^3)*gauss1 (β/2) b t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply ContinuousOn.intervalIntegrable
            simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcont
          · exact ((continuous_gauss1 (β/2) b).const_smul (K*(1+β^3))).intervalIntegrable
              (μ := volume) _ _
          · exact hpt
      _ = K*(1+β^3)*∫ t in (0:ℝ)..1, gauss1 (β/2) b t := intervalIntegral.integral_const_mul _ _
      _ ≤ K*(1+β^3)*Real.sqrt (Real.pi/(β/2)) :=
          mul_le_mul_of_nonneg_left (gauss1_integral_le_sqrt hβ2 b) (by positivity)
      _ = K*(1+β^3)*Real.sqrt (2*Real.pi/β) := by
          congr 2
          field_simp
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hfac : (64/(m:ℝ)^6)*(1+β^3) ≤ 128 := by
    have h1 : β^3 ≤ (m:ℝ)^6 := by
      calc β^3 ≤ ((m:ℝ)^2)^3 := pow_le_pow_left₀ hβ.le hβm 3
        _ = (m:ℝ)^6 := by ring
    have h2 : (1:ℝ) ≤ (m:ℝ)^6 := one_le_pow₀ hm1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hs1 : Real.sqrt (Real.pi/β) = Real.sqrt Real.pi/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hs2 : Real.sqrt (2*Real.pi/β) = Real.sqrt (2*Real.pi)/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hQI : quadrature m (gauss1 β b) ≤ (∫ t in (0:ℝ)..1, gauss1 β b t)+
      (64/(m:ℝ)^6)*(∫ t in (0:ℝ)..1, |iteratedDerivWithin 6 (gauss1 β b) (Icc (0:ℝ) 1) t|) := by
    have := (abs_le.mp hl1).2
    linarith
  have hK0 : 0 ≤ K := by rw [hK]; norm_num
  calc quadrature m (gauss1 β b)
      ≤ Real.sqrt (Real.pi/β)+(64/(m:ℝ)^6)*(K*(1+β^3)*Real.sqrt (2*Real.pi/β)) :=
        hQI.trans (add_le_add (gauss1_integral_le_sqrt hβ b)
          (mul_le_mul_of_nonneg_left hint (by positivity)))
    _ = Real.sqrt (Real.pi/β)+K*((64/(m:ℝ)^6)*(1+β^3))*Real.sqrt (2*Real.pi/β) := by ring
    _ ≤ Real.sqrt (Real.pi/β)+K*128*Real.sqrt (2*Real.pi/β) := by
        gcongr
    _ = (Real.sqrt Real.pi+128*K*Real.sqrt (2*Real.pi))/Real.sqrt β := by
        rw [hs1, hs2]
        field_simp

end SphericalRiesz
