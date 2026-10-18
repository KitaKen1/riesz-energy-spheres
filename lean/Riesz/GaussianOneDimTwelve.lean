import Riesz.GaussianOneDimBounds
import Riesz.GaussianCompositionTwelfth
import Riesz.BoundaryTwelveL1Error
import Riesz.BoundaryTwelveTensor

/-! Gaussian averages on the actual twelfth-order rule. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem gauss1_twelveQuadrature_le_one {m : ℕ} (hm : 74 ≤ m) {β : ℝ} (hβ : 0 ≤ β) (b : ℝ) :
    twelveQuadrature m (gauss1 β b) ≤ 1 := by
  have h := twelveQuadrature_mono hm (f := gauss1 β b) (g := fun _ => (1:ℝ))
    (fun t _ => gauss1_le_one hβ b t)
  rwa [twelveQuadrature_const hm] at h

/-- Twelfth derivative of the one-dimensional profile. -/
theorem gauss1_twelfth_le {β : ℝ} (hβ : 0 ≤ β) (b t : ℝ) :
    ‖iteratedFDeriv ℝ 12 (gauss1 β b) t‖ ≤
      (479001600*531441*(10:ℝ)^30)*(1+β^6)*gauss1 (β/2) b t := by
  have hF : ContDiffAt ℝ 12 (fun s : ℝ => s-b) t := by fun_prop
  have hderiv : deriv (fun s : ℝ => s-b) = fun _ => 1 := by
    funext s
    simp
  have hFL : ∀ j, 1 ≤ j → j ≤ 12 → ‖iteratedFDeriv ℝ j (fun s : ℝ => s-b) t‖ ≤ 1 := by
    intro j hj _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
    rw [iteratedDeriv_succ', hderiv, iteratedDeriv_const]
    split_ifs <;> simp
  have h := norm_iteratedFDeriv_twelve_exp_neg_mul_norm_sq_le hF le_rfl hFL hβ
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
theorem gauss1_twelveQuadrature_le {m : ℕ} (hm : 74 ≤ m) {β : ℝ} (hβ : 0 < β)
    (hβm : β ≤ (m:ℝ)^2) (b : ℝ) :
    twelveQuadrature m (gauss1 β b) ≤
      (Real.sqrt Real.pi+(2*(10:ℝ)^24)*(479001600*531441*(10:ℝ)^30)*Real.sqrt (2*Real.pi))/Real.sqrt β := by
  set K : ℝ := 479001600*531441*(10:ℝ)^30 with hK
  have hcd : ContDiffOn ℝ 12 (gauss1 β b) (Icc (0:ℝ) 1) := by
    apply ContDiff.contDiffOn
    unfold gauss1
    fun_prop
  have hl1 := twelveQuadrature_twelfth_order_l1_bound_on hm hcd
  have hu : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |iteratedDerivWithin 12 (gauss1 β b) (Icc (0:ℝ) 1) t| ≤
      K*(1+β^6)*gauss1 (β/2) b t := by
    intro t ht
    have hca : ContDiffAt ℝ 12 (gauss1 β b) t := by
      unfold gauss1
      fun_prop
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hca ht, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact gauss1_twelfth_le hβ.le b t
  have hβ2 : 0 < β/2 := by positivity
  have hint : (∫ t in (0:ℝ)..1, |iteratedDerivWithin 12 (gauss1 β b) (Icc (0:ℝ) 1) t|) ≤
      K*(1+β^6)*Real.sqrt (2*Real.pi/β) := by
    have hcont : ContinuousOn (fun t => |iteratedDerivWithin 12 (gauss1 β b) (Icc (0:ℝ) 1) t|)
        (Icc (0:ℝ) 1) :=
      (hcd.continuousOn_iteratedDerivWithin (by norm_num) hu).abs
    calc _ ≤ ∫ t in (0:ℝ)..1, K*(1+β^6)*gauss1 (β/2) b t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply ContinuousOn.intervalIntegrable
            simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcont
          · exact ((continuous_gauss1 (β/2) b).const_smul (K*(1+β^6))).intervalIntegrable
              (μ := volume) _ _
          · exact hpt
      _ = K*(1+β^6)*∫ t in (0:ℝ)..1, gauss1 (β/2) b t := intervalIntegral.integral_const_mul _ _
      _ ≤ K*(1+β^6)*Real.sqrt (Real.pi/(β/2)) :=
          mul_le_mul_of_nonneg_left (gauss1_integral_le_sqrt hβ2 b) (by positivity)
      _ = K*(1+β^6)*Real.sqrt (2*Real.pi/β) := by
          congr 2
          field_simp
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hfac : (10^24/(m:ℝ)^12)*(1+β^6) ≤ (2*(10:ℝ)^24) := by
    have h1 : β^6 ≤ (m:ℝ)^12 := by
      calc β^6 ≤ ((m:ℝ)^2 )^6 := pow_le_pow_left₀ hβ.le hβm 6
        _ = (m:ℝ)^12 := by ring
    have h2 : (1:ℝ) ≤ (m:ℝ)^12 := one_le_pow₀ hm1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hs1 : Real.sqrt (Real.pi/β) = Real.sqrt Real.pi/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hs2 : Real.sqrt (2*Real.pi/β) = Real.sqrt (2*Real.pi)/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hQI : twelveQuadrature m (gauss1 β b) ≤ (∫ t in (0:ℝ)..1, gauss1 β b t)+
      (10^24/(m:ℝ)^12)*(∫ t in (0:ℝ)..1, |iteratedDerivWithin 12 (gauss1 β b) (Icc (0:ℝ) 1) t|) := by
    have := (abs_le.mp hl1).2
    linarith
  have hK0 : 0 ≤ K := by rw [hK]; norm_num
  calc twelveQuadrature m (gauss1 β b)
      ≤ Real.sqrt (Real.pi/β)+(10^24/(m:ℝ)^12)*(K*(1+β^6)*Real.sqrt (2*Real.pi/β)) :=
        hQI.trans (add_le_add (gauss1_integral_le_sqrt hβ b)
          (mul_le_mul_of_nonneg_left hint (by positivity)))
    _ = Real.sqrt (Real.pi/β)+K*((10^24/(m:ℝ)^12)*(1+β^6))*Real.sqrt (2*Real.pi/β) := by ring
    _ ≤ Real.sqrt (Real.pi/β)+K*(2*(10:ℝ)^24)*Real.sqrt (2*Real.pi/β) := by
        gcongr
    _ = (Real.sqrt Real.pi+(2*(10:ℝ)^24)*K*Real.sqrt (2*Real.pi))/Real.sqrt β := by
        rw [hs1, hs2]
        field_simp

end SphericalRiesz
