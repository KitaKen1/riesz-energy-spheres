import Riesz.NormalizedBumpError
import Riesz.GaussianCompositionSixthSmall

/-! Localized sixth-order error of one Gaussian bump for small `τ` (stage NEG).

The same nearest-point argument as `normalized_bump_quadrature_error`, with the small-`τ`
sixth-derivative bound: for `0 < τ ≤ 1`,
`|Q_n h - I h| ≤ K'(L,C₀) n⁻⁶ √τ ∫_cube e^{-(τ/8)‖Ψx-w‖²} dx`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The sixth-derivative constant for small `τ`. -/
def sixthConstSmall (L : ℝ) : ℝ := 720*1568*(64*L^2)^6

/-- The constant of the localized bump error for small `τ`. -/
def bumpErrorConstSmall (L C₀ : ℝ) : ℝ :=
  512*sixthConstSmall L*(Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))^8

theorem normalized_bump_quadrature_error_small
    {Ψ : (Fin 8 → ℝ) → Ambient9} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 8, ContDiffAt ℝ 6 Ψ x)
    (hder : ∀ x ∈ UnitCube 8, ∀ j, 1 ≤ j → j ≤ 6 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 8 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hβn : τ*C₀^2/128 ≤ (n:ℝ)^2)
    (w : Ambient9) :
    |cubeQuadrature 8 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 8 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConstSmall L C₀/(n:ℝ)^6*Real.sqrt τ*
        cubeIntegral 8 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hL0 : 0 < L := by linarith
  -- the nearest point of the cube
  have hcont : ContinuousOn Ψ (UnitCube 8) := fun x hx => (hcd x hx).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hmin⟩ := (unitCube_isCompact 8).exists_isMinOn
    ⟨fun _ => 0, fun _ => by norm_num⟩ ((hcont.sub continuousOn_const).norm)
  set ρ := ‖Ψ x0-w‖ with hρdef
  have hρmin : ∀ y ∈ UnitCube 8, ρ ≤ ‖Ψ y-w‖ := fun y hy => hmin hy
  set β := τ*C₀^2/128 with hβdef
  set γ := τ*L^2/4 with hγdef
  have hβ : 0 < β := by positivity
  have hγ : 0 < γ := by positivity
  -- the upper envelope
  have henv : ∀ y ∈ UnitCube 8, Real.exp (-(τ*‖Ψ y-w‖^2/2)) ≤
      Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j) := by
    intro y hy
    rw [prod_gauss1_eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : ‖Ψ y-Ψ x0‖ ≤ 2*‖Ψ y-w‖ := by
      calc ‖Ψ y-Ψ x0‖ = ‖(Ψ y-w)-(Ψ x0-w)‖ := by congr 1; abel
        _ ≤ ‖Ψ y-w‖+‖Ψ x0-w‖ := norm_sub_le _ _
        _ ≤ 2*‖Ψ y-w‖ := by linarith [hρmin y hy]
    have h2 := hlow y hy x0 hx0
    have h3 := sum_sq_le_eight_pi_norm_sq (y-x0)
    simp only [Pi.sub_apply] at h3
    have hρy := hρmin y hy
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have h4 : C₀^2*‖y-x0‖^2 ≤ 4*‖Ψ y-w‖^2 := by
      have : C₀*‖y-x0‖ ≤ 2*‖Ψ y-w‖ := h2.trans h1
      have hc : 0 ≤ C₀*‖y-x0‖ := by positivity
      nlinarith
    have h5 : ρ^2 ≤ ‖Ψ y-w‖^2 := pow_le_pow_left₀ hρ0 hρy 2
    have h6 : C₀^2*∑ j, (y j-x0 j)^2 ≤ 32*‖Ψ y-w‖^2 := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg C₀)
      nlinarith
    rw [hβdef]
    have hτ0 := hτ.le
    nlinarith [mul_le_mul_of_nonneg_left h5 hτ0, mul_le_mul_of_nonneg_left h6 hτ0]
  -- the lower envelope
  have hlowenv : ∀ y ∈ UnitCube 8, Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (y j) ≤
      Real.exp (-(τ/8*‖Ψ y-w‖^2)) := by
    intro y hy
    rw [prod_gauss1_eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : ‖Ψ y-w‖ ≤ ρ+L*‖y-x0‖ := by
      calc ‖Ψ y-w‖ = ‖(Ψ y-Ψ x0)+(Ψ x0-w)‖ := by congr 1; abel
        _ ≤ ‖Ψ y-Ψ x0‖+‖Ψ x0-w‖ := norm_add_le _ _
        _ ≤ L*‖y-x0‖+ρ := add_le_add (hup y hy x0 hx0) le_rfl
        _ = ρ+L*‖y-x0‖ := add_comm _ _
    have h2 : ‖Ψ y-w‖^2 ≤ 2*ρ^2+2*L^2*‖y-x0‖^2 := by
      have hρ0 : 0 ≤ ρ := norm_nonneg _
      have h0 : 0 ≤ ‖Ψ y-w‖ := norm_nonneg _
      nlinarith [sq_nonneg (ρ-L*‖y-x0‖), mul_nonneg hL0.le (norm_nonneg (y-x0))]
    have h3 := pi_norm_sq_le_sum (y-x0)
    simp only [Pi.sub_apply] at h3
    have h4 : ‖Ψ y-w‖^2 ≤ 2*ρ^2+2*L^2*∑ j, (y j-x0 j)^2 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2*L^2)
      linarith
    rw [hγdef]
    have hτ0 := hτ.le
    nlinarith [mul_le_mul_of_nonneg_left h4 hτ0]
  -- the slice derivative bound
  set A := sixthConstSmall L*Real.sqrt τ*Real.exp (-(τ*ρ^2/4)) with hAdef
  have hA : 0 ≤ A := by rw [hAdef, sixthConstSmall]; positivity
  set f : (Fin 8 → ℝ) → ℝ := fun x => Real.exp (-(τ*‖Ψ x-w‖^2)) with hfdef
  have hfcd : ∀ x ∈ UnitCube 8, ContDiffAt ℝ 6 f x := by
    intro x hx
    have h1 : ContDiffAt ℝ 6 (fun x => Ψ x-w) x := (hcd x hx).sub contDiffAt_const
    have h2 : ContDiffAt ℝ 6 (fun x => ‖Ψ x-w‖^2) x := h1.norm_sq ℝ
    exact Real.contDiff_exp.contDiffAt.comp x ((h2.const_smul τ).neg)
  have hM : ∀ i v, v ∈ UnitCube 8 → ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Icc (0 : ℝ) 1) t| ≤
        A*∏ j, gauss1 β (x0 j) (Function.update v i t j) := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    refine (sixth_coordinate_within_abs_le_of_contDiffAt 8 i v t ht (hfcd _ hy)).trans ?_
    set y := Function.update v i t with hydef
    have hFcd : ContDiffAt ℝ 6 (fun x => Ψ x-w) y := (hcd y hy).sub contDiffAt_const
    have hFL : ∀ j, 1 ≤ j → j ≤ 6 → ‖iteratedFDeriv ℝ j (fun x => Ψ x-w) y‖ ≤ L := by
      intro j hj hj6
      have hjc : ContDiffAt ℝ j Ψ y := (hcd y hy).of_le (by exact_mod_cast hj6)
      rw [show (fun x => Ψ x-w) = Ψ-(fun _ => w) from rfl,
        iteratedFDeriv_sub_apply hjc contDiffAt_const, iteratedFDeriv_const_of_ne (by omega) w]
      simpa only [Pi.zero_apply, sub_zero] using hder y hy j hj hj6
    have h := norm_iteratedFDeriv_six_exp_neg_mul_norm_sq_le_sqrt hFcd hL hFL hτ.le hτ1
    calc ‖iteratedFDeriv ℝ 6 f y‖ ≤
          (720*1568*(64*L^2)^6)*Real.sqrt τ*Real.exp (-(τ*‖Ψ y-w‖^2/2)) := h
      _ ≤ (720*1568*(64*L^2)^6)*Real.sqrt τ*
          (Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j)) :=
          mul_le_mul_of_nonneg_left (henv y hy) (by positivity)
      _ = A*∏ j, gauss1 β (x0 j) (y j) := by rw [hAdef, sixthConstSmall]; ring
  -- one-dimensional bounds
  set B := min 1 (gaussRuleConst/Real.sqrt β) with hBdef
  have hQB : ∀ j, quadrature n (gauss1 β (x0 j)) ≤ B := by
    intro j
    exact le_min (gauss1_quadrature_le_one hn hβ.le _)
      (gauss1_quadrature_le hn hβ hβn _)
  have hIB : ∀ j, (∫ t in (0:ℝ)..1, gauss1 β (x0 j) t) ≤ B := by
    intro j
    refine le_min (gauss1_integral_le_one hβ.le _) ((gauss1_integral_le_sqrt hβ _).trans ?_)
    rw [Real.sqrt_div' _ hβ.le]
    exact div_le_div_of_nonneg_right sqrt_pi_le_gaussRuleConst (Real.sqrt_nonneg _)
  have herr := cubeQuadrature_sixth_order_envelope_on 8 hn
    (fun x hx => (hfcd x hx).continuousAt.continuousWithinAt)
    (fun i v hv => by
      intro t ht
      have hy := update_mem_unitCube hv i ht
      have hu : ContDiffAt ℝ 6 (fun u : ℝ => Function.update v i u) t := by
        rw [show (fun u : ℝ => Function.update v i u) =
          (fun u => ContinuousLinearMap.single ℝ (fun _ : Fin 8 => ℝ) i u+Function.update v i 0)
          from funext (coordinate_update_as_line 8 i v)]
        fun_prop
      exact ((hfcd _ hy).comp t hu).contDiffWithinAt)
    (fun j => gauss1 β (x0 j)) (fun j => continuous_gauss1 β _) (fun j t => gauss1_nonneg β _ t)
    (fun _ => B) hQB hIB hA hM
  -- the lower bound of the right side
  set J := Real.exp (-1)*min (1/2) (1/Real.sqrt γ) with hJdef
  have hJ0 : 0 ≤ J := by rw [hJdef]; positivity
  have hJI : ∀ j, J ≤ ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t := fun j =>
    gauss1_integral_ge hγ ⟨(hx0 j).1, (hx0 j).2⟩
  have hratio : B ≤ (Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))*J := by
    apply gauss1_bound_ratio hβ hγ gaussRuleConst_nonneg (by positivity)
    have hγβ : γ = (32*L^2/C₀^2)*β := by
      rw [hγdef, hβdef]; field_simp; norm_num
    rw [hγβ, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
      Real.sqrt_mul (by norm_num), Real.sqrt_sq hL0.le, Real.sqrt_sq hC₀.le]
  have hrhs : Real.exp (-(τ*ρ^2/4))*J^8 ≤
      cubeIntegral 8 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
    have hprod : J^8 ≤ cubeIntegral 8 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) := by
      rw [cubeIntegral_prod]
      calc J^8 = ∏ _j : Fin 8, J := by simp
        _ ≤ ∏ j, ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t :=
            Finset.prod_le_prod₀ (fun _ _ => hJ0) (fun j _ => hJI j)
    calc Real.exp (-(τ*ρ^2/4))*J^8
        ≤ Real.exp (-(τ*ρ^2/4))*cubeIntegral 8 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = cubeIntegral 8 (fun x => Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) :=
          (cubeIntegral_mul_const 8 _ _).symm
      _ ≤ cubeIntegral 8 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
          have hc1 : ContinuousOn (fun x : Fin 8 → ℝ =>
              Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) (UnitCube 8) :=
            (continuous_const.mul (continuous_finsetProd _ fun j _ =>
              (continuous_gauss1 γ _).comp (continuous_apply j))).continuousOn
          have hc2 : ContinuousOn (fun x : Fin 8 → ℝ => Real.exp (-(τ/8*‖Ψ x-w‖^2)))
              (UnitCube 8) :=
            Real.continuous_exp.comp_continuousOn
              (((hcont.sub continuousOn_const).norm.pow 2).const_smul (τ/8)).neg
          have h := cubeIntegral_abs_le_of_le 8 hc1 hc2 (fun x hx => by
            rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
              (Finset.prod_nonneg fun j _ => gauss1_nonneg γ _ _))]
            exact hlowenv x hx)
          exact (le_abs_self _).trans h
  -- assemble
  have hB0 : 0 ≤ B := le_min zero_le_one (div_nonneg gaussRuleConst_nonneg (Real.sqrt_nonneg _))
  have hB8 : B^8 ≤ (Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))^8*J^8 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hratio 8
  have hprodB : ∏ _j : Fin 8, B = B^8 := by simp
  rw [hprodB] at herr
  have hn6 : (0:ℝ) < (n:ℝ)^6 := by positivity
  calc |cubeQuadrature 8 n f-cubeIntegral 8 f|
      ≤ 64/(n:ℝ)^6*((8:ℕ)*(A*B^8)) := herr
    _ = 512/(n:ℝ)^6*(sixthConstSmall L*Real.sqrt τ)*(Real.exp (-(τ*ρ^2/4))*B^8) := by
        rw [hAdef]; push_cast; ring
    _ ≤ 512/(n:ℝ)^6*(sixthConstSmall L*Real.sqrt τ)*(Real.exp (-(τ*ρ^2/4))*
          ((Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))^8*J^8)) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [sixthConstSmall]; positivity)
        exact mul_le_mul_of_nonneg_left hB8 (Real.exp_pos _).le
    _ = 512/(n:ℝ)^6*(sixthConstSmall L*Real.sqrt τ)*
          (Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))^8*
            (Real.exp (-(τ*ρ^2/4))*J^8) := by ring
    _ ≤ 512/(n:ℝ)^6*(sixthConstSmall L*Real.sqrt τ)*
          (Real.exp 1*max 2 (gaussRuleConst*(Real.sqrt 32*L/C₀)))^8*
            cubeIntegral 8 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) :=
        mul_le_mul_of_nonneg_left hrhs (by rw [sixthConstSmall]; positivity)
    _ = bumpErrorConstSmall L C₀/(n:ℝ)^6*Real.sqrt τ*
          cubeIntegral 8 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
        rw [bumpErrorConstSmall]; ring


#print axioms normalized_bump_quadrature_error_small

end SphericalRiesz
