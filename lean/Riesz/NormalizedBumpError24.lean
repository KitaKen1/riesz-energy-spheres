import Riesz.GaussianOneDimTwelve
import Riesz.BoundaryTwelveEnvelope
import Riesz.NormalizedBumpError
import Riesz.EqualAreaMovingHigherBounds24

/-! Localized twelfth-order Gaussian bump error in the actual 24-dimensional
chart domain and ambient R25.  The nearest-point/product-envelope argument
is reused from the dimension-eight proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem twelfth_coordinate_within_abs_le_of_contDiffAt (d : ℕ)
    {F : (Fin d → ℝ) → ℝ} (i : Fin d) (v : Fin d → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hf : ContDiffAt ℝ 12 F (Function.update v i t)) :
    |iteratedDerivWithin 12 (fun u => F (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤
      ‖iteratedFDeriv ℝ 12 F (Function.update v i t)‖ := by
  let g : ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i
  let a := Function.update v i 0
  let H : (Fin d → ℝ) → ℝ := fun z => F (z+a)
  have hepoint : g t+a = Function.update v i t := (coordinate_update_as_line d i v t).symm
  have hH : ContDiffAt ℝ 12 H (g t) := by
    apply ContDiffAt.comp (g := F) (f := fun z => z+a) (g t)
    · rw [hepoint]; exact hf
    · fun_prop
  have heq : (fun u => F (Function.update v i u)) = H ∘ g := by
    funext u
    rw [coordinate_update_as_line]
    rfl
  obtain ⟨U,hU,hgtU,hHU⟩ := hH.contDiffOn' le_rfl (by simp)
  have hHU' : ContDiffOn ℝ 12 H U := by simpa using hHU
  have hp : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hline := g.iteratedFDerivWithin_comp_right hHU' hU.uniqueDiffOn hp.uniqueDiffOn hgtU
    (i := 12) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 12 hp hgtU,
    iteratedFDerivWithin_of_isOpen 12 hU hgtU] at hline
  rw [heq,iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hH.comp t g.contDiff.contDiffAt) ht,← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,hline]
  have hshift : iteratedFDeriv ℝ 12 H (g t) = iteratedFDeriv ℝ 12 F (Function.update v i t) := by
    dsimp only [H]
    rw [iteratedFDeriv_comp_add_right,hepoint]
  rw [hshift]
  have hnorm : ‖g‖ = 1 := ContinuousLinearMap.norm_single ℝ (fun _ : Fin d => ℝ) i
  simpa only [hnorm,Finset.prod_const_one,mul_one] using
    (iteratedFDeriv ℝ 12 F (Function.update v i t)).norm_compContinuousLinearMap_le (fun _ => g)

theorem pi_norm_sq_le_sum24 (x : Fin 24 → ℝ) : ‖x‖^2 ≤ ∑ j, (x j)^2 := by
  have hs : 0 ≤ ∑ j, (x j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ j, (x j)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  calc ‖x‖^2 ≤ Real.sqrt (∑ j, (x j)^2)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ j, (x j)^2 := Real.sq_sqrt hs

theorem sum_sq_le_twentyFour_pi_norm_sq (x : Fin 24 → ℝ) : ∑ j, (x j)^2 ≤ 24*‖x‖^2 := by
  have h : ∀ j, (x j)^2 ≤ ‖x‖^2 := by
    intro j
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x j) 2
  calc ∑ j, (x j)^2 ≤ ∑ _j : Fin 24, ‖x‖^2 := Finset.sum_le_sum fun j _ => h j
    _ = 24*‖x‖^2 := by simp

/-- The product of one-dimensional Gaussians in all coordinates. -/
theorem prod_gauss1_eq24 (β : ℝ) (x0 y : Fin 24 → ℝ) :
    ∏ j, gauss1 β (x0 j) (y j) = Real.exp (-(β*∑ j, (y j-x0 j)^2)) := by
  unfold gauss1
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Constant of the twelfth derivative bound. -/
def twelfthConst (L : ℝ) : ℝ := 479001600*531441*(10:ℝ)^30*L^12

/-- Constant of the one-dimensional rule average. -/
def gaussRuleConst12 : ℝ := Real.sqrt Real.pi+(2*(10:ℝ)^24)*(479001600*531441*(10:ℝ)^30)*Real.sqrt (2*Real.pi)

theorem gaussRuleConst12_nonneg : 0 ≤ gaussRuleConst12 := by
  unfold gaussRuleConst12
  positivity

theorem sqrt_pi_le_gaussRuleConst12 : Real.sqrt Real.pi ≤ gaussRuleConst12 := by
  unfold gaussRuleConst12
  have : 0 ≤ (2*(10:ℝ)^24)*(479001600*531441*(10:ℝ)^30:ℝ)*Real.sqrt (2*Real.pi) := by positivity
  linarith

/-- The constant of the localized twelfth-order bump error. -/
def bumpErrorConst24 (L C₀ : ℝ) : ℝ :=
  (24*(10:ℝ)^24)*twelfthConst L*(Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))^24

theorem normalized_bump_quadrature_error24
    {Ψ : (Fin 24 → ℝ) → AmbientD 24} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 12 Ψ x)
    (hder : ∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 12 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 74 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 24) :
    |twelveCubeQuadrature 24 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 24 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConst24 L C₀/(n:ℝ)^12*(1+τ^6)*
        cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hL0 : 0 < L := by linarith
  -- the nearest point of the cube
  have hcont : ContinuousOn Ψ (UnitCube 24) := fun x hx => (hcd x hx).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hmin⟩ := (unitCube_isCompact 24).exists_isMinOn
    ⟨fun _ => 0, fun _ => by norm_num⟩ ((hcont.sub continuousOn_const).norm)
  set ρ := ‖Ψ x0-w‖ with hρdef
  have hρmin : ∀ y ∈ UnitCube 24, ρ ≤ ‖Ψ y-w‖ := fun y hy => hmin hy
  set β := τ*C₀^2/384 with hβdef
  set γ := τ*L^2/4 with hγdef
  have hβ : 0 < β := by positivity
  have hγ : 0 < γ := by positivity
  -- the upper envelope
  have henv : ∀ y ∈ UnitCube 24, Real.exp (-(τ*‖Ψ y-w‖^2/2)) ≤
      Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j) := by
    intro y hy
    rw [prod_gauss1_eq24, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : ‖Ψ y-Ψ x0‖ ≤ 2*‖Ψ y-w‖ := by
      calc ‖Ψ y-Ψ x0‖ = ‖(Ψ y-w)-(Ψ x0-w)‖ := by congr 1; abel
        _ ≤ ‖Ψ y-w‖+‖Ψ x0-w‖ := norm_sub_le _ _
        _ ≤ 2*‖Ψ y-w‖ := by linarith [hρmin y hy]
    have h2 := hlow y hy x0 hx0
    have h3 := sum_sq_le_twentyFour_pi_norm_sq (y-x0)
    simp only [Pi.sub_apply] at h3
    have hρy := hρmin y hy
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have h4 : C₀^2*‖y-x0‖^2 ≤ 4*‖Ψ y-w‖^2 := by
      have : C₀*‖y-x0‖ ≤ 2*‖Ψ y-w‖ := h2.trans h1
      have hc : 0 ≤ C₀*‖y-x0‖ := by positivity
      nlinarith
    have h5 : ρ^2 ≤ ‖Ψ y-w‖^2 := pow_le_pow_left₀ hρ0 hρy 2
    have h6 : C₀^2*∑ j, (y j-x0 j)^2 ≤ 96*‖Ψ y-w‖^2 := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg C₀)
      nlinarith
    rw [hβdef]
    have hτ0 := hτ.le
    nlinarith [mul_le_mul_of_nonneg_left h5 hτ0, mul_le_mul_of_nonneg_left h6 hτ0]
  -- the lower envelope
  have hlowenv : ∀ y ∈ UnitCube 24, Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (y j) ≤
      Real.exp (-(τ/8*‖Ψ y-w‖^2)) := by
    intro y hy
    rw [prod_gauss1_eq24, ← Real.exp_add]
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
    have h3 := pi_norm_sq_le_sum24 (y-x0)
    simp only [Pi.sub_apply] at h3
    have h4 : ‖Ψ y-w‖^2 ≤ 2*ρ^2+2*L^2*∑ j, (y j-x0 j)^2 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2*L^2)
      linarith
    rw [hγdef]
    have hτ0 := hτ.le
    nlinarith [mul_le_mul_of_nonneg_left h4 hτ0]
  -- the slice derivative bound
  set A := twelfthConst L*(1+τ^6)*Real.exp (-(τ*ρ^2/4)) with hAdef
  have hA : 0 ≤ A := by rw [hAdef, twelfthConst]; positivity
  set f : (Fin 24 → ℝ) → ℝ := fun x => Real.exp (-(τ*‖Ψ x-w‖^2)) with hfdef
  have hfcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 12 f x := by
    intro x hx
    have h1 : ContDiffAt ℝ 12 (fun x => Ψ x-w) x := (hcd x hx).sub contDiffAt_const
    have h2 : ContDiffAt ℝ 12 (fun x => ‖Ψ x-w‖^2) x := h1.norm_sq ℝ
    exact Real.contDiff_exp.contDiffAt.comp x ((h2.const_smul τ).neg)
  have hM : ∀ i v, v ∈ UnitCube 24 → ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u)) (Icc (0 : ℝ) 1) t| ≤
        A*∏ j, gauss1 β (x0 j) (Function.update v i t j) := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    refine (twelfth_coordinate_within_abs_le_of_contDiffAt 24 i v t ht (hfcd _ hy)).trans ?_
    set y := Function.update v i t with hydef
    have hFcd : ContDiffAt ℝ 12 (fun x => Ψ x-w) y := (hcd y hy).sub contDiffAt_const
    have hFL : ∀ j, 1 ≤ j → j ≤ 12 → ‖iteratedFDeriv ℝ j (fun x => Ψ x-w) y‖ ≤ L := by
      intro j hj hj6
      have hjc : ContDiffAt ℝ j Ψ y := (hcd y hy).of_le (by exact_mod_cast hj6)
      rw [show (fun x => Ψ x-w) = Ψ-(fun _ => w) from rfl,
        iteratedFDeriv_sub_apply hjc contDiffAt_const, iteratedFDeriv_const_of_ne (by omega) w]
      simpa only [Pi.zero_apply, sub_zero] using hder y hy j hj hj6
    have h := norm_iteratedFDeriv_twelve_exp_neg_mul_norm_sq_le hFcd hL hFL hτ.le
    calc ‖iteratedFDeriv ℝ 12 f y‖ ≤
          (479001600*531441*(10:ℝ)^30*L^12)*(1+τ^6)*Real.exp (-(τ*‖Ψ y-w‖^2/2)) := h
      _ ≤ (479001600*531441*(10:ℝ)^30*L^12)*(1+τ^6)*
          (Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j)) :=
          mul_le_mul_of_nonneg_left (henv y hy) (by positivity)
      _ = A*∏ j, gauss1 β (x0 j) (y j) := by rw [hAdef, twelfthConst]; ring
  -- one-dimensional bounds
  set B := min 1 (gaussRuleConst12/Real.sqrt β) with hBdef
  have hQB : ∀ j, twelveQuadrature n (gauss1 β (x0 j)) ≤ B := by
    intro j
    exact le_min (gauss1_twelveQuadrature_le_one hn hβ.le _)
      (gauss1_twelveQuadrature_le hn hβ hβn _)
  have hIB : ∀ j, (∫ t in (0:ℝ)..1, gauss1 β (x0 j) t) ≤ B := by
    intro j
    refine le_min (gauss1_integral_le_one hβ.le _) ((gauss1_integral_le_sqrt hβ _).trans ?_)
    rw [Real.sqrt_div' _ hβ.le]
    exact div_le_div_of_nonneg_right sqrt_pi_le_gaussRuleConst12 (Real.sqrt_nonneg _)
  have herr := twelveCubeQuadrature_twelfth_order_envelope_on 24 hn
    (fun x hx => (hfcd x hx).continuousAt.continuousWithinAt)
    (fun i v hv => by
      intro t ht
      have hy := update_mem_unitCube hv i ht
      have hu : ContDiffAt ℝ 12 (fun u : ℝ => Function.update v i u) t := by
        rw [show (fun u : ℝ => Function.update v i u) =
          (fun u => ContinuousLinearMap.single ℝ (fun _ : Fin 24 => ℝ) i u+Function.update v i 0)
          from funext (coordinate_update_as_line 24 i v)]
        fun_prop
      exact ((hfcd _ hy).comp t hu).contDiffWithinAt)
    (fun j => gauss1 β (x0 j)) (fun j => continuous_gauss1 β _) (fun j t => gauss1_nonneg β _ t)
    (fun _ => B) hQB hIB hA hM
  -- the lower bound of the right side
  set J := Real.exp (-1)*min (1/2) (1/Real.sqrt γ) with hJdef
  have hJ0 : 0 ≤ J := by rw [hJdef]; positivity
  have hJI : ∀ j, J ≤ ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t := fun j =>
    gauss1_integral_ge hγ ⟨(hx0 j).1, (hx0 j).2⟩
  have hratio : B ≤ (Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))*J := by
    apply gauss1_bound_ratio hβ hγ gaussRuleConst12_nonneg (by positivity)
    have hγβ : γ = (96*L^2/C₀^2)*β := by
      rw [hγdef, hβdef]; field_simp; norm_num
    rw [hγβ, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
      Real.sqrt_mul (by norm_num), Real.sqrt_sq hL0.le, Real.sqrt_sq hC₀.le]
  have hrhs : Real.exp (-(τ*ρ^2/4))*J^24 ≤
      cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
    have hprod : J^24 ≤ cubeIntegral 24 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) := by
      rw [cubeIntegral_prod]
      calc J^24 = ∏ _j : Fin 24, J := by simp
        _ ≤ ∏ j, ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t :=
            Finset.prod_le_prod₀ (fun _ _ => hJ0) (fun j _ => hJI j)
    calc Real.exp (-(τ*ρ^2/4))*J^24
        ≤ Real.exp (-(τ*ρ^2/4))*cubeIntegral 24 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = cubeIntegral 24 (fun x => Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) :=
          (cubeIntegral_mul_const 24 _ _).symm
      _ ≤ cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
          have hc1 : ContinuousOn (fun x : Fin 24 → ℝ =>
              Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) (UnitCube 24) :=
            (continuous_const.mul (continuous_finsetProd _ fun j _ =>
              (continuous_gauss1 γ _).comp (continuous_apply j))).continuousOn
          have hc2 : ContinuousOn (fun x : Fin 24 → ℝ => Real.exp (-(τ/8*‖Ψ x-w‖^2)))
              (UnitCube 24) :=
            Real.continuous_exp.comp_continuousOn
              (((hcont.sub continuousOn_const).norm.pow 2).const_smul (τ/8)).neg
          have h := cubeIntegral_abs_le_of_le 24 hc1 hc2 (fun x hx => by
            rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
              (Finset.prod_nonneg fun j _ => gauss1_nonneg γ _ _))]
            exact hlowenv x hx)
          exact (le_abs_self _).trans h
  -- assemble
  have hB0 : 0 ≤ B := le_min zero_le_one (div_nonneg gaussRuleConst12_nonneg (Real.sqrt_nonneg _))
  have hB8 : B^24 ≤ (Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))^24*J^24 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hratio 24
  have hprodB : ∏ _j : Fin 24, B = B^24 := by simp
  rw [hprodB] at herr
  have hn6 : (0:ℝ) < (n:ℝ)^12 := by positivity
  calc |twelveCubeQuadrature 24 n f-cubeIntegral 24 f|
      ≤ 10^24/(n:ℝ)^12*((24:ℕ)*(A*B^24)) := herr
    _ = (24*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConst L*(1+τ^6))*(Real.exp (-(τ*ρ^2/4))*B^24) := by
        rw [hAdef]; push_cast; ring
    _ ≤ (24*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConst L*(1+τ^6))*(Real.exp (-(τ*ρ^2/4))*
          ((Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))^24*J^24)) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [twelfthConst]; positivity)
        exact mul_le_mul_of_nonneg_left hB8 (Real.exp_pos _).le
    _ = (24*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConst L*(1+τ^6))*
          (Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))^24*
            (Real.exp (-(τ*ρ^2/4))*J^24) := by ring
    _ ≤ (24*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConst L*(1+τ^6))*
          (Real.exp 1*max 2 (gaussRuleConst12*(Real.sqrt 96*L/C₀)))^24*
            cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) :=
        mul_le_mul_of_nonneg_left hrhs (by rw [twelfthConst]; positivity)
    _ = bumpErrorConst24 L C₀/(n:ℝ)^12*(1+τ^6)*
          cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
        rw [bumpErrorConst24]; ring

end SphericalRiesz
