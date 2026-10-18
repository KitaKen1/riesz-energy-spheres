import Riesz.GaussianOneDimBounds
import Riesz.GaussianCompositionFourteenth
import Riesz.BoundaryFourteen
import Riesz.NormalizedBumpError24
import Riesz.EqualAreaMovingHigherBounds24
import Riesz.LeechTwelfthGaussianBudget24
import Riesz.LeechForegroundBump24
import Riesz.LeechForegroundDefect24
import Riesz.LeechCommonBudget24
import Riesz.LeechForegroundWindow24

/-! # The fourteenth-order Leech foreground on `S²⁴`

The order-fourteen forms of the checked order-twelve foreground modules, built on the
equal-weight rule of `Riesz.BoundaryFourteen`:

* one-dimensional Gaussian sums of the rule and the product envelope,
* the error of a normalized Gaussian bump on a chart cube, `K (1+τ⁷)/n¹⁴` for every `τ` and
  `K_s √τ/n¹⁴` for `τ ≤ 1` (the second form is linear in the Gaussian parameter after squaring),
* the fourteenth-order nodes of a small Leech patch and of a patch family: injectivity,
  cardinality, short-range and density budgets, and the Gaussian window of a family,
* the bump error on the sphere and the mixed Gaussian defect of a patch family, of size
  `N² B(t/8) (K (1/n¹⁴+(2πα)⁷))²` in general and `N² B(t/8) (K_s √(2πα)/n¹³)²` at macroscopic
  scales `2π n² α ≤ 1`.

Order fourteen is what negative exponents on `S²⁴` need: with `N² B(t/8)` of size `N α⁻¹²` the
defect is `O(N α²)` in the scaled Gaussian parameter `α`, integrable against `α^(s/2-1)` at
zero for `-2 < s < 0`, while order twelve leaves a term of size `N` there. -/

section

/-! Gaussian averages on the actual fourteenth-order rule. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem gauss1_fourteenQuadrature_le_one {m : ℕ} (hm : 48 ≤ m) {β : ℝ} (hβ : 0 ≤ β) (b : ℝ) :
    fourteenQuadrature m (gauss1 β b) ≤ 1 := by
  have h := fourteenQuadrature_mono hm (f := gauss1 β b) (g := fun _ => (1:ℝ))
    (fun t _ => gauss1_le_one hβ b t)
  rwa [fourteenQuadrature_const hm] at h

/-- Fourteenth derivative of the one-dimensional profile. -/
theorem gauss1_fourteenth_le {β : ℝ} (hβ : 0 ≤ β) (b t : ℝ) :
    ‖iteratedFDeriv ℝ 14 (gauss1 β b) t‖ ≤
      (87178291200*4782969*(10:ℝ)^38)*(1+β^7)*gauss1 (β/2) b t := by
  have hF : ContDiffAt ℝ 14 (fun s : ℝ => s-b) t := by fun_prop
  have hderiv : deriv (fun s : ℝ => s-b) = fun _ => 1 := by
    funext s
    simp
  have hFL : ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j (fun s : ℝ => s-b) t‖ ≤ 1 := by
    intro j hj _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
    rw [iteratedDeriv_succ', hderiv, iteratedDeriv_const]
    split_ifs <;> simp
  have h := norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le hF le_rfl hFL hβ
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
theorem gauss1_fourteenQuadrature_le {m : ℕ} (hm : 48 ≤ m) {β : ℝ} (hβ : 0 < β)
    (hβm : β ≤ (m:ℝ)^2) (b : ℝ) :
    fourteenQuadrature m (gauss1 β b) ≤
      (Real.sqrt Real.pi+(2*(10:ℝ)^24)*(87178291200*4782969*(10:ℝ)^38)*Real.sqrt (2*Real.pi))/Real.sqrt β := by
  set K : ℝ := 87178291200*4782969*(10:ℝ)^38 with hK
  have hcd : ContDiffOn ℝ 14 (gauss1 β b) (Icc (0:ℝ) 1) := by
    apply ContDiff.contDiffOn
    unfold gauss1
    fun_prop
  have hl1 := fourteenQuadrature_fourteenth_order_l1_bound_on hm hcd
  have hu : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |iteratedDerivWithin 14 (gauss1 β b) (Icc (0:ℝ) 1) t| ≤
      K*(1+β^7)*gauss1 (β/2) b t := by
    intro t ht
    have hca : ContDiffAt ℝ 14 (gauss1 β b) t := by
      unfold gauss1
      fun_prop
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hca ht, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact gauss1_fourteenth_le hβ.le b t
  have hβ2 : 0 < β/2 := by positivity
  have hint : (∫ t in (0:ℝ)..1, |iteratedDerivWithin 14 (gauss1 β b) (Icc (0:ℝ) 1) t|) ≤
      K*(1+β^7)*Real.sqrt (2*Real.pi/β) := by
    have hcont : ContinuousOn (fun t => |iteratedDerivWithin 14 (gauss1 β b) (Icc (0:ℝ) 1) t|)
        (Icc (0:ℝ) 1) :=
      (hcd.continuousOn_iteratedDerivWithin (by norm_num) hu).abs
    calc _ ≤ ∫ t in (0:ℝ)..1, K*(1+β^7)*gauss1 (β/2) b t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply ContinuousOn.intervalIntegrable
            simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcont
          · exact ((continuous_gauss1 (β/2) b).const_smul (K*(1+β^7))).intervalIntegrable
              (μ := volume) _ _
          · exact hpt
      _ = K*(1+β^7)*∫ t in (0:ℝ)..1, gauss1 (β/2) b t := intervalIntegral.integral_const_mul _ _
      _ ≤ K*(1+β^7)*Real.sqrt (Real.pi/(β/2)) :=
          mul_le_mul_of_nonneg_left (gauss1_integral_le_sqrt hβ2 b) (by positivity)
      _ = K*(1+β^7)*Real.sqrt (2*Real.pi/β) := by
          congr 2
          field_simp
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hfac : (10^24/(m:ℝ)^14)*(1+β^7) ≤ (2*(10:ℝ)^24) := by
    have h1 : β^7 ≤ (m:ℝ)^14 := by
      calc β^7 ≤ ((m:ℝ)^2 )^7 := pow_le_pow_left₀ hβ.le hβm 7
        _ = (m:ℝ)^14 := by ring
    have h2 : (1:ℝ) ≤ (m:ℝ)^14 := one_le_pow₀ hm1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hs1 : Real.sqrt (Real.pi/β) = Real.sqrt Real.pi/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hs2 : Real.sqrt (2*Real.pi/β) = Real.sqrt (2*Real.pi)/Real.sqrt β :=
    Real.sqrt_div' _ hβ.le
  have hQI : fourteenQuadrature m (gauss1 β b) ≤ (∫ t in (0:ℝ)..1, gauss1 β b t)+
      (10^24/(m:ℝ)^14)*(∫ t in (0:ℝ)..1, |iteratedDerivWithin 14 (gauss1 β b) (Icc (0:ℝ) 1) t|) := by
    have := (abs_le.mp hl1).2
    linarith
  have hK0 : 0 ≤ K := by rw [hK]; norm_num
  calc fourteenQuadrature m (gauss1 β b)
      ≤ Real.sqrt (Real.pi/β)+(10^24/(m:ℝ)^14)*(K*(1+β^7)*Real.sqrt (2*Real.pi/β)) :=
        hQI.trans (add_le_add (gauss1_integral_le_sqrt hβ b)
          (mul_le_mul_of_nonneg_left hint (by positivity)))
    _ = Real.sqrt (Real.pi/β)+K*((10^24/(m:ℝ)^14)*(1+β^7))*Real.sqrt (2*Real.pi/β) := by ring
    _ ≤ Real.sqrt (Real.pi/β)+K*(2*(10:ℝ)^24)*Real.sqrt (2*Real.pi/β) := by
        gcongr
    _ = (Real.sqrt Real.pi+(2*(10:ℝ)^24)*K*Real.sqrt (2*Real.pi))/Real.sqrt β := by
        rw [hs1, hs2]
        field_simp

end SphericalRiesz
end
end

section

/-! Localized fourteenth-order Gaussian bump error in the actual 24-dimensional
chart domain and ambient R25.

The nearest-point/product-envelope argument of the order-twelve proof is stated once for an
arbitrary bound `Kφ e^(-τ‖Ψ-w‖²/2)` of the fourteenth derivative of the bump.  Two instances:
`Kφ = fourteenthConst L (1+τ⁷)` for every `τ > 0`, and `Kφ = fourteenthSmallConst L √τ` for
`τ ≤ 1`.  The second one makes the patch Gaussian defect linear in `τ` at macroscopic scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem fourteenth_coordinate_within_abs_le_of_contDiffAt (d : ℕ)
    {F : (Fin d → ℝ) → ℝ} (i : Fin d) (v : Fin d → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hf : ContDiffAt ℝ 14 F (Function.update v i t)) :
    |iteratedDerivWithin 14 (fun u => F (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤
      ‖iteratedFDeriv ℝ 14 F (Function.update v i t)‖ := by
  let g : ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i
  let a := Function.update v i 0
  let H : (Fin d → ℝ) → ℝ := fun z => F (z+a)
  have hepoint : g t+a = Function.update v i t := (coordinate_update_as_line d i v t).symm
  have hH : ContDiffAt ℝ 14 H (g t) := by
    apply ContDiffAt.comp (g := F) (f := fun z => z+a) (g t)
    · rw [hepoint]; exact hf
    · fun_prop
  have heq : (fun u => F (Function.update v i u)) = H ∘ g := by
    funext u
    rw [coordinate_update_as_line]
    rfl
  obtain ⟨U,hU,hgtU,hHU⟩ := hH.contDiffOn' le_rfl (by simp)
  have hHU' : ContDiffOn ℝ 14 H U := by simpa using hHU
  have hp : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hline := g.iteratedFDerivWithin_comp_right hHU' hU.uniqueDiffOn hp.uniqueDiffOn hgtU
    (i := 14) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 14 hp hgtU,
    iteratedFDerivWithin_of_isOpen 14 hU hgtU] at hline
  rw [heq,iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hH.comp t g.contDiff.contDiffAt) ht,← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,hline]
  have hshift : iteratedFDeriv ℝ 14 H (g t) = iteratedFDeriv ℝ 14 F (Function.update v i t) := by
    dsimp only [H]
    rw [iteratedFDeriv_comp_add_right,hepoint]
  rw [hshift]
  have hnorm : ‖g‖ = 1 := ContinuousLinearMap.norm_single ℝ (fun _ : Fin d => ℝ) i
  simpa only [hnorm,Finset.prod_const_one,mul_one] using
    (iteratedFDeriv ℝ 14 F (Function.update v i t)).norm_compContinuousLinearMap_le (fun _ => g)

/-- Constant of the fourteenth derivative bound. -/
def fourteenthConst (L : ℝ) : ℝ := 87178291200*4782969*(10:ℝ)^38*L^14

/-- Constant of the one-dimensional rule average. -/
def gaussRuleConst14 : ℝ := Real.sqrt Real.pi+(2*(10:ℝ)^24)*(87178291200*4782969*(10:ℝ)^38)*Real.sqrt (2*Real.pi)

theorem gaussRuleConst14_nonneg : 0 ≤ gaussRuleConst14 := by
  unfold gaussRuleConst14
  positivity

theorem sqrt_pi_le_gaussRuleConst14 : Real.sqrt Real.pi ≤ gaussRuleConst14 := by
  unfold gaussRuleConst14
  have : 0 ≤ (2*(10:ℝ)^24)*(87178291200*4782969*(10:ℝ)^38:ℝ)*Real.sqrt (2*Real.pi) := by positivity
  linarith

/-- The constant of the localized fourteenth-order bump error. -/
def bumpErrorConstFourteen24 (L C₀ : ℝ) : ℝ :=
  (24*(10:ℝ)^24)*fourteenthConst L*(Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24

/-- The envelope factor of the localized bump error (independent of the derivative bound). -/
def bumpEnvelopeConst24 (L C₀ : ℝ) : ℝ :=
  (24*(10:ℝ)^24)*(Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24

theorem bumpEnvelopeConst24_nonneg (L C₀ : ℝ) : 0 ≤ bumpEnvelopeConst24 L C₀ := by
  unfold bumpEnvelopeConst24
  positivity

/-- Localized fourteenth-order bump error for an arbitrary Gaussian bound `Kφ` of the
fourteenth derivative of the bump. -/
theorem normalized_bump_quadrature_error_fourteen24_of_derivative
    {Ψ : (Fin 24 → ℝ) → AmbientD 24} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 Ψ x)
    (hlow : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 24)
    {Kφ : ℝ} (hKφ : 0 ≤ Kφ)
    (hD : ∀ y ∈ UnitCube 24,
      ‖iteratedFDeriv ℝ 14 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2))) y‖ ≤
        Kφ*Real.exp (-(τ*‖Ψ y-w‖^2/2))) :
    |fourteenCubeQuadrature 24 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 24 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpEnvelopeConst24 L C₀*Kφ/(n:ℝ)^14*
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
  set A := Kφ*Real.exp (-(τ*ρ^2/4)) with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  set f : (Fin 24 → ℝ) → ℝ := fun x => Real.exp (-(τ*‖Ψ x-w‖^2)) with hfdef
  have hfcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 f x := by
    intro x hx
    have h1 : ContDiffAt ℝ 14 (fun x => Ψ x-w) x := (hcd x hx).sub contDiffAt_const
    have h2 : ContDiffAt ℝ 14 (fun x => ‖Ψ x-w‖^2) x := h1.norm_sq ℝ
    exact Real.contDiff_exp.contDiffAt.comp x ((h2.const_smul τ).neg)
  have hM : ∀ i v, v ∈ UnitCube 24 → ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin 14 (fun u => f (Function.update v i u)) (Icc (0 : ℝ) 1) t| ≤
        A*∏ j, gauss1 β (x0 j) (Function.update v i t j) := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    refine (fourteenth_coordinate_within_abs_le_of_contDiffAt 24 i v t ht (hfcd _ hy)).trans ?_
    set y := Function.update v i t with hydef
    calc ‖iteratedFDeriv ℝ 14 f y‖ ≤ Kφ*Real.exp (-(τ*‖Ψ y-w‖^2/2)) := hD y hy
      _ ≤ Kφ*(Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j)) :=
          mul_le_mul_of_nonneg_left (henv y hy) hKφ
      _ = A*∏ j, gauss1 β (x0 j) (y j) := by rw [hAdef]; ring
  -- one-dimensional bounds
  set B := min 1 (gaussRuleConst14/Real.sqrt β) with hBdef
  have hQB : ∀ j, fourteenQuadrature n (gauss1 β (x0 j)) ≤ B := by
    intro j
    exact le_min (gauss1_fourteenQuadrature_le_one hn hβ.le _)
      (gauss1_fourteenQuadrature_le hn hβ hβn _)
  have hIB : ∀ j, (∫ t in (0:ℝ)..1, gauss1 β (x0 j) t) ≤ B := by
    intro j
    refine le_min (gauss1_integral_le_one hβ.le _) ((gauss1_integral_le_sqrt hβ _).trans ?_)
    rw [Real.sqrt_div' _ hβ.le]
    exact div_le_div_of_nonneg_right sqrt_pi_le_gaussRuleConst14 (Real.sqrt_nonneg _)
  have herr := fourteenCubeQuadrature_fourteenth_order_envelope_on 24 hn
    (fun x hx => (hfcd x hx).continuousAt.continuousWithinAt)
    (fun i v hv => by
      intro t ht
      have hy := update_mem_unitCube hv i ht
      have hu : ContDiffAt ℝ 14 (fun u : ℝ => Function.update v i u) t := by
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
  have hratio : B ≤ (Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))*J := by
    apply gauss1_bound_ratio hβ hγ gaussRuleConst14_nonneg (by positivity)
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
  have hB0 : 0 ≤ B := le_min zero_le_one (div_nonneg gaussRuleConst14_nonneg (Real.sqrt_nonneg _))
  have hB8 : B^24 ≤ (Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24*J^24 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hratio 24
  have hprodB : ∏ _j : Fin 24, B = B^24 := by simp
  rw [hprodB] at herr
  have hn6 : (0:ℝ) < (n:ℝ)^14 := by positivity
  calc |fourteenCubeQuadrature 24 n f-cubeIntegral 24 f|
      ≤ 10^24/(n:ℝ)^14*((24:ℕ)*(A*B^24)) := herr
    _ = (24*(10:ℝ)^24)/(n:ℝ)^14*Kφ*(Real.exp (-(τ*ρ^2/4))*B^24) := by
        rw [hAdef]; push_cast; ring
    _ ≤ (24*(10:ℝ)^24)/(n:ℝ)^14*Kφ*(Real.exp (-(τ*ρ^2/4))*
          ((Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24*J^24)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hB8 (Real.exp_pos _).le
    _ = (24*(10:ℝ)^24)/(n:ℝ)^14*Kφ*
          (Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24*
            (Real.exp (-(τ*ρ^2/4))*J^24) := by ring
    _ ≤ (24*(10:ℝ)^24)/(n:ℝ)^14*Kφ*
          (Real.exp 1*max 2 (gaussRuleConst14*(Real.sqrt 96*L/C₀)))^24*
            cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) :=
        mul_le_mul_of_nonneg_left hrhs (by positivity)
    _ = bumpEnvelopeConst24 L C₀*Kφ/(n:ℝ)^14*
          cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
        rw [bumpEnvelopeConst24]; ring

/-- Constant of the small-`τ` fourteenth derivative bound. -/
def fourteenthSmallConst (L : ℝ) : ℝ := 87178291200*10569662464*(16384*L^2)^14

theorem fourteenthConst_nonneg {L : ℝ} (_hL : 0 ≤ L) : 0 ≤ fourteenthConst L := by
  unfold fourteenthConst
  positivity

theorem fourteenthSmallConst_nonneg (L : ℝ) : 0 ≤ fourteenthSmallConst L := by
  unfold fourteenthSmallConst
  positivity

/-- The constant of the small-`τ` localized fourteenth-order bump error. -/
def bumpErrorConstFourteenSmall24 (L C₀ : ℝ) : ℝ :=
  bumpEnvelopeConst24 L C₀*fourteenthSmallConst L

theorem bumpErrorConstFourteen24_eq (L C₀ : ℝ) :
    bumpErrorConstFourteen24 L C₀ = bumpEnvelopeConst24 L C₀*fourteenthConst L := by
  unfold bumpErrorConstFourteen24 bumpEnvelopeConst24
  ring

private theorem bump_shift_derivative {Ψ : (Fin 24 → ℝ) → AmbientD 24} {L : ℝ}
    (hcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (w : AmbientD 24) {y : Fin 24 → ℝ} (hy : y ∈ UnitCube 24) :
    ContDiffAt ℝ 14 (fun x => Ψ x-w) y ∧
      ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j (fun x => Ψ x-w) y‖ ≤ L := by
  refine ⟨(hcd y hy).sub contDiffAt_const, ?_⟩
  intro j hj hj6
  have hjc : ContDiffAt ℝ j Ψ y := (hcd y hy).of_le (by exact_mod_cast hj6)
  rw [show (fun x => Ψ x-w) = Ψ-(fun _ => w) from rfl,
    iteratedFDeriv_sub_apply hjc contDiffAt_const, iteratedFDeriv_const_of_ne (by omega) w]
  simpa only [Pi.zero_apply, sub_zero] using hder y hy j hj hj6

/-- Localized fourteenth-order bump error, every `τ > 0`. -/
theorem normalized_bump_quadrature_error_fourteen24
    {Ψ : (Fin 24 → ℝ) → AmbientD 24} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 24) :
    |fourteenCubeQuadrature 24 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 24 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConstFourteen24 L C₀/(n:ℝ)^14*(1+τ^7)*
        cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hK : 0 ≤ fourteenthConst L*(1+τ^7) :=
    mul_nonneg (fourteenthConst_nonneg (by linarith)) (by positivity)
  have h := normalized_bump_quadrature_error_fourteen24_of_derivative hL hC₀ hcd hlow hup hn hτ
    hβn w hK (fun y hy => by
      obtain ⟨hFcd, hFL⟩ := bump_shift_derivative hcd hder w hy
      have h := norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le hFcd hL hFL hτ.le
      simpa only [fourteenthConst] using h)
  rw [bumpErrorConstFourteen24_eq]
  calc _ ≤ bumpEnvelopeConst24 L C₀*(fourteenthConst L*(1+τ^7))/(n:ℝ)^14*
          cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := h
    _ = _ := by ring

/-- Localized fourteenth-order bump error with a factor `√τ`, for `τ ≤ 1`. -/
theorem normalized_bump_quadrature_error_fourteen_small24
    {Ψ : (Fin 24 → ℝ) → AmbientD 24} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 24) :
    |fourteenCubeQuadrature 24 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 24 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConstFourteenSmall24 L C₀/(n:ℝ)^14*Real.sqrt τ*
        cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hK : 0 ≤ fourteenthSmallConst L*Real.sqrt τ :=
    mul_nonneg (fourteenthSmallConst_nonneg L) (Real.sqrt_nonneg τ)
  have h := normalized_bump_quadrature_error_fourteen24_of_derivative hL hC₀ hcd hlow hup hn hτ
    hβn w hK (fun y hy => by
      obtain ⟨hFcd, hFL⟩ := bump_shift_derivative hcd hder w hy
      have h := norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le_sqrt hFcd hL hFL hτ.le hτ1
      simpa only [fourteenthSmallConst] using h)
  unfold bumpErrorConstFourteenSmall24
  calc _ ≤ bumpEnvelopeConst24 L C₀*(fourteenthSmallConst L*Real.sqrt τ)/(n:ℝ)^14*
          cubeIntegral 24 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := h
    _ = _ := by ring

end SphericalRiesz
end
end

section

/-! Fourteenth-order nodes of small Leech patches on S24: labels, theta rows, short-range budgets, the node families of a patch family and the sharp Gaussian window of the foreground.  Port of the order-twelve declarations to the order-fourteen rule (strip 24, middle block from 48 nodes on). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open Set MeasureTheory
open scoped ENNReal NNReal
open scoped ENNReal
namespace SphericalRiesz
open Boundary

open Boundary

/-- Boundary corrections retain control by their distinct integer labels. -/
theorem fourteenRule_label_sub_le {n : ℕ} (hn : 48 ≤ n) (u w : FourteenNodeIndex n) :
    |(fourteenMidpointLabel n u:ℝ)-(fourteenMidpointLabel n w:ℝ)| ≤
      2*|fourteenUnscaledRuleNode n u-fourteenUnscaledRuleNode n w| := by
  have haux : ∀ i j : FourteenNodeIndex n, fourteenMidpointLabel n i < fourteenMidpointLabel n j →
      |(fourteenMidpointLabel n i:ℝ)-(fourteenMidpointLabel n j:ℝ)| ≤
        2*|fourteenUnscaledRuleNode n i-fourteenUnscaledRuleNode n j| := by
    intro i j hij
    have hg : (fourteenMidpointLabel n i:ℝ)+1 ≤ fourteenMidpointLabel n j := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hi := abs_lt.mp (fourteenUnscaledRuleNode_close_to_label hn i)
    have hj := abs_lt.mp (fourteenUnscaledRuleNode_close_to_label hn j)
    rw [abs_of_nonpos (by linarith : (fourteenMidpointLabel n i:ℝ)-(fourteenMidpointLabel n j:ℝ) ≤ 0)]
    have hdiff : -(fourteenMidpointLabel n i:ℝ)+(fourteenMidpointLabel n j:ℝ) ≤
        2*(fourteenUnscaledRuleNode n j-fourteenUnscaledRuleNode n i) := by linarith
    calc
      _ ≤ 2*(fourteenUnscaledRuleNode n j-fourteenUnscaledRuleNode n i) := by linarith
      _ ≤ 2*|fourteenUnscaledRuleNode n j-fourteenUnscaledRuleNode n i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = _ := by rw [abs_sub_comm]
  rcases lt_trichotomy (fourteenMidpointLabel n u) (fourteenMidpointLabel n w) with h | h | h
  · exact haux u w h
  · simp [h]
  · simpa only [abs_sub_comm] using haux w u h

def leechFourteenthLabel24 (n : ℕ) (hn : 48 ≤ n) :
    (Fin 24 → FourteenNodeIndex n) ↪ leechLattice where
  toFun u := ⟨leechIntegerPoint (fun i => (fourteenMidpointLabel n (u i):ℤ)),
    (leechLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := leechMap_injective (congrArg (fun z : leechLattice => WithLp.ofLp (z : LeechAmbient)) h)
    funext i
    apply fourteenMidpointLabel_injective hn
    have hi : (fourteenMidpointLabel n (u i):ℝ) = (fourteenMidpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem leechFourteenthLabel24_norm_le {n : ℕ} (hn : 48 ≤ n)
    (u w : Fin 24 → FourteenNodeIndex n) :
    ‖((leechFourteenthLabel24 n hn w-leechFourteenthLabel24 n hn u : leechLattice) : LeechAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)*‖fourteenCubeNode 24 n u-fourteenCubeNode 24 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 24 → ℝ := fun i => (fourteenMidpointLabel n (u i):ℝ)-(fourteenMidpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖fourteenCubeNode 24 n u-fourteenCubeNode 24 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := fourteenRule_label_sub_le hn (u i) (w i)
    have he : |fourteenUnscaledRuleNode n (u i)-fourteenUnscaledRuleNode n (w i)| =
        (n:ℝ)*|fourteenCubeNode 24 n u i-fourteenCubeNode 24 n w i| := by
      simp only [fourteenCubeNode,fourteenRuleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|fourteenCubeNode 24 n u i-fourteenCubeNode 24 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖fourteenCubeNode 24 n u-fourteenCubeNode 24 n w‖ := by
        have hi := norm_le_pi_norm (fourteenCubeNode 24 n u-fourteenCubeNode 24 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((leechFourteenthLabel24 n hn w-leechFourteenthLabel24 n hn u : leechLattice) : LeechAmbient)‖ =
      ‖equalAreaFlatDerivative24 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative24,
        equalAreaFlatDerivative24_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖leechIntegerPoint (fun i => (fourteenMidpointLabel n (w i):ℤ))-
      leechIntegerPoint (fun i => (fourteenMidpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (leechMap z)‖
    rw [norm_sub_rev,leechIntegerPoint,leechIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative24‖*‖z‖ := equalAreaFlatDerivative24.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative24‖*((2*(n:ℝ))*‖fourteenCubeNode 24 n u-fourteenCubeNode 24 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaLeechFourteenth24_gaussian_row {n : ℕ} (hn : 48 ≤ n)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y))
    (u : Fin 24 → FourteenNodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨fourteenCubeNode 24 n u,fun i => ⟨(fourteenCubeNode_mem_open 24 n hn u i).1.le,(fourteenCubeNode_mem_open 24 n hn u i).2.le⟩⟩)
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨fourteenCubeNode 24 n w,fun i => ⟨(fourteenCubeNode_mem_open 24 n hn w i).1.le,(fourteenCubeNode_mem_open 24 n hn w i).2.le⟩⟩)) ≤
    leechGaussianThetaReal24 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative24_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply leechPatchGaussian_row_le (leechFourteenthLabel24 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaLeechPatch g v c ε (fourteenCubeNode 24 n i))
    (equalAreaLeechPatch g v c ε (fourteenCubeNode 24 n j))
  rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
  have hi : fourteenCubeNode 24 n i ∈ UnitCube 24 := fun k => ⟨(fourteenCubeNode_mem_open 24 n hn i k).1.le,(fourteenCubeNode_mem_open 24 n hn i k).2.le⟩
  have hj : fourteenCubeNode 24 n j ∈ UnitCube 24 := fun k => ⟨(fourteenCubeNode_mem_open 24 n hn j k).1.le,(fourteenCubeNode_mem_open 24 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := leechFourteenthLabel24_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
  have hdiv : ‖((leechFourteenthLabel24 n hn j-leechFourteenthLabel24 n hn i : leechLattice) :
      LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖fourteenCubeNode 24 n i-fourteenCubeNode 24 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((leechFourteenthLabel24 n hn j-leechFourteenthLabel24 n hn i : leechLattice) : LeechAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by ring
    _ ≤ ε*L*‖fourteenCubeNode 24 n i-fourteenCubeNode 24 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith

/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def leechFourteenthSphereNodes24 (n : ℕ) (hn : 48 ≤ n)
    (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    (Fin 24 → FourteenNodeIndex n) → SphereD 24 := fun u =>
  equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
    ⟨fourteenCubeNode 24 n u,fun i =>
      ⟨(fourteenCubeNode_mem_open 24 n hn u i).1.le,(fourteenCubeNode_mem_open 24 n hn u i).2.le⟩⟩

/-- The actual fourteenth-order sphere nodes are all distinct. -/
theorem leechFourteenthSphereNodes24_injective (n : ℕ) (hn : 48 ≤ n)
    (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    Function.Injective (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall) := by
  intro u w h
  have hcube := (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall).injective h
  exact fourteenCubeNode_injective 24 n hn (congrArg Subtype.val hcube)

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaLeechFourteenth24_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (n : ℕ) (hn : 48 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel24 t p
        (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^24*leechGaussianTailBudget24 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((leechFourteenthLabel24 n hn j-leechFourteenthLabel24 n hn i :
      leechLattice) : LeechAmbient)‖ ≤
      dist (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall i)
        (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaLeechPatch g v c ε (fourteenCubeNode 24 n i))
      (equalAreaLeechPatch g v c ε (fourteenCubeNode 24 n j))
    rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
    have hi : fourteenCubeNode 24 n i ∈ UnitCube 24 := fun k =>
      ⟨(fourteenCubeNode_mem_open 24 n hn i k).1.le,(fourteenCubeNode_mem_open 24 n hn i k).2.le⟩
    have hj : fourteenCubeNode 24 n j ∈ UnitCube 24 := fun k =>
      ⟨(fourteenCubeNode_mem_open 24 n hn j k).1.le,(fourteenCubeNode_mem_open 24 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := leechFourteenthLabel24_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
    have hdiv : ‖((leechFourteenthLabel24 n hn j-leechFourteenthLabel24 n hn i : leechLattice) :
        LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖fourteenCubeNode 24 n i-fourteenCubeNode 24 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖leechInverseMap‖)))*
          (‖((leechFourteenthLabel24 n hn j-leechFourteenthLabel24 n hn i : leechLattice) :
            LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖leechInverseMap‖)))*‖fourteenCubeNode 24 n i-fourteenCubeNode 24 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := leechPatch_shortRange_budget_le (leechFourteenthLabel24 n hn)
    (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 24 → FourteenNodeIndex n) = n^24 := by
    simp [fourteenNodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- At the actual n^24 sphere density the corrected foreground has one explicit budget for
all n>=48.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaLeechFourteenth24_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 48 ≤ n),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 (n^24)) p
        (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechFourteenthSphereNodes24 n hn g v c hc ε hε hsmall w))/(n:ℝ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechFourteenth24_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall p hp n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  have hcN := sphereGaussianDensityFactor24_pos (N := n^24) (by positivity)
  have hscale : leechCorrectedDensityBudgetScale24 ε ≤
      sphereGaussianDensityFactor24 (n^24)*
        (ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor24_pow_twentyFour]
    unfold leechCorrectedDensityBudgetScale24
    apply le_of_eq
    field_simp
  have hb := hcost g v c hv hc ε hε hs hsmall n hn
    (sphereGaussianDensityFactor24 (n^24)) (leechCorrectedDensityBudgetScale24 ε) p
    hcN (leechCorrectedDensityBudgetScale24_pos hε) hp hscale
  apply (div_le_iff₀ (pow_pos hnR 24)).mpr
  simpa only [mul_comm] using hb

/-- Rational allocation also removes the shrinking chart size from the budget: with n=a*m,
N=(d*m)^24 and epsilon=r*a/d, the positive theta scale depends only on r.
Thus the computed foreground bound is common across a,d,m, rather than merely a fixed chart. -/
theorem equalAreaLeechFourteenth24_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 48 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p
        (leechFourteenthSphereNodes24 (a*m) hn g v c hc ε hε hsmall u)
        (leechFourteenthSphereNodes24 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechFourteenth24_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall r p hr hp a d m ha hd hm hratio hn
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hD := equalAreaFlatDerivative24_norm_pos
  have he : ε = r*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR.ne').mpr hratio
  have hcN := sphereGaussianDensityFactor24_pos (N := (d*m)^24) (by positivity)
  have hscale : leechCorrectedDensityBudgetScale24 r ≤
      sphereGaussianDensityFactor24 ((d*m)^24)*
        (ε/(4*(a*m:ℕ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor24_pow_twentyFour, he]
    unfold leechCorrectedDensityBudgetScale24
    push_cast
    apply le_of_eq
    field_simp
  have hb := hcost g v c hv hc ε hε hs hsmall (a*m) hn
    (sphereGaussianDensityFactor24 ((d*m)^24)) (leechCorrectedDensityBudgetScale24 r) p
    hcN (leechCorrectedDensityBudgetScale24_pos hr) hp hscale
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (a*m:ℕ)^24)).mpr
  simpa only [Nat.cast_pow, mul_comm] using hb

/-- Fourteenth-order nodes of a small patch on the sphere. -/
def smallLeechPatchNodesF24 (p : SmallLeechCubePatch24) (n : ℕ) (hn : 48 ≤ n) :
    (Fin 24 → FourteenNodeIndex n) → SphereD 24 :=
  leechFourteenthSphereNodes24 n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallLeechPatchNodesF24_injective (p : SmallLeechCubePatch24) (n : ℕ) (hn : 48 ≤ n) :
    Function.Injective (smallLeechPatchNodesF24 p n hn) :=
  leechFourteenthSphereNodes24_injective n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallLeechPatchNodesF24_coe (p : SmallLeechCubePatch24) (n : ℕ) (hn : 48 ≤ n)
    (u : Fin 24 → FourteenNodeIndex n) :
    (smallLeechPatchNodesF24 p n hn u : AmbientD 24) = smallLeechCubeMap24 p (fourteenCubeNode 24 n u) :=
  rfl

theorem smallLeechPatchNodesF24_mem (p : SmallLeechCubePatch24) (n : ℕ) (hn : 48 ≤ n)
    (u : Fin 24 → FourteenNodeIndex n) :
    smallLeechPatchNodesF24 p n hn u ∈ smallLeechSpherePatch24 p := by
  refine ⟨fourteenCubeNode 24 n u, fun i => ⟨(fourteenCubeNode_mem_open 24 n hn u i).1.le,
    (fourteenCubeNode_mem_open 24 n hn u i).2.le⟩, rfl⟩

/-- All fourteenth-order nodes of a patch family of one common scale. -/
def leechFamilyNodesF24 {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (n : ℕ) (hn : 48 ≤ n) :
    Fin K × (Fin 24 → FourteenNodeIndex n) → SphereD 24 :=
  fun q => smallLeechPatchNodesF24 (P q.1) n hn q.2

open Boundary

theorem leechFamilyNodesF24_injective {K : ℕ} (P : Fin K → SmallLeechCubePatch24)
    (hdisj : Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
      (smallLeechSpherePatch24 (P j)))) (n : ℕ) (hn : 48 ≤ n) :
    Function.Injective (leechFamilyNodesF24 P n hn) := by
  rintro ⟨i,u⟩ ⟨j,w⟩ h
  change smallLeechPatchNodesF24 (P i) n hn u = smallLeechPatchNodesF24 (P j) n hn w at h
  have hij : i = j := by
    by_contra hne
    have hi := smallLeechPatchNodesF24_mem (P i) n hn u
    have hj := smallLeechPatchNodesF24_mem (P j) n hn w
    rw [← h] at hj
    exact Set.disjoint_left.mp (hdisj hne) hi hj
  subst hij
  rw [smallLeechPatchNodesF24_injective (P i) n hn h]

/-- Indices of the uncorrected middle block of the fourteenth-order tensor rule. -/
def fourteenMiddleCube (n : ℕ) : (Fin 24 → Fin (n-48)) ↪ (Fin 24 → FourteenNodeIndex n) where
  toFun u := fun i => Sum.inr (Sum.inl (u i))
  inj' := by
    intro u w h
    funext i
    exact Sum.inl_injective (Sum.inr_injective (congrFun h i))

theorem fourteenCubeNode_middle (n : ℕ) (u : Fin 24 → Fin (n-48)) (i : Fin 24) :
    fourteenCubeNode 24 n (fourteenMiddleCube n u) i = ((u i:ℝ)+24+1/2)/(n:ℝ) := rfl

/-- Middle nodes are lattice midpoints: their flat distances are lattice distances at scale
`1/n`. -/
theorem fourteenMiddleCube_flat_distance (n : ℕ) (u w : Fin 24 → Fin (n-48)) :
    dist (WithLp.toLp 2 (leechMap (fourteenCubeNode 24 n (fourteenMiddleCube n u))) : LeechAmbient)
      (WithLp.toLp 2 (leechMap (fourteenCubeNode 24 n (fourteenMiddleCube n w)))) =
      (n:ℝ)⁻¹*‖((leechGridLattice24 (n-48) w-leechGridLattice24 (n-48) u : leechLattice) :
        LeechAmbient)‖ := by
  have he : fourteenCubeNode 24 n (fourteenMiddleCube n u)-fourteenCubeNode 24 n (fourteenMiddleCube n w) =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, fourteenCubeNode_middle, div_eq_mul_inv]
    ring
  rw [dist_eq_norm, ← WithLp.toLp_sub, ← map_sub, he, map_smul, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
  congr 1
  change ‖WithLp.toLp 2 (leechMap (fun i => (u i:ℝ)-(w i:ℝ)))‖ =
    ‖leechIntegerPoint (fun i => (w i:ℤ))-leechIntegerPoint (fun i => (u i:ℤ))‖
  rw [norm_sub_rev]
  rw [leechIntegerPoint, leechIntegerPoint, ← WithLp.toLp_sub, ← map_sub]
  simp only [Int.cast_natCast]
  rfl

/-- Middle nodes of a small patch: sharp theta rows, uniformly in the refinement. -/
theorem smallLeechPatch_middle_rowF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 24 → Fin (n-48),
      (∑ w, sphereGaussianKernel24 t
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n w))) ≤
      leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaLeechPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x : (Fin 24 → Fin (n-48)) → UnitCube 24 := fun w =>
    ⟨fourteenCubeNode 24 n (fourteenMiddleCube n w), fun i =>
      ⟨(fourteenCubeNode_mem_open 24 n hn (fourteenMiddleCube n w) i).1.le,
        (fourteenCubeNode_mem_open 24 n hn (fourteenMiddleCube n w) i).2.le⟩⟩
  have hrow := hb p.g p.v p.c hv p.c_mem p.ε p.ε_pos hε p.small (leechGridLattice24 (n-48)) x
    (n:ℝ)⁻¹ (inv_pos.mpr hnR) (fun i j => fourteenMiddleCube_flat_distance n i j) t ht u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n w))) ≤
      leechGaussianThetaReal24 (t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n w))) =
      sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n w)) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
      (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n w))) (Finset.mem_univ u)).symm
  have hθ : t*((1-η)*p.ε/(n:ℝ))^2/Real.pi = t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi := by
    rw [div_eq_mul_inv ((1-η)*p.ε) (n:ℝ)]
  rw [hsplit, sphereGaussianKernel24_self t, hθ]
  linarith

/-- All nodes of a small patch: conservative theta rows, uniformly in the refinement. -/
theorem smallLeechPatch_all_rowF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 24 → FourteenNodeIndex n,
      (∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn w)) ≤
      leechGaussianThetaReal24
        (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hrow := equalAreaLeechFourteenth24_gaussian_row hn p.g p.v p.c p.c_mem p.ε_pos p.small
    patchChartLower24_pos ht
    (fun x hx y hy => hgeom p.v hv p.ε p.ε_pos hε p.g p.c p.c_mem x hx y hy) u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn u) (smallLeechPatchNodesF24 p n hn w)) ≤
      leechGaussianThetaReal24
        (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
      (smallLeechPatchNodesF24 p n hn w)) =
      sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn u)+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn w) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn u) (smallLeechPatchNodesF24 p n hn w))
      (Finset.mem_univ u)).symm
  rw [hsplit, sphereGaussianKernel24_self t]
  linarith

/-- The full Gaussian pair sum of one small patch: sharp theta rows on the middle block and
conservative rows for the `n²⁴-(n-48)²⁴` other nodes. -/
theorem smallLeechPatch_pairSum_leF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t →
      (∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn w)) ≤
      (n:ℝ)^24*leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi)+
        2*((n:ℝ)^24-((n:ℝ)-48)^24)*leechGaussianThetaReal24
          (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := by
  obtain ⟨ρ₁,hρ₁,hρ₁',hsharp⟩ := smallLeechPatch_middle_rowF hη hη1
  obtain ⟨ρ₂,hρ₂,_,hall⟩ := smallLeechPatch_all_rowF
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε n hn t ht
  have hv₁ := hv.trans (min_le_left ρ₁ ρ₂)
  have hv₂ := hv.trans (min_le_right ρ₁ ρ₂)
  have hε₁ := hε.trans (min_le_left ρ₁ ρ₂)
  have hε₂ := hε.trans (min_le_right ρ₁ ρ₂)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  have hη0 : 0 < 1-η := by linarith
  obtain ⟨θs, hθs⟩ : ∃ θs : ℝ, θs =
      leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := ⟨_, rfl⟩
  obtain ⟨θc, hθc⟩ : ∃ θc : ℝ, θc = leechGaussianThetaReal24
      (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := ⟨_, rfl⟩
  have hθs0 : 0 ≤ θs := by
    rw [hθs]
    exact zero_le_one.trans (leechGaussianThetaReal24_ge_one
      (div_pos (mul_pos ht (pow_pos (div_pos (mul_pos hη0 p.ε_pos) hnR) 2)) Real.pi_pos))
  rw [← hθs, ← hθc]
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 24 → FourteenNodeIndex n),
      S = Finset.univ.map (fourteenMiddleCube n) := ⟨_, rfl⟩
  have h74 : ((n-48 : ℕ) : ℝ) = (n:ℝ)-48 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hcardS : (S.card : ℝ) = ((n:ℝ)-48)^24 := by
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
      Nat.cast_pow, h74]
  have hcardT : (Fintype.card (Fin 24 → FourteenNodeIndex n) : ℝ) = (n:ℝ)^24 := by
    rw [fourteenCubeNode_card 24 n hn]
    exact Nat.cast_pow _ _
  have hcardC : (Sᶜ.card : ℝ) = (n:ℝ)^24-((n:ℝ)-48)^24 := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ S), hcardT, hcardS]
  have hsplit : (∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
      (smallLeechPatchNodesF24 p n hn w)) ≤
      (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn w))+
      2*(∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
        (smallLeechPatchNodesF24 p n hn w)) :=
    pairSum_le_core_add_rest S (fun u w => sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 p n hn u) (smallLeechPatchNodesF24 p n hn w))
      (fun u w => sphereGaussianKernel24_nonneg _ _ _)
      (fun u w => sphereGaussianKernel24_comm t _ _)
  have hcore : (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
      (smallLeechPatchNodesF24 p n hn w)) ≤ (n:ℝ)^24*θs := by
    have hrows : ∀ u : Fin 24 → Fin (n-48), (∑ w ∈ S, sphereGaussianKernel24 t
        (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
        (smallLeechPatchNodesF24 p n hn w)) ≤ θs := by
      intro u
      rw [hS, Finset.sum_map, hθs]
      exact hsharp p hv₁ hε₁ n hn t ht u
    have hpow : ((n:ℝ)-48)^24 ≤ (n:ℝ)^24 := by
      have h0 : 0 ≤ (n:ℝ)-48 := by
        rw [← h74]
        exact Nat.cast_nonneg _
      exact pow_le_pow_left₀ h0 (by linarith) 24
    calc (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
          (smallLeechPatchNodesF24 p n hn w))
        = ∑ u : Fin 24 → Fin (n-48), ∑ w ∈ S, sphereGaussianKernel24 t
            (smallLeechPatchNodesF24 p n hn (fourteenMiddleCube n u))
            (smallLeechPatchNodesF24 p n hn w) := by
          rw [hS, Finset.sum_map]
      _ ≤ ∑ _u : Fin 24 → Fin (n-48), θs := Finset.sum_le_sum fun u _ => hrows u
      _ = ((n:ℝ)-48)^24*θs := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
            Fintype.card_fin, Nat.cast_pow, h74]
      _ ≤ (n:ℝ)^24*θs := mul_le_mul_of_nonneg_right hpow hθs0
  have hrest : (∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 p n hn u)
      (smallLeechPatchNodesF24 p n hn w)) ≤ ((n:ℝ)^24-((n:ℝ)-48)^24)*θc := by
    calc _ ≤ ∑ _u ∈ Sᶜ, θc := Finset.sum_le_sum fun u _ => by
            rw [hθc]
            exact hall p hv₂ hε₂ n hn t ht u
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardC]
  calc _ ≤ _ := hsplit
    _ ≤ (n:ℝ)^24*θs+2*(((n:ℝ)^24-((n:ℝ)-48)^24)*θc) :=
        add_le_add hcore (mul_le_mul_of_nonneg_left hrest (by norm_num))
    _ = _ := by rw [mul_assoc]

/-- Pair sum of a separated family: the patch sums plus the squared cardinality times the cross
bound. -/
theorem leechFamily_pairSum_le_patchesF {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (n : ℕ)
    (hn : 48 ≤ n) (k : SphereD 24 → SphereD 24 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i j, i ≠ j → ∀ u w, k (smallLeechPatchNodesF24 (P i) n hn u)
      (smallLeechPatchNodesF24 (P j) n hn w) ≤ τ) :
    (∑ q, ∑ q', k (leechFamilyNodesF24 P n hn q) (leechFamilyNodesF24 P n hn q')) ≤
      (∑ i, ∑ u, ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
        (smallLeechPatchNodesF24 (P i) n hn w))+((K:ℝ)*(n:ℝ)^24)^2*τ := by
  classical
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcardNodes : (Fintype.card (Fin 24 → FourteenNodeIndex n) : ℝ) = (n:ℝ)^24 := by
    rw [fourteenCubeNode_card 24 n hn]
    exact Nat.cast_pow _ _
  have hrow : ∀ i u, (∑ j, ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
      (smallLeechPatchNodesF24 (P j) n hn w)) ≤
      (∑ w, k (smallLeechPatchNodesF24 (P i) n hn u) (smallLeechPatchNodesF24 (P i) n hn w))+
        (K:ℝ)*((n:ℝ)^24*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
        (smallLeechPatchNodesF24 (P j) n hn w)) ≤
        (if j = i then ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
          (smallLeechPatchNodesF24 (P i) n hn w) else 0)+(n:ℝ)^24*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 24).le hτ)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 24 → FourteenNodeIndex n, τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = (n:ℝ)^24*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
            (smallLeechPatchNodesF24 (P i) n hn w) else 0)+(n:ℝ)^24*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit : (∑ q, ∑ q', k (leechFamilyNodesF24 P n hn q) (leechFamilyNodesF24 P n hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
        (smallLeechPatchNodesF24 (P j) n hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
          (smallLeechPatchNodesF24 (P i) n hn w))+(K:ℝ)*((n:ℝ)^24*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, k (smallLeechPatchNodesF24 (P i) n hn u)
          (smallLeechPatchNodesF24 (P i) n hn w))+(K:ℝ)*((n:ℝ)^24*((K:ℝ)*((n:ℝ)^24*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ = _ := by ring

/-- Gaussian window of a separated fourteenth-order foreground family at exact mass. -/
theorem leechPatchFamily_gaussianWindow_leF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m) (α : ℝ), 0 < α →
      (∑ q, ∑ q', sphereGaussianKernel24 (sphereGaussianScale24 ((d*m)^24) α)
          (leechFamilyNodesF24 P (a*m) hn q) (leechFamilyNodesF24 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
          2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
            leechGaussianThetaReal24 (α*leechConservativeRowFactor24))+
        ((K:ℝ)*((a*m:ℕ):ℝ)^24)^2*
          Real.exp (-(sphereGaussianScale24 ((d*m)^24) α*δ^2)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_pairSum_leF hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn α hα
  have hNpos : 0 < (d*m)^24 := by positivity
  have ht0 : 0 < sphereGaussianScale24 ((d*m)^24) α := sphereGaussianScale24_pos hNpos hα
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = sphereGaussianScale24 ((d*m)^24) α := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  rw [← htdef, ← hndef]
  have ht : 0 < t := by rw [htdef]; exact ht0
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hn0' : n ≠ 0 := hn0.ne'
  have hD := equalAreaFlatDerivative24_norm_pos
  have hπ := Real.pi_pos
  have hnπ : n^2*Real.pi ≠ 0 := (mul_pos (pow_pos hn0 2) hπ).ne'
  -- theta arguments at exact mass
  have hte : ∀ i, t*(P i).ε^2 = Real.pi*n^2*α := by
    intro i
    have h := sphereGaussian_exact_mass_bump_scale24 a d m hd (P i).ε α (hratio i)
    rw [← htdef, ← hndef] at h
    linarith
  have hsharp : ∀ i, t*((1-η)*(P i).ε/n)^2/Real.pi = α*(1-η)^2 := by
    intro i
    have h1 : t*((1-η)*(P i).ε/n)^2/Real.pi =
        (t*(P i).ε^2)*(1-η)^2/(n^2*Real.pi) := by ring
    rw [h1, hte i, div_eq_iff hnπ]
    ring
  have hfac : leechConservativeRowFactor24 =
      patchChartLower24^2/(2*‖equalAreaFlatDerivative24‖)^2 := by
    unfold leechConservativeRowFactor24
    rw [div_pow]
  have hcons : ∀ i, t*((P i).ε*patchChartLower24/(2*n*‖equalAreaFlatDerivative24‖))^2/Real.pi =
      α*leechConservativeRowFactor24 := by
    intro i
    have h1 : t*((P i).ε*patchChartLower24/(2*n*‖equalAreaFlatDerivative24‖))^2/Real.pi =
        (t*(P i).ε^2)*(patchChartLower24^2/(2*‖equalAreaFlatDerivative24‖)^2)/
          (n^2*Real.pi) := by ring
    rw [h1, hte i, hfac, div_eq_iff hnπ]
    ring
  have hsub : n^24-(n-48)^24 = n^24*(1-(1-48/n)^24) := by
    have h74 : n-48 = n*(1-48/n) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hn0']
    rw [h74, mul_pow]
    ring
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P i) (a*m) hn w)) ≤
      n^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
        2*(1-(1-48/n)^24)*leechGaussianThetaReal24 (α*leechConservativeRowFactor24)) := by
    intro i
    have h := hb (P i) (hv i) (hε i) (a*m) hn t ht
    rw [← hndef, hsharp i, hcons i, hsub] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, sphereGaussianKernel24 t
      (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P j) (a*m) hn w) ≤
      Real.exp (-(t*δ^2)) := by
    intro i j hij u w
    have hdist := hsep i j hij _ (smallLeechPatchNodesF24_mem (P i) _ hn u) _
      (smallLeechPatchNodesF24_mem (P j) _ hn w)
    unfold sphereGaussianKernel24
    apply Real.exp_le_exp.mpr
    have hsq : δ^2 ≤ dist (smallLeechPatchNodesF24 (P i) (a*m) hn u)
        (smallLeechPatchNodesF24 (P j) (a*m) hn w)^2 := pow_le_pow_left₀ hδ.le hdist 2
    have hmul := mul_le_mul_of_nonneg_left hsq ht.le
    linarith
  have hfam := leechFamily_pairSum_le_patchesF P (a*m) hn (sphereGaussianKernel24 t)
    (Real.exp_pos (-(t*δ^2))).le hcross
  rw [← hndef] at hfam
  calc _ ≤ (∑ i, ∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodesF24 (P i) (a*m) hn u)
          (smallLeechPatchNodesF24 (P i) (a*m) hn w))+((K:ℝ)*n^24)^2*Real.exp (-(t*δ^2)) := hfam
    _ ≤ (∑ _i : Fin K, n^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
          2*(1-(1-48/n)^24)*leechGaussianThetaReal24 (α*leechConservativeRowFactor24)))+
          ((K:ℝ)*n^24)^2*Real.exp (-(t*δ^2)) :=
        add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end SphericalRiesz
end
end

section

/-! Fourteenth-order Gaussian bump error of the Leech patch nodes on `S²⁴`, and the neutralized
Gaussian defect of a foreground family against the smooth residual background.

At exact mass (`ε d = r₀ a`, `n = a m`, `N = (d m)²⁴`) the node sum of an ambient Gaussian bump
differs from `N ∫_patch` by at most `K (n⁻¹⁴ + (2πα)⁷)` times `N ∫_patch` of the softened bump,
for every `α ∈ (0,4]`; at macroscopic scales `2π n² α ≤ 1` the factor is `K' √(2πα)/n¹³`.
Squaring gives the defect of the mixed measure (foreground points plus `N σ` on the complement
of the patches):

`defect(α) ≤ 8^(25/2) (K (n⁻¹⁴ + (2πα)⁷))² N² B(t/8)`, and for `2π n² α ≤ 1`
`defect(α) ≤ 8^(25/2) K'² (2πα) n⁻²⁶ N² B(t/8)`,

so the defect is of size `N α²` at mesoscopic scales and linear in `α` at macroscopic scales.
This is the input of the macroscopic end for negative exponents; the order-twelve rule only
gives a constant times `N`.  No configuration and no attaining sequence is asserted here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff ENNReal NNReal
namespace SphericalRiesz
open Boundary

theorem smallLeechPatch_normalized_chart_bounds14 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      (∀ x ∈ UnitCube 24, ContDiffAt ℝ 14 (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x) ∧
      (∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 14 →
        ‖iteratedFDeriv ℝ j (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper24) ∧
      (∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, patchChartLower24*‖x-y‖ ≤
        ‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-equalAreaNormalizedLeechPatch p.g p.v p.c p.ε y‖) ∧
      (∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
        ‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-equalAreaNormalizedLeechPatch p.g p.v p.c p.ε y‖ ≤
          patchChartUpper24*‖x-y‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁', h₁⟩ := equalAreaNormalizedLeechPatch_Cn_uniform 14 1 one_pos
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε
  have hv₁ : ‖p.v‖ ≤ ρ₁ := hv.trans (min_le_left _ _)
  have hv₂ : ‖p.v‖ ≤ ρ₂ := hv.trans (min_le_right _ _)
  have hε₁ : p.ε*equalAreaScaleRadius24 ≤ ρ₁ := hε.trans (min_le_left _ _)
  have hε₂ : p.ε*equalAreaScaleRadius24 ≤ ρ₂ := hε.trans (min_le_right _ _)
  have hb := fun x hx => h₁ p.v hv₁ p.ε p.ε_pos hε₁ p.g p.c p.c_mem x hx
  have hflat : ‖equalAreaRotatedFlatDerivative24 p.g‖ ≤ ‖equalAreaFlatDerivative24‖ :=
    equalAreaRotation24_comp_norm_le p.g equalAreaFlatDerivative24
  have hfd : ∀ x ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper24 := by
    intro x hx
    have h := (hb x hx).2.2.1
    calc ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖
        = ‖(fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative24 p.g)+equalAreaRotatedFlatDerivative24 p.g‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative24 p.g‖+‖equalAreaRotatedFlatDerivative24 p.g‖ :=
          norm_add_le _ _
      _ ≤ 1+‖equalAreaFlatDerivative24‖ := add_le_add h hflat
      _ = patchChartUpper24 := by rw [patchChartUpper24]; ring
  refine ⟨fun x hx => (hb x hx).1.of_le (by simp), ?_, ?_, ?_⟩
  · intro x hx j hj hj6
    rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 1 := by omega
      subst this
      rw [norm_iteratedFDeriv_one]
      exact hfd x hx
    · exact ((hb x hx).2.2.2 j h (by omega)).trans one_le_patchChartUpper24
  · intro x hx y hy
    have h := h₂ p.v hv₂ p.ε p.ε_pos hε₂ p.g p.c p.c_mem x hx y hy
    rw [dist_eq_norm] at h
    simpa only [patchChartLower24] using h
  · intro x hx y hy
    exact unitCube24_convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hb z hz).1.differentiableAt (by simp))) hfd hy hx

/-- Localized fourteenth-order error of an ambient Gaussian bump on one small patch: every
scale, and with a factor `√τ` at macroscopic scales `τ = 2tε² ≤ 1`. -/
theorem smallLeechPatch_bump_quadrature14 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ n : ℕ, 48 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2*patchChartLower24^2/384 ≤ (n:ℝ)^2 →
      ∀ z : AmbientD 24,
      |fourteenCubeQuadrature 24 n (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)-
        cubeIntegral 24 (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)| ≤
        bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24/(n:ℝ)^14*(1+(2*t*p.ε^2)^7)*
          cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) ∧
      (2*t*p.ε^2 ≤ 1 →
      |fourteenCubeQuadrature 24 n (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)-
        cubeIntegral 24 (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)| ≤
        bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24/(n:ℝ)^14*
          Real.sqrt (2*t*p.ε^2)*
          cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2)))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallLeechPatch_normalized_chart_bounds14
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτn z
  obtain ⟨hcd, hder, hlow, hup⟩ := hb p hv hε
  have hτ : 0 < 2*t*p.ε^2 := by have := p.ε_pos; positivity
  have hf1 : (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z) =
      fun x => Real.exp (-((2*t*p.ε^2)*‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-
        p.ε⁻¹ • (z-smallLeechCubeMap24 p p.c)‖^2)) := by
    funext x
    unfold ambientBump25
    rw [smallLeechCubeMap24_sub_norm_sq]
    ring_nf
  have hf2 : (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) =
      fun x => Real.exp (-((2*t*p.ε^2)/8*‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-
        p.ε⁻¹ • (z-smallLeechCubeMap24 p p.c)‖^2)) := by
    funext x
    rw [smallLeechCubeMap24_sub_norm_sq]
    ring_nf
  rw [hf1, hf2]
  exact ⟨normalized_bump_quadrature_error_fourteen24 one_le_patchChartUpper24
      patchChartLower24_pos hcd hder hlow hup hn hτ hτn _,
    fun hτ1 => normalized_bump_quadrature_error_fourteen_small24 one_le_patchChartUpper24
      patchChartLower24_pos hcd hder hlow hup hn hτ hτ1 hτn _⟩

theorem bumpErrorConstFourteen24_patch_nonneg :
    0 ≤ bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24 := by
  rw [bumpErrorConstFourteen24_eq]
  exact mul_nonneg (bumpEnvelopeConst24_nonneg _ _)
    (fourteenthConst_nonneg (by linarith [one_le_patchChartUpper24]))

theorem bumpErrorConstFourteenSmall24_patch_nonneg :
    0 ≤ bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24 :=
  mul_nonneg (bumpEnvelopeConst24_nonneg _ _) (fourteenthSmallConst_nonneg _)

/-- One patch, exact mass: the node sum against `N ∫_patch` of the bump, at every scale and at
macroscopic scales. -/
theorem smallLeechPatch_bump_sphere_errorF24 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 24,
      |(∑ u : Fin 24 → FourteenNodeIndex (a*m),
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α)
            (smallLeechPatchNodesF24 p (a*m) hn u : AmbientD 24) z)-
        (((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)| ≤
      bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7)*
        ((((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α/8) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)) ∧
      (2*Real.pi*((a*m:ℕ):ℝ)^2*α ≤ 1 →
      |(∑ u : Fin 24 → FourteenNodeIndex (a*m),
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α)
            (smallLeechPatchNodesF24 p (a*m) hn u : AmbientD 24) z)-
        (((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)| ≤
      bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13)*
        ((((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α/8) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_quadrature14
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε a d m hd hm hratio hn α hα z
  have hts : 0 < sphereGaussianScale24 ((d*m)^24) α :=
    sphereGaussianScale24_pos (by positivity) hα.1
  have hmesh := sphereGaussian_exact_mass_twelfth_mesh24 a d m hd p.ε hratio hα
  obtain ⟨hquad, hquadS⟩ := hb p hv hε (a*m) hn _ hts hmesh z
  have hτ := sphereGaussian_exact_mass_bump_scale24 a d m hd p.ε α hratio
  set t := sphereGaussianScale24 ((d*m)^24) α with ht
  have hn0 : (0:ℝ) < ((a*m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < a*m)
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdens := leechTwelfth_rational_exact_patch_mass24 a d m hd hm p.ε hratio
  have hsum : (∑ u : Fin 24 → FourteenNodeIndex (a*m),
      ambientBump25 t (smallLeechPatchNodesF24 p (a*m) hn u : AmbientD 24) z) =
      ((a*m:ℕ):ℝ)^24*fourteenCubeQuadrature 24 (a*m)
        (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z) := by
    rw [fourteenCubeQuadrature_as_node_sum, mul_div_cancel₀ _ (pow_pos hn0 24).ne']
    exact Finset.sum_congr rfl fun u _ => by rw [smallLeechPatchNodesF24_coe]
  have hI : ∀ τ : ℝ, (((d*m)^24:ℕ):ℝ)*(∫ y in smallLeechSpherePatch24 p,
      ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24)) =
      ((a*m:ℕ):ℝ)^24*cubeIntegral 24 (fun x => ambientBump25 τ (smallLeechCubeMap24 p x) z) := by
    intro τ
    rw [smallLeechSpherePatch24_setIntegral p (fun y => ambientBump25 τ y z)
      (by unfold ambientBump25; fun_prop), hdens]
    push_cast
    field_simp
  have hsoft : (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) =
      fun x => ambientBump25 (t/8) (smallLeechCubeMap24 p x) z := by
    funext x
    unfold ambientBump25
    rw [show t/4*‖smallLeechCubeMap24 p x-z‖^2 = 2*(t/8)*‖smallLeechCubeMap24 p x-z‖^2 by ring]
  rw [hsoft] at hquad hquadS
  rw [hsum, hI t, hI (t/8), ← mul_sub, abs_mul, abs_of_pos (pow_pos hn0 24)]
  set I8 := cubeIntegral 24 (fun x => ambientBump25 (t/8) (smallLeechCubeMap24 p x) z) with hI8
  constructor
  · calc
      _ ≤ ((a*m:ℕ):ℝ)^24*(bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24/
          ((a*m:ℕ):ℝ)^14*(1+(2*t*p.ε^2)^7)*I8) :=
        mul_le_mul_of_nonneg_left hquad (by positivity)
      _ = _ := by
        rw [hτ]
        field_simp
  · intro hsmall
    have hτ1 : 2*t*p.ε^2 ≤ 1 := by rw [hτ]; exact hsmall
    have hsq : Real.sqrt (2*t*p.ε^2) = ((a*m:ℕ):ℝ)*Real.sqrt (2*Real.pi*α) := by
      rw [hτ, show 2*Real.pi*((a*m:ℕ):ℝ)^2*α = ((a*m:ℕ):ℝ)^2*(2*Real.pi*α) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0.le]
    calc
      _ ≤ ((a*m:ℕ):ℝ)^24*(bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24/
          ((a*m:ℕ):ℝ)^14*Real.sqrt (2*t*p.ε^2)*I8) :=
        mul_le_mul_of_nonneg_left (hquadS hτ1) (by positivity)
      _ = _ := by
        rw [hsq]
        field_simp

/-- A finite disjoint family: a common relative patch error passes to the union and is bounded
by the softened bump field of the whole sphere. -/
theorem leechPatchFamily_bump_of_patchF {K : ℕ} (P : Fin K → SmallLeechCubePatch24)
    (hdisj : Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
      (smallLeechSpherePatch24 (P j))))
    (n : ℕ) (hn : 48 ≤ n) (N : ℝ) (hN : 0 ≤ N) {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (z : AmbientD 24)
    (hpatch : ∀ i, |(∑ u : Fin 24 → FourteenNodeIndex n,
        ambientBump25 t (smallLeechPatchNodesF24 (P i) n hn u : AmbientD 24) z)-
        N*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24)| ≤
      C*(N*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24))) :
    |(∑ i, ∑ u : Fin 24 → FourteenNodeIndex n,
        ambientBump25 t (smallLeechPatchNodesF24 (P i) n hn u : AmbientD 24) z)-
      N*∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
        ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24)| ≤
    C*(N*bumpField25 (t/8) ambientSphereProbability24 z) := by
  have hsplit : ∀ τ : ℝ, 0 ≤ τ → (∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
      ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24)) =
      ∑ i, ∫ y in smallLeechSpherePatch24 (P i),
        ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24) := by
    intro τ hτ
    rw [integral_iUnion (fun i => smallLeechSpherePatch24_measurable (P i))
      (fun i j hij => hdisj hij) (ambientBump25_sphere_integrable hτ z).integrableOn,
      tsum_fintype]
  have hle : (∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
      ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) ≤
      bumpField25 (t/8) ambientSphereProbability24 z := by
    rw [bumpField25_sphere_eq]
    exact setIntegral_le_integral (ambientBump25_sphere_integrable (by positivity) z)
      (Filter.Eventually.of_forall fun y => ambientBump25_nonneg _ _ _)
  rw [hsplit t ht.le, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ u : Fin 24 → FourteenNodeIndex n,
          ambientBump25 t (smallLeechPatchNodesF24 (P i) n hn u : AmbientD 24) z)-
        N*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*(N*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) :=
      Finset.sum_le_sum fun i _ => hpatch i
    _ = C*(N*∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
          ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) := by
      rw [hsplit (t/8) (by positivity), Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul_of_nonneg_left hle hN

/-- A relative bump error `C` of the foreground gives the mixed defect `8^(25/2) C² N² B(t/8)`. -/
theorem leechPatchFamily_mixed_defect_of_bumpF {K : ℕ} (P : Fin K → SmallLeechCubePatch24)
    (n : ℕ) (hn : 48 ≤ n) (N : ℕ) {t C : ℝ} (ht : 0 < t)
    (hb : ∀ z : AmbientD 24, |(∑ i, ∑ u : Fin 24 → FourteenNodeIndex n,
        ambientBump25 t (smallLeechPatchNodesF24 (P i) n hn u : AmbientD 24) z)-
      (N:ℝ)*∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
        ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24)| ≤
      C*((N:ℝ)*bumpField25 (t/8) ambientSphereProbability24 z)) :
    gaussianMeasureDefect t (N:ℝ)
      (mixedForegroundMeasure24 (leechFamilyNodesF24 P n hn) N (leechFamilyUnion24 P)ᶜ)
      ambientSphereProbability24 ≤
    (8:ℝ)^((25:ℝ)/2)*C^2*(N:ℝ)^2*sphereGaussianBackground24 (t/8) := by
  have ht8 : 0 < t/8 := by positivity
  let W : AmbientD 24 → ℝ := fun z => C*((N:ℝ)*bumpField25 (t/8) ambientSphereProbability24 z)
  have hWsq : (fun z => W z^2) = fun z => (C*(N:ℝ))^2*
      (bumpField25 (t/8) ambientSphereProbability24 z*
        bumpField25 (t/8) ambientSphereProbability24 z) := by
    funext z
    simp only [W]
    ring
  have hWi : Integrable (fun z => W z^2) := by
    rw [hWsq]
    exact (bumpField25_mul_integrable ht8 ambientSphereProbability24
      ambientSphereProbability24).const_mul _
  have hle : ∀ z, |bumpField25 t (mixedForegroundMeasure24 (leechFamilyNodesF24 P n hn)
      N (leechFamilyUnion24 P)ᶜ) z-(N:ℝ)*bumpField25 t ambientSphereProbability24 z| ≤ W z := by
    intro z
    rw [mixedForeground_bumpError_eq _ _ _ (leechFamilyUnion24_measurable P) ht.le,
      Fintype.sum_prod_type]
    exact hb z
  have hmain := gaussianMeasureDefect_le_of_bump25 ht (N:ℝ) _ ambientSphereProbability24 hWi hle
  have hint : (∫ z, W z^2) = (C*(N:ℝ))^2*((Real.pi/(4*(t/8)))^((25:ℝ)/2)*
      sphereGaussianBackground24 (t/8)) := by
    rw [hWsq, integral_const_mul, ← bumpField25_sphere_sq_integral ht8]
    simp_rw [sq]
  have hconst : (4*t/Real.pi)^((25:ℝ)/2)*(Real.pi/(4*(t/8)))^((25:ℝ)/2) = (8:ℝ)^((25:ℝ)/2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    _ ≤ (4*t/Real.pi)^((25:ℝ)/2)*∫ z, W z^2 := hmain
    _ = ((4*t/Real.pi)^((25:ℝ)/2)*(Real.pi/(4*(t/8)))^((25:ℝ)/2))*(C*(N:ℝ))^2*
        sphereGaussianBackground24 (t/8) := by rw [hint]; ring
    _ = _ := by rw [hconst]; ring

/-- Neutralized Gaussian defect of the fourteenth-order foreground family with the smooth
residual background: every `α ∈ (0,4]`, and linear in `α` at macroscopic scales. -/
theorem leechPatchFamily_mixed_defect_leF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodesF24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (8:ℝ)^((25:ℝ)/2)*(bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7))^2*(((d*m)^24:ℕ):ℝ)^2*
        sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8) ∧
      (2*Real.pi*((a*m:ℕ):ℝ)^2*α ≤ 1 →
      gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodesF24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (8:ℝ)^((25:ℝ)/2)*(bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13))^2*(((d*m)^24:ℕ):ℝ)^2*
        sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_sphere_errorF24
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  have hts : 0 < sphereGaussianScale24 ((d*m)^24) α :=
    sphereGaussianScale24_pos (by positivity) hα.1
  have hN0 : (0:ℝ) ≤ (((d*m)^24:ℕ):ℝ) := by positivity
  constructor
  · have hC : 0 ≤ bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7) := by
      have := hα.1
      exact mul_nonneg bumpErrorConstFourteen24_patch_nonneg (by positivity)
    exact leechPatchFamily_mixed_defect_of_bumpF P (a*m) hn ((d*m)^24) hts fun z =>
      leechPatchFamily_bump_of_patchF P hdisj (a*m) hn _ hN0 hts hC z fun i =>
        (hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z).1
  · intro hsmall
    have hC : 0 ≤ bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13) :=
      mul_nonneg bumpErrorConstFourteenSmall24_patch_nonneg (by positivity)
    exact leechPatchFamily_mixed_defect_of_bumpF P (a*m) hn ((d*m)^24) hts fun z =>
      leechPatchFamily_bump_of_patchF P hdisj (a*m) hn _ hN0 hts hC z fun i =>
        (hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z).2 hsmall

end SphericalRiesz
end
end
