import Riesz.GaussianOneDimBounds
import Riesz.GaussianCompositionFourteenth
import Riesz.BoundaryFourteen
import Riesz.HexConstruction2
import Riesz.EqualAreaHex2
import Riesz.SphereRieszNeg2
import Riesz.NegMassSplit8
import Riesz.SphereRieszTransfer8
import Riesz.SphereStratification2
import Riesz.HexGaussianBridge2

/-! Sharp negative Riesz asymptotics on the actual two-dimensional sphere.

Fourteenth-order triangular foreground nodes, exact-mass geometric residual cells, joint selection of added nodes at cutoff 1/L, and a foreground tolerance L^3 supply configurations at every sufficiently large size. Both asymptotic bounds are unconditional: triangular contact is provided by HexGaussianBridge2. No partition or contact certificate is assumed in the public final statements. -/

section

/-! # The fourteenth-order foreground of the triangular lattice on `S²` (stage S2-5)

Dimension-2 port of `LeechFourteenth24`: the order-fourteen forms of the order-twelve foreground
parts, built on the equal-weight rule of `Riesz.BoundaryFourteen`.  The rule does not depend on
the dimension: `n ≥ 48` nodes per coordinate, a strip of `24` corrected nodes at each end
(`FourteenNodeIndex n = Fin 24 ⊕ (Fin (n-48) ⊕ Fin 24)`), order `14`, constant `10^24`.  What
changes is the chart cube `[0,1]²` (a patch has `n²` nodes), the ambient space `ℝ³` and the
lattice, which is the triangular lattice of covolume one.

* one-dimensional Gaussian sums of the rule and the product envelope,
* the error of a normalized Gaussian bump on a chart cube, `K (1+τ⁷)/n¹⁴` for every `τ` and
  `K_s √τ/n¹⁴` for `τ ≤ 1` (the second form is linear in the Gaussian parameter after squaring),
* the fourteenth-order nodes of a small patch of the triangular lattice and of a patch family:
  injectivity, cardinality `n²`, short-range and density budgets, and the Gaussian window of a
  family (`n²-(n-48)²` nodes of a patch lie outside the uncorrected middle block),
* the bump error on the sphere and the mixed Gaussian defect of a patch family, at most
  `8^(3/2) N² B(t/8) (K (1/n¹⁴+(2πα)⁷))²` in general and `8^(3/2) N² B(t/8) (K_s √(2πα)/n¹³)²` at
  macroscopic scales `2π n² α ≤ 1`; the exponent `3/2 = (d+1)/2` comes from the bump-square
  identity in `ℝ³`.

On `S²` the background satisfies `N B(t/8) ≤ 8 α⁻¹` at the density scale `t = α N/4`, so at
mesoscopic scales `2π n² α ≥ 1` the defect is `O(N α¹³)` in the scaled Gaussian parameter `α`,
and at macroscopic scales it is linear in `α`.  Negative exponents `-2 < s < 0` only need the
defect to be integrable against `α^(s/2-1)` at zero after division by `N`; a rule of lower
order would do on `S²`, the order fourteen is kept from dimension 24, where it is needed. -/

section

/-! Gaussian averages on the actual fourteenth-order rule. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem gauss1_fourteenQuadrature2_le_one {m : ℕ} (hm : 48 ≤ m) {β : ℝ} (hβ : 0 ≤ β) (b : ℝ) :
    fourteenQuadrature m (gauss1 β b) ≤ 1 := by
  have h := fourteenQuadrature_mono hm (f := gauss1 β b) (g := fun _ => (1:ℝ))
    (fun t _ => gauss1_le_one hβ b t)
  rwa [fourteenQuadrature_const hm] at h

/-- Fourteenth derivative of the one-dimensional profile. -/
theorem gauss1_fourteenth2_le {β : ℝ} (hβ : 0 ≤ β) (b t : ℝ) :
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
theorem gauss1_fourteenQuadrature2_le {m : ℕ} (hm : 48 ≤ m) {β : ℝ} (hβ : 0 < β)
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
    exact gauss1_fourteenth2_le hβ.le b t
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

/-! Localized fourteenth-order Gaussian bump error on the chart cube `[0,1]²` with values in the
ambient space `ℝ³`.

The nearest-point/product-envelope argument of the order-twelve proof is stated once for an
arbitrary bound `Kφ e^(-τ‖Ψ-w‖²/2)` of the fourteenth derivative of the bump.  Two instances:
`Kφ = fourteenthConst2 L (1+τ⁷)` for every `τ > 0`, and `Kφ = fourteenthSmallConst2 L √τ` for
`τ ≤ 1`.  The second one makes the patch Gaussian defect linear in `τ` at macroscopic scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem fourteenth_coordinate_within_abs_le_of_contDiffAt2 (d : ℕ)
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
def fourteenthConst2 (L : ℝ) : ℝ := 87178291200*4782969*(10:ℝ)^38*L^14

/-- Constant of the one-dimensional rule average. -/
def gaussRule2Const14 : ℝ := Real.sqrt Real.pi+(2*(10:ℝ)^24)*(87178291200*4782969*(10:ℝ)^38)*Real.sqrt (2*Real.pi)

theorem gaussRule2Const14_nonneg : 0 ≤ gaussRule2Const14 := by
  unfold gaussRule2Const14
  positivity

theorem sqrt_pi_le_gaussRule2Const14 : Real.sqrt Real.pi ≤ gaussRule2Const14 := by
  unfold gaussRule2Const14
  have : 0 ≤ (2*(10:ℝ)^24)*(87178291200*4782969*(10:ℝ)^38:ℝ)*Real.sqrt (2*Real.pi) := by positivity
  linarith

/-- The constant of the localized fourteenth-order bump error. -/
def bumpErrorConstFourteen2 (L C₀ : ℝ) : ℝ :=
  (2*(10:ℝ)^24)*fourteenthConst2 L*(Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2

/-- The envelope factor of the localized bump error (independent of the derivative bound). -/
def bumpEnvelopeConst2 (L C₀ : ℝ) : ℝ :=
  (2*(10:ℝ)^24)*(Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2

theorem bumpEnvelopeConst2_nonneg (L C₀ : ℝ) : 0 ≤ bumpEnvelopeConst2 L C₀ := by
  unfold bumpEnvelopeConst2
  positivity

/-- Localized fourteenth-order bump error for an arbitrary Gaussian bound `Kφ` of the
fourteenth derivative of the bump. -/
theorem normalized_bump_quadrature_error_fourteen2_of_derivative
    {Ψ : (Fin 2 → ℝ) → AmbientD 2} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 Ψ x)
    (hlow : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 2)
    {Kφ : ℝ} (hKφ : 0 ≤ Kφ)
    (hD : ∀ y ∈ UnitCube 2,
      ‖iteratedFDeriv ℝ 14 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2))) y‖ ≤
        Kφ*Real.exp (-(τ*‖Ψ y-w‖^2/2))) :
    |fourteenCubeQuadrature 2 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 2 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpEnvelopeConst2 L C₀*Kφ/(n:ℝ)^14*
        cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hL0 : 0 < L := by linarith
  -- the nearest point of the cube
  have hcont : ContinuousOn Ψ (UnitCube 2) := fun x hx => (hcd x hx).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hmin⟩ := (unitCube_isCompact 2).exists_isMinOn
    ⟨fun _ => 0, fun _ => by norm_num⟩ ((hcont.sub continuousOn_const).norm)
  set ρ := ‖Ψ x0-w‖ with hρdef
  have hρmin : ∀ y ∈ UnitCube 2, ρ ≤ ‖Ψ y-w‖ := fun y hy => hmin hy
  set β := τ*C₀^2/384 with hβdef
  set γ := τ*L^2/4 with hγdef
  have hβ : 0 < β := by positivity
  have hγ : 0 < γ := by positivity
  -- the upper envelope
  have henv : ∀ y ∈ UnitCube 2, Real.exp (-(τ*‖Ψ y-w‖^2/2)) ≤
      Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j) := by
    intro y hy
    rw [prod_gauss1_eq2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : ‖Ψ y-Ψ x0‖ ≤ 2*‖Ψ y-w‖ := by
      calc ‖Ψ y-Ψ x0‖ = ‖(Ψ y-w)-(Ψ x0-w)‖ := by congr 1; abel
        _ ≤ ‖Ψ y-w‖+‖Ψ x0-w‖ := norm_sub_le _ _
        _ ≤ 2*‖Ψ y-w‖ := by linarith [hρmin y hy]
    have h2 := hlow y hy x0 hx0
    have h3 := sum_sq_le_twentyFour_pi_norm_sqS2 (y-x0)
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
  have hlowenv : ∀ y ∈ UnitCube 2, Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (y j) ≤
      Real.exp (-(τ/8*‖Ψ y-w‖^2)) := by
    intro y hy
    rw [prod_gauss1_eq2, ← Real.exp_add]
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
    have h3 := pi_norm_sq_le_sum2 (y-x0)
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
  set f : (Fin 2 → ℝ) → ℝ := fun x => Real.exp (-(τ*‖Ψ x-w‖^2)) with hfdef
  have hfcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 f x := by
    intro x hx
    have h1 : ContDiffAt ℝ 14 (fun x => Ψ x-w) x := (hcd x hx).sub contDiffAt_const
    have h2 : ContDiffAt ℝ 14 (fun x => ‖Ψ x-w‖^2) x := h1.norm_sq ℝ
    exact Real.contDiff_exp.contDiffAt.comp x ((h2.const_smul τ).neg)
  have hM : ∀ i v, v ∈ UnitCube 2 → ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin 14 (fun u => f (Function.update v i u)) (Icc (0 : ℝ) 1) t| ≤
        A*∏ j, gauss1 β (x0 j) (Function.update v i t j) := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    refine (fourteenth_coordinate_within_abs_le_of_contDiffAt2 2 i v t ht (hfcd _ hy)).trans ?_
    set y := Function.update v i t with hydef
    calc ‖iteratedFDeriv ℝ 14 f y‖ ≤ Kφ*Real.exp (-(τ*‖Ψ y-w‖^2/2)) := hD y hy
      _ ≤ Kφ*(Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 β (x0 j) (y j)) :=
          mul_le_mul_of_nonneg_left (henv y hy) hKφ
      _ = A*∏ j, gauss1 β (x0 j) (y j) := by rw [hAdef]; ring
  -- one-dimensional bounds
  set B := min 1 (gaussRule2Const14/Real.sqrt β) with hBdef
  have hQB : ∀ j, fourteenQuadrature n (gauss1 β (x0 j)) ≤ B := by
    intro j
    exact le_min (gauss1_fourteenQuadrature2_le_one hn hβ.le _)
      (gauss1_fourteenQuadrature2_le hn hβ hβn _)
  have hIB : ∀ j, (∫ t in (0:ℝ)..1, gauss1 β (x0 j) t) ≤ B := by
    intro j
    refine le_min (gauss1_integral_le_one hβ.le _) ((gauss1_integral_le_sqrt hβ _).trans ?_)
    rw [Real.sqrt_div' _ hβ.le]
    exact div_le_div_of_nonneg_right sqrt_pi_le_gaussRule2Const14 (Real.sqrt_nonneg _)
  have herr := fourteenCubeQuadrature_fourteenth_order_envelope_on 2 hn
    (fun x hx => (hfcd x hx).continuousAt.continuousWithinAt)
    (fun i v hv => by
      intro t ht
      have hy := update_mem_unitCube hv i ht
      have hu : ContDiffAt ℝ 14 (fun u : ℝ => Function.update v i u) t := by
        rw [show (fun u : ℝ => Function.update v i u) =
          (fun u => ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i u+Function.update v i 0)
          from funext (coordinate_update_as_line 2 i v)]
        fun_prop
      exact ((hfcd _ hy).comp t hu).contDiffWithinAt)
    (fun j => gauss1 β (x0 j)) (fun j => continuous_gauss1 β _) (fun j t => gauss1_nonneg β _ t)
    (fun _ => B) hQB hIB hA hM
  -- the lower bound of the right side
  set J := Real.exp (-1)*min (1/2) (1/Real.sqrt γ) with hJdef
  have hJ0 : 0 ≤ J := by rw [hJdef]; positivity
  have hJI : ∀ j, J ≤ ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t := fun j =>
    gauss1_integral_ge hγ ⟨(hx0 j).1, (hx0 j).2⟩
  have hratio : B ≤ (Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))*J := by
    apply gauss1_bound_ratio hβ hγ gaussRule2Const14_nonneg (by positivity)
    have hγβ : γ = (96*L^2/C₀^2)*β := by
      rw [hγdef, hβdef]; field_simp; norm_num
    rw [hγβ, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
      Real.sqrt_mul (by norm_num), Real.sqrt_sq hL0.le, Real.sqrt_sq hC₀.le]
  have hrhs : Real.exp (-(τ*ρ^2/4))*J^2 ≤
      cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
    have hprod : J^2 ≤ cubeIntegral 2 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) := by
      rw [cubeIntegral_prod]
      calc J^2 = ∏ _j : Fin 2, J := by simp
        _ ≤ ∏ j, ∫ t in (0:ℝ)..1, gauss1 γ (x0 j) t :=
            Finset.prod_le_prod₀ (fun _ _ => hJ0) (fun j _ => hJI j)
    calc Real.exp (-(τ*ρ^2/4))*J^2
        ≤ Real.exp (-(τ*ρ^2/4))*cubeIntegral 2 (fun x => ∏ j, gauss1 γ (x0 j) (x j)) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = cubeIntegral 2 (fun x => Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) :=
          (cubeIntegral_mul_const 2 _ _).symm
      _ ≤ cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
          have hc1 : ContinuousOn (fun x : Fin 2 → ℝ =>
              Real.exp (-(τ*ρ^2/4))*∏ j, gauss1 γ (x0 j) (x j)) (UnitCube 2) :=
            (continuous_const.mul (continuous_finsetProd _ fun j _ =>
              (continuous_gauss1 γ _).comp (continuous_apply j))).continuousOn
          have hc2 : ContinuousOn (fun x : Fin 2 → ℝ => Real.exp (-(τ/8*‖Ψ x-w‖^2)))
              (UnitCube 2) :=
            Real.continuous_exp.comp_continuousOn
              (((hcont.sub continuousOn_const).norm.pow 2).const_smul (τ/8)).neg
          have h := cubeIntegral_abs_le_of_le 2 hc1 hc2 (fun x hx => by
            rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
              (Finset.prod_nonneg fun j _ => gauss1_nonneg γ _ _))]
            exact hlowenv x hx)
          exact (le_abs_self _).trans h
  -- assemble
  have hB0 : 0 ≤ B := le_min zero_le_one (div_nonneg gaussRule2Const14_nonneg (Real.sqrt_nonneg _))
  have hB8 : B^2 ≤ (Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2*J^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hratio 2
  have hprodB : ∏ _j : Fin 2, B = B^2 := by simp
  rw [hprodB] at herr
  have hn6 : (0:ℝ) < (n:ℝ)^14 := by positivity
  calc |fourteenCubeQuadrature 2 n f-cubeIntegral 2 f|
      ≤ 10^24/(n:ℝ)^14*((2:ℕ)*(A*B^2)) := herr
    _ = (2*(10:ℝ)^24)/(n:ℝ)^14*Kφ*(Real.exp (-(τ*ρ^2/4))*B^2) := by
        rw [hAdef]; push_cast; ring
    _ ≤ (2*(10:ℝ)^24)/(n:ℝ)^14*Kφ*(Real.exp (-(τ*ρ^2/4))*
          ((Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2*J^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hB8 (Real.exp_pos _).le
    _ = (2*(10:ℝ)^24)/(n:ℝ)^14*Kφ*
          (Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2*
            (Real.exp (-(τ*ρ^2/4))*J^2) := by ring
    _ ≤ (2*(10:ℝ)^24)/(n:ℝ)^14*Kφ*
          (Real.exp 1*max 2 (gaussRule2Const14*(Real.sqrt 96*L/C₀)))^2*
            cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) :=
        mul_le_mul_of_nonneg_left hrhs (by positivity)
    _ = bumpEnvelopeConst2 L C₀*Kφ/(n:ℝ)^14*
          cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
        rw [bumpEnvelopeConst2]; ring

/-- Constant of the small-`τ` fourteenth derivative bound. -/
def fourteenthSmallConst2 (L : ℝ) : ℝ := 87178291200*10569662464*(16384*L^2)^14

theorem fourteenthConst2_nonneg {L : ℝ} (_hL : 0 ≤ L) : 0 ≤ fourteenthConst2 L := by
  unfold fourteenthConst2
  positivity

theorem fourteenthSmallConst2_nonneg (L : ℝ) : 0 ≤ fourteenthSmallConst2 L := by
  unfold fourteenthSmallConst2
  positivity

/-- The constant of the small-`τ` localized fourteenth-order bump error. -/
def bumpErrorConstFourteenSmall2 (L C₀ : ℝ) : ℝ :=
  bumpEnvelopeConst2 L C₀*fourteenthSmallConst2 L

theorem bumpErrorConstFourteen2_eq (L C₀ : ℝ) :
    bumpErrorConstFourteen2 L C₀ = bumpEnvelopeConst2 L C₀*fourteenthConst2 L := by
  unfold bumpErrorConstFourteen2 bumpEnvelopeConst2
  ring

private theorem bump_shift_derivative2 {Ψ : (Fin 2 → ℝ) → AmbientD 2} {L : ℝ}
    (hcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (w : AmbientD 2) {y : Fin 2 → ℝ} (hy : y ∈ UnitCube 2) :
    ContDiffAt ℝ 14 (fun x => Ψ x-w) y ∧
      ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j (fun x => Ψ x-w) y‖ ≤ L := by
  refine ⟨(hcd y hy).sub contDiffAt_const, ?_⟩
  intro j hj hj6
  have hjc : ContDiffAt ℝ j Ψ y := (hcd y hy).of_le (by exact_mod_cast hj6)
  rw [show (fun x => Ψ x-w) = Ψ-(fun _ => w) from rfl,
    iteratedFDeriv_sub_apply hjc contDiffAt_const, iteratedFDeriv_const_of_ne (by omega) w]
  simpa only [Pi.zero_apply, sub_zero] using hder y hy j hj hj6

/-- Localized fourteenth-order bump error, every `τ > 0`. -/
theorem normalized_bump_quadrature_error_fourteen2
    {Ψ : (Fin 2 → ℝ) → AmbientD 2} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 2) :
    |fourteenCubeQuadrature 2 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 2 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConstFourteen2 L C₀/(n:ℝ)^14*(1+τ^7)*
        cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hK : 0 ≤ fourteenthConst2 L*(1+τ^7) :=
    mul_nonneg (fourteenthConst2_nonneg (by linarith)) (by positivity)
  have h := normalized_bump_quadrature_error_fourteen2_of_derivative hL hC₀ hcd hlow hup hn hτ
    hβn w hK (fun y hy => by
      obtain ⟨hFcd, hFL⟩ := bump_shift_derivative2 hcd hder w hy
      have h := norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le hFcd hL hFL hτ.le
      simpa only [fourteenthConst2] using h)
  rw [bumpErrorConstFourteen2_eq]
  calc _ ≤ bumpEnvelopeConst2 L C₀*(fourteenthConst2 L*(1+τ^7))/(n:ℝ)^14*
          cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := h
    _ = _ := by ring

/-- Localized fourteenth-order bump error with a factor `√τ`, for `τ ≤ 1`. -/
theorem normalized_bump_quadrature_error_fourteen_small2
    {Ψ : (Fin 2 → ℝ) → AmbientD 2} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 Ψ x)
    (hder : ∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 48 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 2) :
    |fourteenCubeQuadrature 2 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 2 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConstFourteenSmall2 L C₀/(n:ℝ)^14*Real.sqrt τ*
        cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
  have hK : 0 ≤ fourteenthSmallConst2 L*Real.sqrt τ :=
    mul_nonneg (fourteenthSmallConst2_nonneg L) (Real.sqrt_nonneg τ)
  have h := normalized_bump_quadrature_error_fourteen2_of_derivative hL hC₀ hcd hlow hup hn hτ
    hβn w hK (fun y hy => by
      obtain ⟨hFcd, hFL⟩ := bump_shift_derivative2 hcd hder w hy
      have h := norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le_sqrt hFcd hL hFL hτ.le hτ1
      simpa only [fourteenthSmallConst2] using h)
  unfold bumpErrorConstFourteenSmall2
  calc _ ≤ bumpEnvelopeConst2 L C₀*(fourteenthSmallConst2 L*Real.sqrt τ)/(n:ℝ)^14*
          cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := h
    _ = _ := by ring

end SphericalRiesz
end
end

section

/-! Fourteenth-order nodes of small patches of the triangular lattice on `S²`: labels, theta rows,
short-range budgets, the node families of a patch family and the sharp Gaussian window of the
foreground.  Port of the order-twelve declarations to the order-fourteen rule (strip `24`, middle
block from `48` nodes on); a patch has `n²` nodes. -/
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
theorem fourteenRule2_label_sub_le {n : ℕ} (hn : 48 ≤ n) (u w : FourteenNodeIndex n) :
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

def hexFourteenthLabel2 (n : ℕ) (hn : 48 ≤ n) :
    (Fin 2 → FourteenNodeIndex n) ↪ hexLattice where
  toFun u := ⟨hexIntegerPoint (fun i => (fourteenMidpointLabel n (u i):ℤ)),
    (hexLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := hexMap_injective (congrArg (fun z : hexLattice => WithLp.ofLp (z : HexAmbient)) h)
    funext i
    apply fourteenMidpointLabel_injective hn
    have hi : (fourteenMidpointLabel n (u i):ℝ) = (fourteenMidpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem hexFourteenthLabel2_norm_le {n : ℕ} (hn : 48 ≤ n)
    (u w : Fin 2 → FourteenNodeIndex n) :
    ‖((hexFourteenthLabel2 n hn w-hexFourteenthLabel2 n hn u : hexLattice) : HexAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)*‖fourteenCubeNode 2 n u-fourteenCubeNode 2 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 2 → ℝ := fun i => (fourteenMidpointLabel n (u i):ℝ)-(fourteenMidpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖fourteenCubeNode 2 n u-fourteenCubeNode 2 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := fourteenRule2_label_sub_le hn (u i) (w i)
    have he : |fourteenUnscaledRuleNode n (u i)-fourteenUnscaledRuleNode n (w i)| =
        (n:ℝ)*|fourteenCubeNode 2 n u i-fourteenCubeNode 2 n w i| := by
      simp only [fourteenCubeNode,fourteenRuleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|fourteenCubeNode 2 n u i-fourteenCubeNode 2 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖fourteenCubeNode 2 n u-fourteenCubeNode 2 n w‖ := by
        have hi := norm_le_pi_norm (fourteenCubeNode 2 n u-fourteenCubeNode 2 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((hexFourteenthLabel2 n hn w-hexFourteenthLabel2 n hn u : hexLattice) : HexAmbient)‖ =
      ‖equalAreaFlatDerivative2 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative2,
        equalAreaFlatDerivative2_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖hexIntegerPoint (fun i => (fourteenMidpointLabel n (w i):ℤ))-
      hexIntegerPoint (fun i => (fourteenMidpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (hexMap z)‖
    rw [norm_sub_rev,hexIntegerPoint,hexIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative2‖*‖z‖ := equalAreaFlatDerivative2.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative2‖*((2*(n:ℝ))*‖fourteenCubeNode 2 n u-fourteenCubeNode 2 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaHexFourteenth2_gaussian_row {n : ℕ} (hn : 48 ≤ n)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y))
    (u : Fin 2 → FourteenNodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨fourteenCubeNode 2 n u,fun i => ⟨(fourteenCubeNode_mem_open 2 n hn u i).1.le,(fourteenCubeNode_mem_open 2 n hn u i).2.le⟩⟩)
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨fourteenCubeNode 2 n w,fun i => ⟨(fourteenCubeNode_mem_open 2 n hn w i).1.le,(fourteenCubeNode_mem_open 2 n hn w i).2.le⟩⟩)) ≤
    hexGaussianThetaReal2 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative2_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply hexPatchGaussian_row_le (hexFourteenthLabel2 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaHexPatch g v c ε (fourteenCubeNode 2 n i))
    (equalAreaHexPatch g v c ε (fourteenCubeNode 2 n j))
  rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
  have hi : fourteenCubeNode 2 n i ∈ UnitCube 2 := fun k => ⟨(fourteenCubeNode_mem_open 2 n hn i k).1.le,(fourteenCubeNode_mem_open 2 n hn i k).2.le⟩
  have hj : fourteenCubeNode 2 n j ∈ UnitCube 2 := fun k => ⟨(fourteenCubeNode_mem_open 2 n hn j k).1.le,(fourteenCubeNode_mem_open 2 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := hexFourteenthLabel2_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
  have hdiv : ‖((hexFourteenthLabel2 n hn j-hexFourteenthLabel2 n hn i : hexLattice) :
      HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖fourteenCubeNode 2 n i-fourteenCubeNode 2 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((hexFourteenthLabel2 n hn j-hexFourteenthLabel2 n hn i : hexLattice) : HexAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by ring
    _ ≤ ε*L*‖fourteenCubeNode 2 n i-fourteenCubeNode 2 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith

/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def hexFourteenthSphereNodes2 (n : ℕ) (hn : 48 ≤ n)
    (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    (Fin 2 → FourteenNodeIndex n) → SphereD 2 := fun u =>
  equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
    ⟨fourteenCubeNode 2 n u,fun i =>
      ⟨(fourteenCubeNode_mem_open 2 n hn u i).1.le,(fourteenCubeNode_mem_open 2 n hn u i).2.le⟩⟩

/-- The actual fourteenth-order sphere nodes are all distinct. -/
theorem hexFourteenthSphereNodes2_injective (n : ℕ) (hn : 48 ≤ n)
    (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    Function.Injective (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall) := by
  intro u w h
  have hcube := (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall).injective h
  exact fourteenCubeNode_injective 2 n hn (congrArg Subtype.val hcube)

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaHexFourteenth2_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (n : ℕ) (hn : 48 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel2 t p
        (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^2*hexGaussianTailBudget2 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative2_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((hexFourteenthLabel2 n hn j-hexFourteenthLabel2 n hn i :
      hexLattice) : HexAmbient)‖ ≤
      dist (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall i)
        (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaHexPatch g v c ε (fourteenCubeNode 2 n i))
      (equalAreaHexPatch g v c ε (fourteenCubeNode 2 n j))
    rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
    have hi : fourteenCubeNode 2 n i ∈ UnitCube 2 := fun k =>
      ⟨(fourteenCubeNode_mem_open 2 n hn i k).1.le,(fourteenCubeNode_mem_open 2 n hn i k).2.le⟩
    have hj : fourteenCubeNode 2 n j ∈ UnitCube 2 := fun k =>
      ⟨(fourteenCubeNode_mem_open 2 n hn j k).1.le,(fourteenCubeNode_mem_open 2 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := hexFourteenthLabel2_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
    have hdiv : ‖((hexFourteenthLabel2 n hn j-hexFourteenthLabel2 n hn i : hexLattice) :
        HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖fourteenCubeNode 2 n i-fourteenCubeNode 2 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖hexInverseMap‖)))*
          (‖((hexFourteenthLabel2 n hn j-hexFourteenthLabel2 n hn i : hexLattice) :
            HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖hexInverseMap‖)))*‖fourteenCubeNode 2 n i-fourteenCubeNode 2 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := hexPatch_shortRange_budget_le (hexFourteenthLabel2 n hn)
    (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 2 → FourteenNodeIndex n) = n^2 := by
    simp [fourteenNodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- At the actual `n²` sphere density the corrected foreground has one explicit budget for
all n>=48.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaHexFourteenth2_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 48 ≤ n),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 (n^2)) p
        (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexFourteenthSphereNodes2 n hn g v c hc ε hε hsmall w))/(n:ℝ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexFourteenth2_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall p hp n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative2_norm_pos
  have hcN := sphereGaussianDensityFactor2_pos (N := n^2) (by positivity)
  have hscale : hexCorrectedDensityBudgetScale2 ε ≤
      sphereGaussianDensityFactor2 (n^2)*
        (ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor2_pow_twentyFour]
    unfold hexCorrectedDensityBudgetScale2
    apply le_of_eq
    field_simp
  have hb := hcost g v c hv hc ε hε hs hsmall n hn
    (sphereGaussianDensityFactor2 (n^2)) (hexCorrectedDensityBudgetScale2 ε) p
    hcN (hexCorrectedDensityBudgetScale2_pos hε) hp hscale
  apply (div_le_iff₀ (pow_pos hnR 2)).mpr
  simpa only [mul_comm] using hb

/-- Rational allocation also removes the shrinking chart size from the budget: with n=a*m,
`N = (d*m)²` and `ε = r*a/d`, the positive theta scale depends only on r.
Thus the computed foreground bound is common across a,d,m, rather than merely a fixed chart. -/
theorem equalAreaHexFourteenth2_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 48 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p
        (hexFourteenthSphereNodes2 (a*m) hn g v c hc ε hε hsmall u)
        (hexFourteenthSphereNodes2 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexFourteenth2_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall r p hr hp a d m ha hd hm hratio hn
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hD := equalAreaFlatDerivative2_norm_pos
  have he : ε = r*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR.ne').mpr hratio
  have hcN := sphereGaussianDensityFactor2_pos (N := (d*m)^2) (by positivity)
  have hscale : hexCorrectedDensityBudgetScale2 r ≤
      sphereGaussianDensityFactor2 ((d*m)^2)*
        (ε/(4*(a*m:ℕ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor2_pow_twentyFour, he]
    unfold hexCorrectedDensityBudgetScale2
    push_cast
    apply le_of_eq
    field_simp
  have hb := hcost g v c hv hc ε hε hs hsmall (a*m) hn
    (sphereGaussianDensityFactor2 ((d*m)^2)) (hexCorrectedDensityBudgetScale2 r) p
    hcN (hexCorrectedDensityBudgetScale2_pos hr) hp hscale
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (a*m:ℕ)^2)).mpr
  simpa only [Nat.cast_pow, mul_comm] using hb

/-- Fourteenth-order nodes of a small patch on the sphere. -/
def smallHexPatchNodesF2 (p : SmallHexCubePatch2) (n : ℕ) (hn : 48 ≤ n) :
    (Fin 2 → FourteenNodeIndex n) → SphereD 2 :=
  hexFourteenthSphereNodes2 n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallHexPatchNodesF2_injective (p : SmallHexCubePatch2) (n : ℕ) (hn : 48 ≤ n) :
    Function.Injective (smallHexPatchNodesF2 p n hn) :=
  hexFourteenthSphereNodes2_injective n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallHexPatchNodesF2_coe (p : SmallHexCubePatch2) (n : ℕ) (hn : 48 ≤ n)
    (u : Fin 2 → FourteenNodeIndex n) :
    (smallHexPatchNodesF2 p n hn u : AmbientD 2) = smallHexCubeMap2 p (fourteenCubeNode 2 n u) :=
  rfl

theorem smallHexPatchNodesF2_mem (p : SmallHexCubePatch2) (n : ℕ) (hn : 48 ≤ n)
    (u : Fin 2 → FourteenNodeIndex n) :
    smallHexPatchNodesF2 p n hn u ∈ smallHexSpherePatch2 p := by
  refine ⟨fourteenCubeNode 2 n u, fun i => ⟨(fourteenCubeNode_mem_open 2 n hn u i).1.le,
    (fourteenCubeNode_mem_open 2 n hn u i).2.le⟩, rfl⟩

/-- All fourteenth-order nodes of a patch family of one common scale. -/
def hexFamilyNodesF2 {K : ℕ} (P : Fin K → SmallHexCubePatch2) (n : ℕ) (hn : 48 ≤ n) :
    Fin K × (Fin 2 → FourteenNodeIndex n) → SphereD 2 :=
  fun q => smallHexPatchNodesF2 (P q.1) n hn q.2

open Boundary

theorem hexFamilyNodesF2_injective {K : ℕ} (P : Fin K → SmallHexCubePatch2)
    (hdisj : Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
      (smallHexSpherePatch2 (P j)))) (n : ℕ) (hn : 48 ≤ n) :
    Function.Injective (hexFamilyNodesF2 P n hn) := by
  rintro ⟨i,u⟩ ⟨j,w⟩ h
  change smallHexPatchNodesF2 (P i) n hn u = smallHexPatchNodesF2 (P j) n hn w at h
  have hij : i = j := by
    by_contra hne
    have hi := smallHexPatchNodesF2_mem (P i) n hn u
    have hj := smallHexPatchNodesF2_mem (P j) n hn w
    rw [← h] at hj
    exact Set.disjoint_left.mp (hdisj hne) hi hj
  subst hij
  rw [smallHexPatchNodesF2_injective (P i) n hn h]

/-- Indices of the uncorrected middle block of the fourteenth-order tensor rule. -/
def fourteenMiddleCube2 (n : ℕ) : (Fin 2 → Fin (n-48)) ↪ (Fin 2 → FourteenNodeIndex n) where
  toFun u := fun i => Sum.inr (Sum.inl (u i))
  inj' := by
    intro u w h
    funext i
    exact Sum.inl_injective (Sum.inr_injective (congrFun h i))

theorem fourteenCubeNode_middle2 (n : ℕ) (u : Fin 2 → Fin (n-48)) (i : Fin 2) :
    fourteenCubeNode 2 n (fourteenMiddleCube2 n u) i = ((u i:ℝ)+24+1/2)/(n:ℝ) := rfl

/-- Middle nodes are lattice midpoints: their flat distances are lattice distances at scale
`1/n`. -/
theorem fourteenMiddleCube2_flat_distance (n : ℕ) (u w : Fin 2 → Fin (n-48)) :
    dist (WithLp.toLp 2 (hexMap (fourteenCubeNode 2 n (fourteenMiddleCube2 n u))) : HexAmbient)
      (WithLp.toLp 2 (hexMap (fourteenCubeNode 2 n (fourteenMiddleCube2 n w)))) =
      (n:ℝ)⁻¹*‖((hexGridLattice2 (n-48) w-hexGridLattice2 (n-48) u : hexLattice) :
        HexAmbient)‖ := by
  have he : fourteenCubeNode 2 n (fourteenMiddleCube2 n u)-fourteenCubeNode 2 n (fourteenMiddleCube2 n w) =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, fourteenCubeNode_middle2, div_eq_mul_inv]
    ring
  rw [dist_eq_norm, ← WithLp.toLp_sub, ← map_sub, he, map_smul, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
  congr 1
  change ‖WithLp.toLp 2 (hexMap (fun i => (u i:ℝ)-(w i:ℝ)))‖ =
    ‖hexIntegerPoint (fun i => (w i:ℤ))-hexIntegerPoint (fun i => (u i:ℤ))‖
  rw [norm_sub_rev]
  rw [hexIntegerPoint, hexIntegerPoint, ← WithLp.toLp_sub, ← map_sub]
  simp only [Int.cast_natCast]
  rfl

/-- Middle nodes of a small patch: sharp theta rows, uniformly in the refinement. -/
theorem smallHexPatch_middle_rowF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 2 → Fin (n-48),
      (∑ w, sphereGaussianKernel2 t
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n w))) ≤
      hexGaussianThetaReal2 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaHexPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x : (Fin 2 → Fin (n-48)) → UnitCube 2 := fun w =>
    ⟨fourteenCubeNode 2 n (fourteenMiddleCube2 n w), fun i =>
      ⟨(fourteenCubeNode_mem_open 2 n hn (fourteenMiddleCube2 n w) i).1.le,
        (fourteenCubeNode_mem_open 2 n hn (fourteenMiddleCube2 n w) i).2.le⟩⟩
  have hrow := hb p.g p.v p.c hv p.c_mem p.ε p.ε_pos hε p.small (hexGridLattice2 (n-48)) x
    (n:ℝ)⁻¹ (inv_pos.mpr hnR) (fun i j => fourteenMiddleCube2_flat_distance n i j) t ht u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n w))) ≤
      hexGaussianThetaReal2 (t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n w))) =
      sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n w)) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
      (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n w))) (Finset.mem_univ u)).symm
  have hθ : t*((1-η)*p.ε/(n:ℝ))^2/Real.pi = t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi := by
    rw [div_eq_mul_inv ((1-η)*p.ε) (n:ℝ)]
  rw [hsplit, sphereGaussianKernel2_self t, hθ]
  linarith

/-- All nodes of a small patch: conservative theta rows, uniformly in the refinement. -/
theorem smallHexPatch_all_rowF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 2 → FourteenNodeIndex n,
      (∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn w)) ≤
      hexGaussianThetaReal2
        (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hrow := equalAreaHexFourteenth2_gaussian_row hn p.g p.v p.c p.c_mem p.ε_pos p.small
    patchChartLower2_pos ht
    (fun x hx y hy => hgeom p.v hv p.ε p.ε_pos hε p.g p.c p.c_mem x hx y hy) u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn u) (smallHexPatchNodesF2 p n hn w)) ≤
      hexGaussianThetaReal2
        (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
      (smallHexPatchNodesF2 p n hn w)) =
      sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn u)+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn w) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn u) (smallHexPatchNodesF2 p n hn w))
      (Finset.mem_univ u)).symm
  rw [hsplit, sphereGaussianKernel2_self t]
  linarith

/-- The full Gaussian pair sum of one small patch: sharp theta rows on the middle block and
conservative rows for the `n²-(n-48)²` other nodes. -/
theorem smallHexPatch_pairSum_leF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 48 ≤ n) (t : ℝ), 0 < t →
      (∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn w)) ≤
      (n:ℝ)^2*hexGaussianThetaReal2 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi)+
        2*((n:ℝ)^2-((n:ℝ)-48)^2)*hexGaussianThetaReal2
          (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi) := by
  obtain ⟨ρ₁,hρ₁,hρ₁',hsharp⟩ := smallHexPatch_middle_rowF hη hη1
  obtain ⟨ρ₂,hρ₂,_,hall⟩ := smallHexPatch_all_rowF
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε n hn t ht
  have hv₁ := hv.trans (min_le_left ρ₁ ρ₂)
  have hv₂ := hv.trans (min_le_right ρ₁ ρ₂)
  have hε₁ := hε.trans (min_le_left ρ₁ ρ₂)
  have hε₂ := hε.trans (min_le_right ρ₁ ρ₂)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative2_norm_pos
  have hη0 : 0 < 1-η := by linarith
  obtain ⟨θs, hθs⟩ : ∃ θs : ℝ, θs =
      hexGaussianThetaReal2 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := ⟨_, rfl⟩
  obtain ⟨θc, hθc⟩ : ∃ θc : ℝ, θc = hexGaussianThetaReal2
      (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi) := ⟨_, rfl⟩
  have hθs0 : 0 ≤ θs := by
    rw [hθs]
    exact zero_le_one.trans (hexGaussianThetaReal2_ge_one
      (div_pos (mul_pos ht (pow_pos (div_pos (mul_pos hη0 p.ε_pos) hnR) 2)) Real.pi_pos))
  rw [← hθs, ← hθc]
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 2 → FourteenNodeIndex n),
      S = Finset.univ.map (fourteenMiddleCube2 n) := ⟨_, rfl⟩
  have h74 : ((n-48 : ℕ) : ℝ) = (n:ℝ)-48 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hcardS : (S.card : ℝ) = ((n:ℝ)-48)^2 := by
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
      Nat.cast_pow, h74]
  have hcardT : (Fintype.card (Fin 2 → FourteenNodeIndex n) : ℝ) = (n:ℝ)^2 := by
    rw [fourteenCubeNode_card 2 n hn]
    exact Nat.cast_pow _ _
  have hcardC : (Sᶜ.card : ℝ) = (n:ℝ)^2-((n:ℝ)-48)^2 := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ S), hcardT, hcardS]
  have hsplit : (∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
      (smallHexPatchNodesF2 p n hn w)) ≤
      (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn w))+
      2*(∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
        (smallHexPatchNodesF2 p n hn w)) :=
    pairSum_le_core_add_restS2 S (fun u w => sphereGaussianKernel2 t
      (smallHexPatchNodesF2 p n hn u) (smallHexPatchNodesF2 p n hn w))
      (fun u w => sphereGaussianKernel2_nonneg _ _ _)
      (fun u w => sphereGaussianKernel2_comm t _ _)
  have hcore : (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
      (smallHexPatchNodesF2 p n hn w)) ≤ (n:ℝ)^2*θs := by
    have hrows : ∀ u : Fin 2 → Fin (n-48), (∑ w ∈ S, sphereGaussianKernel2 t
        (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
        (smallHexPatchNodesF2 p n hn w)) ≤ θs := by
      intro u
      rw [hS, Finset.sum_map, hθs]
      exact hsharp p hv₁ hε₁ n hn t ht u
    have hpow : ((n:ℝ)-48)^2 ≤ (n:ℝ)^2 := by
      have h0 : 0 ≤ (n:ℝ)-48 := by
        rw [← h74]
        exact Nat.cast_nonneg _
      exact pow_le_pow_left₀ h0 (by linarith) 2
    calc (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
          (smallHexPatchNodesF2 p n hn w))
        = ∑ u : Fin 2 → Fin (n-48), ∑ w ∈ S, sphereGaussianKernel2 t
            (smallHexPatchNodesF2 p n hn (fourteenMiddleCube2 n u))
            (smallHexPatchNodesF2 p n hn w) := by
          rw [hS, Finset.sum_map]
      _ ≤ ∑ _u : Fin 2 → Fin (n-48), θs := Finset.sum_le_sum fun u _ => hrows u
      _ = ((n:ℝ)-48)^2*θs := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
            Fintype.card_fin, Nat.cast_pow, h74]
      _ ≤ (n:ℝ)^2*θs := mul_le_mul_of_nonneg_right hpow hθs0
  have hrest : (∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 p n hn u)
      (smallHexPatchNodesF2 p n hn w)) ≤ ((n:ℝ)^2-((n:ℝ)-48)^2)*θc := by
    calc _ ≤ ∑ _u ∈ Sᶜ, θc := Finset.sum_le_sum fun u _ => by
            rw [hθc]
            exact hall p hv₂ hε₂ n hn t ht u
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardC]
  calc _ ≤ _ := hsplit
    _ ≤ (n:ℝ)^2*θs+2*(((n:ℝ)^2-((n:ℝ)-48)^2)*θc) :=
        add_le_add hcore (mul_le_mul_of_nonneg_left hrest (by norm_num))
    _ = _ := by rw [mul_assoc]

/-- Pair sum of a separated family: the patch sums plus the squared cardinality times the cross
bound. -/
theorem hexFamily_pairSum_le_patchesF {K : ℕ} (P : Fin K → SmallHexCubePatch2) (n : ℕ)
    (hn : 48 ≤ n) (k : SphereD 2 → SphereD 2 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i j, i ≠ j → ∀ u w, k (smallHexPatchNodesF2 (P i) n hn u)
      (smallHexPatchNodesF2 (P j) n hn w) ≤ τ) :
    (∑ q, ∑ q', k (hexFamilyNodesF2 P n hn q) (hexFamilyNodesF2 P n hn q')) ≤
      (∑ i, ∑ u, ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
        (smallHexPatchNodesF2 (P i) n hn w))+((K:ℝ)*(n:ℝ)^2)^2*τ := by
  classical
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcardNodes : (Fintype.card (Fin 2 → FourteenNodeIndex n) : ℝ) = (n:ℝ)^2 := by
    rw [fourteenCubeNode_card 2 n hn]
    exact Nat.cast_pow _ _
  have hrow : ∀ i u, (∑ j, ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
      (smallHexPatchNodesF2 (P j) n hn w)) ≤
      (∑ w, k (smallHexPatchNodesF2 (P i) n hn u) (smallHexPatchNodesF2 (P i) n hn w))+
        (K:ℝ)*((n:ℝ)^2*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
        (smallHexPatchNodesF2 (P j) n hn w)) ≤
        (if j = i then ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
          (smallHexPatchNodesF2 (P i) n hn w) else 0)+(n:ℝ)^2*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 2).le hτ)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 2 → FourteenNodeIndex n, τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = (n:ℝ)^2*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
            (smallHexPatchNodesF2 (P i) n hn w) else 0)+(n:ℝ)^2*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit : (∑ q, ∑ q', k (hexFamilyNodesF2 P n hn q) (hexFamilyNodesF2 P n hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
        (smallHexPatchNodesF2 (P j) n hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
          (smallHexPatchNodesF2 (P i) n hn w))+(K:ℝ)*((n:ℝ)^2*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, k (smallHexPatchNodesF2 (P i) n hn u)
          (smallHexPatchNodesF2 (P i) n hn w))+(K:ℝ)*((n:ℝ)^2*((K:ℝ)*((n:ℝ)^2*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ = _ := by ring

/-- Gaussian window of a separated fourteenth-order foreground family at exact mass. -/
theorem hexPatchFamily_gaussianWindow_leF {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m) (α : ℝ), 0 < α →
      (∑ q, ∑ q', sphereGaussianKernel2 (sphereGaussianScale2 ((d*m)^2) α)
          (hexFamilyNodesF2 P (a*m) hn q) (hexFamilyNodesF2 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
          2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
            hexGaussianThetaReal2 (α*hexConservativeRowFactor2))+
        ((K:ℝ)*((a*m:ℕ):ℝ)^2)^2*
          Real.exp (-(sphereGaussianScale2 ((d*m)^2) α*δ^2)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_pairSum_leF hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn α hα
  have hNpos : 0 < (d*m)^2 := by positivity
  have ht0 : 0 < sphereGaussianScale2 ((d*m)^2) α := sphereGaussianScale2_pos hNpos hα
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = sphereGaussianScale2 ((d*m)^2) α := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  rw [← htdef, ← hndef]
  have ht : 0 < t := by rw [htdef]; exact ht0
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hn0' : n ≠ 0 := hn0.ne'
  have hD := equalAreaFlatDerivative2_norm_pos
  have hπ := Real.pi_pos
  have hnπ : n^2*Real.pi ≠ 0 := (mul_pos (pow_pos hn0 2) hπ).ne'
  -- theta arguments at exact mass
  have hte : ∀ i, t*(P i).ε^2 = Real.pi*n^2*α := by
    intro i
    have h := sphereGaussian_exact_mass_bump_scale2 a d m hd (P i).ε α (hratio i)
    rw [← htdef, ← hndef] at h
    linarith
  have hsharp : ∀ i, t*((1-η)*(P i).ε/n)^2/Real.pi = α*(1-η)^2 := by
    intro i
    have h1 : t*((1-η)*(P i).ε/n)^2/Real.pi =
        (t*(P i).ε^2)*(1-η)^2/(n^2*Real.pi) := by ring
    rw [h1, hte i, div_eq_iff hnπ]
    ring
  have hfac : hexConservativeRowFactor2 =
      patchChartLower2^2/(2*‖equalAreaFlatDerivative2‖)^2 := by
    unfold hexConservativeRowFactor2
    rw [div_pow]
  have hcons : ∀ i, t*((P i).ε*patchChartLower2/(2*n*‖equalAreaFlatDerivative2‖))^2/Real.pi =
      α*hexConservativeRowFactor2 := by
    intro i
    have h1 : t*((P i).ε*patchChartLower2/(2*n*‖equalAreaFlatDerivative2‖))^2/Real.pi =
        (t*(P i).ε^2)*(patchChartLower2^2/(2*‖equalAreaFlatDerivative2‖)^2)/
          (n^2*Real.pi) := by ring
    rw [h1, hte i, hfac, div_eq_iff hnπ]
    ring
  have hsub : n^2-(n-48)^2 = n^2*(1-(1-48/n)^2) := by
    have h74 : n-48 = n*(1-48/n) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hn0']
    rw [h74, mul_pow]
    ring
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, sphereGaussianKernel2 t
      (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P i) (a*m) hn w)) ≤
      n^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
        2*(1-(1-48/n)^2)*hexGaussianThetaReal2 (α*hexConservativeRowFactor2)) := by
    intro i
    have h := hb (P i) (hv i) (hε i) (a*m) hn t ht
    rw [← hndef, hsharp i, hcons i, hsub] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, sphereGaussianKernel2 t
      (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P j) (a*m) hn w) ≤
      Real.exp (-(t*δ^2)) := by
    intro i j hij u w
    have hdist := hsep i j hij _ (smallHexPatchNodesF2_mem (P i) _ hn u) _
      (smallHexPatchNodesF2_mem (P j) _ hn w)
    unfold sphereGaussianKernel2
    apply Real.exp_le_exp.mpr
    have hsq : δ^2 ≤ dist (smallHexPatchNodesF2 (P i) (a*m) hn u)
        (smallHexPatchNodesF2 (P j) (a*m) hn w)^2 := pow_le_pow_left₀ hδ.le hdist 2
    have hmul := mul_le_mul_of_nonneg_left hsq ht.le
    linarith
  have hfam := hexFamily_pairSum_le_patchesF P (a*m) hn (sphereGaussianKernel2 t)
    (Real.exp_pos (-(t*δ^2))).le hcross
  rw [← hndef] at hfam
  calc _ ≤ (∑ i, ∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodesF2 (P i) (a*m) hn u)
          (smallHexPatchNodesF2 (P i) (a*m) hn w))+((K:ℝ)*n^2)^2*Real.exp (-(t*δ^2)) := hfam
    _ ≤ (∑ _i : Fin K, n^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
          2*(1-(1-48/n)^2)*hexGaussianThetaReal2 (α*hexConservativeRowFactor2)))+
          ((K:ℝ)*n^2)^2*Real.exp (-(t*δ^2)) :=
        add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end SphericalRiesz
end
end

section

/-! Fourteenth-order Gaussian bump error of the patch nodes of the triangular lattice on `S²`,
and the neutralized Gaussian defect of a foreground family against the smooth residual
background.

At exact mass (`ε d = r₀ a`, `n = a m`, `N = (d m)²`) the node sum of an ambient Gaussian bump
differs from `N ∫_patch` by at most `K (n⁻¹⁴ + (2πα)⁷)` times `N ∫_patch` of the softened bump,
for every `α ∈ (0,4]`; at macroscopic scales `2π n² α ≤ 1` the factor is `K' √(2πα)/n¹³`.
Squaring gives the defect of the mixed measure (foreground points plus `N σ` on the complement
of the patches); the bump-square identity in `ℝ³` has the exponent `(d+1)/2 = 3/2`:

`defect(α) ≤ 8^(3/2) (K (n⁻¹⁴ + (2πα)⁷))² N² B(t/8)`, and for `2π n² α ≤ 1`
`defect(α) ≤ 8^(3/2) K'² (2πα) n⁻²⁶ N² B(t/8)`,

so, with `N B(t/8) ≤ 8 α⁻¹` on `S²`, the defect is of size `N α¹³` at mesoscopic scales and
linear in `α` at macroscopic scales.  This is the input of the macroscopic end for negative
exponents.  No configuration and no attaining sequence is asserted here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff ENNReal NNReal
namespace SphericalRiesz
open Boundary

theorem smallHexPatch_normalized_chart_bounds14 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      (∀ x ∈ UnitCube 2, ContDiffAt ℝ 14 (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x) ∧
      (∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 14 →
        ‖iteratedFDeriv ℝ j (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper2) ∧
      (∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, patchChartLower2*‖x-y‖ ≤
        ‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-equalAreaNormalizedHexPatch p.g p.v p.c p.ε y‖) ∧
      (∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
        ‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-equalAreaNormalizedHexPatch p.g p.v p.c p.ε y‖ ≤
          patchChartUpper2*‖x-y‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁', h₁⟩ := equalAreaNormalizedHexPatch_Cn_uniform 14 1 one_pos
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε
  have hv₁ : ‖p.v‖ ≤ ρ₁ := hv.trans (min_le_left _ _)
  have hv₂ : ‖p.v‖ ≤ ρ₂ := hv.trans (min_le_right _ _)
  have hε₁ : p.ε*equalAreaScaleRadius2 ≤ ρ₁ := hε.trans (min_le_left _ _)
  have hε₂ : p.ε*equalAreaScaleRadius2 ≤ ρ₂ := hε.trans (min_le_right _ _)
  have hb := fun x hx => h₁ p.v hv₁ p.ε p.ε_pos hε₁ p.g p.c p.c_mem x hx
  have hflat : ‖equalAreaRotatedFlatDerivative2 p.g‖ ≤ ‖equalAreaFlatDerivative2‖ :=
    equalAreaRotation2_comp_norm_le p.g equalAreaFlatDerivative2
  have hfd : ∀ x ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper2 := by
    intro x hx
    have h := (hb x hx).2.2.1
    calc ‖fderiv ℝ (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x‖
        = ‖(fderiv ℝ (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative2 p.g)+equalAreaRotatedFlatDerivative2 p.g‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative2 p.g‖+‖equalAreaRotatedFlatDerivative2 p.g‖ :=
          norm_add_le _ _
      _ ≤ 1+‖equalAreaFlatDerivative2‖ := add_le_add h hflat
      _ = patchChartUpper2 := by rw [patchChartUpper2]; ring
  refine ⟨fun x hx => (hb x hx).1.of_le (by simp), ?_, ?_, ?_⟩
  · intro x hx j hj hj6
    rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 1 := by omega
      subst this
      rw [norm_iteratedFDeriv_one]
      exact hfd x hx
    · exact ((hb x hx).2.2.2 j h (by omega)).trans one_le_patchChartUpper2
  · intro x hx y hy
    have h := h₂ p.v hv₂ p.ε p.ε_pos hε₂ p.g p.c p.c_mem x hx y hy
    rw [dist_eq_norm] at h
    simpa only [patchChartLower2] using h
  · intro x hx y hy
    exact unitCube2_convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hb z hz).1.differentiableAt (by simp))) hfd hy hx

/-- Localized fourteenth-order error of an ambient Gaussian bump on one small patch: every
scale, and with a factor `√τ` at macroscopic scales `τ = 2tε² ≤ 1`. -/
theorem smallHexPatch_bump_quadrature14 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ n : ℕ, 48 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2*patchChartLower2^2/384 ≤ (n:ℝ)^2 →
      ∀ z : AmbientD 2,
      |fourteenCubeQuadrature 2 n (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)-
        cubeIntegral 2 (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)| ≤
        bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2/(n:ℝ)^14*(1+(2*t*p.ε^2)^7)*
          cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) ∧
      (2*t*p.ε^2 ≤ 1 →
      |fourteenCubeQuadrature 2 n (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)-
        cubeIntegral 2 (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)| ≤
        bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2/(n:ℝ)^14*
          Real.sqrt (2*t*p.ε^2)*
          cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2)))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallHexPatch_normalized_chart_bounds14
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτn z
  obtain ⟨hcd, hder, hlow, hup⟩ := hb p hv hε
  have hτ : 0 < 2*t*p.ε^2 := by have := p.ε_pos; positivity
  have hf1 : (fun x => ambientBump3 t (smallHexCubeMap2 p x) z) =
      fun x => Real.exp (-((2*t*p.ε^2)*‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-
        p.ε⁻¹ • (z-smallHexCubeMap2 p p.c)‖^2)) := by
    funext x
    unfold ambientBump3
    rw [smallHexCubeMap2_sub_norm_sq]
    ring_nf
  have hf2 : (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) =
      fun x => Real.exp (-((2*t*p.ε^2)/8*‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-
        p.ε⁻¹ • (z-smallHexCubeMap2 p p.c)‖^2)) := by
    funext x
    rw [smallHexCubeMap2_sub_norm_sq]
    ring_nf
  rw [hf1, hf2]
  exact ⟨normalized_bump_quadrature_error_fourteen2 one_le_patchChartUpper2
      patchChartLower2_pos hcd hder hlow hup hn hτ hτn _,
    fun hτ1 => normalized_bump_quadrature_error_fourteen_small2 one_le_patchChartUpper2
      patchChartLower2_pos hcd hder hlow hup hn hτ hτ1 hτn _⟩

theorem bumpErrorConstFourteen2_patch_nonneg :
    0 ≤ bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2 := by
  rw [bumpErrorConstFourteen2_eq]
  exact mul_nonneg (bumpEnvelopeConst2_nonneg _ _)
    (fourteenthConst2_nonneg (by linarith [one_le_patchChartUpper2]))

theorem bumpErrorConstFourteenSmall2_patch_nonneg :
    0 ≤ bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2 :=
  mul_nonneg (bumpEnvelopeConst2_nonneg _ _) (fourteenthSmallConst2_nonneg _)

/-- One patch, exact mass: the node sum against `N ∫_patch` of the bump, at every scale and at
macroscopic scales. -/
theorem smallHexPatch_bump_sphere_errorF2 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 2,
      |(∑ u : Fin 2 → FourteenNodeIndex (a*m),
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α)
            (smallHexPatchNodesF2 p (a*m) hn u : AmbientD 2) z)-
        (((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)| ≤
      bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7)*
        ((((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α/8) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)) ∧
      (2*Real.pi*((a*m:ℕ):ℝ)^2*α ≤ 1 →
      |(∑ u : Fin 2 → FourteenNodeIndex (a*m),
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α)
            (smallHexPatchNodesF2 p (a*m) hn u : AmbientD 2) z)-
        (((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)| ≤
      bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13)*
        ((((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α/8) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_quadrature14
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε a d m hd hm hratio hn α hα z
  have hts : 0 < sphereGaussianScale2 ((d*m)^2) α :=
    sphereGaussianScale2_pos (by positivity) hα.1
  have hmesh := sphereGaussian_exact_mass_twelfth_mesh2 a d m hd p.ε hratio hα
  obtain ⟨hquad, hquadS⟩ := hb p hv hε (a*m) hn _ hts hmesh z
  have hτ := sphereGaussian_exact_mass_bump_scale2 a d m hd p.ε α hratio
  set t := sphereGaussianScale2 ((d*m)^2) α with ht
  have hn0 : (0:ℝ) < ((a*m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < a*m)
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdens := hexTwelfth_rational_exact_patch_mass2 a d m hd hm p.ε hratio
  have hsum : (∑ u : Fin 2 → FourteenNodeIndex (a*m),
      ambientBump3 t (smallHexPatchNodesF2 p (a*m) hn u : AmbientD 2) z) =
      ((a*m:ℕ):ℝ)^2*fourteenCubeQuadrature 2 (a*m)
        (fun x => ambientBump3 t (smallHexCubeMap2 p x) z) := by
    rw [fourteenCubeQuadrature_as_node_sum, mul_div_cancel₀ _ (pow_pos hn0 2).ne']
    exact Finset.sum_congr rfl fun u _ => by rw [smallHexPatchNodesF2_coe]
  have hI : ∀ τ : ℝ, (((d*m)^2:ℕ):ℝ)*(∫ y in smallHexSpherePatch2 p,
      ambientBump3 τ (y : AmbientD 2) z ∂(sphereProbabilityD 2)) =
      ((a*m:ℕ):ℝ)^2*cubeIntegral 2 (fun x => ambientBump3 τ (smallHexCubeMap2 p x) z) := by
    intro τ
    rw [smallHexSpherePatch2_setIntegral p (fun y => ambientBump3 τ y z)
      (by unfold ambientBump3; fun_prop), hdens]
    push_cast
    field_simp
  have hsoft : (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) =
      fun x => ambientBump3 (t/8) (smallHexCubeMap2 p x) z := by
    funext x
    unfold ambientBump3
    rw [show t/4*‖smallHexCubeMap2 p x-z‖^2 = 2*(t/8)*‖smallHexCubeMap2 p x-z‖^2 by ring]
  rw [hsoft] at hquad hquadS
  rw [hsum, hI t, hI (t/8), ← mul_sub, abs_mul, abs_of_pos (pow_pos hn0 2)]
  set I8 := cubeIntegral 2 (fun x => ambientBump3 (t/8) (smallHexCubeMap2 p x) z) with hI8
  constructor
  · calc
      _ ≤ ((a*m:ℕ):ℝ)^2*(bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2/
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
      _ ≤ ((a*m:ℕ):ℝ)^2*(bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2/
          ((a*m:ℕ):ℝ)^14*Real.sqrt (2*t*p.ε^2)*I8) :=
        mul_le_mul_of_nonneg_left (hquadS hτ1) (by positivity)
      _ = _ := by
        rw [hsq]
        field_simp

/-- A finite disjoint family: a common relative patch error passes to the union and is bounded
by the softened bump field of the whole sphere. -/
theorem hexPatchFamily_bump_of_patchF {K : ℕ} (P : Fin K → SmallHexCubePatch2)
    (hdisj : Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
      (smallHexSpherePatch2 (P j))))
    (n : ℕ) (hn : 48 ≤ n) (N : ℝ) (hN : 0 ≤ N) {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (z : AmbientD 2)
    (hpatch : ∀ i, |(∑ u : Fin 2 → FourteenNodeIndex n,
        ambientBump3 t (smallHexPatchNodesF2 (P i) n hn u : AmbientD 2) z)-
        N*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2)| ≤
      C*(N*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2))) :
    |(∑ i, ∑ u : Fin 2 → FourteenNodeIndex n,
        ambientBump3 t (smallHexPatchNodesF2 (P i) n hn u : AmbientD 2) z)-
      N*∫ y in ⋃ i, smallHexSpherePatch2 (P i),
        ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2)| ≤
    C*(N*bumpField3 (t/8) ambientSphereProbability2 z) := by
  have hsplit : ∀ τ : ℝ, 0 ≤ τ → (∫ y in ⋃ i, smallHexSpherePatch2 (P i),
      ambientBump3 τ (y : AmbientD 2) z ∂(sphereProbabilityD 2)) =
      ∑ i, ∫ y in smallHexSpherePatch2 (P i),
        ambientBump3 τ (y : AmbientD 2) z ∂(sphereProbabilityD 2) := by
    intro τ hτ
    rw [integral_iUnion (fun i => smallHexSpherePatch2_measurable (P i))
      (fun i j hij => hdisj hij) (ambientBump3_sphere_integrable hτ z).integrableOn,
      tsum_fintype]
  have hle : (∫ y in ⋃ i, smallHexSpherePatch2 (P i),
      ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2)) ≤
      bumpField3 (t/8) ambientSphereProbability2 z := by
    rw [bumpField3_sphere_eq]
    exact setIntegral_le_integral (ambientBump3_sphere_integrable (by positivity) z)
      (Filter.Eventually.of_forall fun y => ambientBump3_nonneg _ _ _)
  rw [hsplit t ht.le, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ u : Fin 2 → FourteenNodeIndex n,
          ambientBump3 t (smallHexPatchNodesF2 (P i) n hn u : AmbientD 2) z)-
        N*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*(N*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2)) :=
      Finset.sum_le_sum fun i _ => hpatch i
    _ = C*(N*∫ y in ⋃ i, smallHexSpherePatch2 (P i),
          ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2)) := by
      rw [hsplit (t/8) (by positivity), Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul_of_nonneg_left hle hN

/-- A relative bump error `C` of the foreground gives the mixed defect `8^(3/2) C² N² B(t/8)`. -/
theorem hexPatchFamily_mixed_defect_of_bumpF {K : ℕ} (P : Fin K → SmallHexCubePatch2)
    (n : ℕ) (hn : 48 ≤ n) (N : ℕ) {t C : ℝ} (ht : 0 < t)
    (hb : ∀ z : AmbientD 2, |(∑ i, ∑ u : Fin 2 → FourteenNodeIndex n,
        ambientBump3 t (smallHexPatchNodesF2 (P i) n hn u : AmbientD 2) z)-
      (N:ℝ)*∫ y in ⋃ i, smallHexSpherePatch2 (P i),
        ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2)| ≤
      C*((N:ℝ)*bumpField3 (t/8) ambientSphereProbability2 z)) :
    gaussianMeasureDefect t (N:ℝ)
      (mixedForegroundMeasure2 (hexFamilyNodesF2 P n hn) N (hexFamilyUnion2 P)ᶜ)
      ambientSphereProbability2 ≤
    (8:ℝ)^((3:ℝ)/2)*C^2*(N:ℝ)^2*sphereGaussianBackground2 (t/8) := by
  have ht8 : 0 < t/8 := by positivity
  let W : AmbientD 2 → ℝ := fun z => C*((N:ℝ)*bumpField3 (t/8) ambientSphereProbability2 z)
  have hWsq : (fun z => W z^2) = fun z => (C*(N:ℝ))^2*
      (bumpField3 (t/8) ambientSphereProbability2 z*
        bumpField3 (t/8) ambientSphereProbability2 z) := by
    funext z
    simp only [W]
    ring
  have hWi : Integrable (fun z => W z^2) := by
    rw [hWsq]
    exact (bumpField3_mul_integrable ht8 ambientSphereProbability2
      ambientSphereProbability2).const_mul _
  have hle : ∀ z, |bumpField3 t (mixedForegroundMeasure2 (hexFamilyNodesF2 P n hn)
      N (hexFamilyUnion2 P)ᶜ) z-(N:ℝ)*bumpField3 t ambientSphereProbability2 z| ≤ W z := by
    intro z
    rw [mixedForeground_bumpError_eqS2 _ _ _ (hexFamilyUnion2_measurable P) ht.le,
      Fintype.sum_prod_type]
    exact hb z
  have hmain := gaussianMeasureDefect_le_of_bump3 ht (N:ℝ) _ ambientSphereProbability2 hWi hle
  have hint : (∫ z, W z^2) = (C*(N:ℝ))^2*((Real.pi/(4*(t/8)))^((3:ℝ)/2)*
      sphereGaussianBackground2 (t/8)) := by
    rw [hWsq, integral_const_mul, ← bumpField3_sphere_sq_integral ht8]
    simp_rw [sq]
  have hconst : (4*t/Real.pi)^((3:ℝ)/2)*(Real.pi/(4*(t/8)))^((3:ℝ)/2) = (8:ℝ)^((3:ℝ)/2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    _ ≤ (4*t/Real.pi)^((3:ℝ)/2)*∫ z, W z^2 := hmain
    _ = ((4*t/Real.pi)^((3:ℝ)/2)*(Real.pi/(4*(t/8)))^((3:ℝ)/2))*(C*(N:ℝ))^2*
        sphereGaussianBackground2 (t/8) := by rw [hint]; ring
    _ = _ := by rw [hconst]; ring

/-- Neutralized Gaussian defect of the fourteenth-order foreground family with the smooth
residual background: every `α ∈ (0,4]`, and linear in `α` at macroscopic scales. -/
theorem hexPatchFamily_mixed_defect_leF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodesF2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (8:ℝ)^((3:ℝ)/2)*(bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7))^2*(((d*m)^2:ℕ):ℝ)^2*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8) ∧
      (2*Real.pi*((a*m:ℕ):ℝ)^2*α ≤ 1 →
      gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodesF2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (8:ℝ)^((3:ℝ)/2)*(bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13))^2*(((d*m)^2:ℕ):ℝ)^2*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_sphere_errorF2
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  have hts : 0 < sphereGaussianScale2 ((d*m)^2) α :=
    sphereGaussianScale2_pos (by positivity) hα.1
  have hN0 : (0:ℝ) ≤ (((d*m)^2:ℕ):ℝ) := by positivity
  constructor
  · have hC : 0 ≤ bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^14+(2*Real.pi*α)^7) := by
      have := hα.1
      exact mul_nonneg bumpErrorConstFourteen2_patch_nonneg (by positivity)
    exact hexPatchFamily_mixed_defect_of_bumpF P (a*m) hn ((d*m)^2) hts fun z =>
      hexPatchFamily_bump_of_patchF P hdisj (a*m) hn _ hN0 hts hC z fun i =>
        (hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z).1
  · intro hsmall
    have hC : 0 ≤ bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2*
        (Real.sqrt (2*Real.pi*α)/((a*m:ℕ):ℝ)^13) :=
      mul_nonneg bumpErrorConstFourteenSmall2_patch_nonneg (by positivity)
    exact hexPatchFamily_mixed_defect_of_bumpF P (a*m) hn ((d*m)^2) hts fun z =>
      hexPatchFamily_bump_of_patchF P hdisj (a*m) hn _ hN0 hts hC z fun i =>
        (hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z).2 hsmall

end SphericalRiesz
end
end
end

section

/-! # Block configurations and a sharp sequence for negative exponents on `S²`

Two parts.

* The macroscopic profile of the fourteenth-order foreground: for the mixed measure of a Hex
  patch family (foreground nodes plus `N σ` on the complement of the patches) and every scaled
  Gaussian parameter `α ∈ (0,4]`, `defect(α) ≤ N (A α² + B (N/n²⁶) α)` with constants independent
  of the family; against the weight `α^p`, `-2 < p`, it integrates over `(0,w]` to
  `A w^(p+3)/(p+3) + B (N/n²⁶) w^(p+2)/(p+2)`.
* The block: for a tolerance index `L ≥ 2`, a near-full rational family of residual fraction
  below `L⁻¹⁴`, the fourteenth-order nodes of a refinement and one residual point per cell of an
  exact-mass stratification of the complement, chosen jointly for the subtracted macroscopic
  kernel and one Gaussian window, form an actual configuration of `N = (d m)²` points with a
  Gaussian window at every scale `α ≥ 1/L` and a small macroscopic end at every cutoff
  `0 < w ≤ 1`.  Along `L → ∞` the transfer theorem gives configurations whose normalized
  negative-exponent energy is eventually at least `C_s - η`.

The stratification of the residual regions is a hypothesis of this module
(`HexResidualStratifiable2`), discharged by the geometric construction in
`SphereStratification2`; no contact certificate is used. -/

section

/-! Macroscopic profile of the fourteenth-order foreground defect on S² (stage NEG).

For the mixed measure of a fourteenth-order Hex patch family (foreground nodes plus `N σ` on
the complement of the patches) and every `α ∈ (0,4]`,

`defect(α) ≤ N (A α² + B (N/n²⁶) α)`,

with constants `A`, `B` independent of the family: for `2π n² α > 1` the general bound and
`n⁻¹⁴ ≤ (2πα)⁷`, `N B₂ ≤ 8¹²/α¹²` give `N A α²`; for `2π n² α ≤ 1` the macroscopic bound and
`B₂ ≤ 1` give `N B (N/n²⁶) α`.  Since `N/n²⁶ = (d/a)²/n²⁴`, the second term vanishes under
refinement.  Against the weight `α^p`, `-2 < p`, the profile integrates over `(0,w]` to
`A w^(p+3)/(p+3) + B (N/n²⁶) w^(p+2)/(p+2)`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- Family-independent constant of the mesoscopic foreground defect `N A α²`. -/
def hexMacroConstA2 : ℝ :=
  4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*
    (bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2)^2*(2*Real.pi)^14

/-- Constant of the macroscopic foreground defect `N B (N/n²⁶) α`. -/
def hexMacroConstB2 : ℝ :=
  (8:ℝ)^((3:ℝ)/2)*
    (bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2)^2*(2*Real.pi)

theorem hexMacroConstA2_nonneg : 0 ≤ hexMacroConstA2 := by
  unfold hexMacroConstA2
  positivity

theorem hexMacroConstB2_nonneg : 0 ≤ hexMacroConstB2 := by
  unfold hexMacroConstB2
  positivity

/-- The weighted integral of a profile `A α² + B α` over `(0,w]`. -/
theorem negMacro_poly_integralS2 {p w : ℝ} (hp : -2 < p) (hw : 0 ≤ w) (A B : ℝ) :
    IntegrableOn (fun α : ℝ => α^p*(A*α^2+B*α)) (Ioc 0 w) ∧
    (∫ α in Ioc (0:ℝ) w, α^p*(A*α^2+B*α)) = A*(w^(p+3)/(p+3))+B*(w^(p+2)/(p+2)) := by
  have h2 : IntegrableOn (fun α : ℝ => A*α^(p+2)) (Ioc 0 w) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  have h1 : IntegrableOn (fun α : ℝ => B*α^(p+1)) (Ioc 0 w) := negMacro2_dom_integrableOn hp hw B
  have heq : ∀ α ∈ Ioc (0:ℝ) w, α^p*(A*α^2+B*α) = A*α^(p+2)+B*α^(p+1) := by
    intro α hα
    have h0 : 0 < α := hα.1
    rw [Real.rpow_add h0 p 2, Real.rpow_two, Real.rpow_add_one h0.ne' p]
    ring
  have h3 : p+2+1 = p+3 := by ring
  constructor
  · exact (h2.add h1).congr_fun (fun α hα => (heq α hα).symm) measurableSet_Ioc
  · rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_add h2 h1,
      negMacro2_dom_integral hp hw B, integral_const_mul,
      ← intervalIntegral.integral_of_le hw, integral_rpow (Or.inl (by linarith : -1 < p+2)),
      h3, Real.zero_rpow (by linarith : p+3 ≠ 0), sub_zero]

/-- The foreground defect of a fourteenth-order family: `N (A α² + B (N/n²⁶) α)` on `(0,4]`. -/
theorem hexPatchFamily_mixed_defect_macroF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodesF2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (((d*m)^2:ℕ):ℝ)*(hexMacroConstA2*α^2+
        hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := hexPatchFamily_mixed_defect_leF
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  obtain ⟨hA, hB⟩ := hb P hv hε hdisj a d m hd hm hratio hn α hα
  have hα0 : 0 < α := hα.1
  have hNpos : 0 < (d*m)^2 := by positivity
  have hscale : sphereGaussianScale2 ((d*m)^2) α/8 = sphereGaussianScale2 ((d*m)^2) (α/8) := by
    unfold sphereGaussianScale2
    ring
  have hcap0 := sphereGaussianBackground2_scaled_cap hNpos (α := α/8) (by positivity)
  rw [← hscale] at hcap0
  have hB1' : sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8) ≤ 1 :=
    sphereGaussianBackground2_le_one
      (by rw [hscale]; exact (sphereGaussianScale2_pos hNpos (by positivity)).le)
  have hB0' := sphereGaussianBackground2_nonneg (sphereGaussianScale2 ((d*m)^2) α/8)
  -- abbreviations as opaque reals with their equations
  obtain ⟨NR, hNR⟩ : ∃ NR : ℝ, NR = (((d*m)^2:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ,
      K₀ = bumpErrorConstFourteen2 patchChartUpper2 patchChartLower2 := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ,
      Ks = bumpErrorConstFourteenSmall2 patchChartUpper2 patchChartLower2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α)
      (((d*m)^2:ℕ):ℝ) (mixedForegroundMeasure2 (hexFamilyNodesF2 P (a*m) hn) ((d*m)^2)
        (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 := ⟨_, rfl⟩
  have hAc : hexMacroConstA2 = 4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14 := by
    rw [hK₀]
    rfl
  have hBc : hexMacroConstB2 = (8:ℝ)^((3:ℝ)/2)*Ks^2*(2*Real.pi) := by
    rw [hKs]
    rfl
  rw [← hD, ← hNR, ← hndef, hAc, hBc]
  rw [← hD, ← hNR, ← hndef, ← hBdef, ← hK₀] at hA
  rw [← hD, ← hNR, ← hndef, ← hBdef, ← hKs] at hB
  rw [← hNR, ← hBdef] at hcap0
  rw [← hBdef] at hB1' hB0'
  have hNR0 : 0 < NR := by rw [hNR]; exact_mod_cast hNpos
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast (by omega : 0 < a*m)
  have hT : 0 < (8:ℝ)^((3:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hcap1 : NR*B ≤ (8:ℝ)/α := by
    simpa only [inv_div,div_one] using hcap0
  have hcap : NR*B ≤ (8:ℝ)^12/α^12 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < α^12)).mpr
    have hfirst : α^12*(NR*B) ≤ (8:ℝ)^12 := by
      calc α^12*(NR*B) ≤ α^12*((8:ℝ)/α) :=
            mul_le_mul_of_nonneg_left hcap1 (by positivity)
        _ = 8*α^11 := by field_simp
        _ ≤ 8*(8:ℝ)^11 := by gcongr; linarith [hα.2]
        _ = (8:ℝ)^12 := by ring
    simpa only [mul_comm] using hfirst
  have hAterm : 0 ≤ 4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2 := by positivity
  have hBterm : 0 ≤ (8:ℝ)^((3:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α := by positivity
  by_cases hsmall : 2*Real.pi*n^2*α ≤ 1
  · have h := hB hsmall
    have hsq : (Ks*(Real.sqrt (2*Real.pi*α)/n^13))^2 = Ks^2*(2*Real.pi*α)/n^26 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi*α)]
      ring
    rw [hsq] at h
    have h1 : (8:ℝ)^((3:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*B ≤
        (8:ℝ)^((3:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*1 :=
      mul_le_mul_of_nonneg_left hB1' (by positivity)
    have h2 : (8:ℝ)^((3:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*1 =
        NR*((8:ℝ)^((3:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α) := by
      ring
    calc D ≤ (8:ℝ)^((3:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*B := h
      _ ≤ NR*((8:ℝ)^((3:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α) := h1.trans_eq h2
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hNR0.le
  · have hlarge : 1 < 2*Real.pi*n^2*α := lt_of_not_ge hsmall
    have h2 : 1/n^2 ≤ 2*Real.pi*α := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : 1/n^14 ≤ (2*Real.pi*α)^7 := by
      calc 1/n^14 = (1/n^2)^7 := by ring
        _ ≤ (2*Real.pi*α)^7 := pow_le_pow_left₀ (by positivity) h2 7
    have h7 : 0 ≤ (2*Real.pi*α)^7 := by positivity
    have hn14 : 0 ≤ 1/n^14 := by positivity
    have h3 : (1/n^14+(2*Real.pi*α)^7)^2 ≤ (2*(2*Real.pi*α)^7)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsq : (K₀*(1/n^14+(2*Real.pi*α)^7))^2 ≤ K₀^2*(4*(2*Real.pi)^14*α^14) := by
      calc (K₀*(1/n^14+(2*Real.pi*α)^7))^2 = K₀^2*(1/n^14+(2*Real.pi*α)^7)^2 := by ring
        _ ≤ K₀^2*(2*(2*Real.pi*α)^7)^2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = _ := by ring
    have hstep : (8:ℝ)^((3:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR*(NR*B) ≤
        (8:ℝ)^((3:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hT.le) hNR0.le) hcap
        (mul_nonneg hNR0.le hB0') (by positivity)
    have heq : (8:ℝ)^((3:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12) =
        NR*(4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2) := by
      have hα12 : α^12 ≠ 0 := by positivity
      calc (8:ℝ)^((3:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12)
          = NR*(4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*(α^12*α^2/α^12)) := by ring
        _ = _ := by rw [mul_div_cancel_left₀ _ hα12]
    calc D ≤ (8:ℝ)^((3:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR^2*B := hA
      _ = (8:ℝ)^((3:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR*(NR*B) := by ring
      _ ≤ NR*(4*(8:ℝ)^((3:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2) := hstep.trans_eq heq
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hNR0.le

end SphericalRiesz
end
end

section

/-! Block configurations and a sharp sequence for negative exponents on S² (stage NEG).

For a tolerance index `L ≥ 2` take a near-full rational Hex patch family of residual fraction
below `L⁻¹⁴`, the fourteenth-order nodes of a refinement `m`, and one residual point per cell of
an exact-mass stratification of the complement with `Σ_j c_N d_j² ≤ B n + N/L²`, chosen jointly
for the subtracted macroscopic kernel and one Gaussian window.  The resulting configuration of
`N = (d m)²` points satisfies

* the window `Full_α ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) C/L²` for every `α ≥ 1/L`,
* the macroscopic end `∫_{(0,w]} α^(s/2-1)(F+1) ≤ 2(A w^(s/2+2)/(s/2+2)+w^(s/2+1)/(L(s/2+1)))+2C/L²`
  for every cutoff `0 < w ≤ 1`,

with `A` and `C` independent of `L` and of the refinement.  Along `L → ∞` the transfer theorem
gives a sequence of configurations whose normalized negative-exponent energy is eventually at
least `C_s - η`.  The stratification of the residual regions is a hypothesis of this file
(`HexResidualStratifiable2`); it is discharged separately. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

/-- Exact-mass stratifications of the complements of Hex patch families with cells at the
density scale up to `o(N)`: `Σ_j c_N d_j² ≤ B r + ε N`. -/
def HexResidualStratifiable2 (Bst : ℝ) : Prop :=
  ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
    Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i)) (smallHexSpherePatch2 (P j))) →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N r : ℕ,
    N₀ ≤ N → 0 < r →
    (r:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ →
    ∃ C : Fin r → Set (SphereD 2), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = (hexFamilyUnion2 P)ᶜ ∧
      (∀ j, sphereProbabilityD 2 (C j) =
        sphereProbabilityD 2 (hexFamilyUnion2 P)ᶜ/(r:ℝ≥0∞)) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, sphereGaussianDensityFactor2 N*(dm j)^2 ≤ Bst*r+ε*N

/-- Common residual constant of the negative-exponent blocks. -/
def hexNegBlockConst2 (s Bst : ℝ) : ℝ := 2+(Bst+1)/(s/2+1)

/-- The number of residual points of a refinement of a fourteenth-order family. -/
theorem hexFamilyF_residual_count {K : ℕ} (P : Fin K → SmallHexCubePatch2) (a d : ℕ)
    (hd : 0 < d)
    (hmassP : (sphereProbabilityD 2).real (hexFamilyUnion2 P) = (K:ℝ)*((a:ℝ)/d)^2)
    (hbudget : K*a^2 < d^2) (m : ℕ) (hm : 0 < m) (hn : 48 ≤ a*m) :
    ∃ n : ℕ, 0 < n ∧
      Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m)))+n = (d*m)^2 ∧
      (n:ℝ)/(((d*m)^2:ℕ):ℝ) = 1-(K:ℝ)*((a:ℝ)/d)^2 ∧
      (n:ℝ) = (((d*m)^2:ℕ):ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ := by
  have hcardM : Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) = K*(a*m)^2 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 2 (a*m) hn]
  have hlt : K*(a*m)^2 < (d*m)^2 := by
    have h1 : K*(a*m)^2 = K*a^2*m^2 := by rw [mul_pow, mul_assoc]
    have h2 : (d*m)^2 = d^2*m^2 := mul_pow d m 2
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hbudget (pow_pos hm 2)
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hfrac : (((d*m)^2-K*(a*m)^2 : ℕ) : ℝ)/(((d*m)^2:ℕ):ℝ) =
      1-(K:ℝ)*((a:ℝ)/d)^2 := by
    rw [Nat.cast_sub hlt.le]
    push_cast
    field_simp
  have hres : (sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
      (((d*m)^2-K*(a*m)^2 : ℕ) : ℝ)/(((d*m)^2:ℕ):ℝ) := by
    rw [probReal_compl_eq_one_sub (hexFamilyUnion2_measurable P), hmassP, hfrac]
  refine ⟨(d*m)^2-K*(a*m)^2, Nat.sub_pos_of_lt hlt, ?_, hfrac, ?_⟩
  · rw [hcardM]
    exact Nat.add_sub_of_le hlt.le
  · rw [hres, mul_div_cancel₀ _ hNR.ne']

/-- One block for negative exponents: explicit conditions on the family, the refinement and the
residual cells give an actual configuration with a Gaussian window and a small macroscopic
end. -/
theorem exists_hex_neg_block_configuration2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {L : ℕ}
    (hL : 2 ≤ L) {Bst : ℝ} (hBst : 0 ≤ Bst) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ m : ℕ, 0 < m → 48 ≤ a*m →
      2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) ≤ 1/(L:ℝ) →
      (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) →
      ∀ {n : ℕ}, 0 < n →
      Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m)))+n = (d*m)^2 →
      (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ) →
      ∀ (C : Fin n → Set (SphereD 2)) (dm : Fin n → ℝ), (∀ i, MeasurableSet (C i)) →
      Pairwise (fun i j => Disjoint (C i) (C j)) →
      (∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹) →
      (⋃ j, C j) = (hexFamilyUnion2 P)ᶜ →
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) →
      (∑ j, sphereGaussianDensityFactor2 ((d*m)^2)*(dm j)^2) ≤
        Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) →
      ∃ X : ConfigurationD 2 ((d*m)^2),
        (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(hexNegBlockConst2 s Bst/(L:ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
            2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(hexNegBlockConst2 s Bst/(L:ℝ)^2)) := by
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := hexConservativeRowFactor2_pos
  obtain ⟨ρ₁,hρ₁,_,hmacro⟩ := hexPatchFamily_mixed_defect_macroF
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := hexPatchFamily_gaussianWindow_leF hη hη1
  refine ⟨min ρ₁ ρ₃, lt_min hρ₁ hρ₃, ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep m hm hn he4 he5 he6 n hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hstrat
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i => (hv i).trans (min_le_right _ _)
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₁ := fun i => (hε i).trans (min_le_left _ _)
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₃ := fun i => (hε i).trans (min_le_right _ _)
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2) := sphereGaussianDensityFactor2_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)) :=
    (sphereGaussianScale2_pos hNpos hη).le
  -- one joint residual choice
  obtain ⟨z, hz, _, havoid, _, hjoint⟩ := exists_hex_neg_joint_residual2 hNpos hnpos hc0.le
    hp ht₀ (zero_le_one : (0:ℝ) ≤ 1) (hexFamilyNodesF2 P (a*m) hn) C hCm hCd hCmass dm hdiam
  rw [show s/2-1+2 = s/2+1 by ring] at hjoint
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hcard
  have hn0R : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hMN : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^2:ℕ):ℝ) := by linarith
  have hMK : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^2 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 2 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the residual quantities are at most `N C/L²`
  have hBcap : (((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) ≤ (L:ℝ)^12 := by
    have h := sphereGaussianBackground2_scaled_cap hNpos hη
    have h' : (((d*m)^2:ℕ):ℝ)*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) ≤ (L:ℝ) := by
      simpa only [one_div,inv_inv] using h
    exact h'.trans (by simpa only [pow_one] using
      pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 12))
  have hNB0 : 0 ≤ (((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) :=
    mul_nonneg hNR.le (sphereGaussianBackground2_nonneg _)
  have hsumdm : sphereGaussianDensityFactor2 ((d*m)^2)/(s/2+1)*∑ j, (dm j)^2 ≤
      (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1) := by
    rw [div_mul_eq_mul_div, Finset.mul_sum]
    exact div_le_div_of_nonneg_right hstrat hp2.le
  have hLpow : 1/(L:ℝ)^14 ≤ 1/(L:ℝ)^2 :=
    one_div_le_one_div_of_le (pow_pos hL0 2) (pow_le_pow_right₀ hL1 (by norm_num))
  have hn2 : (n:ℝ) ≤ 1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) :=
    hnfrac.trans (mul_le_mul_of_nonneg_right hLpow hNR.le)
  have hL14 : (L:ℝ)^14 = (L:ℝ)^2*(L:ℝ)^12 := by ring
  have hL12 : (0:ℝ) < (L:ℝ)^12 := pow_pos hL0 12
  have hc12 : 1/(L:ℝ)^14*(L:ℝ)^12 = 1/(L:ℝ)^2 := by
    rw [hL14, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hL12.ne', mul_one]
  have hnB : (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) ≤
      1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by
    calc (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
          sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))))
        ≤ (1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ))*(L:ℝ)^12 :=
          mul_le_mul hnfrac hBcap hNB0
            (mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 14).le) hNR.le)
      _ = (1/(L:ℝ)^14*(L:ℝ)^12)*(((d*m)^2:ℕ):ℝ) := by ring
      _ = 1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by rw [hc12]
  have hRbound : (n:ℝ)+(Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1)+
      (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) ≤
      (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by
    have h1 : (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1) ≤
        ((Bst+1)*(1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)))/(s/2+1) := by
      refine div_le_div_of_nonneg_right ?_ hp2.le
      have h := mul_le_mul_of_nonneg_left hn2 hBst
      linarith
    have e : (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) =
        1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)+((Bst+1)*(1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)))/(s/2+1)+
          1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by
      unfold hexNegBlockConst2
      ring
    rw [e]
    linarith
  have hcell0 : 0 ≤ cellPairSum (sphereGaussianKernel2
      (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel2_nonneg _ _ _
  have hcellN : cellPairSum (sphereGaussianKernel2
      (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z ≤
      (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by linarith
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
      (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1) (fun _ => 0) z ≤
      (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by linarith
  refine ⟨combinedConfiguration2 (hexFamilyNodesF2 P (a*m) hn) z hcard
    (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid, ?_, ?_⟩
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration2_fullScaled_le hNpos (hexFamilyNodesF2 P (a*m) hn) z
      hcard (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    have hθ : hexGaussianThetaReal2 (α*hexConservativeRowFactor2) ≤
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) :=
      hexGaussianThetaReal2_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h48 : (48:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-48/((a*m:ℕ):ℝ))^2 := by
      have h1 : 48/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h48
      have h2 : 0 ≤ 48/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-48/((a*m:ℕ):ℝ))^2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (α*hexConservativeRowFactor2) ≤ 1/(L:ℝ) :=
      (mul_le_mul_of_nonneg_left hθ (mul_nonneg (by norm_num) hfr0)).trans he4
    have hscale : sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)) ≤
        sphereGaussianScale2 ((d*m)^2) α := by
      rw [sphereGaussianScale2_eq_factor, sphereGaussianScale2_eq_factor]
      exact mul_le_mul_of_nonneg_left hα hc0.le
    have hE : Real.exp (-(sphereGaussianScale2 ((d*m)^2) α*δ^2)) ≤
        Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hscale (sq_nonneg δ)))
    have hfg := hexBlock_window_arith hNR hM0 hMN hA0 hR0 hR (Real.exp_pos _).le hE he5 hw
    have hres : cellPairSum (sphereGaussianKernel2
        (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z/(((d*m)^2:ℕ):ℝ) ≤
        hexNegBlockConst2 s Bst/(L:ℝ)^2 := by
      rw [div_le_iff₀ hNR]
      linarith
    have h2L : hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))
  · -- the macroscopic end
    intro w hw hw1
    have hPm := hexFamilyUnion2_measurable P
    have hσR : (sphereProbabilityD 2) (⋃ j, C j) =
        (n:ℝ≥0∞)*(((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
      rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
      simp [hCmass]
    have hRne : (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ ≠ 0 := by
      rw [← hCu, hσR]
      exact mul_ne_zero (by exact_mod_cast hnpos.ne')
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    have hmassR : (n:ℝ) =
        (((d*m)^2:ℕ):ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ := by
      rw [← hCu, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_comm (n:ℝ), ← mul_assoc,
        mul_inv_cancel₀ hNR.ne', one_mul]
    obtain ⟨hgint, hgval⟩ := negMacro_poly_integralS2 hp hw.le hexMacroConstA2
      (hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26))
    have hmain : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 (hexFamilyNodesF2 P (a*m) hn) z hcard
          (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid)+1)) ≤
        2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(hexMacroConstA2*α^2+
          hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α))+
        2/(((d*m)^2:ℕ):ℝ)*residualNeutralizedEnergy
          (sphereRestrictedProbability2 (hexFamilyUnion2 P)ᶜ)
          (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1)
          (fun _ => 0) z :=
      combinedConfiguration2_macroEnd_le hs hs0 hNpos
        (hexFamilyNodesF2 P (a*m) hn) z hcard (hexFamilyNodesF2_injective P hdisj (a*m) hn)
        hz havoid hPm hRne hmassR hw1
        (fun α => hexMacroConstA2*α^2+
          hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) hgint
        (fun α hα => hmacro P hv₁ hε₁ hdisj a d m hd hm hratio hn α
          ⟨hα.1, hα.2.trans (hw1.trans (by norm_num))⟩)
    rw [hgval, show s/2-1+3 = s/2+2 by ring, show s/2-1+2 = s/2+1 by ring, ← hCu] at hmain
    have hwq : 0 ≤ w^(s/2+1)/(s/2+1) := div_nonneg (Real.rpow_nonneg hw.le _) hp2.le
    have hB' : hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*(w^(s/2+1)/(s/2+1)) ≤
        1/(L:ℝ)*(w^(s/2+1)/(s/2+1)) := mul_le_mul_of_nonneg_right he6 hwq
    have h2N : 2/(((d*m)^2:ℕ):ℝ)*residualNeutralizedEnergy
        (sphereRestrictedProbability2 (⋃ j, C j))
        (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1) (fun _ => 0) z ≤
        2*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hNE (by positivity : (0:ℝ) ≤ 2/(((d*m)^2:ℕ):ℝ))
      have e : 2/(((d*m)^2:ℕ):ℝ)*((((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2)) =
          2*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
      rw [e] at h
      exact h
    linarith

/-- The explicit conditions of a negative-exponent block hold for every sufficiently large
refinement. -/
theorem hexNegBlock_conditions_eventually {L : ℕ} (hL : 2 ≤ L) (a d : ℕ)
    (ha : 0 < a) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 48 ≤ a*m ∧
      2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) ≤ 1/(L:ℝ) ∧
      (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) ∧
      hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have ham : Tendsto (fun m : ℕ => a*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^2 := fun m => by positivity
  -- the corrected fraction
  have h4 : Tendsto (fun m : ℕ => 2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
      hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((a*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp ham
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h48 : Tendsto (fun _ : ℕ => (48:ℝ)) atTop (𝓝 48) := tendsto_const_nhds
    have hx : Tendsto (fun m : ℕ => (48:ℝ)/((a*m:ℕ):ℝ)) atTop (𝓝 0) := h48.div_atTop hcast
    have h := (((hone.sub ((hone.sub hx).pow 2)).const_mul 2).mul_const
      (hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2)))
    have h0 : 2*((1:ℝ)-(1-0)^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) = 0 := by norm_num
    rw [h0] at h
    exact h
  have e4 := (tendsto_order.mp h4).2 (1/(L:ℝ)) hη
  -- the cross-patch window
  have h5 : Tendsto (fun m : ℕ => (((d*m)^2:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (sphereGaussianScale2_separated_tendsto hNt hNp hη hδ)
  have e5 := (tendsto_order.mp h5).2 (1/(L:ℝ)) hη
  -- the macroscopic gain
  have h6 : Tendsto (fun m : ℕ => (hexMacroConstB2*(d:ℝ)^2/(a:ℝ)^26)/(m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have e6 := (tendsto_order.mp h6).2 (1/(L:ℝ)) hη
  filter_upwards [eventually_ge_atTop 48, e4, e5, e6] with m hm1 hm4 hm5 hm6
  refine ⟨by omega, hm1.trans (Nat.le_mul_of_pos_left m ha), hm4.le, hm5.le, ?_⟩
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0:ℝ) < m := by linarith
  have hm0' : (m:ℝ) ≠ 0 := hm0.ne'
  have hBn := hexMacroConstB2_nonneg
  have hEq : hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) =
      (hexMacroConstB2*(d:ℝ)^2/(a:ℝ)^26)/(m:ℝ)^24 := by
    have h24 : (((d*m)^2:ℕ):ℝ) = (d:ℝ)^2*(m:ℝ)^2 := by push_cast; ring
    have h26 : ((a*m:ℕ):ℝ)^26 = (a:ℝ)^26*(m:ℝ)^24*(m:ℝ)^2 := by push_cast; ring
    rw [h24,h26,mul_div_mul_right _ _ (pow_ne_zero 2 hm0'),div_mul_eq_div_div]
    ring
  have hc0 : 0 ≤ hexMacroConstB2*(d:ℝ)^2/(a:ℝ)^26 := by positivity
  have hm24 : (m:ℝ) ≤ (m:ℝ)^24 := by
    simpa only [pow_one] using pow_le_pow_right₀ hmR (by norm_num : 1 ≤ 24)
  rw [hEq]
  exact (div_le_div_of_nonneg_left hc0 hm0 hm24).trans hm6.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a negative-exponent block configuration. -/
theorem exists_hex_neg_block2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {Bst : ℝ} (hBst : 0 ≤ Bst)
    (hstrat : HexResidualStratifiable2 Bst) {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 2 ((d*m)^2),
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
        (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(hexNegBlockConst2 s Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
          2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(hexNegBlockConst2 s Bst/(L:ℝ)^2)) := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_hex_neg_block_configuration2 hs hs0 hL hBst
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_hex_patch_family2 ρ (1/(L:ℝ)^14) hρ (one_div_pos.mpr (pow_pos hL0 14))
  obtain ⟨N₀, hN₀⟩ := hstrat P hdisj (1/(L:ℝ)^2) (one_div_pos.mpr (pow_pos hL0 2))
  refine ⟨d, hd, ?_⟩
  have hNt : Tendsto (fun m : ℕ => (d*m)^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  filter_upwards [hexNegBlock_conditions_eventually hL a d ha hd hδ,
    hNt.eventually (eventually_ge_atTop N₀)] with m hm hmN
  obtain ⟨hm0, hn, he4, he5, he6⟩ := hm
  obtain ⟨n, hnpos, hcard, hfrac, hmass⟩ :=
    hexFamilyF_residual_count P a d hd hmassP hKad m hm0 hn
  obtain ⟨C, dm, hCm, hCd, hCu, hCmassA, hdiam, hsum⟩ := hN₀ ((d*m)^2) n hmN hnpos hmass
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hσA : (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ =
      (n:ℝ≥0∞)*(((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
    have hreal : (sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
        (n:ℝ)/(((d*m)^2:ℕ):ℝ) := by
      rw [eq_div_iff hNR.ne']
      linarith
    rw [← ofReal_measureReal (measure_ne_top (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ),
      hreal, ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv]
  have hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
    intro i
    rw [hCmassA i, hσA, ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt,
      one_mul]
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^2:ℕ):ℝ) < 1/(L:ℝ)^14 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep m hm0 hn he4 he5 he6 hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hsum

/-- A sharp sequence for negative exponents, given the stratification of residual regions:
configurations of sizes tending to infinity whose normalized energy is eventually at least
`C_s - η`. -/
theorem sphere2_riesz_neg_sharp_sequence_of_stratifiable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : HexResidualStratifiable2 Bst) :
    ∃ (N : ℕ → ℕ) (X : ∀ k, ConfigurationD 2 (N k)), Tendsto N atTop atTop ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        sphereRieszCoefficientNeg2 s-η ≤ normalizedEnergyNeg2 s (X k) := by
  have hp2 : 0 < s/2+1 := by linarith
  have hp3 : 0 < s/2+2 := by linarith
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 2 ((d*m)^2),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
            2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2)) :=
    fun j => exists_hex_neg_block2 hs hs0 hBst hstrat (L := j+2) (by omega)
  choose d hd hev using hblocks
  have hpick : ∀ j : ℕ, ∃ m : ℕ, j+1 ≤ m ∧ ∃ X : ConfigurationD 2 ((d j*m)^2),
      (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
        (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
          (1+((j+2:ℕ):ℝ))*(hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
          2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2)) :=
    fun j => ((eventually_ge_atTop (j+1)).and (hev j)).exists
  choose m hmj X hW hM using hpick
  have hmpos : ∀ j, 0 < m j := fun j => lt_of_lt_of_le (Nat.succ_pos j) (hmj j)
  have hNpos : ∀ j, 0 < (d j*m j)^2 := fun j => pow_pos (Nat.mul_pos (hd j) (hmpos j)) 2
  have hNt : Tendsto (fun j : ℕ => (d j*m j)^2) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.le_succ j).trans ((hmj j).trans
      ((Nat.le_mul_of_pos_left (m j) (hd j)).trans (Nat.le_self_pow (by norm_num) _))))
      tendsto_id
  refine ⟨fun j => (d j*m j)^2, X, hNt, ?_⟩
  have hLt : Tendsto (fun j : ℕ => j+2) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right j 2) tendsto_id
  have hLR : Tendsto (fun j : ℕ => ((j+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLt
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hu : Tendsto (fun j : ℕ => 1/((j+2:ℕ):ℝ)) atTop (𝓝 0) := hone.div_atTop hLR
  -- the pointwise window
  have hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      sphereGaussianFullScaled2 α (X j) ≤ hexGaussianThetaReal2 α+ε := by
    intro α hα ε hε
    have hΦ := hexBlockWindowBound_tendsto (B := hexNegBlockConst2 s Bst) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (hexGaussianThetaReal2 α+ε) (by linarith)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with j hj1 hj2
    exact (hW j α hj2.le).trans hj1.le
  -- the macroscopic end
  have hmacro : ∀ η : ℝ, 0 < η → ∃ w : ℝ, 0 < w ∧ ∀ᶠ j in atTop,
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X j)+1)) ≤ η := by
    intro η hη
    have hA := hexMacroConstA2_nonneg
    have hden : 0 < 4*(hexMacroConstA2+1) := by linarith
    have hw0 : 0 < η*(s/2+2)/(4*(hexMacroConstA2+1)) := div_pos (mul_pos hη hp3) hden
    refine ⟨min 1 (η*(s/2+2)/(4*(hexMacroConstA2+1))), lt_min one_pos hw0, ?_⟩
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min 1 (η*(s/2+2)/(4*(hexMacroConstA2+1))) := ⟨_, rfl⟩
    rw [← hwdef]
    have hw : 0 < w := by rw [hwdef]; exact lt_min one_pos hw0
    have hw1 : w ≤ 1 := by rw [hwdef]; exact min_le_left _ _
    have hw2 : w ≤ η*(s/2+2)/(4*(hexMacroConstA2+1)) := by rw [hwdef]; exact min_le_right _ _
    have hpow3 : w^(s/2+2) ≤ w := by
      have h := Real.rpow_le_rpow_of_exponent_ge hw hw1 (by linarith : (1:ℝ) ≤ s/2+2)
      rwa [Real.rpow_one] at h
    have hpow2 : w^(s/2+1) ≤ 1 := Real.rpow_le_one hw.le hw1 hp2.le
    have hfirst : 2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))) ≤ η/2 := by
      have h1 : w^(s/2+2)/(s/2+2) ≤ η/(4*(hexMacroConstA2+1)) := by
        rw [div_le_iff₀ hp3]
        calc w^(s/2+2) ≤ w := hpow3
          _ ≤ η*(s/2+2)/(4*(hexMacroConstA2+1)) := hw2
          _ = η/(4*(hexMacroConstA2+1))*(s/2+2) := by ring
      have h2 : hexMacroConstA2*(w^(s/2+2)/(s/2+2)) ≤
          hexMacroConstA2*(η/(4*(hexMacroConstA2+1))) := mul_le_mul_of_nonneg_left h1 hA
      have h3 : hexMacroConstA2*(η/(4*(hexMacroConstA2+1))) ≤ η/4 := by
        rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
        linarith
      linarith
    have hCc : Tendsto (fun _ : ℕ => hexNegBlockConst2 s Bst) atTop
        (𝓝 (hexNegBlockConst2 s Bst)) := tendsto_const_nhds
    have hsq : Tendsto (fun j : ℕ => hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2) atTop (𝓝 0) :=
      hCc.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hLR)
    have hφ : Tendsto (fun j : ℕ => 2*(1/((j+2:ℕ):ℝ)*(1/(s/2+1)))+
        2*(hexNegBlockConst2 s Bst/((j+2:ℕ):ℝ)^2)) atTop (𝓝 (2*(0*(1/(s/2+1)))+2*0)) :=
      ((hu.mul_const _).const_mul 2).add (hsq.const_mul 2)
    have hφ0 : (2*(0*(1/(s/2+1)))+2*0 : ℝ) = 0 := by ring
    rw [hφ0] at hφ
    have e := (tendsto_order.mp hφ).2 (η/2) (half_pos hη)
    filter_upwards [e] with j hj
    have hMj := hM j w hw hw1
    have hsec : 1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)) ≤ 1/((j+2:ℕ):ℝ)*(1/(s/2+1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow2 hp2.le)
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  exact sphere2_riesz_neg_lower_of_full_profile hs hs0 hNt hNpos X hp hmacro

end SphericalRiesz
end
end
end

section

/-! Dimension-two rational sizes, density ratios and mass splitting. The all-N construction is
implemented separately; no high-dimensional gap arithmetic is included here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

def rationalSizeFloorIndex2 (d N : ℕ) : ℕ :=
  ⌊((N:ℝ) ^ (1/2:ℝ))/(d:ℝ)⌋₊

def rationalSizeFloor2 (d N : ℕ) : ℕ := (d*rationalSizeFloorIndex2 d N)^2

theorem rationalSizeFloorIndex2_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeFloorIndex2 d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (rationalSizeIndex2_argument_tendsto d hd)

theorem rationalSizeFloor2_le (d N : ℕ) (hd : 0 < d) : rationalSizeFloor2 d N ≤ N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hx : 0 ≤ ((N:ℝ) ^ (1/2:ℝ))/(d:ℝ) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hdR.le
  have hr : ((d*rationalSizeFloorIndex2 d N:ℕ):ℝ) ≤ (N:ℝ) ^ (1/2:ℝ) := by
    have h := Nat.floor_le hx
    change (rationalSizeFloorIndex2 d N:ℝ) ≤ _ at h
    have hh := (le_div_iff₀ hdR).mp h
    push_cast
    linarith
  have hpow := pow_le_pow_left₀ (by positivity) hr 2
  rw [real_second_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeFloor2_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeFloor2 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (rationalSizeIndex2_argument_tendsto d hd)).pow 2
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeFloorIndex2 d N:ℕ):ℝ)/((N:ℝ)^(1/2:ℝ)/(d:ℝ)))^2 = _
  rw [div_pow, div_pow, real_second_root_pow]
  unfold rationalSizeFloor2
  push_cast
  field_simp [hnz, hdz]

/-! ### The density ratio between two sizes -/

/-- The ratio `(N/M)^(1/1)` of the Gaussian density factors of the sizes `N` and `M`. -/
def sphereScaleRatio2 (M N : ℕ) : ℝ := ((N:ℝ)/(M:ℝ))^(1/1:ℝ)

theorem real_twelfth_root_powS2 {x : ℝ} (_hx : 0 ≤ x) : (x^(1/1:ℝ))^1 = x := by
  simp

theorem sphereScaleRatio2_pos {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    0 < sphereScaleRatio2 M N := by
  unfold sphereScaleRatio2
  exact Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hN) (by exact_mod_cast hM)) _

theorem sphereScaleRatio2_pow (M N : ℕ) : (sphereScaleRatio2 M N)^1 = (N:ℝ)/(M:ℝ) := by
  unfold sphereScaleRatio2
  exact real_twelfth_root_powS2 (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg M))

theorem sphereScaleRatio2_one_le {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    1 ≤ sphereScaleRatio2 M N := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h : (1:ℝ) ≤ (N:ℝ)/(M:ℝ) := by
    rw [le_div_iff₀ hMR, one_mul]
    exact_mod_cast hMN
  unfold sphereScaleRatio2
  exact Real.one_le_rpow h (by norm_num)

theorem sphereScaleRatio2_le_two {M N : ℕ} (hM : 0 < M) (hN2 : (N:ℝ) ≤ 2*(M:ℝ)) :
    sphereScaleRatio2 M N ≤ 2 := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h : (N:ℝ)/(M:ℝ) ≤ 2 := by
    rw [div_le_iff₀ hMR]
    exact hN2
  have h0 : 0 ≤ (N:ℝ)/(M:ℝ) := div_nonneg (Nat.cast_nonneg N) hMR.le
  unfold sphereScaleRatio2
  calc ((N:ℝ)/(M:ℝ))^(1/1:ℝ) ≤ (2:ℝ)^(1/1:ℝ) := Real.rpow_le_rpow h0 h (by norm_num)
    _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

/-- The Gaussian scale of the size `N` in terms of the size `M`. -/
theorem sphereGaussianScale2_ratio {M N : ℕ} (hM : 0 < M) (α : ℝ) :
    sphereGaussianScale2 N α = sphereGaussianScale2 M (sphereScaleRatio2 M N*α) := by
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [sphereGaussianScale2_eq_factor,sphereGaussianScale2_eq_factor,
    sphereGaussianDensityFactor2_eq_quarter,sphereGaussianDensityFactor2_eq_quarter]
  norm_num only [sphereScaleRatio2,one_div_one,Real.rpow_one]
  have hh : (M:ℝ)/4*((N:ℝ)/(M:ℝ)) = (N:ℝ)/4 := by
    rw [div_mul_div_comm,mul_comm (M:ℝ) (N:ℝ),mul_div_mul_right _ _ hMR]
  rw [← mul_assoc,hh]

theorem sphereGaussianDensityFactor2_ratio {M N : ℕ} (hM : 0 < M) :
    sphereGaussianDensityFactor2 N = sphereScaleRatio2 M N*sphereGaussianDensityFactor2 M := by
  have h := sphereGaussianScale2_ratio (N := N) hM 1
  simp only [sphereGaussianScale2_eq_factor, mul_one] at h
  rw [h]
  ring

/-- The defect of the kept points at the scale of the larger size. -/
theorem sphereGaussianDefect2_kept {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (Y : ConfigurationD 2 M) {α : ℝ} (hα : 0 ≤ α) :
    sphereGaussianDefect2 (sphereGaussianScale2 N α) (M:ℝ) Y =
      (M:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1) := by
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [sphereGaussianCenteredScaled2_add_one hM
    (mul_nonneg (sphereScaleRatio2_pos hM hN).le hα) Y, ← sphereGaussianScale2_ratio hM α,
    mul_div_cancel₀ _ hMR]

/-! ### Two densities -/

/-- Cauchy–Schwarz with two densities for a combined configuration: kept points against their
own number, added points against their own number. -/
theorem combinedConfiguration2_massSplit_le {ι : Type*} [Fintype ι] {n N : ℕ}
    (x : ι → SphereD 2) (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianDefect2 t (N:ℝ) (combinedConfiguration2 x z hcard hx hz havoid) ≤
      2*gaussianMeasureDefect t (Fintype.card ι:ℝ)
          (finitePointMeasure (fun i => (x i : AmbientD 2))) ambientSphereProbability2+
        2*gaussianMeasureDefect t (n:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 2)))
          ambientSphereProbability2 := by
  rw [sphereGaussianDefect2_eq_diffuse ht, diffuseGaussianDefect_eq_measureDefect ht]
  have hfpm : finitePointMeasure (fun i : Fin N =>
      ((combinedConfiguration2 x z hcard hx hz havoid i : SphereD 2) : AmbientD 2)) =
      finitePointMeasure (fun a : ι ⊕ Fin n => ((Sum.elim x z a : SphereD 2) : AmbientD 2)) := by
    unfold finitePointMeasure
    exact Equiv.sum_comp ((Fintype.equivFinOfCardEq
      (show Fintype.card (ι ⊕ Fin n) = N by
        rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm)
      (fun a => Measure.dirac ((Sum.elim x z a : SphereD 2) : AmbientD 2))
  have hfun : (fun a : ι ⊕ Fin n => ((Sum.elim x z a : SphereD 2) : AmbientD 2)) =
      Sum.elim (fun i => (x i : AmbientD 2)) (fun j => (z j : AmbientD 2)) := by
    funext a
    cases a <;> rfl
  have hNsum : (N:ℝ) = (Fintype.card ι:ℝ)+(n:ℝ) := by exact_mod_cast hcard.symm
  rw [hfpm, hfun, finitePointMeasure_sum_elim, hNsum]
  exact gaussianMeasureDefect_mass_add_le ht _ _ _ _ _

theorem ambientRestricted2_univ : ambientRestricted2 univ = ambientSphereProbability2 := by
  unfold ambientRestricted2 ambientSphereProbability2
  rw [Measure.restrict_univ]

/-- For `r` points against `r σ` on the whole sphere the neutralized Gaussian energy is the
ambient defect. -/
theorem wholeSphere_residualEnergy_eq_defectS2 {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (z : Fin r → SphereD 2) :
    residualNeutralizedEnergy (sphereRestrictedProbability2 univ) (sphereGaussianKernel2 t)
        (fun _ => 0) z =
      gaussianMeasureDefect t (r:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 2)))
        ambientSphereProbability2 := by
  have hR : (sphereProbabilityD 2) univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  have hmass : (r:ℝ) = (r:ℝ)*(sphereProbabilityD 2).real univ := by
    rw [probReal_univ, mul_one]
  rw [residualGaussianEnergy2_eq_defect ht z univ hR hmass, ambientRestricted2_univ]

/-- Substitution `β = l α` in a weighted integral over an initial interval. -/
theorem rpow_weighted_comp_mul_integralS2 {p l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (f : ℝ → ℝ) :
    (∫ α in Ioc (0:ℝ) w, α^p*f (l*α)) = l^(-(p+1))*∫ β in Ioc (0:ℝ) (l*w), β^p*f β := by
  have hlw : 0 ≤ l*w := mul_nonneg hl.le hw
  rw [← intervalIntegral.integral_of_le hw, ← intervalIntegral.integral_of_le hlw]
  set g : ℝ → ℝ := fun β => β^p*f β with hg
  have hpt : Set.EqOn (fun α : ℝ => α^p*f (l*α)) (fun α => l^(-p)*g (l*α)) (uIcc 0 w) := by
    intro α hα
    rw [uIcc_of_le hw] at hα
    have hα0 : 0 ≤ α := hα.1
    simp only [hg]
    rw [Real.mul_rpow hl.le hα0]
    have hll : l^(-p)*l^p = 1 := by
      rw [← Real.rpow_add hl]
      simp
    calc α^p*f (l*α) = (l^(-p)*l^p)*α^p*f (l*α) := by rw [hll]; ring
      _ = l^(-p)*(l^p*α^p*f (l*α)) := by ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left g hl.ne', mul_zero, smul_eq_mul]
  rw [show (-(p+1)) = -p+(-1) by ring, Real.rpow_add hl, Real.rpow_neg_one]
  ring

/-- The same mass-split bound with the residual kernel at the actual cutoff. -/
theorem addedConfiguration2_macroEnd_le_at_cutoff {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {M r N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (Y : ConfigurationD 2 M) (z : Fin r → SphereD 2)
    (hcard : Fintype.card (Fin M)+r = N) (hz : Function.Injective z)
    (havoid : ∀ j, z j ∉ range (⇑Y)) {w : ℝ} (hw : 0 ≤ w) :
    (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1)) ≤
      2*((sphereScaleRatio2 M N)^(-(s/2-1+1))*
        ∫ β in Ioc (0:ℝ) (sphereScaleRatio2 M N*w),
          β^(s/2-1)*(sphereGaussianCenteredScaled2 β Y+1))+
        2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
          (negMacroKernel2 (sphereGaussianDensityFactor2 N) (s/2-1) w) (fun _ => 0) z := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hMN : (M:ℝ) ≤ N := by
    have h : (Fintype.card (Fin M):ℝ)+(r:ℝ) = N := by exact_mod_cast hcard
    rw [Fintype.card_fin] at h
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hc : 0 < sphereGaussianDensityFactor2 N := sphereGaussianDensityFactor2_pos hN
  have hp : -2 < s/2-1 := by linarith
  have hl : 0 < sphereScaleRatio2 M N := sphereScaleRatio2_pos hM hN
  have hRu : (sphereProbabilityD 2) univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  have : IsProbabilityMeasure (sphereRestrictedProbability2 univ) :=
    sphereRestrictedProbability2_probability _ hRu
  obtain ⟨hNEint, hNEeq⟩ := negMacro2_residualNeutralizedEnergy_eq hc.le hp hw
    (sphereRestrictedProbability2 univ) z
  set E : ℝ → ℝ := fun α => residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
    (sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α)) (fun _ => 0) z with hE
  have hE0 : ∀ α : ℝ, 0 < α → 0 ≤ E α := by
    intro α hα
    have ht : 0 ≤ sphereGaussianDensityFactor2 N*α := mul_nonneg hc.le hα.le
    simp only [hE]
    rw [wholeSphere_residualEnergy_eq_defectS2 ht z]
    exact gaussianMeasureDefect_nonneg ht _ _ _
  -- the kept part is integrable after the substitution
  have hGint : IntegrableOn
      (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled2 β Y+1)) (Ioi 0) :=
    sphereGaussianCenteredScaled2_neg_integrable hs hs0 hM Y
  have hGl : IntegrableOn (fun α : ℝ => (sphereScaleRatio2 M N*α)^(s/2-1)*
      (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled2 β Y+1)) 0 hl).mpr
      (by rw [mul_zero]; exact hGint)
  have hKint : IntegrableOn (fun α : ℝ => α^(s/2-1)*
      (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hGl.const_mul ((sphereScaleRatio2 M N)^(-(s/2-1))))
      (fun α hα => ?_) measurableSet_Ioi
    have hα0 : (0:ℝ) < α := hα
    show (sphereScaleRatio2 M N)^(-(s/2-1))*((sphereScaleRatio2 M N*α)^(s/2-1)*
        (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)) =
      α^(s/2-1)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)
    rw [Real.mul_rpow hl.le hα0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hl,
      neg_add_cancel, Real.rpow_zero, one_mul]
  have hKintw : IntegrableOn (fun α : ℝ => α^(s/2-1)*
      (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)) (Ioc 0 w) :=
    hKint.mono_set Ioc_subset_Ioi_self
  have hpt : ∀ α ∈ Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
      (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1) ≤
      2*(α^(s/2-1)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1))+
        2/(N:ℝ)*(α^(s/2-1)*E α) := by
    intro α hα
    have hα0 : 0 < α := hα.1
    have ht : 0 ≤ sphereGaussianDensityFactor2 N*α := mul_nonneg hc.le hα0.le
    have hwα : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα0.le _
    have hF := sphereGaussianCenteredScaled2_add_one hN hα0.le
      (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)
    have hD := combinedConfiguration2_massSplit_le (⇑Y) z hcard Y.injective hz havoid ht
    have hY : gaussianMeasureDefect (sphereGaussianDensityFactor2 N*α)
        (Fintype.card (Fin M):ℝ) (finitePointMeasure (fun i => (Y i : AmbientD 2)))
        ambientSphereProbability2 =
        (M:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1) := by
      rw [Fintype.card_fin, ← diffuseGaussianDefect_eq_measureDefect ht,
        ← sphereGaussianDefect2_eq_diffuse ht, ← sphereGaussianScale2_eq_factor,
        sphereGaussianDefect2_kept hM hN Y hα0.le]
    have hres := wholeSphere_residualEnergy_eq_defectS2 ht z
    have hK0 : 0 ≤ sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1 :=
      sphereGaussianCenteredScaled2_add_one_nonneg hM (mul_nonneg hl.le hα0.le) Y
    rw [sphereGaussianScale2_eq_factor] at hF
    rw [hY, ← hres] at hD
    have hbound : sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1 ≤
        2*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)+2/(N:ℝ)*E α := by
      rw [hF, div_le_iff₀ hNR]
      have he : (2*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)+
          2/(N:ℝ)*E α)*(N:ℝ) =
          2*((N:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1))+2*E α := by
        calc (2*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)+
              2/(N:ℝ)*E α)*(N:ℝ)
            = 2*((N:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1))+
              2*E α*((N:ℝ)/(N:ℝ)) := by ring
          _ = _ := by rw [div_self hNR.ne', mul_one]
      rw [he]
      have hMK : (M:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1) ≤
          (N:ℝ)*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1) :=
        mul_le_mul_of_nonneg_right hMN hK0
      simp only [hE]
      linarith
    calc α^(s/2-1)*(sphereGaussianCenteredScaled2 α
          (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1)
        ≤ α^(s/2-1)*(2*(sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1)+
            2/(N:ℝ)*E α) := mul_le_mul_of_nonneg_left hbound hwα
      _ = _ := by ring
  have hFint : IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled2 α
      (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1)) (Ioc 0 w) :=
    (sphereGaussianCenteredScaled2_neg_integrable hs hs0 hN _).mono_set Ioc_subset_Ioi_self
  have hEint : IntegrableOn (fun α : ℝ => α^(s/2-1)*E α) (Ioc 0 w) := hNEint
  calc (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 (⇑Y) z hcard Y.injective hz havoid)+1))
      ≤ ∫ α in Ioc (0:ℝ) w, (2*(α^(s/2-1)*
          (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1))+
            2/(N:ℝ)*(α^(s/2-1)*E α)) :=
        setIntegral_mono_on hFint ((hKintw.const_mul 2).add (hEint.const_mul _))
          measurableSet_Ioc hpt
    _ = 2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*
          (sphereGaussianCenteredScaled2 (sphereScaleRatio2 M N*α) Y+1))+
          2/(N:ℝ)*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*E α) := by
        rw [integral_add (hKintw.const_mul 2) (hEint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = _ := by
        rw [rpow_weighted_comp_mul_integralS2 hl hw
          (fun β => sphereGaussianCenteredScaled2 β Y+1)]
        simp only [hE]
        rw [hNEeq]

theorem negMacro2_residual_cutoff_rescale {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p)
    (hw : 0 < w) (μ : Measure (SphereD 2)) [IsProbabilityMeasure μ] {n : ℕ}
    (z : Fin n → SphereD 2) :
    residualNeutralizedEnergy μ (negMacroKernel2 c p w) (fun _ => 0) z =
      w^(p+1)*residualNeutralizedEnergy μ (negMacroKernel2 (c*w) p 1) (fun _ => 0) z := by
  rw [(negMacro2_residualNeutralizedEnergy_eq hc hp hw.le μ z).2,
    (negMacro2_residualNeutralizedEnergy_eq (mul_nonneg hc hw.le) hp zero_le_one μ z).2]
  have hcomp : (fun β : ℝ => β^p*residualNeutralizedEnergy μ
      (sphereGaussianKernel2 (c*w*β)) (fun _ => 0) z) =
      (fun β => β^p*residualNeutralizedEnergy μ
        (sphereGaussianKernel2 (c*(w*β))) (fun _ => 0) z) := by
    funext β
    rw [mul_assoc]
  rw [hcomp,rpow_weighted_comp_mul_integralS2 hw zero_le_one
    (fun α => residualNeutralizedEnergy μ (sphereGaussianKernel2 (c*α)) (fun _ => 0) z),mul_one]
  rw [← mul_assoc,← Real.rpow_add hw]
  simp

end SphericalRiesz
end
end

section

/-! Dimension-two rational sizes, density ratios and mass splitting. The all-N construction is
implemented separately; no high-dimensional gap arithmetic is included here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

theorem sphereRieszConstNeg2_eq_pair_integral {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    sphereRieszConstNeg2 s =
      ∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  set μ := (sphereProbabilityD 2).prod (sphereProbabilityD 2) with hμ
  set ν := volume.restrict (Ioi (0:ℝ)) with hν
  set f : SphereD 2 × SphereD 2 → ℝ → ℝ :=
    fun p t => t^(s/2-1)*(sphereGaussianKernel2 t p.1 p.2-1) with hf
  have hdom1 : IntegrableOn (fun t : ℝ => 4*(t^(s/2-1)*min t 1)) (Ioi 0) := by
    apply integrableOn_Ioi_of_rpow_min_bound (C := 4) (a := s/2) (by linarith) (by linarith)
    · intro t ht
      have ht0 : (0:ℝ) < t := ht
      exact (continuousAt_const.mul ((Real.continuousAt_rpow_const t (s/2-1)
        (Or.inl ht0.ne')).mul (continuous_id.min continuous_const).continuousAt)).continuousWithinAt
    · intro t ht
      have h0 : 0 ≤ 4*(t^(s/2-1)*min t 1) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ht.le _)
          (le_min ht.le zero_le_one))
      rw [abs_of_nonneg h0]
  have hdom : Integrable (fun z : (SphereD 2 × SphereD 2) × ℝ =>
      (1:ℝ)*(4*(z.2^(s/2-1)*min z.2 1))) (μ.prod ν) :=
    Integrable.mul_prod (integrable_const (1:ℝ)) hdom1
  have hmeas : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun z : (SphereD 2 × SphereD 2) × ℝ => z.2^(s/2-1)) :=
      measurable_snd.pow_const _
    have h2 : Continuous (fun z : (SphereD 2 × SphereD 2) × ℝ =>
        Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1) := by fun_prop
    exact h1.mul h2.measurable
  have hpos : ∀ᵐ z ∂(μ.prod ν), z.2 ∈ Ioi (0:ℝ) :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd)
      (ae_restrict_mem measurableSet_Ioi)
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hpos] with z hz
    have ht0 : (0:ℝ) < z.2 := hz
    have hd := sphere2_dist_le_two z.1.1 z.1.2
    have hd0 : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
    obtain ⟨hb1, hb2⟩ := one_sub_exp_neg_bounds
      (mul_nonneg ht0.le (sq_nonneg (dist z.1.1 z.1.2)))
    have hw : 0 ≤ z.2^(s/2-1) := Real.rpow_nonneg ht0.le _
    have hd2 : (dist z.1.1 z.1.2)^2 ≤ 4 := by nlinarith
    have hm : min (z.2*(dist z.1.1 z.1.2)^2) 1 ≤ 4*min z.2 1 := by
      rcases le_total z.2 1 with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hd2 ht0.le])
      · rw [min_eq_right h]
        linarith [min_le_right (z.2*(dist z.1.1 z.1.2)^2) 1]
    change ‖z.2^(s/2-1)*(Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1)‖ ≤
      1*(4*(z.2^(s/2-1)*min z.2 1))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub,
      one_mul]
    calc z.2^(s/2-1)*(1-Real.exp (-(z.2*(dist z.1.1 z.1.2)^2)))
        ≤ z.2^(s/2-1)*(4*min z.2 1) := mul_le_mul_of_nonneg_left (hb2.trans hm) hw
      _ = 4*(z.2^(s/2-1)*min z.2 1) := by ring
  have hswap := integral_integral_swap hint
  have hleft : (∫ p, (∫ t, f p t ∂ν) ∂μ) =
      Real.Gamma (s/2)*∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    exact (sphereGaussianPair2_mellin_neg hs hs0 p.1 p.2).2
  have hright : (∫ t, (∫ p, f p t ∂μ) ∂ν) =
      ∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianBackground2 t-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    simp only [hf]
    rw [integral_const_mul, integral_sub (sphereGaussianKernel2_pair_integrable ht0)
      (integrable_const (1:ℝ))]
    simp [sphereGaussianBackground2]
  rw [hleft, hright] at hswap
  unfold sphereRieszConstNeg2
  rw [← hswap]
  field_simp


end SphericalRiesz
end
end

section

/-! Control the triangular theta profile near zero when its argument is slightly distorted.
This is needed for the dimension-two all-N construction with a shrinking macro cutoff. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace SphericalRiesz

theorem hexGaussianThetaReal2_antitone_scaleS2 {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    hexGaussianThetaReal2 β ≤ hexGaussianThetaReal2 α := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hsα := (Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hα)).summable
  have hsβ := (Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hβ)).summable
  apply hsβ.tsum_le_tsum _ hsα
  intro x
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ Real.pi_pos.le)
    (sq_nonneg ‖(x : HexAmbient)‖)
  linarith

theorem hexGaussianThetaReal2_inverseS2 {α : ℝ} (hα : 0 < α) :
    hexGaussianThetaReal2 α⁻¹ = α*hexGaussianThetaReal2 α := by
  have h := hexThetaImag_transform hα
  rw [hexThetaImag_eq_real hα,hexThetaImag_eq_real (inv_pos.mpr hα)] at h
  exact_mod_cast h

theorem hexGaussianThetaReal2_small_defect_scaleS2 {α b : ℝ} (hα : 0 < α)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    hexGaussianThetaReal2 (α*b)-(α*b)⁻¹ ≤ (hexGaussianThetaReal2 α-α⁻¹)/b := by
  have hab : 0 < α*b := mul_pos hα hb
  have harg : α⁻¹ ≤ (α*b)⁻¹ := inv_anti₀ hab (by nlinarith)
  have hθ := hexGaussianThetaReal2_antitone_scaleS2 (inv_pos.mpr hα) harg
  rw [hexGaussianThetaReal2_inverseS2 hab,hexGaussianThetaReal2_inverseS2 hα] at hθ
  have hbase : b*hexGaussianThetaReal2 (α*b) ≤ hexGaussianThetaReal2 α := by
    nlinarith
  have hinv : b*(α*b)⁻¹ = α⁻¹ := by field_simp
  apply (le_div_iff₀ hb).mpr
  nlinarith

theorem hexGaussianThetaReal2_window_small_boundS2 {α T : ℝ} (hα : 0 < α) (hT : 2 ≤ T) :
    (1+1/T)^2*hexGaussianThetaReal2 (α*(1-1/T)^2)-α⁻¹ ≤
      16*(hexGaussianThetaReal2 α-α⁻¹)+16/(T*α) := by
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < 1/T := by positivity
  have hu2 : 1/T ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) hT)
  let b : ℝ := (1-1/T)^2
  let A : ℝ := (1+1/T)^2
  have hb0 : 0 < b := by dsimp [b]; exact sq_pos_of_pos (by linarith)
  have hbquarter : 1/4 ≤ b := by dsimp [b]; nlinarith
  have hb1 : b ≤ 1 := by dsimp [b]; nlinarith
  have hA0 : 0 ≤ A := sq_nonneg _
  have hA4 : A ≤ 4 := by dsimp [A]; nlinarith
  have hAb : A-b = 4/T := by dsimp [A,b]; ring
  have hratio : A/b ≤ 16 := (div_le_iff₀ hb0).mpr (by nlinarith)
  have hdensity : A/b-1 ≤ 16/T := by
    rw [div_sub_one hb0.ne',div_le_div_iff₀ hb0 hT0,hAb]
    have hmul := mul_le_mul_of_nonneg_left hbquarter (show 0 ≤ 16/T by positivity)
    field_simp at hmul ⊢
    nlinarith
  have hprof := hexGaussianThetaReal2_small_defect_scaleS2 hα hb0 hb1
  have hψ0 : 0 ≤ hexGaussianThetaReal2 α-α⁻¹ :=
    sub_nonneg.mpr (hexGaussianThetaReal2_ge_inv_pow hα)
  have heq : A*hexGaussianThetaReal2 (α*b)-α⁻¹ =
      A*(hexGaussianThetaReal2 (α*b)-(α*b)⁻¹)+(A/b-1)*α⁻¹ := by
    field_simp
    ring
  change A*hexGaussianThetaReal2 (α*b)-α⁻¹ ≤ _
  rw [heq]
  calc A*(hexGaussianThetaReal2 (α*b)-(α*b)⁻¹)+(A/b-1)*α⁻¹
      ≤ A*((hexGaussianThetaReal2 α-α⁻¹)/b)+(A/b-1)*α⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left hprof hA0) le_rfl
    _ = (A/b)*(hexGaussianThetaReal2 α-α⁻¹)+(A/b-1)*α⁻¹ := by ring
    _ ≤ 16*(hexGaussianThetaReal2 α-α⁻¹)+(16/T)*α⁻¹ := add_le_add
      (mul_le_mul_of_nonneg_right hratio hψ0)
      (mul_le_mul_of_nonneg_right hdensity (inv_nonneg.mpr hα.le))
    _ = _ := by ring

end SphericalRiesz
end
end

section

/-! Integrating a Gaussian window above a shrinking cutoff.
The reference part is integrable at zero; the density and additive errors are paid only on
the interval above the cutoff, where their explicit power integrals are finite. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

theorem sphereGaussianBackground2_scaled_lowerS2 {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) :
    α⁻¹-1/((N:ℝ)*α^2) ≤ (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have ht := sphereGaussianScale2_pos hN hα
  have h := mul_le_mul_of_nonneg_left (sphereGaussianBackground2_lower ht) hNR.le
  have heq : (N:ℝ)*((1/4:ℝ)/sphereGaussianScale2 N α-
      (1/16:ℝ)/(sphereGaussianScale2 N α)^2) = α⁻¹-1/((N:ℝ)*α^2) := by
    rw [sphereGaussianScale2_eq_factor,sphereGaussianDensityFactor2_eq_quarter]
    field_simp [hNR.ne',hα.ne']
    ring
  rwa [heq] at h

theorem sphereGaussianCenteredScaled2_small_windowS2 {N L : ℕ} (hN : 0 < N)
    (hL : 2 ≤ L) (hsize : (L:ℝ)^6 ≤ (N:ℝ)) (X : ConfigurationD 2 N)
    {α D : ℝ} (hα : 1/(L:ℝ) ≤ α)
    (hwindow : sphereGaussianFullScaled2 α X ≤
      (1+1/(L:ℝ)^3)^2*hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+D/(L:ℝ)^3) :
    sphereGaussianCenteredScaled2 α X+1 ≤
      16*(hexGaussianThetaReal2 α-α⁻¹)+16/((L:ℝ)^3*α)+(D+1)/(L:ℝ)^3 := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hα0 : 0 < α := (one_div_pos.mpr hL0).trans_le hα
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hT : (2:ℝ) ≤ (L:ℝ)^3 := hLR.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 3))
  have hθ := hexGaussianThetaReal2_window_small_boundS2 hα0 hT
  have hbg := sphereGaussianBackground2_scaled_lowerS2 hN hα0
  have hαL : 1 ≤ (L:ℝ)*α := by
    have h := (div_le_iff₀ hL0).mp hα
    nlinarith
  have hden : (L:ℝ)^3 ≤ (N:ℝ)*α^2 := by
    calc (L:ℝ)^3 ≤ (L:ℝ)^4 := pow_le_pow_right₀ hL1 (by norm_num : 3 ≤ 4)
      _ ≤ (L:ℝ)^4*((L:ℝ)*α)^2 := by
        have hh : (1:ℝ) ≤ ((L:ℝ)*α)^2 := one_le_pow₀ hαL
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
          (show 0 ≤ (L:ℝ)^4 by positivity)
      _ = (L:ℝ)^6*α^2 := by ring
      _ ≤ (N:ℝ)*α^2 := mul_le_mul_of_nonneg_right hsize (sq_nonneg _)
  have herr : 1/((N:ℝ)*α^2) ≤ 1/(L:ℝ)^3 :=
    one_div_le_one_div_of_le (by positivity) hden
  have heq : sphereGaussianCenteredScaled2 α X+1 =
      sphereGaussianFullScaled2 α X-(N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) := by
    unfold sphereGaussianCenteredScaled2 sphereGaussianFullScaled2
    ring
  rw [heq]
  have hrest : D/(L:ℝ)^3+1/(L:ℝ)^3 = (D+1)/(L:ℝ)^3 := by ring
  rw [← hrest]
  linarith

/-- An integrable majorant on the interval above the cutoff pays for the middle part. -/
theorem initial_integral_le_cutoff_add_majorantS2 {f g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : IntegrableOn f (Ioc 0 b))
    (hg : IntegrableOn g (Ioc 0 b)) (hg0 : ∀ α ∈ Ioc 0 b, 0 ≤ g α)
    (hfg : ∀ α ∈ Ioc a b, f α ≤ g α) :
    (∫ α in Ioc (0:ℝ) b, f α) ≤ (∫ α in Ioc (0:ℝ) a, f α)+∫ α in Ioc (0:ℝ) b, g α := by
  have hsub : Ioc a b ⊆ Ioc (0:ℝ) b := Ioc_subset_Ioc_left ha.le
  have hm := setIntegral_mono_on (hf.mono_set hsub) (hg.mono_set hsub) measurableSet_Ioc hfg
  have hg' : (∫ α in Ioc a b, g α) ≤ ∫ α in Ioc (0:ℝ) b, g α := by
    apply setIntegral_mono_set hg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact hg0 α hα
    · exact hsub.eventuallyLE
  have heq : (∫ α in Ioc (0:ℝ) b, f α) =
      (∫ α in Ioc (0:ℝ) a, f α)+(∫ α in Ioc a b, f α) := by
    conv_lhs => rw [← Ioc_union_Ioc_eq_Ioc ha.le hab]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hf.mono_set (Ioc_subset_Ioc_right hab)) (hf.mono_set hsub)
  rw [heq]
  linarith

/-- The window errors are bounded by positive powers of the scale above `1/L`. -/
theorem sphereGaussianCenteredScaled2_cutoff_majorantS2 {N L : ℕ}
    (hN : 0 < N) (hL : 2 ≤ L) (hsize : (L:ℝ)^6 ≤ N) (X : ConfigurationD 2 N)
    {α D : ℝ} (hD : 0 ≤ D) (hα : 1/(L:ℝ) ≤ α)
    (hwindow : sphereGaussianFullScaled2 α X ≤
      (1+1/(L:ℝ)^3)^2*hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+D/(L:ℝ)^3) :
    sphereGaussianCenteredScaled2 α X+1 ≤
      16*(hexGaussianThetaReal2 α-α⁻¹)+16*α^2+(D+1)*α^3 := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hα0 : 0 < α := (one_div_pos.mpr hL0).trans_le hα
  have hi : 1/(L:ℝ)^3 ≤ α^3 := by
    simpa only [div_pow,one_pow] using pow_le_pow_left₀ (by positivity) hα 3
  have hdiv : 16/((L:ℝ)^3*α) ≤ 16*α^2 := by
    rw [← div_div,div_le_iff₀ hα0]
    have hh := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 16)
    have heq : 16*α^2*α = 16*α^3 := by ring
    rw [heq]
    simpa only [mul_one_div] using hh
  have hadd : (D+1)/(L:ℝ)^3 ≤ (D+1)*α^3 := by
    have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ D+1 by linarith)
    simpa only [mul_one_div] using h
  exact (sphereGaussianCenteredScaled2_small_windowS2 hN hL hsize X hα hwindow).trans
    (add_le_add (add_le_add le_rfl hdiv) hadd)

/-- A vanishing initial interval and the window imply the fixed-cutoff hypothesis of the
negative Mellin transfer. The majorant is integrable at zero in the full range `-2 < s < 0`. -/
theorem sphere2_neg_macro_of_shrinking_cutoffS2 {s D : ℝ} (hs : -2 < s) (hs0 : s < 0)
    (hD : 0 ≤ D) {L N : ℕ → ℕ} (hLt : Tendsto L atTop atTop)
    (hL : ∀ k, 2 ≤ L k) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 2 (N k)) (hsize : ∀ k, (L k:ℝ)^6 ≤ N k)
    (hwindow : ∀ k α, 1/(L k:ℝ) ≤ α → sphereGaussianFullScaled2 α (X k) ≤
      (1+1/(L k:ℝ)^3)^2*hexGaussianThetaReal2 (α*(1-1/(L k:ℝ)^3)^2)+D/(L k:ℝ)^3)
    {e : ℕ → ℝ} (het : Tendsto e atTop (𝓝 0))
    (hcut : ∀ k, (∫ α in Ioc (0:ℝ) (1/(L k:ℝ)),
      α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤ e k) :
    ∀ η : ℝ, 0 < η → ∃ w : ℝ, 0 < w ∧ ∀ᶠ k in atTop,
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤ η := by
  let g : ℝ → ℝ := fun α => 16*hexGaussianRieszProfileNeg2 s α+
    16*α^(s/2+1)+(D+1)*α^(s/2+2)
  have hg : IntegrableOn g (Ioc 0 1) := by
    have h1 : IntegrableOn (hexGaussianRieszProfileNeg2 s) (Ioc 0 1) :=
      (hexGaussianRieszProfileNeg2_integrable hs0).mono_set Ioc_subset_Ioi_self
    have h2 : IntegrableOn (fun α : ℝ => α^(s/2+1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have h3 : IntegrableOn (fun α : ℝ => α^(s/2+2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    exact ((h1.const_mul 16).add (h2.const_mul 16)).add (h3.const_mul (D+1))
  have hg0 : ∀ α : ℝ, 0 < α → 0 ≤ g α := by
    intro α hα
    dsimp [g,hexGaussianRieszProfileNeg2]
    have hψ := sub_nonneg.mpr (hexGaussianThetaReal2_ge_inv_pow hα)
    positivity
  intro η hη
  obtain ⟨j,hj⟩ := ((tendsto_order.mp (tendsto_setIntegral_Ioc_zero_inv hg)).2
    (η/2) (half_pos hη)).exists
  let w : ℝ := 1/((j:ℝ)+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    apply (div_le_one (show (0:ℝ) < (j:ℝ)+1 by positivity)).mpr
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have hu : Tendsto (fun k => 1/(L k:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
  refine ⟨w,hw,?_⟩
  filter_upwards [(tendsto_order.mp hu).2 w hw,
    (tendsto_order.mp het).2 (η/2) (half_pos hη)] with k hk hk'
  have hL0 : (0:ℝ) < L k := by exact_mod_cast (by have := hL k; omega : 0 < L k)
  have ha : (0:ℝ) < 1/(L k:ℝ) := by positivity
  have hf := (sphereGaussianCenteredScaled2_neg_integrable hs hs0 (hN k) (X k)).mono_set
    (show Ioc 0 w ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hgw := hg.mono_set (Ioc_subset_Ioc_right hw1)
  have hbound := initial_integral_le_cutoff_add_majorantS2 ha hk.le hf hgw
    (fun α hα => hg0 α hα.1) (fun α hα => ?_)
  · have hcutk := hcut k
    change (∫ α in Ioc (0:ℝ) w, g α) < η/2 at hj
    linarith
  · have hα0 : 0 < α := ha.trans hα.1
    have hh := mul_le_mul_of_nonneg_left
      (sphereGaussianCenteredScaled2_cutoff_majorantS2 (hN k) (hL k) (hsize k) (X k)
        hD hα.1.le (hwindow k α hα.1.le)) (Real.rpow_nonneg hα0.le (s/2-1))
    have heq : α^(s/2-1)*(16*(hexGaussianThetaReal2 α-α⁻¹)+16*α^2+(D+1)*α^3) = g α := by
      dsimp [g,hexGaussianRieszProfileNeg2]
      rw [show s/2+1 = (s/2-1)+2 by ring,show s/2+2 = (s/2-1)+3 by ring,
        Real.rpow_add hα0,Real.rpow_add hα0]
      norm_num only [Real.rpow_ofNat]
      ring
    exact hh.trans_eq heq

end SphericalRiesz
end
end

section

/-! The added points in dimension two: select the Gaussian window jointly with a
macroscopic kernel at the shrinking cutoff `1/L`. The selector is used at density `c_N/L`
with Gaussian weight `L^5`; this replaces the false high-dimensional gap estimate. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz

theorem exists_hex_neg_added_cutoff_nodes2 {s : ℝ} (hs : -2 < s) (_hs0 : s < 0)
    {Bst : ℝ} (_hBst : 0 ≤ Bst) (hsph : SphereStratifiable2 Bst)
    {L N r : ℕ} (hL : 2 ≤ L) (hN : 0 < N) (hr : 0 < r)
    (hrN : (r:ℝ) ≤ (N:ℝ)/(L:ℝ)^14)
    {ι : Type*} [Fintype ι] (Y : ι → SphereD 2) :
    ∃ z : Fin r → SphereD 2, Function.Injective z ∧ (∀ j, z j ∉ range Y) ∧
      cellPairSum (sphereGaussianKernel2 (sphereGaussianScale2 N (1/(L:ℝ)))) z/(N:ℝ) ≤
        hexNegBlockConst2 s Bst/(L:ℝ)^6 ∧
      residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
        (negMacroKernel2 (sphereGaussianDensityFactor2 N) (s/2-1) (1/(L:ℝ))) (fun _ => 0) z/(N:ℝ) ≤
        hexNegBlockConst2 s Bst*(L:ℝ)^(-(s/2+1)) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hw : (0:ℝ) < 1/(L:ℝ) := by positivity
  have hc := sphereGaussianDensityFactor2_pos hN
  obtain ⟨Q,dm,hQm,hQd,hQu,hQmass,hQdiam,hQcost⟩ := hsph r hr
  have hQmass' : ∀ j, (sphereProbabilityD 2) (Q j) = (r:ℝ≥0∞)⁻¹ := by
    intro j
    simpa only [measure_univ,one_div] using hQmass j
  have hsum : ∑ j, (dm j)^2 ≤ 4*Bst := by
    rw [← Finset.mul_sum,sphereGaussianDensityFactor2_eq_quarter] at hQcost
    nlinarith
  let c : ℝ := sphereGaussianDensityFactor2 N/(L:ℝ)
  let t : ℝ := sphereGaussianScale2 N (1/(L:ℝ))
  have hct : c = t := by dsimp only [t,c]; rw [sphereGaussianScale2_eq_factor]; ring
  obtain ⟨z,hzinj,hzQ,hzY,hNE0,hJoint⟩ := exists_hex_neg_joint_residual2 hr hr
    (c := c) (p := s/2-1) (t₀ := t) (w₃ := (L:ℝ)^5)
    (by dsimp [c]; positivity) hp (by rw [← hct]; dsimp [c]; positivity)
    (by positivity) Y Q hQm hQd hQmass' dm hQdiam
  rw [hQu] at hNE0 hJoint
  have hcost : c/(s/2-1+2)*∑ j, (dm j)^2 ≤ Bst*(N:ℝ)/((L:ℝ)*(s/2+1)) := by
    rw [show s/2-1+2 = s/2+1 by ring]
    calc c/(s/2+1)*∑ j, (dm j)^2 ≤ c/(s/2+1)*(4*Bst) :=
          mul_le_mul_of_nonneg_left hsum (by dsimp [c]; positivity)
      _ = _ := by dsimp [c]; rw [sphereGaussianDensityFactor2_eq_quarter]; field_simp
  have hrL6 : (r:ℝ)*(L:ℝ)^6 ≤ (N:ℝ)/(L:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hrN (show 0 ≤ (L:ℝ)^6 by positivity)
    have heq : ((N:ℝ)/(L:ℝ)^14)*(L:ℝ)^6 = (N:ℝ)/(L:ℝ)^8 := by field_simp
    rw [heq] at hmul
    exact hmul.trans (div_le_div_of_nonneg_left hNR.le hL0
      (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 8)))
  have hrL5 : (r:ℝ)*(L:ℝ)^5 ≤ (N:ℝ)/(L:ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num : 5 ≤ 6)) hrR.le).trans hrL6
  have hrleN : (r:ℝ) ≤ N := by
    have hLp : 1 ≤ (L:ℝ)^14 := one_le_pow₀ hL1
    exact hrN.trans (div_le_self hNR.le hLp)
  have hBcap : (N:ℝ)*sphereGaussianBackground2 t ≤ (L:ℝ) := by
    have h := sphereGaussianBackground2_scaled_cap hN hw
    simpa only [t,pow_one,one_div,inv_inv] using h
  have hbg0 := sphereGaussianBackground2_nonneg t
  have hbgcost : (L:ℝ)^5*((r:ℝ)*((r:ℝ)*sphereGaussianBackground2 t)) ≤ (N:ℝ)/(L:ℝ) := by
    calc (L:ℝ)^5*((r:ℝ)*((r:ℝ)*sphereGaussianBackground2 t))
        ≤ (L:ℝ)^5*((r:ℝ)*((N:ℝ)*sphereGaussianBackground2 t)) := by gcongr
      _ ≤ (L:ℝ)^5*((r:ℝ)*(L:ℝ)) := by gcongr
      _ = (r:ℝ)*(L:ℝ)^6 := by ring
      _ ≤ _ := hrL6
  have hbudget : (r:ℝ)*(L:ℝ)^5+c/(s/2-1+2)*∑ j, (dm j)^2+
      (L:ℝ)^5*((r:ℝ)*((r:ℝ)*sphereGaussianBackground2 t)) ≤
      (N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ) := by
    have hcalc : (N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ) =
        2*((N:ℝ)/(L:ℝ))+(Bst+1)*(N:ℝ)/((L:ℝ)*(s/2+1)) := by
      unfold hexNegBlockConst2
      field_simp [hL0.ne',hp2.ne']
    rw [hcalc]
    have hextra : Bst*(N:ℝ)/((L:ℝ)*(s/2+1)) ≤
        (Bst+1)*(N:ℝ)/((L:ℝ)*(s/2+1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith : Bst ≤ Bst+1) hNR.le
    calc (r:ℝ)*(L:ℝ)^5+c/(s/2-1+2)*∑ j, (dm j)^2+
        (L:ℝ)^5*((r:ℝ)*((r:ℝ)*sphereGaussianBackground2 t))
        ≤ (N:ℝ)/(L:ℝ)+Bst*(N:ℝ)/((L:ℝ)*(s/2+1))+(N:ℝ)/(L:ℝ) :=
          add_le_add (add_le_add hrL5 hcost) hbgcost
      _ = 2*((N:ℝ)/(L:ℝ))+Bst*(N:ℝ)/((L:ℝ)*(s/2+1)) := by ring
      _ ≤ _ := add_le_add le_rfl hextra
  have hJoint' : residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
      (negMacroKernel2 c (s/2-1) 1) (fun _ => 0) z+
      (L:ℝ)^5*cellPairSum (sphereGaussianKernel2 t) z ≤
      (r:ℝ)*(L:ℝ)^5+c/(s/2-1+2)*∑ j, (dm j)^2+
      (L:ℝ)^5*((r:ℝ)*((r:ℝ)*sphereGaussianBackground2 t)) := by
    nlinarith only [hJoint]
  have hJ := hJoint'.trans hbudget
  have hraw0 : 0 ≤ cellPairSum (sphereGaussianKernel2 t) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel2_nonneg _ _ _
  have hraw : cellPairSum (sphereGaussianKernel2 t) z ≤
      (N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ)^6 := by
    have hpos : 0 < (L:ℝ)^5 := by positivity
    have hbound : (L:ℝ)^5*cellPairSum (sphereGaussianKernel2 t) z ≤
        (N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ) := by linarith only [hJ,hNE0]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^6)).mpr
    have hh := mul_le_mul_of_nonneg_right hbound hL0.le
    have heq : ((L:ℝ)^5*cellPairSum (sphereGaussianKernel2 t) z)*(L:ℝ) =
        cellPairSum (sphereGaussianKernel2 t) z*(L:ℝ)^6 := by ring
    rw [heq,div_mul_cancel₀ _ hL0.ne'] at hh
    exact hh
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
      (negMacroKernel2 c (s/2-1) 1) (fun _ => 0) z ≤
      (N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ) := by
    have ht0 : 0 ≤ (L:ℝ)^5*cellPairSum (sphereGaussianKernel2 t) z := by positivity
    linarith only [hJ,ht0]
  refine ⟨z,hzinj,hzY,?_,?_⟩
  · rw [div_le_iff₀ hNR]
    exact hraw.trans_eq (by ring)
  · have hR : (sphereProbabilityD 2) univ ≠ 0 := by simp
    have : IsProbabilityMeasure (sphereRestrictedProbability2 univ) :=
      sphereRestrictedProbability2_probability _ hR
    rw [negMacro2_residual_cutoff_rescale hc.le hp hw]
    have hceq : sphereGaussianDensityFactor2 N*(1/(L:ℝ)) = c := by dsimp [c]; ring
    rw [hceq]
    have hpw : (1/(L:ℝ))^(s/2-1+1) = (L:ℝ)^(-(s/2)) := by
      rw [show s/2-1+1 = s/2 by ring,one_div,Real.inv_rpow hL0.le]
      exact (Real.rpow_neg hL0.le (s/2)).symm
    rw [hpw]
    have hmul := mul_le_mul_of_nonneg_left hNE (Real.rpow_nonneg hL0.le (-(s/2)))
    have heq : (L:ℝ)^(-(s/2))*((N:ℝ)*hexNegBlockConst2 s Bst/(L:ℝ)) =
        (N:ℝ)*(hexNegBlockConst2 s Bst*(L:ℝ)^(-(s/2+1))) := by
      rw [show -(s/2+1) = -(s/2)+(-1) by ring,Real.rpow_add hL0,Real.rpow_neg_one]
      ring
    rw [heq] at hmul
    rw [div_le_iff₀ hNR]
    simpa only [mul_comm] using hmul

end SphericalRiesz
end
end

section

/-! Sharp negative Riesz asymptotics on S² at every sufficiently large size.
The added points use the cutoff `1/L`, while the foreground is built at tolerance `L³`.
This separates the dimension-two density error from the Gaussian window error. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- The geometric construction supplies the residual hypothesis of the rational blocks. -/
theorem hexResidualStratifiable2_of_neg {B : ℝ}
    (h : ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i)) (smallHexSpherePatch2 (P j))) →
      NegStratifiable2 (⋃ i, smallHexSpherePatch2 (P i))ᶜ B) :
    HexResidualStratifiable2 B := by
  intro K P hdisj ε hε
  exact h P hdisj ε hε

def hexNegAllNCutoffError2 (s B L : ℝ) : ℝ :=
  (16*hexMacroConstA2/(s/2+2)+8/(s/2+1)+8*hexNegBlockConst2 s B)/L+
    2*hexNegBlockConst2 s B*L^(-(s/2+1))

theorem hexNegBlockConst2_nonnegS2 {s B : ℝ} (hs : -2 < s) (hB : 0 ≤ B) :
    0 ≤ hexNegBlockConst2 s B := by
  unfold hexNegBlockConst2
  have hden : 0 < s/2+1 := by linarith
  positivity

/-- Combining the two windows costs only a constant times `1/T`. -/
theorem hexNegAllN_window_arithmeticS2 {T C θ : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C) :
    (1+1/T)*((1+1/T)*(θ+2/T)+(1+T)*(C/T^2))+(1+T)*(C/T^2) ≤
      (1+1/T)^2*θ+(8+6*C)/T := by
  have hT0 : 0 < T := by linarith
  have hu0 : 0 ≤ 1/T := by positivity
  have hu1 : 1/T ≤ 1 := (div_le_one hT0).mpr hT
  have heq : (1+1/T)*((1+1/T)*(θ+2/T)+(1+T)*(C/T^2))+(1+T)*(C/T^2)-
      (1+1/T)^2*θ = (2*(1+1/T)^2+C*((1+1/T)^2+(1+1/T)))/T := by
    field_simp
    ring
  have hu2 : (1+1/T)^2 ≤ 4 := by nlinarith
  have hc := mul_le_mul_of_nonneg_left (show (1+1/T)^2+(1+1/T) ≤ 6 by nlinarith) hC
  have hh : (2*(1+1/T)^2+C*((1+1/T)^2+(1+1/T)))/T ≤ (8+6*C)/T :=
    div_le_div_of_nonneg_right (by nlinarith) hT0.le
  linarith

/-- Adding points preserves a sharp window and gives a vanishing shrinking-cutoff integral. -/
theorem exists_added_configuration2_cutoff {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {B : ℝ} (hB : 0 ≤ B) (hsph : SphereStratifiable2 B) {L M r N : ℕ}
    (hL : 2 ≤ L) (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hcard : M+r = N) (hrN : (r:ℝ) ≤ (N:ℝ)/(L:ℝ)^14)
    (hN2 : (N:ℝ) ≤ 2*(M:ℝ)) (Y : ConfigurationD 2 M)
    (hYW : ∀ α : ℝ, 1/(L:ℝ)^3 ≤ α → sphereGaussianFullScaled2 α Y ≤
      (1+1/(L:ℝ)^3)*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+2/(L:ℝ)^3)+
        (1+(L:ℝ)^3)*(hexNegBlockConst2 s B/(L:ℝ)^6))
    (hYM : ∀ w : ℝ, 0 < w → w ≤ 1 →
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α Y+1)) ≤
        2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)^3*(w^(s/2+1)/(s/2+1)))+
          2*(hexNegBlockConst2 s B/(L:ℝ)^6)) :
    ∃ X : ConfigurationD 2 N,
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
        (1+1/(L:ℝ)^3)^2*hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+
          (8+6*hexNegBlockConst2 s B)/(L:ℝ)^3) ∧
      (∫ α in Ioc (0:ℝ) (1/(L:ℝ)), α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
        hexNegAllNCutoffError2 s B (L:ℝ) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hMN : M ≤ N := by omega
  have hC := hexNegBlockConst2_nonnegS2 hs hB
  have hA := hexMacroConstA2_nonneg
  have hp2 : 0 < s/2+1 := by linarith
  have hp3 : 0 < s/2+2 := by linarith
  have hu : 0 < 1/(L:ℝ) := by positivity
  have hu3 : 0 < 1/(L:ℝ)^3 := by positivity
  have hT1 : (1:ℝ) ≤ (L:ℝ)^3 := one_le_pow₀ hL1
  have hL3 : (L:ℝ) ≤ (L:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 3)
  have hL6 : (L:ℝ) ≤ (L:ℝ)^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 6)
  obtain ⟨z,hz,havoid,hraw,hNE⟩ := exists_hex_neg_added_cutoff_nodes2 hs hs0 hB hsph
    hL hN hr hrN (⇑Y)
  have hcard' : Fintype.card (Fin M)+r = N := by simpa using hcard
  let X := combinedConfiguration2 (⇑Y) z hcard' Y.injective hz havoid
  have hl0 := sphereScaleRatio2_pos hM hN
  have hl1 := sphereScaleRatio2_one_le hM hMN
  have hl2 := sphereScaleRatio2_le_two hM hN2
  refine ⟨X,?_,?_⟩
  · intro α hα
    have hα0 : 0 < α := hu.trans_le hα
    have hlα : α ≤ sphereScaleRatio2 M N*α := by nlinarith
    have hαT : 1/(L:ℝ)^3 ≤ sphereScaleRatio2 M N*α :=
      (one_div_le_one_div_of_le hL0 hL3).trans (hα.trans hlα)
    have hY := hYW _ hαT
    have hθ := hexGaussianThetaReal2_antitone_scaleS2
      (show 0 < α*(1-1/(L:ℝ)^3)^2 by
        apply mul_pos hα0
        exact sq_pos_of_pos (by
          have hhalf : 1/(L:ℝ)^3 ≤ 1/2 :=
            one_div_le_one_div_of_le (by norm_num) (hLR.trans hL3)
          linarith))
      (mul_le_mul_of_nonneg_right hlα (sq_nonneg _))
    have hfull := combinedConfiguration2_fullScaled_le hN (⇑Y) z hcard' Y.injective hz havoid
      hu.le hα hu3
    rw [one_div_one_div] at hfull
    have hkept : (∑ a, ∑ b, sphereGaussianKernel2 (sphereGaussianScale2 N α) (Y a) (Y b))/(N:ℝ) ≤
        sphereGaussianFullScaled2 (sphereScaleRatio2 M N*α) Y := by
      rw [sphereGaussianScale2_ratio hM]
      unfold sphereGaussianFullScaled2
      exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sphereGaussianKernel2_nonneg _ _ _) hMR
        (by exact_mod_cast hMN)
    have hybound : sphereGaussianFullScaled2 (sphereScaleRatio2 M N*α) Y ≤
        (1+1/(L:ℝ)^3)*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+2/(L:ℝ)^3)+
          (1+(L:ℝ)^3)*(hexNegBlockConst2 s B/(L:ℝ)^6) :=
      hY.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hθ le_rfl)
        (by positivity)) le_rfl)
    have hh := hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hkept.trans hybound) (by positivity))
      (mul_le_mul_of_nonneg_left hraw (by positivity)))
    have harith := hexNegAllN_window_arithmeticS2
      (T := (L:ℝ)^3) (C := hexNegBlockConst2 s B)
      (θ := hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)) hT1 hC
    rw [show ((L:ℝ)^3)^2 = (L:ℝ)^6 by ring] at harith
    exact hh.trans harith
  · have hlw : sphereScaleRatio2 M N*(1/(L:ℝ)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hl2 hu.le
      have h2 : 2*(1/(L:ℝ)) ≤ 1 := by rw [mul_one_div,div_le_one hL0]; exact hLR
      exact h.trans h2
    have hlw0 := mul_pos hl0 hu
    have hY := hYM _ hlw0 hlw
    have hpw3 : (sphereScaleRatio2 M N*(1/(L:ℝ)))^(s/2+2) ≤ 2/(L:ℝ) := by
      have hh := Real.rpow_le_rpow_of_exponent_ge hlw0 hlw
        (show (1:ℝ) ≤ s/2+2 by linarith)
      rw [Real.rpow_one] at hh
      exact hh.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_right hl2 hu.le)
    have hpw2 : (sphereScaleRatio2 M N*(1/(L:ℝ)))^(s/2+1) ≤ 1 :=
      Real.rpow_le_one hlw0.le hlw hp2.le
    have hlpow : (sphereScaleRatio2 M N)^(-(s/2-1+1)) ≤ 2 := by
      rw [show -(s/2-1+1) = -s/2 by ring]
      calc (sphereScaleRatio2 M N)^(-s/2) ≤ (2:ℝ)^(-s/2) :=
          Real.rpow_le_rpow hl0.le hl2 (by linarith)
        _ ≤ (2:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hY0 : 0 ≤ ∫ α in Ioc (0:ℝ) (sphereScaleRatio2 M N*(1/(L:ℝ))),
        α^(s/2-1)*(sphereGaussianCenteredScaled2 α Y+1) := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro α hα
      exact mul_nonneg (Real.rpow_nonneg hα.1.le _) (sphereGaussianCenteredScaled2_add_one_nonneg
        hM hα.1.le Y)
    have hmacro := addedConfiguration2_macroEnd_le_at_cutoff hs hs0 hM hN Y z hcard' hz havoid hu.le
    have h1 := mul_le_mul_of_nonneg_right hlpow hY0
    have h2 := mul_le_mul_of_nonneg_left hpw3 hA
    have h3 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpw2 hp2.le) hu3.le
    have hA3 := div_le_div_of_nonneg_right h2 hp3.le
    have hNE' : 2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
        (negMacroKernel2 (sphereGaussianDensityFactor2 N) (s/2-1) (1/(L:ℝ))) (fun _ => 0) z ≤
        2*(hexNegBlockConst2 s B*(L:ℝ)^(-(s/2+1))) := by
      have hh := mul_le_mul_of_nonneg_left hNE (by norm_num : (0:ℝ) ≤ 2)
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
    have hR3 : 1/(L:ℝ)^3 ≤ 1/(L:ℝ) := one_div_le_one_div_of_le hL0 hL3
    have hR6 : hexNegBlockConst2 s B/(L:ℝ)^6 ≤ hexNegBlockConst2 s B/(L:ℝ) :=
      div_le_div_of_nonneg_left hC hL0 hL6
    have hR3' := mul_le_mul_of_nonneg_right hR3 (show 0 ≤ 1/(s/2+1) by positivity)
    have heq : hexNegAllNCutoffError2 s B (L:ℝ) =
        4*(2*(hexMacroConstA2*((2/(L:ℝ))/(s/2+2))+
          1/(L:ℝ)*(1/(s/2+1)))+2*(hexNegBlockConst2 s B/(L:ℝ)))+
          2*(hexNegBlockConst2 s B*(L:ℝ)^(-(s/2+1))) := by
      unfold hexNegAllNCutoffError2
      ring
    have hYbound : (∫ α in Ioc (0:ℝ) (sphereScaleRatio2 M N*(1/(L:ℝ))),
        α^(s/2-1)*(sphereGaussianCenteredScaled2 α Y+1)) ≤
        2*(hexMacroConstA2*((2/(L:ℝ))/(s/2+2))+
          1/(L:ℝ)*(1/(s/2+1)))+2*(hexNegBlockConst2 s B/(L:ℝ)) := by
      apply hY.trans
      exact add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (by simpa only [mul_div_assoc] using hA3) (h3.trans hR3'))
        (by norm_num)) (mul_le_mul_of_nonneg_left hR6 (by norm_num))
    change (∫ α in Ioc (0:ℝ) (1/(L:ℝ)),
      α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤ _ at hmacro
    rw [heq]
    calc _ ≤ 2*((sphereScaleRatio2 M N)^(-(s/2-1+1))*
          ∫ α in Ioc (0:ℝ) (sphereScaleRatio2 M N*(1/(L:ℝ))),
            α^(s/2-1)*(sphereGaussianCenteredScaled2 α Y+1))+
          2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability2 univ)
            (negMacroKernel2 (sphereGaussianDensityFactor2 N) (s/2-1) (1/(L:ℝ))) (fun _ => 0) z := hmacro
      _ ≤ 4*(∫ α in Ioc (0:ℝ) (sphereScaleRatio2 M N*(1/(L:ℝ))),
          α^(s/2-1)*(sphereGaussianCenteredScaled2 α Y+1))+
          2*(hexNegBlockConst2 s B*(L:ℝ)^(-(s/2+1))) :=
        add_le_add (by linarith only [h1]) hNE'
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hYbound (by norm_num)) le_rfl

def HexNegAllNBlock2 (s B : ℝ) (L N : ℕ) (X : ConfigurationD 2 N) : Prop :=
  (L:ℝ)^6 ≤ N ∧
    (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
      (1+1/(L:ℝ)^3)^2*hexGaussianThetaReal2 (α*(1-1/(L:ℝ)^3)^2)+
        (8+6*hexNegBlockConst2 s B)/(L:ℝ)^3) ∧
    (∫ α in Ioc (0:ℝ) (1/(L:ℝ)), α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
      hexNegAllNCutoffError2 s B (L:ℝ)

theorem exists_hex_neg_allN_block2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {B : ℝ}
    (hB : 0 ≤ B) (hstrat : HexResidualStratifiable2 B) (hsph : SphereStratifiable2 B)
    {L : ℕ} (hL : 2 ≤ L) :
    ∀ᶠ N : ℕ in atTop, ∃ X : ConfigurationD 2 (N+1), HexNegAllNBlock2 s B L (N+1) X := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hT : 2 ≤ L^3 := hL.trans (by simpa using Nat.le_self_pow (by norm_num : (3:ℕ) ≠ 0) L)
  obtain ⟨d,hd,hev⟩ := exists_hex_neg_block2 hs hs0 hB hstrat hT
  have hidx := rationalSizeFloorIndex2_tendsto d hd
  have hprod : Tendsto (fun N : ℕ => (rationalSizeFloor2 d N:ℝ)/(N:ℝ)*((N:ℝ)/((N:ℝ)+1)))
      atTop (𝓝 1) := by
    simpa only [one_mul] using (rationalSizeFloor2_ratio_tendsto d hd).mul
      (tendsto_natCast_div_add_atTop (1:ℝ))
  have hL14 : (0:ℝ) < (L:ℝ)^14 := by positivity
  have hL14' : 1/(L:ℝ)^14 ≤ 1/2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    exact hLR.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 14))
  have hgap : 1-1/(L:ℝ)^14 < 1 := by have := one_div_pos.mpr hL14; linarith
  filter_upwards [hidx.eventually hev,hidx.eventually (eventually_ge_atTop 1),
    (tendsto_order.mp hprod).1 _ hgap,eventually_gt_atTop 0,eventually_ge_atTop (L^6)]
    with N hN1 hN2 hN3 hN0 hsize
  obtain ⟨Y,hYW,hYM⟩ := hN1
  have hmpos : 0 < rationalSizeFloorIndex2 d N := hN2
  have hMpos : 0 < (d*rationalSizeFloorIndex2 d N)^2 := by positivity
  have hMle := rationalSizeFloor2_le d N hd
  change (d*rationalSizeFloorIndex2 d N)^2 ≤ N at hMle
  let r := N+1-(d*rationalSizeFloorIndex2 d N)^2
  have hr : (d*rationalSizeFloorIndex2 d N)^2+r = N+1 := Nat.add_sub_of_le (by omega)
  have hrpos : 0 < r := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hN1R : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hsumR : (((d*rationalSizeFloorIndex2 d N)^2:ℕ):ℝ)+(r:ℝ) = (N:ℝ)+1 := by
    exact_mod_cast hr
  have hfrac : (1-1/(L:ℝ)^14)*((N:ℝ)+1) < (((d*rationalSizeFloorIndex2 d N)^2:ℕ):ℝ) := by
    have heq : (rationalSizeFloor2 d N:ℝ)/(N:ℝ)*((N:ℝ)/((N:ℝ)+1)) =
        (((d*rationalSizeFloorIndex2 d N)^2:ℕ):ℝ)/((N:ℝ)+1) := by
      unfold rationalSizeFloor2
      rw [div_mul_div_comm,mul_comm (N:ℝ) ((N:ℝ)+1),mul_div_mul_right _ _ hNR.ne']
    rw [heq,lt_div_iff₀ hN1R] at hN3
    exact hN3
  have hrN : (r:ℝ) ≤ ((N+1:ℕ):ℝ)/(L:ℝ)^14 := by
    push_cast only [Nat.cast_add,Nat.cast_one]
    have hh : (r:ℝ) < ((N:ℝ)+1)/(L:ℝ)^14 := by
      calc
        (r:ℝ) = (N:ℝ)+1-(((d*rationalSizeFloorIndex2 d N)^2:ℕ):ℝ) := by
          linarith only [hsumR]
        _ < (N:ℝ)+1-(1-1/(L:ℝ)^14)*((N:ℝ)+1) := sub_lt_sub_left hfrac _
        _ = _ := by ring
    exact hh.le
  have hN2' : ((N+1:ℕ):ℝ) ≤ 2*(((d*rationalSizeFloorIndex2 d N)^2:ℕ):ℝ) := by
    push_cast only [Nat.cast_add,Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-1/(L:ℝ)^14 by linarith) hN1R.le
    linarith only [hh,hfrac]
  have hcast3 : ((L^3:ℕ):ℝ) = (L:ℝ)^3 := by push_cast; rfl
  have hcast6 : (((L^3:ℕ):ℝ))^2 = (L:ℝ)^6 := by rw [hcast3]; ring
  rw [hcast6,hcast3] at hYW hYM
  obtain ⟨X,hXW,hXM⟩ := exists_added_configuration2_cutoff hs hs0 hB hsph hL hMpos
    (Nat.succ_pos N) hrpos hr hrN hN2' Y hYW hYM
  refine ⟨X,?_,hXW,hXM⟩
  exact_mod_cast hsize.trans (Nat.le_succ N)

theorem hexNegAllNCutoffError2_tendstoS2 {s B : ℝ} (hs : -2 < s)
    {L : ℕ → ℕ} (hLt : Tendsto L atTop atTop) :
    Tendsto (fun k => hexNegAllNCutoffError2 s B (L k:ℝ)) atTop (𝓝 0) := by
  have hLR : Tendsto (fun k => (L k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLt
  have h1 : Tendsto (fun k =>
      (16*hexMacroConstA2/(s/2+2)+8/(s/2+1)+8*hexNegBlockConst2 s B)/(L k:ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hLR
  have h2 := (tendsto_rpow_neg_atTop (show 0 < s/2+1 by linarith)).comp hLR
  simpa only [hexNegAllNCutoffError2,mul_zero,add_zero,Function.comp_def] using h1.add (h2.const_mul (2*hexNegBlockConst2 s B))

theorem hexNegAllNWindow_tendstoS2 {α D : ℝ} (hα : 0 < α)
    {L : ℕ → ℕ} (hLt : Tendsto L atTop atTop) :
    Tendsto (fun k => (1+1/(L k:ℝ)^3)^2*
      hexGaussianThetaReal2 (α*(1-1/(L k:ℝ)^3)^2)+D/(L k:ℝ)^3)
      atTop (𝓝 (hexGaussianThetaReal2 α)) := by
  have hLR : Tendsto (fun k => (L k:ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0)).comp (tendsto_natCast_atTop_atTop.comp hLt)
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hu : Tendsto (fun k => 1/(L k:ℝ)^3) atTop (𝓝 0) := hone.div_atTop hLR
  have hD' : Tendsto (fun k => D/(L k:ℝ)^3) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hLR
  have harg := ((hone.sub hu).pow 2).const_mul α
  have hc : ContinuousAt hexGaussianThetaReal2 (α*(1-0)^2) :=
    hexGaussianThetaReal2_continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (by simpa using hα))
  have hh := (((hone.add hu).pow 2).mul (hc.tendsto.comp harg)).add hD'
  simpa only [sub_zero,one_pow,mul_one,add_zero,one_mul,Function.comp_def] using hh

/-- Every sufficiently large point count attains the negative Riesz coefficient. -/
theorem sphere2_riesz_neg_lower_allN_of_stratifiable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {B : ℝ} (hB : 0 ≤ B) (hstrat : HexResidualStratifiable2 B) (hsph : SphereStratifiable2 B) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 2 N,
      sphereRieszCoefficientNeg2 s-η ≤ normalizedEnergyNeg2 s X := by
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ X : ConfigurationD 2 (N+1),
      HexNegAllNBlock2 s B (j+2) (N+1) X :=
    fun j => exists_hex_neg_allN_block2 hs hs0 hB hstrat hsph (L := j+2) (by omega)
  obtain ⟨J,hJt,hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hJ
  have hQ := fun k => hN₁ (N₁+k) (Nat.le_add_right N₁ k)
  choose Z hZ using hQ
  have hNt : Tendsto (fun k : ℕ => N₁+k+1) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₁).trans (Nat.le_succ _)) tendsto_id
  have hNpos : ∀ k : ℕ, 0 < N₁+k+1 := fun k => Nat.succ_pos _
  have hidx : Tendsto (fun k : ℕ => N₁+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₁) tendsto_id
  let L := fun k => J (N₁+k)+2
  have hLt : Tendsto L atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₁+k)) 2) (hJt.comp hidx)
  have hL : ∀ k, 2 ≤ L k := by intro k; dsimp [L]; omega
  have hu : Tendsto (fun k => 1/(L k:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
  have hpoint : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (Z k) ≤ hexGaussianThetaReal2 α+ε := by
    intro α hα ε hε
    have hh := hexNegAllNWindow_tendstoS2 (D := 8+6*hexNegBlockConst2 s B) hα hLt
    filter_upwards [(tendsto_order.mp hh).2 (hexGaussianThetaReal2 α+ε) (by linarith),
      (tendsto_order.mp hu).2 α hα] with k hk hk'
    exact ((hZ k).2.1 α hk'.le).trans hk.le
  have hD : 0 ≤ 8+6*hexNegBlockConst2 s B := by
    have := hexNegBlockConst2_nonnegS2 hs hB
    linarith
  have hmacro := sphere2_neg_macro_of_shrinking_cutoffS2 hs hs0 hD hLt hL hNpos Z
    (fun k => (hZ k).1) (fun k => (hZ k).2.1)
    (hexNegAllNCutoffError2_tendstoS2 hs hLt) (fun k => (hZ k).2.2)
  intro η hη
  have hfin := sphere2_riesz_neg_lower_of_full_profile hs hs0 hNt hNpos Z hpoint hmacro η hη
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.mp hfin
  refine ⟨N₁+k₀+1,fun N hN => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, N = N₁+k+1 := ⟨N-N₁-1,by omega⟩
  exact ⟨Z k,hk₀ k (by omega)⟩

theorem sphere2_riesz_neg_lower_allN {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 2 N,
      sphereRieszCoefficientNeg2 s-η ≤ normalizedEnergyNeg2 s X := by
  obtain ⟨B, hB, hneg, hsph⟩ := sphere2_stratification_hypotheses
  exact sphere2_riesz_neg_lower_allN_of_stratifiable hs hs0 hB
    (hexResidualStratifiable2_of_neg hneg) hsph

/-- Conjecture form of the lower half, with the actual double integral and the Hex Epstein
value.  No hypothesis is used. -/
theorem sphere2_riesz_neg_lower_conjecture_form {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere2_riesz_neg_lower_allN hs hs0 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyNeg2, sphereRieszConstNeg2_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg2_eq_epstein hs0] at hY

/-- Conjecture form of the universal upper half under all-scale Hex contact certificates
(stage G2). -/
theorem sphere2_riesz_neg_upper_conjecture_form
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere2_riesz_neg_upper_of_contact hG2 hs hs0 η hη
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  rwa [normalizedEnergyNeg2, sphereRieszConstNeg2_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg2_eq_epstein hs0] at hX

/-- The sharp asymptotics for every `-2 < s < 0` on S² in conjecture form (all configurations
above, some configuration below, every large `N`), with triangular contact as an input; the unconditional wrapper below supplies it. -/
theorem sphere2_riesz_neg_sharp_asymptotic
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) :=
  ⟨sphere2_riesz_neg_upper_conjecture_form hG2 hs hs0,
    sphere2_riesz_neg_lower_conjecture_form hs hs0⟩


/-- Both halves of the sharp negative Riesz asymptotics, with triangular contact proved. -/
theorem sphere2_riesz_neg_sharp_asymptotic_unconditional
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) :=
  sphere2_riesz_neg_sharp_asymptotic hexGaussianContact_all hs hs0

theorem sphere2_riesz_neg_sharp_asymptotic_explicit
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        (4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) := by
  simpa only [sphereArea2_univ_real] using sphere2_riesz_neg_sharp_asymptotic_unconditional hs hs0

end SphericalRiesz
end
end
