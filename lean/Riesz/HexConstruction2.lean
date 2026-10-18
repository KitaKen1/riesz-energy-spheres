import Riesz.HexGaussianEnds2
import Riesz.GaussianOneDimTwelve
import Riesz.BoundaryTwelveEnvelope
import Riesz.NormalizedBumpError
import Riesz.EqualAreaHex2
import Riesz.BoundaryTwelveTensor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.EquivFin
import Riesz.EqualAreaInverseD
import Riesz.HexProfileLower2
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order
import Riesz.BoundaryTwelveNodeGeometry
import Riesz.StratifiedJointSelection
import Riesz.HexLattice2
import Riesz.SphereRieszLower2
import Riesz.SphereRieszUpperFourLtAllN8
import Riesz.SphereRieszLowerMain2

/-! Construction of sharp positive-exponent Riesz competitors on the unit sphere S².

The triangular lattice has covolume one. Actual small equal-area patches carry the checked
order-twelve equal-weight tensor rule. Near-full rational patch families and exact-mass
residual cells are combined by one joint Gaussian selection, with a small-scale budget,
a short-range tail budget and a sharp Gaussian window. A diagonal choice and ordered-pair
subconfiguration extraction give the sharp upper bound for every sufficiently large integer N,
for all 0 < s < 2. The matching lower bound is supplied by the checked triangular-lattice
Gaussian certificate. The final statements use the actual uniform continuous energy and the
continued Epstein zeta coefficient (4*pi)^(-s/2) Re Z(s/2).

This module concerns positive exponents. Negative exponents, logarithmic energy and cap
discrepancy require a separate dimension-two residual construction. -/

section

/-! Physical-space square form of Gaussian quadratic forms on the actual ambient space R3.

`e^{-t|x-y|²} = (4t/π)^{3/2} ∫ e^{-2t|x-z|²} e^{-2t|y-z|²} dz`.  Hence for finite measures the
neutralized Gaussian energy is `(4t/π)^{3/2} ∫ (B_μ(z) - M B_ν(z))² dz` with the bump fields
`B_μ(z) = ∫ e^{-2t|x-z|²} dμ(x)`.  The bump field is local in `z`, so two-sided quadrature of a
Gaussian energy reduces to one-sided errors of single Gaussian bumps (no mixed derivatives). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- The ambient Gaussian bump `e^{-2t|x-z|²}`. -/
def ambientBump3 (t : ℝ) (x z : (AmbientD 2)) : ℝ := Real.exp (-(2*t*‖x-z‖^2))

theorem ambientBump3_nonneg (t : ℝ) (x z : (AmbientD 2)) : 0 ≤ ambientBump3 t x z :=
  (Real.exp_pos _).le

theorem ambientBump3_le_one {t : ℝ} (ht : 0 ≤ t) (x z : (AmbientD 2)) : ambientBump3 t x z ≤ 1 := by
  unfold ambientBump3
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ 2*t*‖x-z‖^2 := by positivity
  linarith

theorem continuous_ambientBump3 (t : ℝ) :
    Continuous (fun p : (AmbientD 2) × (AmbientD 2) => ambientBump3 t p.1 p.2) := by
  unfold ambientBump3
  fun_prop

theorem ambient3_gaussian_integrable {b : ℝ} (hb : 0 < b) (m : (AmbientD 2)) :
    Integrable (fun z : (AmbientD 2) => Real.exp (-(b*‖z-m‖^2))) := by
  have h := (integrable_rexp_neg_mul_sq_norm3 hb).comp_sub_right m
  simpa only [neg_mul] using h

theorem ambient3_gaussian_integral {b : ℝ} (hb : 0 < b) (m : (AmbientD 2)) :
    ∫ z : (AmbientD 2), Real.exp (-(b*‖z-m‖^2)) = (Real.pi/b)^((3:ℝ)/2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := (AmbientD 2)) hb
  rw [finrank_euclideanSpace_fin] at h
  have h2 := integral_sub_right_eq_self (μ := (volume : Measure (AmbientD 2)))
    (fun z : (AmbientD 2) => Real.exp (-b*‖z‖^2)) m
  simp only [neg_mul] at h2 h
  rw [h2, h]
  norm_num

/-- Completing the square: the product of two bumps is a Gaussian in `x-y` times a bump at the
midpoint. -/
theorem ambientBump3_mul_eq (t : ℝ) (x y z : (AmbientD 2)) :
    ambientBump3 t x z*ambientBump3 t y z =
      Real.exp (-(t*‖x-y‖^2))*Real.exp (-((4*t)*‖z-(1/2:ℝ)•(x+y)‖^2)) := by
  unfold ambientBump3
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hpar := parallelogram_law_with_norm ℝ (x-z) (y-z)
  have h1 : x-z+(y-z) = (-2:ℝ)•(z-(1/2:ℝ)•(x+y)) := by module
  have h2 : x-z-(y-z) = x-y := by abel
  have hn : ‖(-2:ℝ)‖ = 2 := by norm_num
  rw [h1, h2, norm_smul, hn] at hpar
  linear_combination t*hpar

theorem ambientBump3_mul_integrable {t : ℝ} (ht : 0 < t) (x y : (AmbientD 2)) :
    Integrable (fun z => ambientBump3 t x z*ambientBump3 t y z) := by
  simp_rw [ambientBump3_mul_eq]
  exact (ambient3_gaussian_integrable (by positivity) _).const_mul _

theorem ambientBump3_mul_integral {t : ℝ} (ht : 0 < t) (x y : (AmbientD 2)) :
    ∫ z, ambientBump3 t x z*ambientBump3 t y z =
      (Real.pi/(4*t))^((3:ℝ)/2)*gaussianKernel t x y := by
  simp_rw [ambientBump3_mul_eq]
  rw [integral_const_mul, ambient3_gaussian_integral (by positivity)]
  unfold gaussianKernel
  ring

theorem ambientBump3_triple_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 2))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (Function.uncurry fun (z : (AmbientD 2)) (q : (AmbientD 2) × (AmbientD 2)) =>
      ambientBump3 t q.1 z*ambientBump3 t q.2 z) (volume.prod (μ.prod ν)) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : (AmbientD 2)) (q : (AmbientD 2) × (AmbientD 2)) =>
      ambientBump3 t q.1 z*ambientBump3 t q.2 z) (volume.prod (μ.prod ν)) := by
    apply Continuous.aestronglyMeasurable
    unfold ambientBump3 Function.uncurry
    fun_prop
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun q => ambientBump3_mul_integrable ht q.1 q.2, ?_⟩
  have he : (fun q : (AmbientD 2) × (AmbientD 2) =>
      ∫ z, ‖Function.uncurry (fun (z : (AmbientD 2)) (q : (AmbientD 2) × (AmbientD 2)) =>
        ambientBump3 t q.1 z*ambientBump3 t q.2 z) (z, q)‖) =
      fun q => (Real.pi/(4*t))^((3:ℝ)/2)*gaussianKernel t q.1 q.2 := by
    funext q
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (mul_nonneg (ambientBump3_nonneg _ _ _) (ambientBump3_nonneg _ _ _))]
    exact ambientBump3_mul_integral ht q.1 q.2
  rw [he]
  exact (gaussianKernel_product_integrable ht.le _).const_mul _

/-- The bump field of a finite measure. -/
def bumpField3 (t : ℝ) (μ : Measure (AmbientD 2)) (z : (AmbientD 2)) : ℝ :=
  ∫ x, ambientBump3 t x z ∂μ

theorem bumpField3_mul_eq (t : ℝ) (μ ν : Measure (AmbientD 2)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (z : (AmbientD 2)) :
    bumpField3 t μ z*bumpField3 t ν z =
      ∫ q, ambientBump3 t q.1 z*ambientBump3 t q.2 z ∂(μ.prod ν) := by
  unfold bumpField3
  exact (integral_prod_mul (fun x => ambientBump3 t x z) (fun y => ambientBump3 t y z)).symm

theorem bumpField3_mul_integrable {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 2))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z => bumpField3 t μ z*bumpField3 t ν z) := by
  simp_rw [bumpField3_mul_eq t μ ν]
  exact (ambientBump3_triple_integrable ht μ ν).integral_prod_left

/-- Square form of the Gaussian pair energy of two finite measures. -/
theorem gaussianMeasurePair_eq_bump3 {t : ℝ} (ht : 0 < t) (μ ν : Measure (AmbientD 2))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasurePair t μ ν =
      (4*t/Real.pi)^((3:ℝ)/2)*∫ z, bumpField3 t μ z*bumpField3 t ν z := by
  simp_rw [bumpField3_mul_eq t μ ν]
  rw [integral_integral_swap (ambientBump3_triple_integrable ht μ ν)]
  simp_rw [ambientBump3_mul_integral ht]
  rw [integral_const_mul, ← mul_assoc]
  have hc : (4*t/Real.pi)^((3:ℝ)/2)*(Real.pi/(4*t))^((3:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : 4*t/Real.pi*(Real.pi/(4*t)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]
  rw [hc, one_mul]
  rfl

/-- Square form of the neutralized Gaussian energy. -/
theorem gaussianMeasureDefect_eq_bump_sq3 {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure (AmbientD 2))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasureDefect t M μ ν =
      (4*t/Real.pi)^((3:ℝ)/2)*∫ z, (bumpField3 t μ z-M*bumpField3 t ν z)^2 := by
  unfold gaussianMeasureDefect
  rw [gaussianMeasurePair_eq_bump3 ht μ μ, gaussianMeasurePair_eq_bump3 ht μ ν,
    gaussianMeasurePair_eq_bump3 ht ν ν]
  have hμμ := bumpField3_mul_integrable ht μ μ
  have hμν := bumpField3_mul_integrable ht μ ν
  have hνν := bumpField3_mul_integrable ht ν ν
  have hsq : (fun z => (bumpField3 t μ z-M*bumpField3 t ν z)^2) =
      fun z => bumpField3 t μ z*bumpField3 t μ z-2*M*(bumpField3 t μ z*bumpField3 t ν z)+
        M^2*(bumpField3 t ν z*bumpField3 t ν z) := by
    funext z
    ring
  have hA : Integrable (fun z => bumpField3 t μ z*bumpField3 t μ z-
      2*M*(bumpField3 t μ z*bumpField3 t ν z)) := hμμ.sub (hμν.const_mul _)
  have hB : Integrable (fun z => M^2*(bumpField3 t ν z*bumpField3 t ν z)) := hνν.const_mul _
  rw [hsq, integral_add hA hB, integral_sub hμμ (hμν.const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- Upper bound of the neutralized Gaussian energy by a pointwise majorant of the bump error. -/
theorem gaussianMeasureDefect_le_of_bump3 {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure (AmbientD 2))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {W : (AmbientD 2) → ℝ} (hW : Integrable (fun z => W z^2))
    (hle : ∀ z, |bumpField3 t μ z-M*bumpField3 t ν z| ≤ W z) :
    gaussianMeasureDefect t M μ ν ≤ (4*t/Real.pi)^((3:ℝ)/2)*∫ z, W z^2 := by
  rw [gaussianMeasureDefect_eq_bump_sq3 ht]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) hW
  refine ae_of_all _ fun z => ?_
  have h := hle z
  have h0 : 0 ≤ W z := (abs_nonneg _).trans h
  calc (bumpField3 t μ z-M*bumpField3 t ν z)^2 = |bumpField3 t μ z-M*bumpField3 t ν z|^2 :=
        (sq_abs _).symm
    _ ≤ W z^2 := pow_le_pow_left₀ (abs_nonneg _) h 2

end SphericalRiesz
end
end

section

/-! Localized twelfth-order Gaussian bump error in the actual 2-dimensional
chart domain and ambient R3.  The nearest-point/product-envelope argument
is reused from the dimension-eight proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem twelfth_coordinate_within_abs_le_of_contDiffAtS2 (d : ℕ)
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

theorem pi_norm_sq_le_sum2 (x : Fin 2 → ℝ) : ‖x‖^2 ≤ ∑ j, (x j)^2 := by
  have hs : 0 ≤ ∑ j, (x j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ j, (x j)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  calc ‖x‖^2 ≤ Real.sqrt (∑ j, (x j)^2)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ j, (x j)^2 := Real.sq_sqrt hs

theorem sum_sq_le_twentyFour_pi_norm_sqS2 (x : Fin 2 → ℝ) : ∑ j, (x j)^2 ≤ 2*‖x‖^2 := by
  have h : ∀ j, (x j)^2 ≤ ‖x‖^2 := by
    intro j
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x j) 2
  calc ∑ j, (x j)^2 ≤ ∑ _j : Fin 2, ‖x‖^2 := Finset.sum_le_sum fun j _ => h j
    _ = 2*‖x‖^2 := by simp

/-- The product of one-dimensional Gaussians in all coordinates. -/
theorem prod_gauss1_eq2 (β : ℝ) (x0 y : Fin 2 → ℝ) :
    ∏ j, gauss1 β (x0 j) (y j) = Real.exp (-(β*∑ j, (y j-x0 j)^2)) := by
  unfold gauss1
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Constant of the twelfth derivative bound. -/
def twelfthConstS2 (L : ℝ) : ℝ := 479001600*531441*(10:ℝ)^30*L^12

/-- Constant of the one-dimensional rule average. -/
def gaussRuleConst12S2 : ℝ := Real.sqrt Real.pi+(2*(10:ℝ)^24)*(479001600*531441*(10:ℝ)^30)*Real.sqrt (2*Real.pi)

theorem gaussRuleConst12_nonnegS2 : 0 ≤ gaussRuleConst12S2 := by
  unfold gaussRuleConst12S2
  positivity

theorem sqrt_pi_le_gaussRuleConst12S2 : Real.sqrt Real.pi ≤ gaussRuleConst12S2 := by
  unfold gaussRuleConst12S2
  have : 0 ≤ (2*(10:ℝ)^24)*(479001600*531441*(10:ℝ)^30:ℝ)*Real.sqrt (2*Real.pi) := by positivity
  linarith

/-- The constant of the localized twelfth-order bump error. -/
def bumpErrorConst2 (L C₀ : ℝ) : ℝ :=
  (2*(10:ℝ)^24)*twelfthConstS2 L*(Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))^2

theorem normalized_bump_quadrature_error2
    {Ψ : (Fin 2 → ℝ) → AmbientD 2} {L C₀ : ℝ} (hL : 1 ≤ L) (hC₀ : 0 < C₀)
    (hcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 12 Ψ x)
    (hder : ∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 12 → ‖iteratedFDeriv ℝ j Ψ x‖ ≤ L)
    (hlow : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, C₀*‖x-y‖ ≤ ‖Ψ x-Ψ y‖)
    (hup : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, ‖Ψ x-Ψ y‖ ≤ L*‖x-y‖)
    {n : ℕ} (hn : 74 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hβn : τ*C₀^2/384 ≤ (n:ℝ)^2) (w : AmbientD 2) :
    |twelveCubeQuadrature 2 n (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))-
      cubeIntegral 2 (fun x => Real.exp (-(τ*‖Ψ x-w‖^2)))| ≤
      bumpErrorConst2 L C₀/(n:ℝ)^12*(1+τ^6)*
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
  set A := twelfthConstS2 L*(1+τ^6)*Real.exp (-(τ*ρ^2/4)) with hAdef
  have hA : 0 ≤ A := by rw [hAdef, twelfthConstS2]; positivity
  set f : (Fin 2 → ℝ) → ℝ := fun x => Real.exp (-(τ*‖Ψ x-w‖^2)) with hfdef
  have hfcd : ∀ x ∈ UnitCube 2, ContDiffAt ℝ 12 f x := by
    intro x hx
    have h1 : ContDiffAt ℝ 12 (fun x => Ψ x-w) x := (hcd x hx).sub contDiffAt_const
    have h2 : ContDiffAt ℝ 12 (fun x => ‖Ψ x-w‖^2) x := h1.norm_sq ℝ
    exact Real.contDiff_exp.contDiffAt.comp x ((h2.const_smul τ).neg)
  have hM : ∀ i v, v ∈ UnitCube 2 → ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u)) (Icc (0 : ℝ) 1) t| ≤
        A*∏ j, gauss1 β (x0 j) (Function.update v i t j) := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    refine (twelfth_coordinate_within_abs_le_of_contDiffAtS2 2 i v t ht (hfcd _ hy)).trans ?_
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
      _ = A*∏ j, gauss1 β (x0 j) (y j) := by rw [hAdef, twelfthConstS2]; ring
  -- one-dimensional bounds
  set B := min 1 (gaussRuleConst12S2/Real.sqrt β) with hBdef
  have hQB : ∀ j, twelveQuadrature n (gauss1 β (x0 j)) ≤ B := by
    intro j
    exact le_min (gauss1_twelveQuadrature_le_one hn hβ.le _)
      (gauss1_twelveQuadrature_le hn hβ hβn _)
  have hIB : ∀ j, (∫ t in (0:ℝ)..1, gauss1 β (x0 j) t) ≤ B := by
    intro j
    refine le_min (gauss1_integral_le_one hβ.le _) ((gauss1_integral_le_sqrt hβ _).trans ?_)
    rw [Real.sqrt_div' _ hβ.le]
    exact div_le_div_of_nonneg_right sqrt_pi_le_gaussRuleConst12S2 (Real.sqrt_nonneg _)
  have herr := twelveCubeQuadrature_twelfth_order_envelope_on 2 hn
    (fun x hx => (hfcd x hx).continuousAt.continuousWithinAt)
    (fun i v hv => by
      intro t ht
      have hy := update_mem_unitCube hv i ht
      have hu : ContDiffAt ℝ 12 (fun u : ℝ => Function.update v i u) t := by
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
  have hratio : B ≤ (Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))*J := by
    apply gauss1_bound_ratio hβ hγ gaussRuleConst12_nonnegS2 (by positivity)
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
  have hB0 : 0 ≤ B := le_min zero_le_one (div_nonneg gaussRuleConst12_nonnegS2 (Real.sqrt_nonneg _))
  have hB8 : B^2 ≤ (Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))^2*J^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hratio 2
  have hprodB : ∏ _j : Fin 2, B = B^2 := by simp
  rw [hprodB] at herr
  have hn6 : (0:ℝ) < (n:ℝ)^12 := by positivity
  calc |twelveCubeQuadrature 2 n f-cubeIntegral 2 f|
      ≤ 10^24/(n:ℝ)^12*((2:ℕ)*(A*B^2)) := herr
    _ = (2*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConstS2 L*(1+τ^6))*(Real.exp (-(τ*ρ^2/4))*B^2) := by
        rw [hAdef]; push_cast; ring
    _ ≤ (2*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConstS2 L*(1+τ^6))*(Real.exp (-(τ*ρ^2/4))*
          ((Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))^2*J^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [twelfthConstS2]; positivity)
        exact mul_le_mul_of_nonneg_left hB8 (Real.exp_pos _).le
    _ = (2*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConstS2 L*(1+τ^6))*
          (Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))^2*
            (Real.exp (-(τ*ρ^2/4))*J^2) := by ring
    _ ≤ (2*(10:ℝ)^24)/(n:ℝ)^12*(twelfthConstS2 L*(1+τ^6))*
          (Real.exp 1*max 2 (gaussRuleConst12S2*(Real.sqrt 96*L/C₀)))^2*
            cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) :=
        mul_le_mul_of_nonneg_left hrhs (by rw [twelfthConstS2]; positivity)
    _ = bumpErrorConst2 L C₀/(n:ℝ)^12*(1+τ^6)*
          cubeIntegral 2 (fun x => Real.exp (-(τ/8*‖Ψ x-w‖^2))) := by
        rw [bumpErrorConst2]; ring

end SphericalRiesz
end
end

section

/-! Localized order-twelve error on actual physical Hex sphere patches.
One radius and one error constant apply to every rotation and center. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedHexPatch_Cn_uniform (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), ∀ c ∈ UnitCube 2, ∀ x ∈ UnitCube 2,
      ContDiffAt ℝ ∞ (equalAreaNormalizedHexPatch g v c ε) x ∧
      ‖equalAreaNormalizedHexPatch g v c ε x-equalAreaRotatedFlatDerivative2 g (x-c)‖ ≤ η ∧
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) x-equalAreaRotatedFlatDerivative2 g‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedHexPatch g v c ε) x‖ ≤ η := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaMovingNormalizedHexChart_Cn_uniform n η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx
  have hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 := by linarith
  have hnorm : ‖v+ε • hexMap (x-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledHex_norm v ε (x-c) (unitCube2_sub_norm x c hx hc)).trans
      (by simpa only [abs_of_pos hε] using hsmall)
  have hfirst : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) z-equalAreaRotatedFlatDerivative2 g‖ ≤ η := by
    intro z hz
    exact (equalAreaNormalizedHexPatch_first_error g v c ε z).trans
      (hb v hv ε hε hs (z-c) (unitCube2_sub_norm z c hz hc)).1
  refine ⟨equalAreaNormalizedHexPatch_contDiffAt g v c ε x (equalArea2_small_norm_domain _ hnorm),
    ?_,hfirst x hx,?_⟩
  · have h := equalAreaNormalizedHexPatch_increment_error g v c hc ε hε hsmall η hfirst c x hc hx
    simp only [equalAreaNormalizedHexPatch_center,sub_self,map_zero,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hη.le (unitCube2_sub_norm x c hx hc))
  · intro k hk hk7
    rw [equalAreaNormalizedHexPatch_iterated_norm]
    exact (hb v hv ε hε hs (x-c) (unitCube2_sub_norm x c hx hc)).2 k hk hk7

structure SmallHexCubePatch2 where
  g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2
  v : Fin 2 → ℝ
  c : Fin 2 → ℝ
  ε : ℝ
  ε_pos : 0 < ε
  c_mem : c ∈ UnitCube 2
  small : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8

def smallHexCubeMap2 (p : SmallHexCubePatch2) : (Fin 2 → ℝ) → AmbientD 2 :=
  equalAreaHexPatch p.g p.v p.c p.ε

def smallHexCubeEmbedding2 (p : SmallHexCubePatch2) : UnitCube 2 ↪ SphereD 2 :=
  equalAreaHexCubeEmbedding2 p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

/-- Upper derivative and Lipschitz constant of the normalized patch charts. -/
def patchChartUpper2 : ℝ := ‖equalAreaFlatDerivative2‖+1

/-- Lower Lipschitz constant of the normalized patch charts. -/
def patchChartLower2 : ℝ := 1/(2*(1+‖hexInverseMap‖))

theorem one_le_patchChartUpper2 : 1 ≤ patchChartUpper2 := by
  unfold patchChartUpper2
  linarith [norm_nonneg equalAreaFlatDerivative2]

theorem patchChartLower2_pos : 0 < patchChartLower2 := by
  unfold patchChartLower2
  positivity

theorem smallHexPatch_normalized_chart_bounds12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      (∀ x ∈ UnitCube 2, ContDiffAt ℝ 12 (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x) ∧
      (∀ x ∈ UnitCube 2, ∀ j, 1 ≤ j → j ≤ 12 →
        ‖iteratedFDeriv ℝ j (equalAreaNormalizedHexPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper2) ∧
      (∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2, patchChartLower2*‖x-y‖ ≤
        ‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-equalAreaNormalizedHexPatch p.g p.v p.c p.ε y‖) ∧
      (∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
        ‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-equalAreaNormalizedHexPatch p.g p.v p.c p.ε y‖ ≤
          patchChartUpper2*‖x-y‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁', h₁⟩ := equalAreaNormalizedHexPatch_Cn_uniform 12 1 one_pos
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

/-- The patch map in normalized form. -/
theorem smallHexCubeMap2_sub_eq (p : SmallHexCubePatch2) (z : AmbientD 2) (x : Fin 2 → ℝ) :
    smallHexCubeMap2 p x-z = p.ε • (equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallHexCubeMap2 p p.c)) := by
  have hε := p.ε_pos.ne'
  rw [equalAreaNormalizedHexPatch_eq, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hε, one_smul,
    one_smul]
  change equalAreaHexPatch p.g p.v p.c p.ε x-z = _
  unfold smallHexCubeMap2
  abel

theorem smallHexCubeMap2_sub_norm_sq (p : SmallHexCubePatch2) (z : AmbientD 2) (x : Fin 2 → ℝ) :
    ‖smallHexCubeMap2 p x-z‖^2 = p.ε^2*‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallHexCubeMap2 p p.c)‖^2 := by
  rw [smallHexCubeMap2_sub_eq, norm_smul, Real.norm_eq_abs, abs_of_pos p.ε_pos, mul_pow]

/-- Localized twelfth-order error of an ambient Gaussian bump on one small patch. -/
theorem smallHexPatch_bump_quadrature12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ n : ℕ, 74 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2*patchChartLower2^2/384 ≤ (n:ℝ)^2 →
      ∀ z : AmbientD 2,
      |twelveCubeQuadrature 2 n (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)-
        cubeIntegral 2 (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)| ≤
        bumpErrorConst2 patchChartUpper2 patchChartLower2/(n:ℝ)^12*(1+(2*t*p.ε^2)^6)*
          cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallHexPatch_normalized_chart_bounds12
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτn z
  obtain ⟨hcd, hder, hlow, hup⟩ := hb p hv hε
  set w := p.ε⁻¹ • (z-smallHexCubeMap2 p p.c) with hw
  set τ := 2*t*p.ε^2 with hτdef
  have hτ : 0 < τ := by have := p.ε_pos; positivity
  have hf1 : (fun x => ambientBump3 t (smallHexCubeMap2 p x) z) =
      fun x => Real.exp (-(τ*‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    unfold ambientBump3
    rw [smallHexCubeMap2_sub_norm_sq, ← hw, hτdef]
    ring_nf
  have hf2 : (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) =
      fun x => Real.exp (-(τ/8*‖equalAreaNormalizedHexPatch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    rw [smallHexCubeMap2_sub_norm_sq, ← hw, hτdef]
    ring_nf
  rw [hf1, hf2]
  exact normalized_bump_quadrature_error2 one_le_patchChartUpper2 patchChartLower2_pos hcd hder
    hlow hup hn hτ (by rw [hτdef]; exact hτn) w

/-- Squaring the actual patch error cancels its exact n^2 point density. -/
theorem smallHexPatch_bump_squared_density12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ n : ℕ, 74 ≤ n → ∀ t : ℝ, 0 < t →
      2*t*p.ε^2*patchChartLower2^2/384 ≤ (n:ℝ)^2 → ∀ z : AmbientD 2,
      (n:ℝ)^24*(twelveCubeQuadrature 2 n (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)-
        cubeIntegral 2 (fun x => ambientBump3 t (smallHexCubeMap2 p x) z))^2 ≤
      (bumpErrorConst2 patchChartUpper2 patchChartLower2*(1+(2*t*p.ε^2)^6)*
        cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))))^2 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_quadrature12
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht hmesh z
  have h := hb p hv hε n hn t ht hmesh z
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : (n:ℝ)^12*|twelveCubeQuadrature 2 n (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)-
      cubeIntegral 2 (fun x => ambientBump3 t (smallHexCubeMap2 p x) z)| ≤
      bumpErrorConst2 patchChartUpper2 patchChartLower2*(1+(2*t*p.ε^2)^6)*
        cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2))) := by
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n:ℝ)^12)
    calc
      _ ≤ (n:ℝ)^12*(bumpErrorConst2 patchChartUpper2 patchChartLower2/(n:ℝ)^12*
        (1+(2*t*p.ε^2)^6)*cubeIntegral 2 (fun x => Real.exp (-(t/4*‖smallHexCubeMap2 p x-z‖^2)))) := h'
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (by positivity) he 2
  simpa only [mul_pow,←pow_mul,sq_abs] using hh

end SphericalRiesz
end
end

section

/-! Concrete large-alpha budgets for physical Hex patches, including corrected nodes.
The constant below is computed from theta at one positive scale and a Gamma integral.
This supplies a foreground cost, not a small-alpha quadrature estimate. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The theta tail estimate uses the conservative bound norm squared >= 1 and can start at any positive scale. -/
theorem hexGaussianThetaReal2_tail_le_from {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    hexGaussianThetaReal2 t-1 ≤
      Real.exp (-Real.pi*(t-b))*(hexGaussianThetaReal2 b-1) := by
  classical
  let f : ℝ → hexLattice → ℝ := fun u x => Real.exp (-(Real.pi*u*‖(x : HexAmbient)‖^2))
  have hf : ∀ u, 0 < u → HasSum (f u) (hexGaussianThetaReal2 u) := fun u hu =>
    Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hu)
  have hf0 : ∀ u, f u 0 = 1 := fun u => by simp [f]
  have h1 := (hf t (hb.trans_le hbt)).update (0 : hexLattice) 0
  have h2 := ((hf b hb).update (0 : hexLattice) 0).mul_left (Real.exp (-Real.pi*(t-b)))
  rw [hf0] at h1 h2
  have hle : ∀ x, Function.update (f t) (0 : hexLattice) 0 x ≤
      Real.exp (-Real.pi*(t-b))*Function.update (f b) (0 : hexLattice) 0 x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
      have hn := (hexLattice_norm_sq_gt_one x (fun h => hx (Subtype.ext h))).le
      simp only [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hn
        (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hbt))
      nlinarith
  have := hasSum_le hle h1 h2
  linarith

/-- Explicit normalized row cost at a fixed positive density scale. -/
def hexGaussianTailBudget2 (b p : ℝ) : ℝ :=
  (hexGaussianThetaReal2 b-1)*Real.exp (Real.pi*b)*
    ((1/(Real.pi*b))^(p+1)*Real.Gamma (p+1))

theorem hexGaussianTailBudget2_nonneg {b p : ℝ} (hb : 0 < b) (hp : -1 < p) :
    0 ≤ hexGaussianTailBudget2 b p := by
  have htheta : 0 ≤ hexGaussianThetaReal2 b-1 :=
    sub_nonneg.mpr (hexGaussianThetaReal2_ge_one hb)
  have hgamma : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  unfold hexGaussianTailBudget2
  positivity

/-- A uniform row bound, valid even when the initial theta scale is below one. -/
theorem hexPatchGaussian_row_exp_le_from {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (Y : ι → SphereD 2) {ell c b α : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : hexLattice) : HexAmbient)‖ ≤ dist (Y i) (Y j))
    (hα : 1 ≤ α) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel2 (c*α) (Y i) (Y j)) ≤
      (hexGaussianThetaReal2 b-1)*Real.exp (Real.pi*b)*Real.exp (-(Real.pi*b*α)) := by
  have hα0 : 0 < α := zero_lt_one.trans_le hα
  have hβ : b ≤ c*α*ell^2/Real.pi := by
    calc b ≤ c*ell^2/Real.pi := hscale
      _ ≤ (c*ell^2/Real.pi)*α := by
        have hce : 0 ≤ c*ell^2/Real.pi := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hα hce
      _ = c*α*ell^2/Real.pi := by ring
  refine (hexPatchGaussian_row_le U Y hell (mul_pos hc hα0) hd i).trans
    ((hexGaussianThetaReal2_tail_le_from hb hβ).trans ?_)
  have ht : 0 ≤ hexGaussianThetaReal2 b-1 :=
    sub_nonneg.mpr (hexGaussianThetaReal2_ge_one hb)
  have hβ' : b*α ≤ c*α*ell^2/Real.pi := by
    calc
      b*α ≤ (c*ell^2/Real.pi)*α := mul_le_mul_of_nonneg_right hscale hα0.le
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-Real.pi*(b*α-b))*(hexGaussianThetaReal2 b-1) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (by
          have hm := mul_le_mul_of_nonneg_left hβ' (by positivity : 0 ≤ Real.pi)
          nlinarith)) ht
    _ = _ := by
      rw [show (hexGaussianThetaReal2 b-1)*Real.exp (Real.pi*b)*Real.exp (-(Real.pi*b*α)) =
        (Real.exp (Real.pi*b)*Real.exp (-(Real.pi*b*α)))*(hexGaussianThetaReal2 b-1) by ring,
        ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- The actual finite physical patch has the computed short-range row budget. -/
theorem hexPatch_shortRange_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (Y : ι → SphereD 2) {ell c b p : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hp : -1 < p)
    (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : hexLattice) : HexAmbient)‖ ≤ dist (Y i) (Y j)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, shortRangeKernel2 c p (Y i) (Y j)) ≤
      hexGaussianTailBudget2 b p := by
  have hne : ∀ j ∈ Finset.univ.erase i, Y i ≠ Y j := by
    intro j hj he
    have hji : U j-U i ≠ 0 := fun h => (Finset.mem_erase.mp hj).1
      (U.injective (sub_eq_zero.mp h))
    have hn : 0 < ‖((U j-U i : hexLattice) : HexAmbient)‖ :=
      norm_pos_iff.mpr (fun h => hji (Subtype.ext h))
    have := hd i j
    rw [he, dist_self] at this
    exact (not_lt_of_ge this) (mul_pos hell hn)
  have hi : ∀ j ∈ Finset.univ.erase i,
      IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel2 (c*α) (Y i) (Y j)) (Ioi 1) := by
    intro j hj
    simpa only [show 2*(p+1)/2-1=p by ring] using
      sphereGaussianPair2_scaled_tail_integrable (s := 2*(p+1)) hc
        (by linarith) zero_le_one (hne j hj)
  let A : ℝ := (hexGaussianThetaReal2 b-1)*Real.exp (Real.pi*b)
  have hA : 0 ≤ A := mul_nonneg
    (sub_nonneg.mpr (hexGaussianThetaReal2_ge_one hb)) (Real.exp_pos _).le
  have hGval : (∫ α in Ioi (0:ℝ), α^p*Real.exp (-(Real.pi*b*α))) =
      (1/(Real.pi*b))^(p+1)*Real.Gamma (p+1) := by
    simpa only [show p+1-1=p by ring] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p+1) (r := Real.pi*b)
        (by linarith) (by positivity)
  have hG : IntegrableOn (fun α : ℝ => α^p*Real.exp (-(Real.pi*b*α))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hGval]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith))).ne'
  unfold shortRangeKernel2
  rw [← integral_finsetSum _ hi]
  calc
    _ ≤ ∫ α in Ioi (1:ℝ), A*(α^p*Real.exp (-(Real.pi*b*α))) := by
      apply setIntegral_mono_on (integrable_finsetSum _ hi)
        ((hG.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul A) measurableSet_Ioi
      intro α hα
      rw [← Finset.mul_sum]
      have hrow := hexPatchGaussian_row_exp_le_from U Y hell hc hb hscale hd hα.le i
      calc
        _ ≤ α^p*(A*Real.exp (-(Real.pi*b*α))) :=
          mul_le_mul_of_nonneg_left hrow (Real.rpow_nonneg (zero_le_one.trans hα.le) _)
        _ = _ := by ring
    _ ≤ ∫ α in Ioi (0:ℝ), A*(α^p*Real.exp (-(Real.pi*b*α))) := by
      apply setIntegral_mono_set (hG.const_mul A)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg hA (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.exp_pos _).le)
      · exact (Ioi_subset_Ioi zero_le_one).eventuallyLE
    _ = hexGaussianTailBudget2 b p := by
      rw [integral_const_mul, hGval]
      rfl

/-- Full foreground cost, with the diagonal interpreted by the defined tail kernel. -/
theorem hexPatch_shortRange_budget_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (Y : ι → SphereD 2) {ell c b p : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hp : -1 < p)
    (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : hexLattice) : HexAmbient)‖ ≤ dist (Y i) (Y j)) :
    (∑ i, ∑ j, shortRangeKernel2 c p (Y i) (Y j)) ≤
      (Fintype.card ι : ℝ)*hexGaussianTailBudget2 b p := by
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i, shortRangeKernel2 c p (Y i) (Y j) := by
      apply Finset.sum_congr rfl
      intro i _
      have he := Finset.sum_erase_add Finset.univ
        (fun j => shortRangeKernel2 c p (Y i) (Y j)) (Finset.mem_univ i)
      rw [shortRangeKernel2_self c hp.le, add_zero] at he
      exact he.symm
    _ ≤ ∑ _i : ι, hexGaussianTailBudget2 b p :=
      Finset.sum_le_sum fun i _ => hexPatch_shortRange_row_le U Y hell hc hb hp hscale hd i
    _ = _ := by simp

/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def hexCorrectedSphereNodes2 (n : ℕ) (hn : 8 ≤ n)
    (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    (Fin 2 → NodeIndex n) → SphereD 2 := fun u =>
  equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
    ⟨cubeNode 2 n u,fun i =>
      ⟨(cubeNode_mem_open 2 n hn u i).1.le,(cubeNode_mem_open 2 n hn u i).2.le⟩⟩

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaHexCorrected2_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (n : ℕ) (hn : 8 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel2 t p
        (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^2*hexGaussianTailBudget2 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative2_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((hexCorrectedLabel2 n hn j-hexCorrectedLabel2 n hn i :
      hexLattice) : HexAmbient)‖ ≤
      dist (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall i)
        (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaHexPatch g v c ε (cubeNode 2 n i))
      (equalAreaHexPatch g v c ε (cubeNode 2 n j))
    rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
    have hi : cubeNode 2 n i ∈ UnitCube 2 := fun k =>
      ⟨(cubeNode_mem_open 2 n hn i k).1.le,(cubeNode_mem_open 2 n hn i k).2.le⟩
    have hj : cubeNode 2 n j ∈ UnitCube 2 := fun k =>
      ⟨(cubeNode_mem_open 2 n hn j k).1.le,(cubeNode_mem_open 2 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := hexCorrectedLabel2_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
    have hdiv : ‖((hexCorrectedLabel2 n hn j-hexCorrectedLabel2 n hn i : hexLattice) :
        HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖cubeNode 2 n i-cubeNode 2 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖hexInverseMap‖)))*
          (‖((hexCorrectedLabel2 n hn j-hexCorrectedLabel2 n hn i : hexLattice) :
            HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖hexInverseMap‖)))*‖cubeNode 2 n i-cubeNode 2 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := hexPatch_shortRange_budget_le (hexCorrectedLabel2 n hn)
    (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 2 → NodeIndex n) = n^2 := by
    simp [nodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- The real density scale of the actual n^2 point count is exactly quadratic in n. -/
theorem sphereGaussianDensityFactor2_pow_twentyFour (n : ℕ) :
    sphereGaussianDensityFactor2 (n^2) = sphereGaussianDensityFactor2 1*(n:ℝ)^2 := by
  unfold sphereGaussianDensityFactor2 sphereGaussianScale2
  simp only [Nat.cast_pow, Nat.cast_one, Real.rpow_one]
  ring

/-- A positive theta scale computed from the fixed chart size, independent of its mesh. -/
def hexCorrectedDensityBudgetScale2 (ε : ℝ) : ℝ :=
  sphereGaussianDensityFactor2 1*
    (ε/(4*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi

theorem hexCorrectedDensityBudgetScale2_pos {ε : ℝ} (hε : 0 < ε) :
    0 < hexCorrectedDensityBudgetScale2 ε := by
  have hD := equalAreaFlatDerivative2_norm_pos
  have hc := sphereGaussianDensityFactor2_pos (N := 1) (by norm_num)
  unfold hexCorrectedDensityBudgetScale2
  positivity

/-- At the actual n^2 sphere density the corrected foreground has one explicit budget for
all n>=8.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaHexCorrected2_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 8 ≤ n),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 (n^2)) p
        (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexCorrectedSphereNodes2 n hn g v c hc ε hε hsmall w))/(n:ℝ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexCorrected2_shortRange_uniform
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
N=(d*m)^2 and epsilon=r*a/d, the positive theta scale depends only on r.
Thus the computed foreground bound is common across a,d,m, rather than merely a fixed chart. -/
theorem equalAreaHexCorrected2_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 8 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p
        (hexCorrectedSphereNodes2 (a*m) hn g v c hc ε hε hsmall u)
        (hexCorrectedSphereNodes2 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexCorrected2_shortRange_uniform
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

end SphericalRiesz
end
end

section

/-! Connections for constructing a common small-alpha budget from actual
physical bump errors.  The majorant of the global attaining sequence still
has to be built; no existence of a uniform budget is postulated here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def sphereBumpError3 {N : ℕ} (t M : ℝ) (X : ConfigurationD 2 N) (z : AmbientD 2) : ℝ :=
  (∑ i : Fin N, ambientBump3 t (X i : AmbientD 2) z) -
    M*bumpField3 t ambientSphereProbability2 z

theorem sphereGaussianDefect2_eq_bump_sq {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : ConfigurationD 2 N) :
    sphereGaussianDefect2 t M X = (4*t/Real.pi)^((3:ℝ)/2)*
      ∫ z : AmbientD 2, (sphereBumpError3 t M X z)^2 := by
  rw [sphereGaussianDefect2_eq_diffuse ht.le,diffuseGaussianDefect_eq_measureDefect ht.le,
    gaussianMeasureDefect_eq_bump_sq3 ht]
  simp only [sphereBumpError3,bumpField3,finitePointMeasure_integral]

theorem sphereGaussianDefect2_le_of_bump {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : ConfigurationD 2 N) {W : AmbientD 2 → ℝ}
    (hW : Integrable (fun z => W z^2))
    (hle : ∀ z, |sphereBumpError3 t M X z| ≤ W z) :
    sphereGaussianDefect2 t M X ≤ (4*t/Real.pi)^((3:ℝ)/2)*∫ z, W z^2 := by
  rw [sphereGaussianDefect2_eq_diffuse ht.le,diffuseGaussianDefect_eq_measureDefect ht.le]
  apply gaussianMeasureDefect_le_of_bump3 ht M _ _ hW
  simpa only [sphereBumpError3,bumpField3,finitePointMeasure_integral] using hle

/-- An actual profile envelope is integrated with its explicit constant. -/
theorem sphereGaussianSmallBudget2_le_of_profile {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 1) (X : ConfigurationD 2 N) (C : ℝ)
    (hC : ∀ α ∈ Ioc (0:ℝ) 4, sphereGaussianCenteredScaled2 α X+1 ≤ C) :
    sphereGaussianSmallBudget2 q X ≤ C*(4^q/q) := by
  have hi := sphereGaussianSmallBudget2_integrable hN hq hq12 X
  have hw : IntegrableOn (fun α : ℝ => α^(q-1)*C) (Ioc 0 4) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)
      (a:=0) (b:=4)).1).mul_const C
  have hv : (∫ α in Ioc (0:ℝ) 4, α^(q-1)) = 4^q/q := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 4),
      integral_rpow (Or.inl (by linarith))]
    rw [show q-1+1=q by ring, Real.zero_rpow hq.ne']
    ring
  unfold sphereGaussianSmallBudget2
  calc
    _ ≤ ∫ α in Ioc (0:ℝ) 4, α^(q-1)*C := by
      apply setIntegral_mono_on hi hw measurableSet_Ioc
      intro α hα
      exact mul_le_mul_of_nonneg_left (hC α hα) (Real.rpow_nonneg hα.1.le _)
    _ = C*(4^q/q) := by rw [integral_mul_const,hv]; ring

/-- Sufficient bound in physical R3, expressed as the real bump error, not a budget assumption. -/
theorem sphereGaussianSmallBudget2_le_of_bump {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 1) (X : ConfigurationD 2 N) (C : ℝ)
    (W : ℝ → AmbientD 2 → ℝ)
    (hW : ∀ α ∈ Ioc (0:ℝ) 4, Integrable (fun z => W α z^2))
    (hle : ∀ α ∈ Ioc (0:ℝ) 4, ∀ z,
      |sphereBumpError3 (sphereGaussianScale2 N α) (N:ℝ) X z| ≤ W α z)
    (hL2 : ∀ α ∈ Ioc (0:ℝ) 4,
      (4*sphereGaussianScale2 N α/Real.pi)^((3:ℝ)/2)*(∫ z,W α z^2) ≤ C*(N:ℝ)) :
    sphereGaussianSmallBudget2 q X ≤ C*(4^q/q) := by
  apply sphereGaussianSmallBudget2_le_of_profile hN hq hq12 X C
  intro α hα
  have ht : 0 < sphereGaussianScale2 N α := by
    rw [sphereGaussianScale2_eq_factor]
    exact mul_pos (sphereGaussianDensityFactor2_pos hN) hα.1
  have h := (sphereGaussianDefect2_le_of_bump ht (N:ℝ) X (hW α hα) (hle α hα)).trans (hL2 α hα)
  rw [sphereGaussianCenteredScaled2_add_one hN hα.1.le]
  exact (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr h

/-- The twelfth-order tensor error cancels the n^2 point count when squared. -/
theorem twelveCubeQuadrature_squared_density_bound2 {n : ℕ} (hn : 74 ≤ n)
    {f : (Fin 2 → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube 2))
    (hs : ∀ i v, v ∈ UnitCube 2 →
      ContDiffOn ℝ 12 (fun t => f (Function.update v i t)) (Icc (0:ℝ) 1))
    (M : Fin 2 → ℝ) (hM0 : ∀ i, 0 ≤ M i)
    (hM : ∀ i v, v ∈ UnitCube 2 → ∀ t ∈ Icc (0:ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤ M i) :
    (n:ℝ)^24*(twelveCubeQuadrature 2 n f-cubeIntegral 2 f)^2 ≤
      ((10:ℝ)^24*(∑ i,M i))^2 := by
  have h := twelveCubeQuadrature_twelfth_order_bound_on 2 hn hf hs M hM
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 ≤ ∑ i,M i := Finset.sum_nonneg (fun i _ => hM0 i)
  have he : (n:ℝ)^12*|twelveCubeQuadrature 2 n f-cubeIntegral 2 f| ≤ (10:ℝ)^24*(∑ i,M i) := by
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n:ℝ)^12)
    calc
      _ ≤ (n:ℝ)^12*((10^24/(n:ℝ)^12)*(∑ i,M i)) := h'
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)^12*|twelveCubeQuadrature 2 n f-cubeIntegral 2 f|) he 2
  simpa only [mul_pow,← pow_mul,sq_abs] using hh

/-- A common positive allocation radius can satisfy the small-alpha mesh condition. -/
theorem exists_twelfth_small_alpha_radius2 {R C₀ : ℝ} (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ sphereGaussianDensityFactor2 1*r^2*C₀^2 ≤ 48 := by
  let c : ℝ := sphereGaussianDensityFactor2 1*C₀^2
  have hc : 0 ≤ c := by
    have h := sphereGaussianDensityFactor2_pos (N:=1) (by norm_num)
    dsimp [c]; positivity
  let r : ℝ := min R (1/(c+1))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,min_le_left _ _,?_⟩
  have h2 := pow_le_pow_left₀ hr.le (min_le_right R (1/(c+1))) 2
  have h3 : c*(1/(c+1))^2 ≤ 48 := by
    rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg c]
  calc
    sphereGaussianDensityFactor2 1*r^2*C₀^2 = c*r^2 := by dsimp [c]; ring
    _ ≤ c*(1/(c+1))^2 := mul_le_mul_of_nonneg_left h2 hc
    _ ≤ 48 := h3

/-- The actual density scale makes one mesh condition valid for every alpha in (0,4]. -/
theorem sphereGaussian_rational_twelfth_mesh2 (a d m : ℕ) (hd : 0 < d)
    (r ε C₀ : ℝ) (hratio : ε*(d:ℝ)=r*(a:ℝ))
    (hscale : sphereGaussianDensityFactor2 1*r^2*C₀^2 ≤ 48)
    {α : ℝ} (hα : α ∈ Ioc (0:ℝ) 4) :
    2*sphereGaussianScale2 ((d*m)^2) α*ε^2*C₀^2/384 ≤ ((a*m:ℕ):ℝ)^2 := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ε = r*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  have hc : 0 ≤ sphereGaussianDensityFactor2 1*r^2*C₀^2 := by
    have h := sphereGaussianDensityFactor2_pos (N:=1) (by norm_num)
    positivity
  have hα4 := mul_le_mul_of_nonneg_left hα.2 hc
  have hf : 2*sphereGaussianDensityFactor2 1*α*r^2*C₀^2/384 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ)<384)]
    nlinarith
  have heq : 2*sphereGaussianScale2 ((d*m)^2) α*ε^2*C₀^2/384 =
      ((a*m:ℕ):ℝ)^2*(2*sphereGaussianDensityFactor2 1*α*r^2*C₀^2/384) := by
    rw [sphereGaussianScale2_eq_factor,sphereGaussianDensityFactor2_pow_twentyFour,he]
    push_cast
    field_simp
  rw [heq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (sq_nonneg ((a*m:ℕ):ℝ))

/-- The actual patch bump envelope holds on all of (0,4] at rational allocation,
with one common radius and no refinement-dependent mesh premise. -/
theorem smallHexPatch_bump_rational_small_alpha2 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (r : ℝ), sphereGaussianDensityFactor2 1*r^2*patchChartLower2^2 ≤ 48 →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ)=r*(a:ℝ) → 74 ≤ a*m →
      ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 2,
      |twelveCubeQuadrature 2 (a*m)
          (fun x => ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (smallHexCubeMap2 p x) z)-
        cubeIntegral 2
          (fun x => ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (smallHexCubeMap2 p x) z)| ≤
      bumpErrorConst2 patchChartUpper2 patchChartLower2/((a*m:ℕ):ℝ)^12*
        (1+(2*sphereGaussianScale2 ((d*m)^2) α*p.ε^2)^6)*
        cubeIntegral 2 (fun x => Real.exp
          (-(sphereGaussianScale2 ((d*m)^2) α/4*‖smallHexCubeMap2 p x-z‖^2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_quadrature12
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε r hscale a d m hd hm hratio hn α hα z
  have ht : 0 < sphereGaussianScale2 ((d*m)^2) α := by
    rw [sphereGaussianScale2_eq_factor]
    exact mul_pos (sphereGaussianDensityFactor2_pos (by positivity)) hα.1
  exact hb p hv hε (a*m) hn _ ht
    (sphereGaussian_rational_twelfth_mesh2 a d m hd r p.ε patchChartLower2 hratio hscale hα) z

/-- Radius fixed by exact sphere-probability mass, rather than chosen arbitrarily. -/
def hexUnitDensityRadius2 : ℝ := ((sphereAreaD 2).real univ)^((1:ℝ)/2)

theorem hexUnitDensityRadius2_pos : 0 < hexUnitDensityRadius2 :=
  Real.rpow_pos_of_pos (sphereAreaD_univ_pos 2) _

theorem hexUnitDensityRadius2_pow : hexUnitDensityRadius2^2 = (sphereAreaD 2).real univ := by
  unfold hexUnitDensityRadius2
  rw [←Real.rpow_natCast,←Real.rpow_mul (sphereAreaD_univ_pos 2).le]
  norm_num

theorem sphereGaussianDensityFactor2_unit_radius :
    sphereGaussianDensityFactor2 1*hexUnitDensityRadius2^2 = Real.pi := by
  have hA := sphereAreaD_univ_pos 2
  rw [hexUnitDensityRadius2_pow, sphereGaussianDensityFactor2, sphereGaussianScale2]
  norm_num only [Nat.cast_one, Real.rpow_one, mul_one]
  field_simp [hA.ne']

theorem hexUnitDensityRadius2_twelfth_mesh_bound :
    sphereGaussianDensityFactor2 1*hexUnitDensityRadius2^2*patchChartLower2^2 ≤ 48 := by
  rw [sphereGaussianDensityFactor2_unit_radius]
  have hl : patchChartLower2 ≤ 1/2 := by
    unfold patchChartLower2
    rw [div_le_iff₀ (by positivity)]
    linarith [norm_nonneg hexInverseMap]
  have hs := pow_le_pow_left₀ patchChartLower2_pos.le hl 2
  calc
    Real.pi*patchChartLower2^2 ≤ Real.pi*(1/2)^2 := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    _ ≤ 48 := by linarith [Real.pi_lt_four]

/-- Actual patch probability equals its exact n^2/N allocation at every refinement. -/
theorem hexTwelfth_rational_exact_patch_mass2 (a d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (ε : ℝ) (hratio : ε*(d:ℝ)=hexUnitDensityRadius2*(a:ℝ)) :
    equalAreaHexPatchProbabilityDensity2 ε = ((a*m:ℕ):ℝ)^2/((d*m:ℕ):ℝ)^2 := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hA := (sphereAreaD_univ_pos 2).ne'
  have he : ε = hexUnitDensityRadius2*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  rw [equalAreaHexPatchProbabilityDensity2,he,div_pow,mul_pow,hexUnitDensityRadius2_pow]
  push_cast
  field_simp

theorem sphereGaussian_exact_mass_twelfth_mesh2 (a d m : ℕ) (hd : 0 < d)
    (ε : ℝ) (hratio : ε*(d:ℝ)=hexUnitDensityRadius2*(a:ℝ))
    {α : ℝ} (hα : α ∈ Ioc (0:ℝ) 4) :
    2*sphereGaussianScale2 ((d*m)^2) α*ε^2*patchChartLower2^2/384 ≤ ((a*m:ℕ):ℝ)^2 :=
  sphereGaussian_rational_twelfth_mesh2 a d m hd hexUnitDensityRadius2 ε patchChartLower2
    hratio hexUnitDensityRadius2_twelfth_mesh_bound hα

/-- Exact mass allocation also fixes the dimensionless bump scale. -/
theorem sphereGaussian_exact_mass_bump_scale2 (a d m : ℕ) (hd : 0 < d)
    (ε α : ℝ) (hratio : ε*(d:ℝ)=hexUnitDensityRadius2*(a:ℝ)) :
    2*sphereGaussianScale2 ((d*m)^2) α*ε^2 = 2*Real.pi*((a*m:ℕ):ℝ)^2*α := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ε = hexUnitDensityRadius2*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  have heq : sphereGaussianScale2 ((d*m)^2) α*ε^2 =
      (sphereGaussianDensityFactor2 1*hexUnitDensityRadius2^2)*((a*m:ℕ):ℝ)^2*α := by
    rw [sphereGaussianScale2_eq_factor,sphereGaussianDensityFactor2_pow_twentyFour,he]
    push_cast
    field_simp
  rw [show 2*sphereGaussianScale2 ((d*m)^2) α*ε^2 =
    2*(sphereGaussianScale2 ((d*m)^2) α*ε^2) by ring,heq,
    sphereGaussianDensityFactor2_unit_radius]
  ring

end SphericalRiesz
end
end

section

/-! # Near-full rational families of triangular-lattice cube patches on `S²` (stage S2-4)

Dimension-2 port of `SphereRationalFamily24`, the dimension-24 form of the dimension-8 covering
chain (compact coordinate grids, shrunk cells, finite compact cores, small chart cores, sphere
grids and their masses, capped grids, affine cubes, rational normalization of the common scale).
The parts keep the order and the statements of that chain, with `S²⁴`, the Leech map and the
exponent 24 replaced by `S² ⊂ ℝ³`, the map `hexMap` of the triangular lattice of covolume one and
the exponent 2: coordinate cells are squares in `Fin 2 → ℝ` of volume `h²`, a shrunk cell keeps
the factor `(1-γ)²` of the mass, and the unit-density radius is `r₀ = A^(1/2)`, `A = 4π` the area
of `S²`.  The result is `sphere2_near_full_rational_affine_cubes`: for every smallness radius and
every residual fraction there is a finite, pairwise disjoint, separated family of small cube
patches of one common rational scale `r₀ p/q`, each of probability exactly `(p/q)²`, covering more
than `1-b` of the sphere, with `K p² < q²`.  No points, energies or budgets are asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SphericalRiesz

section CompactGrid
open Set Metric

/-! ### CompactGrid

A common finite coordinate grid covers compact cores with the closed
cells inside their open buffers. No interior of a compact core is assumed.
The coordinate norm here is the Pi sup norm, so a cell has diameter at most h. -/

def gridLabel2 (h : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℤ := fun i => Int.floor (x i/h)

def gridHalfOpenCell2 (h : ℝ) (z : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i < h*((z i : ℝ)+1)}

def gridClosedCell2 (h : ℝ) (z : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1)}

theorem gridLabel2_mem_cell (h : ℝ) (hh : 0 < h) (x : Fin 2 → ℝ) :
    x ∈ gridHalfOpenCell2 h (gridLabel2 h x) := by
  intro i
  constructor
  · have ht := (le_div_iff₀ hh).mp (Int.floor_le (x i/h))
    simpa only [gridLabel2, mul_comm] using ht
  · have ht := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x i/h))
    simpa only [gridLabel2, mul_comm] using ht

theorem gridLabel2_eq_of_mem_cell (h : ℝ) (hh : 0 < h) (z : Fin 2 → ℤ)
    (x : Fin 2 → ℝ) (hx : x ∈ gridHalfOpenCell2 h z) : gridLabel2 h x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).1)
  · exact (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).2)

theorem gridHalfOpenCell2_subset_closed (h : ℝ) (z : Fin 2 → ℤ) :
    gridHalfOpenCell2 h z ⊆ gridClosedCell2 h z :=
  fun _ hx i => ⟨(hx i).1,(hx i).2.le⟩

theorem gridHalfOpenCell2_pairwise_disjoint (h : ℝ) (hh : 0 < h) :
    Pairwise (fun z w : Fin 2 → ℤ => Disjoint (gridHalfOpenCell2 h z) (gridHalfOpenCell2 h w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hw
  exact hzw ((gridLabel2_eq_of_mem_cell h hh z x hx).symm.trans
    (gridLabel2_eq_of_mem_cell h hh w x hw))

theorem gridClosedCell2_dist_le (h : ℝ) (hh : 0 ≤ h) (z : Fin 2 → ℤ)
    (x y : Fin 2 → ℝ) (hx : x ∈ gridClosedCell2 h z) (hy : y ∈ gridClosedCell2 h z) :
    dist x y ≤ h := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hh).mpr
  intro i
  change |x i-y i| ≤ h
  apply abs_le.mpr
  have hxi := hx i
  have hyi := hy i
  constructor <;> nlinarith

theorem gridLabel2_image_finite (h : ℝ) (hh : 0 < h)
    (k : Set (Fin 2 → ℝ)) (hk : IsCompact k) : (gridLabel2 h '' k).Finite := by
  obtain ⟨R,hR,hbound⟩ := hk.isBounded.exists_pos_norm_le
  apply (Set.Finite.pi' (fun _ : Fin 2 =>
    Set.finite_Icc (Int.floor (-R/h)) (Int.floor (R/h)))).subset
  rintro z ⟨x,hx,rfl⟩ i
  have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans (hbound x hx)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hi
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hh.le),
    Int.floor_mono (div_le_div_of_nonneg_right hhi hh.le)⟩

theorem gridCells2_cover (h : ℝ) (hh : 0 < h) (k : Set (Fin 2 → ℝ)) :
    k ⊆ ⋃ z ∈ gridLabel2 h '' k, gridHalfOpenCell2 h z := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨gridLabel2 h x,⟨x,hx,rfl⟩,gridLabel2_mem_cell h hh x⟩

theorem gridClosedCells2_subset_buffer (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (k U : Set (Fin 2 → ℝ)) (hbuffer : thickening r k ⊆ U) :
    ∀ z ∈ gridLabel2 h '' k, gridClosedCell2 h z ⊆ U := by
  rintro z ⟨x,hx,rfl⟩ y hy
  apply hbuffer
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  exact (gridClosedCell2_dist_le h hh.le _ y x hy
    (gridHalfOpenCell2_subset_closed _ _ (gridLabel2_mem_cell h hh x))).trans_lt hhr

theorem finite_compact_grid2 {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 2 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, ∃ Z : ι → Finset (Fin 2 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell2 h z ∧
        ∀ z ∈ Z i, gridClosedCell2 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite2_positive_lower_bound8 r hr
  let h := δ/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 2 → ℤ) := fun i => (gridLabel2_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel2 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells2_cover h hh (k i)
  · intro z hz
    apply gridClosedCells2_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i]

end CompactGrid

section GridShrink
open Set MeasureTheory
open scoped ENNReal

/-! ### GridShrink

Exact coordinate volumes and strict gaps for the known shrink factor.
Original half-open cells partition without boundary overlaps; shrunk closed
cells are compact, disjoint, and retain the exact factor (1-gamma)^2 (the coordinate
dimension is 2: a cell is a square of area h^2). -/

def gridShrunkCell2 (h γ : ℝ) (z : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {x | ∀ i, h*((z i : ℝ)+γ/2) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1-γ/2)}

theorem gridHalfOpenCell2_measurable (h : ℝ) (z : Fin 2 → ℤ) :
    MeasurableSet (gridHalfOpenCell2 h z) := by
  have he : gridHalfOpenCell2 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell2, Set.mem_pi]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem gridClosedCell2_isCompact (h : ℝ) (z : Fin 2 → ℤ) :
    IsCompact (gridClosedCell2 h z) := by
  have he : gridClosedCell2 h z =
      Icc (fun i => h*(z i : ℝ)) (fun i => h*((z i : ℝ)+1)) := by
    ext x
    simp only [gridClosedCell2, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell2_isCompact (h γ : ℝ) (z : Fin 2 → ℤ) :
    IsCompact (gridShrunkCell2 h γ z) := by
  have he : gridShrunkCell2 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell2, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell2_subset_halfOpen (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (z : Fin 2 → ℤ) : gridShrunkCell2 h γ z ⊆ gridHalfOpenCell2 h z := by
  intro x hx i
  have hi := hx i
  have hp : 0 < h*γ := mul_pos hh hγ
  constructor <;> nlinarith

theorem gridShrunkCell2_pairwise_disjoint (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) :
    Pairwise (fun z w : Fin 2 → ℤ => Disjoint (gridShrunkCell2 h γ z) (gridShrunkCell2 h γ w)) := by
  intro z w hzw
  exact (gridHalfOpenCell2_pairwise_disjoint h hh hzw).mono
    (gridShrunkCell2_subset_halfOpen h γ hh hγ z)
    (gridShrunkCell2_subset_halfOpen h γ hh hγ w)

theorem gridHalfOpenCell2_volume (h : ℝ) (hh : 0 ≤ h) (z : Fin 2 → ℤ) :
    volume (gridHalfOpenCell2 h z) = ENNReal.ofReal (h^2) := by
  have he : gridHalfOpenCell2 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell2, Set.mem_pi]
  rw [he, Real.volume_pi_Ico]
  have hw : ∀ i : Fin 2, h*((z i : ℝ)+1)-h*(z i : ℝ) = h := by intro i; ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hh 2).symm

theorem gridShrunkCell2_volume (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1) (z : Fin 2 → ℤ) :
    volume (gridShrunkCell2 h γ z) = ENNReal.ofReal ((h*(1-γ))^2) := by
  have he : gridShrunkCell2 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell2, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, Real.volume_Icc_pi]
  have hw : ∀ i : Fin 2, h*((z i : ℝ)+1-γ/2)-h*((z i : ℝ)+γ/2) = h*(1-γ) := by
    intro i
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (mul_nonneg hh (sub_nonneg.mpr hγ)) 2).symm

theorem gridShrunkCell2_volume_factor (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 2 → ℤ) : volume (gridShrunkCell2 h γ z) =
      ENNReal.ofReal ((1-γ)^2)*volume (gridHalfOpenCell2 h z) := by
  rw [gridShrunkCell2_volume h γ hh hγ z,gridHalfOpenCell2_volume h hh z,
    mul_pow,ENNReal.ofReal_mul (pow_nonneg hh 2),mul_comm]

theorem gridFiniteUnion2_volume (h : ℝ) (hh : 0 < h) (Z : Finset (Fin 2 → ℤ)) :
    volume (⋃ z ∈ Z, gridHalfOpenCell2 h z) = (Z.card : ℝ≥0∞)*ENNReal.ofReal (h^2) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell2_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell2_measurable h z)]
  simp only [gridHalfOpenCell2_volume h hh.le, Finset.sum_const, nsmul_eq_mul]

theorem gridShrunkFiniteUnion2_volume_factor (h γ : ℝ) (hh : 0 < h)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (Z : Finset (Fin 2 → ℤ)) :
    volume (⋃ z ∈ Z, gridShrunkCell2 h γ z) =
      ENNReal.ofReal ((1-γ)^2)*volume (⋃ z ∈ Z, gridHalfOpenCell2 h z) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridShrunkCell2_pairwise_disjoint h γ hh hγ hzw)
    (fun z _ => (gridShrunkCell2_isCompact h γ z).isClosed.measurableSet),
    measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell2_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell2_measurable h z), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => gridShrunkCell2_volume_factor h γ hh.le hγ1 z)

end GridShrink

section SphereFiniteCompactCores
open Set MeasureTheory Metric
open scoped Topology ENNReal

/-! ### SphereFiniteCompactCores

Any supplied finite measurable sphere cover admits compact cores with
arbitrarily small lost probability. For an open cover, the cores have a
common positive buffer inside the original cover and disjoint buffers.
This is an actual probability-measure existence theorem on S², not yet a chart
atlas of the triangular lattice or a finite equal-scale cube extraction theorem. -/

theorem sphereProbability2_compact_core (s : Set (SphereD 2)) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) :
    ∃ k ⊆ s, IsCompact k ∧ (sphereProbabilityD 2) (s \ k) < ENNReal.ofReal b := by
  have hS : IsClosed ((SphereD 2) : Set (AmbientD 2)) := isClosed_sphere
  let : PolishSpace (SphereD 2) := hS.polishSpace
  exact hs.exists_isCompact_sdiff_lt (measure_ne_top (sphereProbabilityD 2) s)
    (ENNReal.ofReal_pos.mpr hb).ne'

theorem sphereFiniteCover2_residual_le {K : ℕ} (s k : Fin K → Set (SphereD 2))
    (hcover : (⋃ i, s i) = univ) :
    (sphereProbabilityD 2) (⋃ i, k i)ᶜ ≤ ∑ i : Fin K, (sphereProbabilityD 2) (s i \ k i) := by
  have hsub : (⋃ i, k i)ᶜ ⊆ ⋃ i, s i \ k i := by
    intro x hx
    have hxcover : x ∈ ⋃ i, s i := hcover.symm ▸ mem_univ x
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxcover
    exact mem_iUnion.mpr ⟨i,hi,fun hki => hx (mem_iUnion.mpr ⟨i,hki⟩)⟩
  have hsum : (sphereProbabilityD 2) (⋃ i, s i \ k i) ≤
      ∑ i : Fin K, (sphereProbabilityD 2) (s i \ k i) := by
    simpa only [tsum_fintype] using
      (measure_iUnion_le (μ := (sphereProbabilityD 2)) (fun i : Fin K => s i \ k i))
  exact (measure_mono hsub).trans hsum

theorem sphereFiniteCover2_compact_cores {K : ℕ} (s : Fin K → Set (SphereD 2))
    (hs : ∀ i, MeasurableSet (s i)) (hcover : (⋃ i, s i) = univ)
    (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 2), (∀ i, k i ⊆ s i) ∧ (∀ i, IsCompact (k i)) ∧
      (sphereProbabilityD 2) (⋃ i, k i)ᶜ < ENNReal.ofReal b := by
  classical
  let a : ℝ := b/((K : ℝ)+1)
  have ha : 0 < a := div_pos hb (by positivity)
  have h : ∀ i, ∃ k ⊆ s i, IsCompact k ∧ (sphereProbabilityD 2) (s i \ k) < ENNReal.ofReal a :=
    fun i => sphereProbability2_compact_core (s i) (hs i) a ha
  choose k hsub hcompact hloss using h
  refine ⟨k,hsub,hcompact,?_⟩
  have hab : (K : ℝ)*a < b := by
    have he : ((K : ℝ)+1)*a = b := by
      dsimp [a]
      field_simp
    nlinarith
  calc
    (sphereProbabilityD 2) (⋃ i, k i)ᶜ ≤ ∑ i, (sphereProbabilityD 2) (s i \ k i) :=
      sphereFiniteCover2_residual_le s k hcover
    _ ≤ ∑ _i : Fin K, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => (hloss i).le)
    _ = ENNReal.ofReal ((K : ℝ)*a) := by
      simp [ENNReal.ofReal_mul]
    _ < ENNReal.ofReal b := (ENNReal.ofReal_lt_ofReal_iff hb).mpr hab

theorem sphereFiniteCover2_disjoint_partition {K : ℕ} (U : Fin K → Set (SphereD 2))
    (hU : ∀ i, MeasurableSet (U i)) (hcover : (⋃ i, U i) = univ) :
    ∃ s : Fin K → Set (SphereD 2), (∀ i, MeasurableSet (s i)) ∧ (∀ i, s i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ := by
  refine ⟨disjointed U,?_,fun i => disjointed_subset U i,disjoint_disjointed U,?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hU i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun (_h : j < i) => (hU j).compl)
  · rw [iUnion_disjointed,hcover]

theorem sphereFinitePartition2_separated_cores {K : ℕ} (s : Fin K → Set (SphereD 2))
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 2), ∃ δ > 0,
      (∀ i, k i ⊆ s i ∧ IsCompact (k i)) ∧
      (sphereProbabilityD 2) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      (∀ i j, i ≠ j → ∀ x ∈ k i, ∀ y ∈ k j, δ < dist x y) := by
  obtain ⟨k,hsub,hcomp,hloss⟩ := sphereFiniteCover2_compact_cores s hs hcover b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  obtain ⟨δ,hδ,hsep⟩ := finite2_compact_disjoint_distance8 k hcomp hkd
  exact ⟨k,δ,hδ,fun i => ⟨hsub i,hcomp i⟩,hloss,hsep⟩

theorem sphereFiniteOpenCover2_buffered_cores {K : ℕ} (U : Fin K → Set (SphereD 2))
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 2), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ U i ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ U i) ∧
      (sphereProbabilityD 2) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨s,hsm,hss,hsd,hscov⟩ := sphereFiniteCover2_disjoint_partition U
    (fun i => (hU i).measurableSet) hcover
  obtain ⟨k,hks,hcomp,hloss⟩ := sphereFiniteCover2_compact_cores s hsm hscov b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hsd hij).mono (hks i) (hks j)
  have hkU : ∀ i, k i ⊆ U i := fun i => (hks i).trans (hss i)
  obtain ⟨ρ,hρ,hbuf,hdis⟩ := finite2_compact_chart_buffers8 k U hcomp hkd hU hkU
  exact ⟨k,ρ,hρ,fun i => ⟨hcomp i,hkU i,hbuf i⟩,hloss,hdis⟩

theorem sphere2_finite_ball_cover (r : ℝ) (hr : 0 < r) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 2), (⋃ i, ball (p i) r) = univ := by
  classical
  let : CompactSpace (SphereD 2) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 2)) 1)
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set (SphereD 2))).elim_finite_subcover
    (fun p : (SphereD 2) => ball p r) (fun _ => isOpen_ball)
    (fun p _ => mem_iUnion.mpr ⟨p,mem_ball_self hr⟩)
  let p : Fin t.card → (SphereD 2) := fun i => (t.equivFin.symm i).val
  refine ⟨t.card,p,?_⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,hy⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨t.equivFin ⟨y,hyt⟩,by simpa only [p,Equiv.symm_apply_apply] using hxy⟩

theorem sphere2_finite_ball_buffered_cores (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 2), ∃ k : Fin K → Set (SphereD 2), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      (sphereProbabilityD 2) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,hcover⟩ := sphere2_finite_ball_cover r hr
  obtain ⟨k,ρ,hρ,hk,hloss,hd⟩ := sphereFiniteOpenCover2_buffered_cores
    (fun i => ball (p i) r) (fun _ => isOpen_ball) hcover b hb
  exact ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩

theorem sphereProbability2_mass_of_residual (s : Set (SphereD 2)) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) (hloss : (sphereProbabilityD 2) sᶜ < ENNReal.ofReal b) :
    1-b < (sphereProbabilityD 2).real s := by
  have h := (ENNReal.toReal_lt_toReal (measure_ne_top (sphereProbabilityD 2) sᶜ)
    ENNReal.ofReal_ne_top).mpr hloss
  rw [ENNReal.toReal_ofReal hb.le] at h
  change (sphereProbabilityD 2).real sᶜ < b at h
  rw [measureReal_compl hs,probReal_univ] at h
  linarith

theorem sphere2_finite_ball_buffered_cores_mass (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 2), ∃ k : Fin K → Set (SphereD 2), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      1-b < (sphereProbabilityD 2).real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩ := sphere2_finite_ball_buffered_cores r b hr hb
  exact ⟨K,p,k,ρ,hρ,hk,sphereProbability2_mass_of_residual _
    (MeasurableSet.iUnion fun i => (hk i).1.measurableSet) b hb hloss,hd⟩

end SphereFiniteCompactCores

section SphereSmallChartCores
open Set MeasureTheory Metric
open scoped Topology

/-! ### SphereSmallChartCores

Quantitative small-ball coverage by explicit rotated equal-area charts.
The near-full compact cores now lie in actual small chart images, with
disjoint open buffers. Equal-scale grid cells of the triangular lattice remain a
separate step. -/

theorem equalAreaInverse2_small_ball_norm (q : (SphereD 2)) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole2 r) : ‖equalAreaInverseD (q : (AmbientD 2))‖ ≤ 2*r := by
  have hfirst := northPole2_ball_first_pos q r hr hq
  have hrpos : 0 < r := (dist_nonneg : 0 ≤ dist q northPole2).trans_lt hq
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*r)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |Real.arctan ((q : (AmbientD 2)) 1/(q : (AmbientD 2)) 0)| ≤ 2*r
    have h := (sphere2_coordinate_difference_le_dist q northPole2 1).trans_lt hq
    have hcoord : |(q : (AmbientD 2)) 1| < r := by simpa [northPole2] using h
    have hquot : |(q : (AmbientD 2)) 1/(q : (AmbientD 2)) 0| < 2*r := by
      rw [abs_div,abs_of_pos (by linarith : 0 < (q : (AmbientD 2)) 0)]
      apply (div_lt_iff₀ (by linarith : 0 < (q : (AmbientD 2)) 0)).mpr
      nlinarith
    exact Real.abs_arctan_le_abs.trans hquot.le
  · change |(q : (AmbientD 2)) j.succ.succ| ≤ 2*r
    have h := (sphere2_coordinate_difference_le_dist q northPole2 j.succ.succ).trans_lt hq
    have hcoord : |(q : (AmbientD 2)) j.succ.succ| < r := by
      simpa [northPole2] using h
    linarith

theorem northPole2_ball_chart (q : (SphereD 2)) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole2 r) :
    equalAreaInverseD (q : (AmbientD 2)) ∈ equalAreaChartDomainD ∧
      ‖equalAreaInverseD (q : (AmbientD 2))‖ ≤ 2*r ∧ equalAreaPhiD (equalAreaInverseD (q : (AmbientD 2))) = (q : (AmbientD 2)) := by
  have hf : 0 < (q : (AmbientD 2)) 0 := by
    have h := northPole2_ball_first_pos q r hr hq
    linarith
  exact ⟨equalAreaInverseD_mem_domain q hf,equalAreaInverse2_small_ball_norm q r hr hq,
    equalAreaPhiD_inverse8 q hf⟩

theorem sphere2_ball_rotated_chart (p : (SphereD 2)) (r : ℝ) (hr : r ≤ 1/2) :
    ∃ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), sphereRotationD g northPole2 = p ∧
      ∀ q ∈ ball p r, ∃ u ∈ equalAreaChartDomainD, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhiD u) = (q : (AmbientD 2)) := by
  obtain ⟨g,hg⟩ := sphereRotation2_transitive northPole2 p
  refine ⟨g,hg,?_⟩
  intro q hq
  let z : (SphereD 2) := sphereRotationD g.symm q
  have hgz : sphereRotationD g z = q := by
    apply Subtype.ext
    exact g.apply_symm_apply q
  have hz : z ∈ ball northPole2 r := by
    rw [mem_ball,← sphereRotationD_dist g z northPole2,hgz,hg]
    exact hq
  obtain ⟨hu,hn,hphi⟩ := northPole2_ball_chart z r hr hz
  refine ⟨equalAreaInverseD (z : (AmbientD 2)),hu,hn,?_⟩
  rw [hphi]
  exact g.apply_symm_apply q

theorem sphere2_finite_small_chart_buffered_cores (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ k : Fin K → Set (SphereD 2), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧
        ∀ q ∈ thickening ρ (k i), ∃ u ∈ equalAreaChartDomainD,
          ‖u‖ < a ∧ g i (equalAreaPhiD u) = (q : (AmbientD 2))) ∧
      1-b < (sphereProbabilityD 2).real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  classical
  let r : ℝ := min (a/4) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrhalf : r ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hra : 2*r < a := by
    have h := min_le_left (a/4) (1/4)
    change r ≤ a/4 at h
    linarith
  obtain ⟨K,p,k,ρ,hρ,hk,hmass,hd⟩ := sphere2_finite_ball_buffered_cores_mass r b hr hb
  have h : ∀ i, ∃ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), sphereRotationD g northPole2 = p i ∧
      ∀ q ∈ ball (p i) r, ∃ u ∈ equalAreaChartDomainD, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhiD u) = (q : (AmbientD 2)) :=
    fun i => sphere2_ball_rotated_chart (p i) r hrhalf
  choose g hg hchart using h
  refine ⟨K,g,k,ρ,hρ,?_,hmass,hd⟩
  intro i
  refine ⟨(hk i).1,(hk i).2.2.1,(hk i).2.2.2.1,?_⟩
  intro q hq
  obtain ⟨u,hu,hn,he⟩ := hchart i q ((hk i).2.2.2.2 hq)
  exact ⟨u,hu,hn.trans_lt hra,he⟩

end SphereSmallChartCores

section SphereGrid
open Set Metric MeasureTheory

/-! ### SphereGrid

Apply finite floor grids to the actual near-full rotated small-chart
cores. The unshrunk half-open cells cover those cores, with all closed
cells inside the physically disjoint open buffers. -/

theorem equalAreaRotatedHemisphere2_of_representation (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (q : (SphereD 2)) (u : Fin 2 → ℝ) (hu : u ∈ equalAreaChartDomainD)
    (he : g (equalAreaPhiD u) = (q : (AmbientD 2))) : q ∈ equalAreaRotatedHemisphere2 g := by
  change 0 < (g.symm (q : (AmbientD 2))) 0
  rw [← he,g.symm_apply_apply]
  exact equalAreaPhiD_first_pos u hu

theorem hexCoordinateBuffer2_mem (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (U : Set (SphereD 2))
    (x : Fin 2 → ℝ) (hx : x ∈ hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 g U) :
    hexMap x ∈ equalAreaChartDomainD ∧ ∃ q ∈ U, g (equalAreaPhiD (hexMap x)) = (q : (AmbientD 2)) := by
  obtain ⟨u,hu,rfl⟩ := hx
  rw [hexMap_coordinateInverse8]
  exact equalAreaCoordinateBuffer2_mem g U u hu

theorem hexCoordinateBuffer2_norm_lt (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (U : Set (SphereD 2)) (a : ℝ)
    (hsmall : ∀ q ∈ U, ∃ u ∈ equalAreaChartDomainD, ‖u‖ < a ∧
      g (equalAreaPhiD u) = (q : (AmbientD 2)))
    (x : Fin 2 → ℝ) (hx : x ∈ hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 g U) :
    ‖hexMap x‖ < a := by
  obtain ⟨hu,q,hq,he⟩ := hexCoordinateBuffer2_mem g U x hx
  obtain ⟨u,hu',hn,he'⟩ := hsmall q hq
  have hxu := equalAreaPhiD_injOn hu hu' (g.injective (he.trans he'.symm))
  simpa only [hxu] using hn

theorem hexGridSpherePatch2_subset_buffer (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (s : Set (Fin 2 → ℝ)) (U : Set (SphereD 2))
    (hs : s ⊆ hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 g U) :
    equalAreaHexSpherePatch2 g 0 0 1 s ⊆ U := by
  intro q hq
  obtain ⟨x,hx,he⟩ := hq
  obtain ⟨_,p,hp,he'⟩ := hexCoordinateBuffer2_mem g U x (hs hx)
  have he0 : g (equalAreaPhiD (hexMap x)) = (q : (AmbientD 2)) := by
    simpa only [equalAreaHexPatch,equalAreaMovingHexChart,sub_zero,one_smul,zero_add] using he
  have heq : (q : (AmbientD 2)) = (p : (AmbientD 2)) := by
    exact he0.symm.trans he'
  exact (Subtype.ext heq).symm ▸ hp

theorem sphere2_finite_small_chart_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ U : Fin K → Set (SphereD 2), ∃ h > 0, ∃ Z : Fin K → Finset (Fin 2 → ℤ),
      (∀ i, IsOpen (U i) ∧ ∀ z ∈ Z i,
        hexMap '' gridClosedCell2 h z ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridClosedCell2 h z, ‖hexMap x‖ < a) ∧
        equalAreaHexSpherePatch2 (g i) 0 0 1 (gridClosedCell2 h z) ⊆ U i) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, ⋃ z ∈ Z i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h z)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  obtain ⟨K,g,k,ρ,hρ,hk,hmass,hd⟩ := sphere2_finite_small_chart_buffered_cores a b ha hb
  let U : Fin K → Set (SphereD 2) := fun i => thickening ρ (k i)
  have hkh : ∀ i, k i ⊆ equalAreaRotatedHemisphere2 (g i) := by
    intro i q hq
    obtain ⟨u,hu,_,he⟩ := (hk i).2.2.2 q ((hk i).2.2.1 hq)
    exact equalAreaRotatedHemisphere2_of_representation (g i) q u hu he
  let c : Fin K → Set (Fin 2 → ℝ) := fun i =>
    hexCoordinateInverse2 '' (equalAreaRotatedInverse2 (g i) '' k i)
  let V : Fin K → Set (Fin 2 → ℝ) := fun i =>
    hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 (g i) (U i)
  have hc : ∀ i, IsCompact (c i) := fun i =>
    hexCoordinateCore2_isCompact (g i) (k i) (hk i).1 (hkh i)
  have hV : ∀ i, IsOpen (V i) := fun i =>
    hexCoordinateBuffer2_isOpen (g i) (U i) (hk i).2.1
  have hsub : ∀ i, c i ⊆ V i := fun i => image_mono
    (equalAreaCoordinateCore2_subset_buffer (g i) (k i) (U i) (hkh i) (hk i).2.2.1)
  obtain ⟨h,hh,Z,hgrid⟩ := finite_compact_grid2 c V hc hV hsub
  refine ⟨K,g,U,h,hh,Z,?_,?_,hd⟩
  · intro i
    refine ⟨(hk i).2.1,?_⟩
    intro z hz
    have hcell := (hgrid i).2 z hz
    refine ⟨?_,?_,hexGridSpherePatch2_subset_buffer (g i) _ (U i) hcell⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (hexCoordinateBuffer2_mem (g i) (U i) x (hcell hx)).1
    · intro x hx
      exact hexCoordinateBuffer2_norm_lt (g i) (U i) a (hk i).2.2.2 x (hcell hx)
  · apply hmass.trans_le
    apply measureReal_mono (μ := (sphereProbabilityD 2)) ?_ (measure_ne_top _ _)
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    let x := hexCoordinateInverse2 (equalAreaRotatedInverse2 (g i) q)
    have hx : x ∈ c i := ⟨equalAreaRotatedInverse2 (g i) q,⟨q,hi,rfl⟩,rfl⟩
    obtain ⟨z,hz,hcell⟩ := mem_iUnion₂.mp ((hgrid i).1 hx)
    apply mem_iUnion.mpr
    refine ⟨i,mem_iUnion₂.mpr ⟨z,hz,?_⟩⟩
    refine ⟨x,hcell,?_⟩
    simpa [equalAreaHexPatch,equalAreaMovingHexChart,x,hexMap_coordinateInverse8] using
      equalAreaRotatedPhi2_inverse8 (g i) q (hkh i hi)

end SphereGrid

section SphereGridMass
open Set MeasureTheory
open scoped ENNReal

/-! ### SphereGridMass

Exact finite shrink accounting in the actual sphere probability measure.
Compactness and disjointness concern physical (SphereD 2) images, rather than
only their coordinates. These are interval cells; the affine unit-cube
parameterization and rational node counts are separate obligations. -/

theorem hexGridAffine2_eq_map : equalAreaHexAffine2 0 0 1 = hexMap := by
  funext x
  simp only [equalAreaHexAffine2,sub_zero,one_smul,zero_add]

theorem hexGridSpherePatch2_mono (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    {s t : Set (Fin 2 → ℝ)} (hst : s ⊆ t) :
    equalAreaHexSpherePatch2 g 0 0 1 s ⊆ equalAreaHexSpherePatch2 g 0 0 1 t :=
  preimage_mono (image_mono hst)

theorem hexGridSpherePatch2_isCompact (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (s : Set (Fin 2 → ℝ)) (hs : IsCompact s) :
    IsCompact (equalAreaHexSpherePatch2 g 0 0 1 s) := by
  let : CompactSpace (SphereD 2) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 2)) 1)
  have hf : Continuous (equalAreaHexPatch g 0 0 1) := by
    unfold equalAreaHexPatch equalAreaMovingHexChart
    exact g.continuous.comp (equalAreaPhiD_continuous.comp (by fun_prop))
  exact ((hs.image hf).isClosed.preimage continuous_subtype_val).isCompact

theorem hexGridSpherePatch2_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (s : Set (Fin 2 → ℝ)) (hs : MeasurableSet s)
    (hdom : hexMap '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g 0 0 1 s) =
      ENNReal.ofReal (1/(sphereAreaD 2).real univ)*volume s := by
  simpa only [hexGridAffine2_eq_map,equalAreaHexPatchProbabilityDensity2,one_pow] using
    equalAreaHexSpherePatch2_probability g 0 0 1 zero_lt_one s hs (by
      simpa only [hexGridAffine2_eq_map] using hdom)

theorem hexGridSpherePatch2_measurable (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (s : Set (Fin 2 → ℝ)) (hs : MeasurableSet s)
    (hdom : hexMap '' s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaHexSpherePatch2 g 0 0 1 s) :=
  equalAreaHexSpherePatch2_measurable g 0 0 1 zero_lt_one s hs (by
    simpa only [hexGridAffine2_eq_map] using hdom)

theorem hexGridSpherePatch2_disjoint (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (s t : Set (Fin 2 → ℝ)) (hs : hexMap '' s ⊆ equalAreaChartDomainD)
    (ht : hexMap '' t ⊆ equalAreaChartDomainD) (hd : Disjoint s t) :
    Disjoint (equalAreaHexSpherePatch2 g 0 0 1 s) (equalAreaHexSpherePatch2 g 0 0 1 t) :=
  equalAreaHexSpherePatch2_disjoint g 0 0 1 zero_lt_one s t
    (by simpa only [hexGridAffine2_eq_map] using hs)
    (by simpa only [hexGridAffine2_eq_map] using ht) hd

theorem hexGridShrunkSphereCell2_probability_factor (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (z : Fin 2 → ℤ)
    (hdom : hexMap '' gridClosedCell2 h z ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g 0 0 1 (gridShrunkCell2 h γ z)) =
      ENNReal.ofReal ((1-γ)^2)*
        (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g 0 0 1 (gridHalfOpenCell2 h z)) := by
  have hs := gridShrunkCell2_subset_halfOpen h γ hh hγ z
  have ht := gridHalfOpenCell2_subset_closed h z
  rw [hexGridSpherePatch2_probability g _
    (gridShrunkCell2_isCompact h γ z).isClosed.measurableSet ((image_mono (hs.trans ht)).trans hdom),
    hexGridSpherePatch2_probability g _ (gridHalfOpenCell2_measurable h z)
      ((image_mono ht).trans hdom),gridShrunkCell2_volume_factor h γ hh.le hγ1 z]
  ring

theorem hexGridShrunkSphereFamily2_disjoint {ι : Type*}
    (g : ι → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (z : ι → Fin 2 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i)))
      (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridHalfOpenCell2 h (z j))))) :
    Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)))
      (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridShrunkCell2 h γ (z j)))) := by
  intro i j hij
  exact (hd hij).mono
    (hexGridSpherePatch2_mono _ (gridShrunkCell2_subset_halfOpen h γ hh hγ (z i)))
    (hexGridSpherePatch2_mono _ (gridShrunkCell2_subset_halfOpen h γ hh hγ (z j)))

theorem hexGridShrunkSphereFamily2_probability_factor {ι : Type*} [Fintype ι]
    (g : ι → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (z : ι → Fin 2 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, hexMap '' gridClosedCell2 h (z i) ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i)))
      (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridHalfOpenCell2 h (z j))))) :
    (sphereProbabilityD 2) (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) =
      ENNReal.ofReal ((1-γ)^2)*
        (sphereProbabilityD 2) (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))) := by
  classical
  have hd' := hexGridShrunkSphereFamily2_disjoint g z h γ hh hγ hd
  have hsm : ∀ i, MeasurableSet
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) := fun i =>
    hexGridSpherePatch2_measurable _ _ (gridShrunkCell2_isCompact h γ (z i)).isClosed.measurableSet
      ((image_mono ((gridShrunkCell2_subset_halfOpen h γ hh hγ (z i)).trans
        (gridHalfOpenCell2_subset_closed h (z i)))).trans (hdom i))
  have hhm : ∀ i, MeasurableSet
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))) := fun i =>
    hexGridSpherePatch2_measurable _ _ (gridHalfOpenCell2_measurable h (z i))
      ((image_mono (gridHalfOpenCell2_subset_closed h (z i))).trans (hdom i))
  rw [measure_iUnion hd' hsm,measure_iUnion hd hhm,tsum_fintype,tsum_fintype,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    hexGridShrunkSphereCell2_probability_factor (g i) h γ hh hγ hγ1 (z i) (hdom i))

theorem hexGridShrunkSphereFamily2_probability_real_factor {ι : Type*} [Fintype ι]
    (g : ι → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (z : ι → Fin 2 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, hexMap '' gridClosedCell2 h (z i) ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i)))
      (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridHalfOpenCell2 h (z j))))) :
    (sphereProbabilityD 2).real (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) =
      (1-γ)^2*(sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))) := by
  rw [Measure.real,hexGridShrunkSphereFamily2_probability_factor g z h γ hh hγ hγ1 hdom hd,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr hγ1) 2)]
  rfl

end SphereGridMass

section SphereShrunkGrid
open Set MeasureTheory

/-! ### SphereShrunkGrid

Construct a near-full separated compact interval-cell family on the actual
unit sphere. A common shrink parameter gives exact physical mass accounting.
This does not yet identify the cells with the uniform affine unit-cube class. -/

theorem hexGridSphereSigma2_disjoint {K : ℕ}
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (U : Fin K → Set (SphereD 2))
    (h : ℝ) (hh : 0 < h) (Z : Fin K → Finset (Fin 2 → ℤ))
    (hdom : ∀ i z, z ∈ Z i → hexMap '' gridClosedCell2 h z ⊆ equalAreaChartDomainD)
    (hU : ∀ i z, z ∈ Z i → equalAreaHexSpherePatch2 (g i) 0 0 1
      (gridClosedCell2 h z) ⊆ U i)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    Pairwise (fun p q : (Σ i : Fin K, Z i) => Disjoint
      (equalAreaHexSpherePatch2 (g p.1) 0 0 1 (gridHalfOpenCell2 h p.2.val))
      (equalAreaHexSpherePatch2 (g q.1) 0 0 1 (gridHalfOpenCell2 h q.2.val))) := by
  classical
  rintro ⟨i,z⟩ ⟨j,w⟩ hpq
  by_cases hij : i = j
  · subst j
    have hzw : z.val ≠ w.val := by
      intro he
      exact hpq (by congr 1; exact Subtype.ext he)
    exact hexGridSpherePatch2_disjoint (g i) _ _
      ((image_mono (gridHalfOpenCell2_subset_closed h z.val)).trans (hdom i z.val z.property))
      ((image_mono (gridHalfOpenCell2_subset_closed h w.val)).trans (hdom i w.val w.property))
      (gridHalfOpenCell2_pairwise_disjoint h hh hzw)
  · exact (hd hij).mono
      ((hexGridSpherePatch2_mono _ (gridHalfOpenCell2_subset_closed h z.val)).trans
        (hU i z.val z.property))
      ((hexGridSpherePatch2_mono _ (gridHalfOpenCell2_subset_closed h w.val)).trans
        (hU j w.val w.property))

theorem sphere2_finite_small_chart_grid_flat (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ z : Fin L → Fin 2 → ℤ, ∃ h > 0,
      (∀ i, hexMap '' gridClosedCell2 h (z i) ⊆ equalAreaChartDomainD ∧
        ∀ x ∈ gridClosedCell2 h (z i), ‖hexMap x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i)))
        (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridHalfOpenCell2 h (z j)))) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,Z,hcell,hmass,hd⟩ := sphere2_finite_small_chart_grid a b ha hb
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := hexGridSphereSigma2_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaHexSpherePatch2 (g' j) 0 0 1 (gridHalfOpenCell2 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h z) := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨(e.symm j).1,mem_iUnion₂.mpr
        ⟨(e.symm j).2.val,(e.symm j).2.property,hj⟩⟩
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      obtain ⟨z,hz,hzq⟩ := mem_iUnion₂.mp hi
      refine mem_iUnion.mpr ⟨e ⟨i,⟨z,hz⟩⟩,?_⟩
      change q ∈ equalAreaHexSpherePatch2 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell2 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass

theorem shrinkMass2_loss_budget (b m : ℝ) (hb : 0 < b)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm : 1-min (b/4) (1/4) < m) :
    ∃ γ > 0, γ < 1 ∧ 1-b < (1-γ)^2*m ∧ (1-γ)^2*m < 1 := by
  let β := min (b/4) (1/4)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβb : β ≤ b/4 := min_le_left _ _
  have hβ1 : β ≤ 1/4 := min_le_right _ _
  let γ := β/4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hf0 : 0 ≤ (1-γ)^2 := pow_nonneg (by linarith) _
  have hf1 : (1-γ)^2 < 1 := pow_lt_one₀ (by linarith) (by linarith) (by decide)
  have hber : 1-2*γ ≤ (1-γ)^2 := by
    have h := one_add_mul_le_pow (a := -γ) (by linarith : -2 ≤ -γ) 2
    simpa only [Nat.cast_ofNat,mul_neg,← sub_eq_add_neg] using h
  have hproduct := mul_le_mul_of_nonneg_right hber hm0
  have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 2*γ by positivity)
  have hm' : 1-β < m := hm
  refine ⟨γ,hγ,hγ1,?_,?_⟩
  · dsimp [γ] at hproduct hmul ⊢
    nlinarith
  · exact (mul_le_mul_of_nonneg_left hm1 hf0).trans_lt (by simpa using hf1)

theorem sphere2_near_full_separated_shrunk_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ z : Fin L → Fin 2 → ℤ, ∃ h > 0, ∃ γ > 0, γ < 1 ∧
      (∀ i, hexMap '' gridShrunkCell2 h γ (z i) ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridShrunkCell2 h γ (z i), ‖hexMap x‖ < a) ∧
        IsCompact (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)))
        (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridShrunkCell2 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)),
        ∀ y ∈ equalAreaHexSpherePatch2 (g j) 0 0 1 (gridShrunkCell2 h γ (z j)), δ < dist x y) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hcell,hd,hm⟩ := sphere2_finite_small_chart_grid_flat a
    (min (b/4) (1/4)) ha (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass2_loss_budget b ((sphereProbabilityD 2).real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell2 h γ (z i) ⊆ gridClosedCell2 h (z i) := fun i =>
    (gridShrunkCell2_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell2_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) := fun i =>
    hexGridSpherePatch2_isCompact _ _ (gridShrunkCell2_isCompact h γ (z i))
  have hd' := hexGridShrunkSphereFamily2_disjoint g z h γ hh hγ hd
  have heq := hexGridShrunkSphereFamily2_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,γ,hγ,hγ1,?_,hd',
    finite2_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu

end SphereShrunkGrid

section CappedSphereGrid
open Set Metric MeasureTheory

/-! ### CappedSphereGrid

The constructed sphere grid can use any prescribed positive mesh cap.
The cap is imposed before floor enumeration, while retaining actual near-full
mass, physical separation and the original closed-cell domain bounds. -/

theorem finite_compact_grid2_capped (η : ℝ) (hη : 0 < η) {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 2 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, h < η ∧ ∃ Z : ι → Finset (Fin 2 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell2 h z ∧
        ∀ z ∈ Z i, gridClosedCell2 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite2_positive_lower_bound8 r hr
  let h := min δ η/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 2 → ℤ) := fun i => (gridLabel2_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,by dsimp [h]; linarith [min_le_right δ η],Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel2 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells2_cover h hh (k i)
  · intro z hz
    apply gridClosedCells2_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i,min_le_left δ η]


theorem sphere2_finite_small_chart_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ U : Fin K → Set (SphereD 2), ∃ h > 0, h < η ∧ ∃ Z : Fin K → Finset (Fin 2 → ℤ),
      (∀ i, IsOpen (U i) ∧ ∀ z ∈ Z i,
        hexMap '' gridClosedCell2 h z ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridClosedCell2 h z, ‖hexMap x‖ < a) ∧
        equalAreaHexSpherePatch2 (g i) 0 0 1 (gridClosedCell2 h z) ⊆ U i) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, ⋃ z ∈ Z i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h z)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  obtain ⟨K,g,k,ρ,hρ,hk,hmass,hd⟩ := sphere2_finite_small_chart_buffered_cores a b ha hb
  let U : Fin K → Set (SphereD 2) := fun i => thickening ρ (k i)
  have hkh : ∀ i, k i ⊆ equalAreaRotatedHemisphere2 (g i) := by
    intro i q hq
    obtain ⟨u,hu,_,he⟩ := (hk i).2.2.2 q ((hk i).2.2.1 hq)
    exact equalAreaRotatedHemisphere2_of_representation (g i) q u hu he
  let c : Fin K → Set (Fin 2 → ℝ) := fun i =>
    hexCoordinateInverse2 '' (equalAreaRotatedInverse2 (g i) '' k i)
  let V : Fin K → Set (Fin 2 → ℝ) := fun i =>
    hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 (g i) (U i)
  have hc : ∀ i, IsCompact (c i) := fun i =>
    hexCoordinateCore2_isCompact (g i) (k i) (hk i).1 (hkh i)
  have hV : ∀ i, IsOpen (V i) := fun i =>
    hexCoordinateBuffer2_isOpen (g i) (U i) (hk i).2.1
  have hsub : ∀ i, c i ⊆ V i := fun i => image_mono
    (equalAreaCoordinateCore2_subset_buffer (g i) (k i) (U i) (hkh i) (hk i).2.2.1)
  obtain ⟨h,hh,hhη,Z,hgrid⟩ := finite_compact_grid2_capped η hη c V hc hV hsub
  refine ⟨K,g,U,h,hh,hhη,Z,?_,?_,hd⟩
  · intro i
    refine ⟨(hk i).2.1,?_⟩
    intro z hz
    have hcell := (hgrid i).2 z hz
    refine ⟨?_,?_,hexGridSpherePatch2_subset_buffer (g i) _ (U i) hcell⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (hexCoordinateBuffer2_mem (g i) (U i) x (hcell hx)).1
    · intro x hx
      exact hexCoordinateBuffer2_norm_lt (g i) (U i) a (hk i).2.2.2 x (hcell hx)
  · apply hmass.trans_le
    apply measureReal_mono (μ := (sphereProbabilityD 2)) ?_ (measure_ne_top _ _)
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    let x := hexCoordinateInverse2 (equalAreaRotatedInverse2 (g i) q)
    have hx : x ∈ c i := ⟨equalAreaRotatedInverse2 (g i) q,⟨q,hi,rfl⟩,rfl⟩
    obtain ⟨z,hz,hcell⟩ := mem_iUnion₂.mp ((hgrid i).1 hx)
    apply mem_iUnion.mpr
    refine ⟨i,mem_iUnion₂.mpr ⟨z,hz,?_⟩⟩
    refine ⟨x,hcell,?_⟩
    simpa [equalAreaHexPatch,equalAreaMovingHexChart,x,hexMap_coordinateInverse8] using
      equalAreaRotatedPhi2_inverse8 (g i) q (hkh i hi)


theorem sphere2_finite_small_chart_grid_flat_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ z : Fin L → Fin 2 → ℤ, ∃ h > 0, h < η ∧
      (∀ i, hexMap '' gridClosedCell2 h (z i) ⊆ equalAreaChartDomainD ∧
        ∀ x ∈ gridClosedCell2 h (z i), ‖hexMap x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i)))
        (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridHalfOpenCell2 h (z j)))) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,hhη,Z,hcell,hmass,hd⟩ := sphere2_finite_small_chart_grid_capped a b η ha hb hη
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := hexGridSphereSigma2_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaHexSpherePatch2 (g' j) 0 0 1 (gridHalfOpenCell2 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h z) := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨(e.symm j).1,mem_iUnion₂.mpr
        ⟨(e.symm j).2.val,(e.symm j).2.property,hj⟩⟩
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      obtain ⟨z,hz,hzq⟩ := mem_iUnion₂.mp hi
      refine mem_iUnion.mpr ⟨e ⟨i,⟨z,hz⟩⟩,?_⟩
      change q ∈ equalAreaHexSpherePatch2 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell2 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,hhη,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass


theorem sphere2_near_full_separated_shrunk_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ z : Fin L → Fin 2 → ℤ, ∃ h > 0, h < η ∧ ∃ γ > 0, γ < 1 ∧
      (∀ i, hexMap '' gridShrunkCell2 h γ (z i) ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridShrunkCell2 h γ (z i), ‖hexMap x‖ < a) ∧
        IsCompact (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)))
        (equalAreaHexSpherePatch2 (g j) 0 0 1 (gridShrunkCell2 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)),
        ∀ y ∈ equalAreaHexSpherePatch2 (g j) 0 0 1 (gridShrunkCell2 h γ (z j)), δ < dist x y) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hhη,hcell,hd,hm⟩ := sphere2_finite_small_chart_grid_flat_capped a
    (min (b/4) (1/4)) η ha (lt_min (by positivity) (by norm_num)) hη
  let H := ⋃ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridHalfOpenCell2 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass2_loss_budget b ((sphereProbabilityD 2).real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell2 h γ (z i) ⊆ gridClosedCell2 h (z i) := fun i =>
    (gridShrunkCell2_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell2_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i))) := fun i =>
    hexGridSpherePatch2_isCompact _ _ (gridShrunkCell2_isCompact h γ (z i))
  have hd' := hexGridShrunkSphereFamily2_disjoint g z h γ hh hγ hd
  have heq := hexGridShrunkSphereFamily2_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,hhη,γ,hγ,hγ1,?_,hd',
    finite2_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu

end CappedSphereGrid

section AffineGridCube
open Set MeasureTheory
open Boundary

/-! ### AffineGridCube

Identify the constructed interval cells with the actual common-scale
affine unit-cube class of the triangular lattice (`hexMap`). The original probability,
compactness and physical
gap are retained. This constructs the small patch family, not a global node
configuration or its energy estimate. Rational node counts remain separate. -/

def cubeMidpoint2 : Fin 2 → ℝ := fun _ => 1/2

def gridCenter2 (h : ℝ) (z : Fin 2 → ℤ) : Fin 2 → ℝ :=
  fun i => h*((z i : ℝ)+1/2)

def gridCubeParam2 (h γ : ℝ) (z : Fin 2 → ℤ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  gridCenter2 h z+(h*(1-γ)) • (x-cubeMidpoint2)

theorem cubeMidpoint2_mem_unitCube : cubeMidpoint2 ∈ UnitCube 2 := by
  intro i
  norm_num [cubeMidpoint2]

theorem gridCenter2_mem_shrunk (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 2 → ℤ) : gridCenter2 h z ∈ gridShrunkCell2 h γ z := by
  intro i
  dsimp [gridCenter2]
  have hg : h*γ ≤ h := by nlinarith
  constructor <;> nlinarith

theorem gridCubeParam2_image_unitCube (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1)
    (z : Fin 2 → ℤ) : gridCubeParam2 h γ z '' UnitCube 2 = gridShrunkCell2 h γ z := by
  have hl : 0 < h*(1-γ) := by positivity
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ i
    change h*((z i : ℝ)+γ/2) ≤ h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ∧
      h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ≤ h*((z i : ℝ)+1-γ/2)
    have hi := hx i
    have hlo := mul_nonneg hl.le hi.1
    have hhi := mul_nonneg hl.le (sub_nonneg.mpr hi.2)
    constructor <;> nlinarith
  · intro hy
    let x : Fin 2 → ℝ := fun i => (y i-gridCenter2 h z i)/(h*(1-γ))+1/2
    have hx : x ∈ UnitCube 2 := by
      intro i
      have lo : -(1/2) ≤ (y i-gridCenter2 h z i)/(h*(1-γ)) :=
        (le_div_iff₀ hl).mpr (by dsimp [gridCenter2]; nlinarith [(hy i).1])
      have hi : (y i-gridCenter2 h z i)/(h*(1-γ)) ≤ 1/2 :=
        (div_le_iff₀ hl).mpr (by dsimp [gridCenter2]; nlinarith [(hy i).2])
      change 0 ≤ (y i-gridCenter2 h z i)/(h*(1-γ))+1/2 ∧
        (y i-gridCenter2 h z i)/(h*(1-γ))+1/2 ≤ 1
      constructor <;> linarith
    refine ⟨x,hx,?_⟩
    funext i
    change gridCenter2 h z i+h*(1-γ)*
      ((y i-gridCenter2 h z i)/(h*(1-γ))+1/2-1/2) = y i
    have hc : h*(1-γ)*((y i-gridCenter2 h z i)/(h*(1-γ))) = y i-gridCenter2 h z i :=
      mul_div_cancel₀ _ hl.ne'
    linear_combination hc

theorem equalAreaHexGridCube2_affine_identity (h γ : ℝ) (z : Fin 2 → ℤ)
    (x : Fin 2 → ℝ) :
    hexMap (gridCubeParam2 h γ z x) =
      equalAreaHexAffine2 (hexMap (gridCenter2 h z)) cubeMidpoint2 (h*(1-γ)) x := by
  simp [gridCubeParam2,equalAreaHexAffine2]

theorem equalAreaHexGridCube2_patch_identity (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (h γ : ℝ) (z : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    equalAreaHexPatch g 0 0 1 (gridCubeParam2 h γ z x) =
      equalAreaHexPatch g (hexMap (gridCenter2 h z)) cubeMidpoint2 (h*(1-γ)) x := by
  simp [equalAreaHexPatch,equalAreaMovingHexChart,gridCubeParam2]

theorem gridShrunkSphere2_eq_affineCube (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1) (z : Fin 2 → ℤ) :
    equalAreaHexSpherePatch2 g 0 0 1 (gridShrunkCell2 h γ z) =
      equalAreaHexSpherePatch2 g (hexMap (gridCenter2 h z)) cubeMidpoint2
        (h*(1-γ)) (UnitCube 2) := by
  have hf : (fun x => equalAreaHexPatch g 0 0 1 (gridCubeParam2 h γ z x)) =
      equalAreaHexPatch g (hexMap (gridCenter2 h z)) cubeMidpoint2 (h*(1-γ)) := by
    funext x
    exact equalAreaHexGridCube2_patch_identity g h γ z x
  simp only [equalAreaHexSpherePatch2,← gridCubeParam2_image_unitCube h γ hh hγ z,
    image_image,hf]

theorem equalAreaHexCubeUnion2_probability_real {K : ℕ}
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin K → Fin 2 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 2)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) ε (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) ε (UnitCube 2)))) :
    (sphereProbabilityD 2).real
      (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) (c i) ε (UnitCube 2)) =
      (K : ℝ)*(ε^2/(sphereAreaD 2).real univ) := by
  change (sphereProbabilityD 2).real (equalAreaHexPatchUnion2 g v c (fun _ => ε)
    (fun _ => UnitCube 2)) = _
  have hden : 0 ≤ ε^2/(sphereAreaD 2).real univ :=
    (equalAreaHexPatchProbabilityDensity2_pos ε hε).le
  rw [Measure.real,equalAreaHexCubeUnion2_probability g v c ε hε hc hsmall hd,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hden]

theorem sphere2_near_full_small_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ v : Fin K → Fin 2 → ℝ, ∃ ε > 0, ε*equalAreaScaleRadius2 ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ε*equalAreaScaleRadius2 ≤ 1/8 ∧
        IsCompact (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2))
        (equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ε (UnitCube 2))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2),
        ∀ y ∈ equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ε (UnitCube 2), δ < dist x y) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2)) ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2)) < 1 ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2)) =
        (K : ℝ)*(ε^2/(sphereAreaD 2).real univ) := by
  let a := min ρ (1/16)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have haρ : a ≤ ρ/2 := by
    dsimp [a]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have ha1 : a ≤ 1/32 := by dsimp [a]; linarith [min_le_right ρ (1/16)]
  have hR := equalAreaScaleRadius2_pos
  obtain ⟨K,g,z,h,hh,hhcap,γ,hγ,hγ1,hcell,hd,hgap,hl,hu⟩ :=
    sphere2_near_full_separated_shrunk_grid_capped a b (a/equalAreaScaleRadius2)
      ha hb (by positivity)
  let ε := h*(1-γ)
  let v : Fin K → Fin 2 → ℝ := fun i => hexMap (gridCenter2 h (z i))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : ε*equalAreaScaleRadius2 < a := by
    have heh : ε ≤ h := by dsimp [ε]; nlinarith
    exact (mul_le_mul_of_nonneg_right heh hR.le).trans_lt ((lt_div_iff₀ hR).mp hhcap)
  have hv : ∀ i, ‖v i‖ < a := fun i =>
    (hcell i).2.1 _ (gridCenter2_mem_shrunk h γ hh.le hγ1.le (z i))
  have hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius2 ≤ 1/8 := by
    intro i
    linarith [hv i]
  have heq : ∀ i, equalAreaHexSpherePatch2 (g i) 0 0 1 (gridShrunkCell2 h γ (z i)) =
      equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2) := fun i =>
    gridShrunkSphere2_eq_affineCube (g i) h γ hh hγ1 (z i)
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ε (UnitCube 2))) := by
    simpa only [heq] using hd
  refine ⟨K,g,v,ε,hε,by linarith,?_,hd',?_,?_,?_,
    equalAreaHexCubeUnion2_probability_real g v (fun _ => cubeMidpoint2) ε hε
      (fun _ => cubeMidpoint2_mem_unitCube) hsmall hd'⟩
  · intro i
    exact ⟨by linarith [hv i],hsmall i,
      equalAreaHexSpherePatch2_cube_isCompact (g i) (v i) cubeMidpoint2 ε hε
        cubeMidpoint2_mem_unitCube (hsmall i)⟩
  · simpa only [heq] using hgap
  · simpa only [heq] using hl
  · simpa only [heq] using hu

end AffineGridCube

section RationalScale
open Set MeasureTheory
open Boundary

/-! ### RationalScale

Normalize the common physical side length by the square root of the actual sphere
area (`hexUnitDensityRadius2 = A^(1/2)`, the root of order `d = 2`). A positive rational
normalized length `t` gives the exact rational patch probability `t²`. Shrinking about the cube midpoint preserves physical inclusion;
no new covering or separation theorem is required. -/

def equalAreaHexNormalizedScale2 (t : ℝ) : ℝ := hexUnitDensityRadius2*t

def centeredCubeRescale2 (t : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  cubeMidpoint2+t • (x-cubeMidpoint2)

theorem equalAreaHexNormalizedScale2_density (t : ℝ) :
    (equalAreaHexNormalizedScale2 t)^2/(sphereAreaD 2).real univ = t^2 := by
  have hA : (sphereAreaD 2).real univ ≠ 0 := (sphereAreaD_univ_pos 2).ne'
  rw [equalAreaHexNormalizedScale2,mul_pow,hexUnitDensityRadius2_pow,mul_div_cancel_left₀ _ hA]

theorem exists_positive_nat_fraction_btwn2 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ a < (p : ℝ)/q ∧ (p : ℝ)/q < b := by
  obtain ⟨r,hrl,hru⟩ := exists_rat_btwn hab
  have hr : 0 < r := by exact_mod_cast (ha.trans hrl)
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have heq : (r : ℝ) = (r.num.natAbs : ℝ)/r.den := by
    rw [Rat.cast_def,← Int.natAbs_of_nonneg hn.le]
    simp
  exact ⟨r.num.natAbs,r.den,Int.natAbs_pos.mpr hn.ne',r.den_pos,
    by simpa only [heq] using hrl,by simpa only [heq] using hru⟩

theorem centeredCubeRescale2_mem_unitCube (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (x : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) : centeredCubeRescale2 t x ∈ UnitCube 2 := by
  intro i
  change 0 ≤ 1/2+t*(x i-1/2) ∧ 1/2+t*(x i-1/2) ≤ 1
  have hlo := mul_nonneg ht (hx i).1
  have hhi := mul_nonneg ht (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith

theorem equalAreaHexPatch_smaller_scale_identity
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v : Fin 2 → ℝ)
    (ε ℓ : ℝ) (hε : ε ≠ 0) (x : Fin 2 → ℝ) :
    equalAreaHexPatch g v cubeMidpoint2 ε (centeredCubeRescale2 (ℓ/ε) x) =
      equalAreaHexPatch g v cubeMidpoint2 ℓ x := by
  have hx : centeredCubeRescale2 (ℓ/ε) x-cubeMidpoint2 =
      (ℓ/ε) • (x-cubeMidpoint2) := by simp [centeredCubeRescale2]
  simp only [equalAreaHexPatch,equalAreaMovingHexChart,hx,map_smul,smul_smul]
  rw [mul_div_cancel₀ ℓ hε]

theorem equalAreaHexSphereCube2_scale_mono
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v : Fin 2 → ℝ)
    (ε ℓ : ℝ) (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hle : ℓ ≤ ε) :
    equalAreaHexSpherePatch2 g v cubeMidpoint2 ℓ (UnitCube 2) ⊆
      equalAreaHexSpherePatch2 g v cubeMidpoint2 ε (UnitCube 2) := by
  rintro y ⟨x,hx,hxy⟩
  refine ⟨centeredCubeRescale2 (ℓ/ε) x,
    centeredCubeRescale2_mem_unitCube _ (div_nonneg hℓ hε.le)
      ((div_le_one hε).mpr hle) x hx,?_⟩
  rw [equalAreaHexPatch_smaller_scale_identity g v ε ℓ hε.ne']
  exact hxy

theorem normalizedCubeMass2_integer_budget (K p q : ℕ) (hq : 0 < q)
    (hm : (K : ℝ)*((p : ℝ)/q)^2 < 1) : K*p^2 < q^2 := by
  have hq2 : 0 < (q : ℝ)^2 := by positivity
  have h : (K : ℝ)*(p : ℝ)^2 < (q : ℝ)^2 := by
    apply (div_lt_one hq2).mp
    simpa only [div_pow,mul_div_assoc] using hm
  exact_mod_cast h

theorem equalAreaHexSphereCube2_normalized_probability_real
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v : Fin 2 → ℝ) (t : ℝ) (ht : 0 < t)
    (hsmall : ‖v‖+equalAreaHexNormalizedScale2 t*equalAreaScaleRadius2 ≤ 1/8) :
    (sphereProbabilityD 2).real
      (equalAreaHexSpherePatch2 g v cubeMidpoint2 (equalAreaHexNormalizedScale2 t) (UnitCube 2)) = t^2 := by
  have he : 0 < equalAreaHexNormalizedScale2 t := mul_pos hexUnitDensityRadius2_pos ht
  rw [equalAreaHexSpherePatch2_probability_real g v cubeMidpoint2 _ he _
    (unitCube_measurableSet 2)
    (equalAreaHexAffine2_cube_domain v cubeMidpoint2 _ he cubeMidpoint2_mem_unitCube hsmall)]
  rw [Measure.real,unitCube_volume,ENNReal.toReal_one,mul_one]
  exact equalAreaHexNormalizedScale2_density t

end RationalScale

section RationalCubeFamily
open Set MeasureTheory
open Boundary

/-! ### RationalCubeFamily

Construct the rationally normalized common-scale family of cube patches of the triangular
lattice on S², retaining near-full sphere probability, uniform smallness and the original
physical gap.  Every patch has probability exactly `(p/q)²`, and `K p² < q²`.  No residual points, global
configuration or energy bound is asserted. -/

theorem sphere2_near_full_rational_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∃ v : Fin K → Fin 2 → ℝ, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ∃ ℓ > 0, ℓ = equalAreaHexNormalizedScale2 ((p : ℝ)/q) ∧
      ℓ*equalAreaScaleRadius2 ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ℓ*equalAreaScaleRadius2 ≤ 1/8 ∧
        IsCompact (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2))
        (equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ℓ (UnitCube 2))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2),
        ∀ y ∈ equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ℓ (UnitCube 2), δ < dist x y) ∧
      1-b < (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) < 1 ∧
      (sphereProbabilityD 2).real
        (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) =
        (K : ℝ)*((p : ℝ)/q)^2 ∧
      (∀ i, (sphereProbabilityD 2).real
        (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) = ((p : ℝ)/q)^2) ∧
      K*p^2 < q^2 := by
  obtain ⟨K,g,v,ε,hε,hscale,hcell,hd,hgap,hl,hu,heq⟩ :=
    sphere2_near_full_small_affine_cubes ρ (min (b/4) (1/4)) hρ
      (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2)
  let w := (sphereProbabilityD 2).real H
  have hw : w = (K : ℝ)*(ε^2/(sphereAreaD 2).real univ) := heq
  obtain ⟨γ,hγ,hγ1,hkeep,_⟩ := shrinkMass2_loss_budget b w hb
    measureReal_nonneg hu.le hl
  have hR := hexUnitDensityRadius2_pos
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hlow : 0 < (1-γ)*ε/hexUnitDensityRadius2 := by positivity
  have hinterval : (1-γ)*ε/hexUnitDensityRadius2 < ε/hexUnitDensityRadius2 := by
    apply div_lt_div_of_pos_right _ hR
    nlinarith
  obtain ⟨p,q,hp,hq,hrl,hru⟩ := exists_positive_nat_fraction_btwn2 _ _ hlow hinterval
  let ℓ := equalAreaHexNormalizedScale2 ((p : ℝ)/q)
  have ht : 0 < (p : ℝ)/q := by positivity
  have hℓ : 0 < ℓ := mul_pos hR ht
  have hℓε : ℓ < ε := by
    simpa only [ℓ,equalAreaHexNormalizedScale2,mul_comm] using (lt_div_iff₀ hR).mp hru
  have hℓlo : (1-γ)*ε < ℓ := by
    simpa only [ℓ,equalAreaHexNormalizedScale2,mul_comm] using (div_lt_iff₀ hR).mp hrl
  have hsmall : ∀ i, ‖v i‖+ℓ*equalAreaScaleRadius2 ≤ 1/8 := by
    intro i
    have he := mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius2_pos.le
    linarith [(hcell i).2.1]
  have hsub : ∀ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2) ⊆
      equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ε (UnitCube 2) := fun i =>
    equalAreaHexSphereCube2_scale_mono (g i) (v i) ε ℓ hε hℓ.le hℓε.le
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) cubeMidpoint2 ℓ (UnitCube 2))) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  have hmass := equalAreaHexCubeUnion2_probability_real g v (fun _ => cubeMidpoint2) ℓ hℓ
    (fun _ => cubeMidpoint2_mem_unitCube) hsmall hd'
  have hmass' : (sphereProbabilityD 2).real
      (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) =
      (K : ℝ)*((p : ℝ)/q)^2 := by
    rw [hmass]
    change (K : ℝ)*((equalAreaHexNormalizedScale2 ((p : ℝ)/q))^2/(sphereAreaD 2).real univ) = _
    rw [equalAreaHexNormalizedScale2_density]
  have hupper : (sphereProbabilityD 2).real
      (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) < 1 :=
    (measureReal_mono (iUnion_mono hsub) (measure_ne_top _ _)).trans_lt hu
  have hlower : 1-b < (sphereProbabilityD 2).real
      (⋃ i, equalAreaHexSpherePatch2 (g i) (v i) cubeMidpoint2 ℓ (UnitCube 2)) := by
    apply hkeep.trans_le
    calc
      (1-γ)^2*w = (K : ℝ)*(((1-γ)*ε)^2/(sphereAreaD 2).real univ) := by
        rw [hw,mul_pow]
        ring
      _ ≤ (K : ℝ)*(ℓ^2/(sphereAreaD 2).real univ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hℓlo.le 2) hA.le) (Nat.cast_nonneg _)
      _ = _ := hmass.symm
  have hbudget : K*p^2 < q^2 := normalizedCubeMass2_integer_budget K p q hq
    (by simpa only [hmass'] using hupper)
  refine ⟨K,g,v,p,q,hp,hq,ℓ,hℓ,rfl,
    (mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius2_pos.le).trans hscale,
    ?_,hd',?_,hlower,hupper,hmass',?_,hbudget⟩
  · intro i
    exact ⟨(hcell i).1,hsmall i,
      equalAreaHexSpherePatch2_cube_isCompact (g i) (v i) cubeMidpoint2 ℓ hℓ
        cubeMidpoint2_mem_unitCube (hsmall i)⟩
  · obtain ⟨δ,hδ,hsep⟩ := hgap
    exact ⟨δ,hδ,fun i j hij x hx y hy => hsep i j hij x (hsub i hx) y (hsub j hy)⟩
  · intro i
    exact equalAreaHexSphereCube2_normalized_probability_real (g i) (v i) _ ht (hsmall i)

end RationalCubeFamily

end SphericalRiesz
end
end

section

/-! The actual twelfth-order grid retains the existing Hex theta rows and
computed common rational-density large-alpha budgets. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Boundary corrections retain control by their distinct integer labels. -/
theorem twelveRule_label_sub_leS2 {n : ℕ} (hn : 74 ≤ n) (u w : TwelveNodeIndex n) :
    |(twelveMidpointLabel n u:ℝ)-(twelveMidpointLabel n w:ℝ)| ≤
      2*|twelveUnscaledRuleNode n u-twelveUnscaledRuleNode n w| := by
  have haux : ∀ i j : TwelveNodeIndex n, twelveMidpointLabel n i < twelveMidpointLabel n j →
      |(twelveMidpointLabel n i:ℝ)-(twelveMidpointLabel n j:ℝ)| ≤
        2*|twelveUnscaledRuleNode n i-twelveUnscaledRuleNode n j| := by
    intro i j hij
    have hg : (twelveMidpointLabel n i:ℝ)+1 ≤ twelveMidpointLabel n j := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hi := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hn i)
    have hj := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hn j)
    rw [abs_of_nonpos (by linarith : (twelveMidpointLabel n i:ℝ)-(twelveMidpointLabel n j:ℝ) ≤ 0)]
    have hdiff : -(twelveMidpointLabel n i:ℝ)+(twelveMidpointLabel n j:ℝ) ≤
        2*(twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i) := by linarith
    calc
      _ ≤ 2*(twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i) := by linarith
      _ ≤ 2*|twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = _ := by rw [abs_sub_comm]
  rcases lt_trichotomy (twelveMidpointLabel n u) (twelveMidpointLabel n w) with h | h | h
  · exact haux u w h
  · simp [h]
  · simpa only [abs_sub_comm] using haux w u h

def hexTwelfthLabel2 (n : ℕ) (hn : 74 ≤ n) :
    (Fin 2 → TwelveNodeIndex n) ↪ hexLattice where
  toFun u := ⟨hexIntegerPoint (fun i => (twelveMidpointLabel n (u i):ℤ)),
    (hexLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := hexMap_injective (congrArg (fun z : hexLattice => WithLp.ofLp (z : HexAmbient)) h)
    funext i
    apply twelveMidpointLabel_injective hn
    have hi : (twelveMidpointLabel n (u i):ℝ) = (twelveMidpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem hexTwelfthLabel2_norm_le {n : ℕ} (hn : 74 ≤ n)
    (u w : Fin 2 → TwelveNodeIndex n) :
    ‖((hexTwelfthLabel2 n hn w-hexTwelfthLabel2 n hn u : hexLattice) : HexAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)*‖twelveCubeNode 2 n u-twelveCubeNode 2 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 2 → ℝ := fun i => (twelveMidpointLabel n (u i):ℝ)-(twelveMidpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖twelveCubeNode 2 n u-twelveCubeNode 2 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := twelveRule_label_sub_leS2 hn (u i) (w i)
    have he : |twelveUnscaledRuleNode n (u i)-twelveUnscaledRuleNode n (w i)| =
        (n:ℝ)*|twelveCubeNode 2 n u i-twelveCubeNode 2 n w i| := by
      simp only [twelveCubeNode,twelveRuleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|twelveCubeNode 2 n u i-twelveCubeNode 2 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖twelveCubeNode 2 n u-twelveCubeNode 2 n w‖ := by
        have hi := norm_le_pi_norm (twelveCubeNode 2 n u-twelveCubeNode 2 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((hexTwelfthLabel2 n hn w-hexTwelfthLabel2 n hn u : hexLattice) : HexAmbient)‖ =
      ‖equalAreaFlatDerivative2 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative2,
        equalAreaFlatDerivative2_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖hexIntegerPoint (fun i => (twelveMidpointLabel n (w i):ℤ))-
      hexIntegerPoint (fun i => (twelveMidpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (hexMap z)‖
    rw [norm_sub_rev,hexIntegerPoint,hexIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative2‖*‖z‖ := equalAreaFlatDerivative2.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative2‖*((2*(n:ℝ))*‖twelveCubeNode 2 n u-twelveCubeNode 2 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaHexTwelfth2_gaussian_row {n : ℕ} (hn : 74 ≤ n)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y))
    (u : Fin 2 → TwelveNodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨twelveCubeNode 2 n u,fun i => ⟨(twelveCubeNode_mem_open 2 n hn u i).1.le,(twelveCubeNode_mem_open 2 n hn u i).2.le⟩⟩)
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨twelveCubeNode 2 n w,fun i => ⟨(twelveCubeNode_mem_open 2 n hn w i).1.le,(twelveCubeNode_mem_open 2 n hn w i).2.le⟩⟩)) ≤
    hexGaussianThetaReal2 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative2_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply hexPatchGaussian_row_le (hexTwelfthLabel2 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaHexPatch g v c ε (twelveCubeNode 2 n i))
    (equalAreaHexPatch g v c ε (twelveCubeNode 2 n j))
  rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
  have hi : twelveCubeNode 2 n i ∈ UnitCube 2 := fun k => ⟨(twelveCubeNode_mem_open 2 n hn i k).1.le,(twelveCubeNode_mem_open 2 n hn i k).2.le⟩
  have hj : twelveCubeNode 2 n j ∈ UnitCube 2 := fun k => ⟨(twelveCubeNode_mem_open 2 n hn j k).1.le,(twelveCubeNode_mem_open 2 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := hexTwelfthLabel2_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
  have hdiv : ‖((hexTwelfthLabel2 n hn j-hexTwelfthLabel2 n hn i : hexLattice) :
      HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖twelveCubeNode 2 n i-twelveCubeNode 2 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((hexTwelfthLabel2 n hn j-hexTwelfthLabel2 n hn i : hexLattice) : HexAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by ring
    _ ≤ ε*L*‖twelveCubeNode 2 n i-twelveCubeNode 2 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith


/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def hexTwelfthSphereNodes2 (n : ℕ) (hn : 74 ≤ n)
    (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    (Fin 2 → TwelveNodeIndex n) → SphereD 2 := fun u =>
  equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
    ⟨twelveCubeNode 2 n u,fun i =>
      ⟨(twelveCubeNode_mem_open 2 n hn u i).1.le,(twelveCubeNode_mem_open 2 n hn u i).2.le⟩⟩

/-- The actual twelfth-order sphere nodes are all distinct. -/
theorem hexTwelfthSphereNodes2_injective (n : ℕ) (hn : 74 ≤ n)
    (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    Function.Injective (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall) := by
  intro u w h
  have hcube := (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall).injective h
  exact twelveCubeNode_injective 2 n hn (congrArg Subtype.val hcube)

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaHexTwelfth2_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (n : ℕ) (hn : 74 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel2 t p
        (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^2*hexGaussianTailBudget2 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative2_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative2‖*(1+‖hexInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((hexTwelfthLabel2 n hn j-hexTwelfthLabel2 n hn i :
      hexLattice) : HexAmbient)‖ ≤
      dist (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall i)
        (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaHexPatch g v c ε (twelveCubeNode 2 n i))
      (equalAreaHexPatch g v c ε (twelveCubeNode 2 n j))
    rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
    have hi : twelveCubeNode 2 n i ∈ UnitCube 2 := fun k =>
      ⟨(twelveCubeNode_mem_open 2 n hn i k).1.le,(twelveCubeNode_mem_open 2 n hn i k).2.le⟩
    have hj : twelveCubeNode 2 n j ∈ UnitCube 2 := fun k =>
      ⟨(twelveCubeNode_mem_open 2 n hn j k).1.le,(twelveCubeNode_mem_open 2 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := hexTwelfthLabel2_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
    have hdiv : ‖((hexTwelfthLabel2 n hn j-hexTwelfthLabel2 n hn i : hexLattice) :
        HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖twelveCubeNode 2 n i-twelveCubeNode 2 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖hexInverseMap‖)))*
          (‖((hexTwelfthLabel2 n hn j-hexTwelfthLabel2 n hn i : hexLattice) :
            HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖hexInverseMap‖)))*‖twelveCubeNode 2 n i-twelveCubeNode 2 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := hexPatch_shortRange_budget_le (hexTwelfthLabel2 n hn)
    (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 2 → TwelveNodeIndex n) = n^2 := by
    simp [twelveNodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- At the actual n^2 sphere density the corrected foreground has one explicit budget for
all n>=74.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaHexTwelfth2_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 74 ≤ n),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 (n^2)) p
        (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall u)
        (hexTwelfthSphereNodes2 n hn g v c hc ε hε hsmall w))/(n:ℝ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexTwelfth2_shortRange_uniform
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
N=(d*m)^2 and epsilon=r*a/d, the positive theta scale depends only on r.
Thus the computed foreground bound is common across a,d,m, rather than merely a fixed chart. -/
theorem equalAreaHexTwelfth2_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 74 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p
        (hexTwelfthSphereNodes2 (a*m) hn g v c hc ε hε hsmall u)
        (hexTwelfthSphereNodes2 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^2 ≤
      hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaHexTwelfth2_shortRange_uniform
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


end SphericalRiesz
end
end

section

/-! Physical sphere form of the twelfth-order bump error at exact mass.

For one small Hex cube patch at the exact-mass rational allocation `ε d = r₀ a`, `n = a m`,
`N = (d m)^2`, the node sum of an ambient Gaussian bump differs from `N ∫_patch` by at most
`K (n⁻¹² + (2πα)⁶) N ∫_patch` of the softened bump.  Summing over a finite disjoint family of one
common scale bounds the foreground bump error by the softened bump field of the whole sphere.
No configuration, budget or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

/-- The physical sphere patch of a small Hex cube patch. -/
def smallHexSpherePatch2 (p : SmallHexCubePatch2) : Set (SphereD 2) :=
  equalAreaHexSpherePatch2 p.g p.v p.c p.ε (UnitCube 2)

theorem smallHexSpherePatch2_measurable (p : SmallHexCubePatch2) :
    MeasurableSet (smallHexSpherePatch2 p) :=
  equalAreaHexSpherePatch2_measurable p.g p.v p.c p.ε p.ε_pos _ (unitCube_measurableSet 2)
    (equalAreaHexAffine2_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small)

theorem smallHexCubeMap2_continuousOn (p : SmallHexCubePatch2) :
    ContinuousOn (smallHexCubeMap2 p) (UnitCube 2) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp
    (equalAreaHexCubeEmbedding2_continuous p.g p.v p.c p.ε p.ε_pos p.c_mem p.small)

/-- Transport of a patch integral to the coordinate cube, for continuous ambient functions. -/
theorem smallHexSpherePatch2_setIntegral (p : SmallHexCubePatch2) (f : AmbientD 2 → ℝ)
    (hf : Continuous f) :
    (∫ y in smallHexSpherePatch2 p, f (y : AmbientD 2) ∂(sphereProbabilityD 2)) =
      equalAreaHexPatchProbabilityDensity2 p.ε*
        cubeIntegral 2 (fun x => f (smallHexCubeMap2 p x)) := by
  have h := cubeIntegral_eq_setIntegral_on 2 (fun x => f (smallHexCubeMap2 p x))
    (hf.comp_continuousOn (smallHexCubeMap2_continuousOn p))
  rw [h]
  exact equalAreaHexSpherePatch2_integral p.g p.v p.c p.ε p.ε_pos p.c_mem p.small f

/-- Twelfth-order nodes of a small patch on the sphere. -/
def smallHexPatchNodes2 (p : SmallHexCubePatch2) (n : ℕ) (hn : 74 ≤ n) :
    (Fin 2 → TwelveNodeIndex n) → SphereD 2 :=
  hexTwelfthSphereNodes2 n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallHexPatchNodes2_injective (p : SmallHexCubePatch2) (n : ℕ) (hn : 74 ≤ n) :
    Function.Injective (smallHexPatchNodes2 p n hn) :=
  hexTwelfthSphereNodes2_injective n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallHexPatchNodes2_coe (p : SmallHexCubePatch2) (n : ℕ) (hn : 74 ≤ n)
    (u : Fin 2 → TwelveNodeIndex n) :
    (smallHexPatchNodes2 p n hn u : AmbientD 2) = smallHexCubeMap2 p (twelveCubeNode 2 n u) :=
  rfl

theorem smallHexPatchNodes2_mem (p : SmallHexCubePatch2) (n : ℕ) (hn : 74 ≤ n)
    (u : Fin 2 → TwelveNodeIndex n) :
    smallHexPatchNodes2 p n hn u ∈ smallHexSpherePatch2 p := by
  refine ⟨twelveCubeNode 2 n u, fun i => ⟨(twelveCubeNode_mem_open 2 n hn u i).1.le,
    (twelveCubeNode_mem_open 2 n hn u i).2.le⟩, rfl⟩

theorem ambientBump3_sphere_integrable {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 2) :
    Integrable (fun y : SphereD 2 => ambientBump3 t (y : AmbientD 2) z)
      (sphereProbabilityD 2) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold ambientBump3; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (ambientBump3_nonneg _ _ _)]
  exact ambientBump3_le_one ht _ _

theorem bumpField3_sphere_eq (t : ℝ) (z : AmbientD 2) :
    bumpField3 t ambientSphereProbability2 z =
      ∫ y : SphereD 2, ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2) := by
  unfold bumpField3 ambientSphereProbability2
  rw [integral_map (by fun_prop) (by unfold ambientBump3; fun_prop)]

/-- One patch, exact mass: the node sum against `N ∫_patch` of the bump. -/
theorem smallHexPatch_bump_sphere_error2 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallHexCubePatch2,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 2,
      |(∑ u : Fin 2 → TwelveNodeIndex (a*m),
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α)
            (smallHexPatchNodes2 p (a*m) hn u : AmbientD 2) z)-
        (((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)| ≤
      bumpErrorConst2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6)*
        ((((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 p,
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α/8) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_rational_small_alpha2
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε a d m hd hm hratio hn α hα z
  have hquad := hb p hv hε hexUnitDensityRadius2 hexUnitDensityRadius2_twelfth_mesh_bound
    a d m hd hm hratio hn α hα z
  have hτ := sphereGaussian_exact_mass_bump_scale2 a d m hd p.ε α hratio
  set t := sphereGaussianScale2 ((d*m)^2) α with ht
  have hn0 : (0:ℝ) < ((a*m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < a*m)
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdens := hexTwelfth_rational_exact_patch_mass2 a d m hd hm p.ε hratio
  have hsum : (∑ u : Fin 2 → TwelveNodeIndex (a*m),
      ambientBump3 t (smallHexPatchNodes2 p (a*m) hn u : AmbientD 2) z) =
      ((a*m:ℕ):ℝ)^2*twelveCubeQuadrature 2 (a*m)
        (fun x => ambientBump3 t (smallHexCubeMap2 p x) z) := by
    rw [twelveCubeQuadrature_as_node_sum, mul_div_cancel₀ _ (pow_pos hn0 2).ne']
    exact Finset.sum_congr rfl fun u _ => by rw [smallHexPatchNodes2_coe]
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
  rw [hsoft] at hquad
  rw [hsum, hI t, hI (t/8), ← mul_sub, abs_mul, abs_of_pos (pow_pos hn0 2)]
  calc
    _ ≤ ((a*m:ℕ):ℝ)^2*(bumpErrorConst2 patchChartUpper2 patchChartLower2/((a*m:ℕ):ℝ)^12*
        (1+(2*t*p.ε^2)^6)*
        cubeIntegral 2 (fun x => ambientBump3 (t/8) (smallHexCubeMap2 p x) z)) :=
      mul_le_mul_of_nonneg_left hquad (by positivity)
    _ = _ := by
      rw [hτ]
      field_simp

/-- A finite disjoint family of one common scale: the foreground bump error is bounded by the
softened bump field of the whole sphere. -/
theorem hexPatchFamily_bump_error2 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 2,
      |(∑ i, ∑ u : Fin 2 → TwelveNodeIndex (a*m),
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α)
            (smallHexPatchNodes2 (P i) (a*m) hn u : AmbientD 2) z)-
        (((d*m)^2:ℕ):ℝ)*∫ y in ⋃ i, smallHexSpherePatch2 (P i),
          ambientBump3 (sphereGaussianScale2 ((d*m)^2) α) (y : AmbientD 2) z
            ∂(sphereProbabilityD 2)| ≤
      bumpErrorConst2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6)*
        ((((d*m)^2:ℕ):ℝ)*
          bumpField3 (sphereGaussianScale2 ((d*m)^2) α/8) ambientSphereProbability2 z) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_bump_sphere_error2
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα z
  have hts : 0 < sphereGaussianScale2 ((d*m)^2) α :=
    sphereGaussianScale2_pos (by positivity) hα.1
  set t := sphereGaussianScale2 ((d*m)^2) α with ht
  set C := bumpErrorConst2 patchChartUpper2 patchChartLower2*
    (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6) with hC
  have hC0 : 0 ≤ C := by
    have hK : 0 ≤ bumpErrorConst2 patchChartUpper2 patchChartLower2 := by
      unfold bumpErrorConst2 twelfthConstS2
      have := one_le_patchChartUpper2
      have := gaussRuleConst12_nonnegS2
      positivity
    have hα0 := hα.1
    rw [hC]
    positivity
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
  rw [hsplit t hts.le, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ u : Fin 2 → TwelveNodeIndex (a*m),
          ambientBump3 t (smallHexPatchNodes2 (P i) (a*m) hn u : AmbientD 2) z)-
        (((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*((((d*m)^2:ℕ):ℝ)*∫ y in smallHexSpherePatch2 (P i),
          ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2)) :=
      Finset.sum_le_sum fun i _ => hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z
    _ = C*((((d*m)^2:ℕ):ℝ)*∫ y in ⋃ i, smallHexSpherePatch2 (P i),
          ambientBump3 (t/8) (y : AmbientD 2) z ∂(sphereProbabilityD 2)) := by
      rw [hsplit (t/8) (by positivity), Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact mul_le_mul_of_nonneg_left hle (by positivity)

end SphericalRiesz
end
end

section

/-! Neutralized Gaussian defect of a foreground family against the smooth residual background.

The foreground points together with `N σ` restricted to the complement `R` of the patches form
a finite measure of total charge `N`.  Its neutralized Gaussian energy against `N σ` is the
squared `L²` norm of the foreground bump error, so the twelfth-order family bound gives

`defect(α) ≤ N (C₀ + G (d/a)²⁴ (d m)^(-q) α^(-q/2))`  for every `α ∈ (0,4]`.

The first constant is independent of the family; the second term vanishes as `m → ∞`.  The
residual points, the common budget of an actual configuration and the attaining sequence are
not constructed here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- `L²` norm of the softened sphere bump field. -/
theorem bumpField3_sphere_sq_integral {t : ℝ} (ht : 0 < t) :
    ∫ z, (bumpField3 t ambientSphereProbability2 z)^2 =
      (Real.pi/(4*t))^((3:ℝ)/2)*sphereGaussianBackground2 t := by
  have h := gaussianMeasurePair_eq_bump3 ht ambientSphereProbability2 ambientSphereProbability2
  rw [ambientSphereProbability2_kernel_pair] at h
  have hc : (Real.pi/(4*t))^((3:ℝ)/2)*(4*t/Real.pi)^((3:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : Real.pi/(4*t)*(4*t/Real.pi) = 1 := by field_simp
    rw [this, Real.one_rpow]
  simp_rw [sq]
  rw [h, ← mul_assoc, hc, one_mul]

/-- Foreground points together with the smooth background `N σ` restricted to `R`. -/
def mixedForegroundMeasure2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) : Measure (AmbientD 2) :=
  finitePointMeasure (fun i => (x i : AmbientD 2)) +
    (N : ℝ≥0) • ((sphereProbabilityD 2).restrict R).map (fun y : SphereD 2 => (y : AmbientD 2))

instance mixedForegroundMeasure2_finite {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) : IsFiniteMeasure (mixedForegroundMeasure2 x N R) := by
  unfold mixedForegroundMeasure2
  infer_instance

theorem ambientBump3_integrable_finite {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 2)
    (μ : Measure (AmbientD 2)) [IsFiniteMeasure μ] :
    Integrable (fun x => ambientBump3 t x z) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold ambientBump3; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (ambientBump3_nonneg _ _ _)]
  exact ambientBump3_le_one ht _ _

theorem bumpField3_mixedForeground {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 2) :
    bumpField3 t (mixedForegroundMeasure2 x N R) z =
      (∑ i, ambientBump3 t (x i : AmbientD 2) z)+
        (N:ℝ)*∫ y in R, ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2) := by
  unfold bumpField3 mixedForegroundMeasure2
  rw [integral_add_measure (ambientBump3_integrable_finite ht z _)
    (ambientBump3_integrable_finite ht z _), finitePointMeasure_integral,
    integral_smul_nnreal_measure, integral_map (by fun_prop) (by unfold ambientBump3; fun_prop),
    NNReal.smul_def, NNReal.coe_natCast, smul_eq_mul]

/-- The bump error of the mixed measure is the foreground error against `N σ` on the patches. -/
theorem mixedForeground_bumpError_eqS2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (A : Set (SphereD 2)) (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 2) :
    bumpField3 t (mixedForegroundMeasure2 x N Aᶜ) z-
        (N:ℝ)*bumpField3 t ambientSphereProbability2 z =
      (∑ i, ambientBump3 t (x i : AmbientD 2) z)-
        (N:ℝ)*∫ y in A, ambientBump3 t (y : AmbientD 2) z ∂(sphereProbabilityD 2) := by
  rw [bumpField3_mixedForeground x N Aᶜ ht, bumpField3_sphere_eq,
    ← integral_add_compl hA (ambientBump3_sphere_integrable ht z)]
  ring

/-- All twelfth-order nodes of a patch family of one common scale. -/
def hexFamilyNodes2 {K : ℕ} (P : Fin K → SmallHexCubePatch2) (n : ℕ) (hn : 74 ≤ n) :
    Fin K × (Fin 2 → TwelveNodeIndex n) → SphereD 2 :=
  fun q => smallHexPatchNodes2 (P q.1) n hn q.2

/-- The union of the physical patches of a family. -/
def hexFamilyUnion2 {K : ℕ} (P : Fin K → SmallHexCubePatch2) : Set (SphereD 2) :=
  ⋃ i, smallHexSpherePatch2 (P i)

theorem hexFamilyUnion2_measurable {K : ℕ} (P : Fin K → SmallHexCubePatch2) :
    MeasurableSet (hexFamilyUnion2 P) :=
  MeasurableSet.iUnion fun i => smallHexSpherePatch2_measurable (P i)

theorem bumpErrorConst2_patch_nonneg :
    0 ≤ bumpErrorConst2 patchChartUpper2 patchChartLower2 := by
  unfold bumpErrorConst2 twelfthConstS2
  have := one_le_patchChartUpper2
  have := gaussRuleConst12_nonnegS2
  positivity

/-- Neutralized Gaussian defect of the foreground family with smooth residual background. -/
theorem hexPatchFamily_mixed_defect_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodes2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (8:ℝ)^((3:ℝ)/2)*(bumpErrorConst2 patchChartUpper2 patchChartLower2*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6))^2*(((d*m)^2:ℕ):ℝ)^2*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := hexPatchFamily_bump_error2
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  have hts : 0 < sphereGaussianScale2 ((d*m)^2) α :=
    sphereGaussianScale2_pos (by positivity) hα.1
  set t := sphereGaussianScale2 ((d*m)^2) α with ht
  set C := bumpErrorConst2 patchChartUpper2 patchChartLower2*
    (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6) with hC
  set NR : ℝ := (((d*m)^2:ℕ):ℝ) with hNR
  have ht8 : 0 < t/8 := by positivity
  let W : AmbientD 2 → ℝ := fun z => C*(NR*bumpField3 (t/8) ambientSphereProbability2 z)
  have hWsq : (fun z => W z^2) = fun z => (C*NR)^2*
      (bumpField3 (t/8) ambientSphereProbability2 z*
        bumpField3 (t/8) ambientSphereProbability2 z) := by
    funext z
    simp only [W]
    ring
  have hWi : Integrable (fun z => W z^2) := by
    rw [hWsq]
    exact (bumpField3_mul_integrable ht8 ambientSphereProbability2
      ambientSphereProbability2).const_mul _
  have hle : ∀ z, |bumpField3 t (mixedForegroundMeasure2 (hexFamilyNodes2 P (a*m) hn)
      ((d*m)^2) (hexFamilyUnion2 P)ᶜ) z-NR*bumpField3 t ambientSphereProbability2 z| ≤ W z := by
    intro z
    rw [hNR, mixedForeground_bumpError_eqS2 _ _ _ (hexFamilyUnion2_measurable P) hts.le,
      Fintype.sum_prod_type]
    exact hb P hv hε hdisj a d m hd hm hratio hn α hα z
  have hmain := gaussianMeasureDefect_le_of_bump3 hts NR _ ambientSphereProbability2 hWi hle
  have hint : (∫ z, W z^2) = (C*NR)^2*((Real.pi/(4*(t/8)))^((3:ℝ)/2)*
      sphereGaussianBackground2 (t/8)) := by
    rw [hWsq, integral_const_mul, ← bumpField3_sphere_sq_integral ht8]
    simp_rw [sq]
  have hconst : (4*t/Real.pi)^((3:ℝ)/2)*(Real.pi/(4*(t/8)))^((3:ℝ)/2) = (8:ℝ)^((3:ℝ)/2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    _ ≤ (4*t/Real.pi)^((3:ℝ)/2)*∫ z, W z^2 := hmain
    _ = ((4*t/Real.pi)^((3:ℝ)/2)*(Real.pi/(4*(t/8)))^((3:ℝ)/2))*(C*NR)^2*
        sphereGaussianBackground2 (t/8) := by rw [hint]; ring
    _ = _ := by rw [hconst]; ring

/-- Interpolation between two upper bounds. -/
theorem le_rpow_mul_rpow_of_leS2 {x A B θ : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) (hB : x ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : x ≤ A^(1-θ)*B^θ := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (Real.rpow_nonneg (h ▸ hA) _) (Real.rpow_nonneg (h ▸ hB) _)
  · calc
      x = x^(1-θ)*x^θ := by
        rw [← Real.rpow_add h]
        simp
      _ ≤ A^(1-θ)*B^θ :=
        mul_le_mul (Real.rpow_le_rpow hx hA (by linarith)) (Real.rpow_le_rpow hx hB hθ0)
          (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hA) _)

/-- Family-independent part of the foreground small-alpha profile. -/
def hexForegroundProfileConst2 : ℝ :=
  2*(8:ℝ)^((3:ℝ)/2)*(bumpErrorConst2 patchChartUpper2 patchChartLower2)^2*(16*Real.pi)^12

/-- Gain of the refinement-dependent part of the foreground small-alpha profile. -/
def hexForegroundProfileGain2 (q : ℝ) : ℝ :=
  2*(8:ℝ)^((3:ℝ)/2)*(bumpErrorConst2 patchChartUpper2 patchChartLower2)^2*(8:ℝ)^(q/2)

theorem hexForegroundProfileConst2_nonneg : 0 ≤ hexForegroundProfileConst2 := by
  unfold hexForegroundProfileConst2
  positivity

theorem hexForegroundProfileGain2_nonneg (q : ℝ) : 0 ≤ hexForegroundProfileGain2 q := by
  unfold hexForegroundProfileGain2
  positivity

/-- Small-alpha profile of the foreground defect: a family-independent constant plus a term
which vanishes under refinement. -/
theorem hexPatchFamily_mixed_defect_profile :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (q : ℝ), 0 < q → q ≤ 2 → ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale2 ((d*m)^2) α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodes2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (((d*m)^2:ℕ):ℝ)*(hexForegroundProfileConst2+
        hexForegroundProfileGain2 q*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-q)*α^(-(q/2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := hexPatchFamily_mixed_defect_le
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn q hq hq2 α hα
  have hmain := hb P hv hε hdisj a d m hd hm hratio hn α hα
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at hn
    · exact h
  have hα0 : 0 < α := hα.1
  have hNpos : 0 < (d*m)^2 := by positivity
  set K₀ := bumpErrorConst2 patchChartUpper2 patchChartLower2 with hK₀
  have hK₀0 : 0 ≤ K₀ := bumpErrorConst2_patch_nonneg
  set D : ℝ := ((d*m:ℕ):ℝ) with hD
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast Nat.mul_pos hd hm
  have hnpos : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hNR : (((d*m)^2:ℕ):ℝ) = D^2 := by rw [hD]; push_cast; ring
  rw [hNR] at hmain ⊢
  -- the scaled background
  have hscale : sphereGaussianScale2 ((d*m)^2) α/8 = sphereGaussianScale2 ((d*m)^2) (α/8) := by
    unfold sphereGaussianScale2
    ring
  set B := sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) α/8) with hBdef
  have hB0 : 0 ≤ B := sphereGaussianBackground2_nonneg _
  have hB1 : B ≤ 1 := sphereGaussianBackground2_le_one
    (by rw [hscale]; exact (sphereGaussianScale2_pos hNpos (by positivity)).le)
  have hcap : D^2*B ≤ (8:ℝ)/α := by
    have h := sphereGaussianBackground2_scaled_cap hNpos (α := α/8) (by positivity)
    rw [← hscale, ← hBdef, hNR] at h
    simpa only [inv_div, div_one] using h
  have hx0 : 0 ≤ D^2*B := by positivity
  have hxN : D^2*B ≤ D^2 := by nlinarith [pow_pos hDpos 2]
  have hθ0 : 0 ≤ q/2 := by positivity
  have hθ1 : q/2 ≤ 1 := by linarith
  have hinterp := le_rpow_mul_rpow_of_leS2 hx0 hxN hcap hθ0 hθ1
  -- the two rpow simplifications
  have hpowN : (D^2)^(1-q/2) = D^2*D^(-q) := by
    calc (D^2)^(1-q/2) = (D^(2:ℝ))^(1-q/2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      _ = D^((2:ℝ)*(1-q/2)) := (Real.rpow_mul hDpos.le _ _).symm
      _ = D^((2:ℝ)+(-q)) := by congr 1; ring
      _ = D^(2:ℝ)*D^(-q) := Real.rpow_add hDpos _ _
      _ = D^2*D^(-q) := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hpowU : ((8:ℝ)/α)^(q/2) = (8:ℝ)^(q/2)*α^(-(q/2)) := by
    rw [Real.div_rpow (by norm_num) hα0.le, Real.rpow_neg hα0.le, div_eq_mul_inv]
  rw [hpowN, hpowU] at hinterp
  have hDq : 0 < D^(-q) := Real.rpow_pos_of_pos hDpos _
  have hαq : 0 < α^(-(q/2)) := Real.rpow_pos_of_pos hα0 _
  have h8q : 0 < (8:ℝ)^(q/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hT : 0 < (8:ℝ)^((3:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : (K₀*(1/n^12+(2*Real.pi*α)^6))^2 ≤
      K₀^2*(2/n^2+2*(2*Real.pi)^12*α^12) := by
    have h : (1/n^12+(2*Real.pi*α)^6)^2 ≤ 2/n^2+2*(2*Real.pi)^12*α^12 := by
      have h1 : (1/n^12+(2*Real.pi*α)^6)^2 ≤ 2*(1/n^12)^2+2*((2*Real.pi*α)^6)^2 := by
        nlinarith [sq_nonneg (1/n^12-(2*Real.pi*α)^6)]
      calc _ ≤ 2*(1/n^12)^2+2*((2*Real.pi*α)^6)^2 := h1
        _ = 2/n^24+2*(2*Real.pi)^12*α^12 := by field_simp
        _ ≤ _ := by
          have hn1 : 1 ≤ n := by rw [hndef]; exact_mod_cast (by omega : 1 ≤ a*m)
          have hpow : n^2 ≤ n^24 := pow_le_pow_right₀ hn1 (by norm_num)
          gcongr
    calc _ = K₀^2*(1/n^12+(2*Real.pi*α)^6)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have hratio' : D^2/n^2 = ((d:ℝ)/(a:ℝ))^2 := by
    rw [hD, hndef]
    push_cast
    have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  -- assemble
  have hfirst : α^12*(D^2*B) ≤ (8:ℝ)^12 := by
    calc α^12*(D^2*B) ≤ α^12*((8:ℝ)/α) :=
          mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 8*α^11 := by field_simp
      _ ≤ 8*(8:ℝ)^11 := by gcongr; linarith [hα.2]
      _ = (8:ℝ)^12 := by ring
  calc
    _ ≤ (8:ℝ)^((3:ℝ)/2)*(K₀*(1/n^12+(2*Real.pi*α)^6))^2*(D^2)^2*B := hmain
    _ = (8:ℝ)^((3:ℝ)/2)*(K₀*(1/n^12+(2*Real.pi*α)^6))^2*D^2*(D^2*B) := by ring
    _ ≤ (8:ℝ)^((3:ℝ)/2)*(K₀^2*(2/n^2+2*(2*Real.pi)^12*α^12))*D^2*(D^2*B) := by
      gcongr
    _ = D^2*((8:ℝ)^((3:ℝ)/2)*K₀^2*(2*(2*Real.pi)^12*(α^12*(D^2*B))+
        2/n^2*(D^2*B))) := by ring
    _ ≤ D^2*((8:ℝ)^((3:ℝ)/2)*K₀^2*(2*(2*Real.pi)^12*(8:ℝ)^12+
        2/n^2*(D^2*D^(-q)*((8:ℝ)^(q/2)*α^(-(q/2)))))) := by
      gcongr
    _ = _ := by
      unfold hexForegroundProfileConst2 hexForegroundProfileGain2
      rw [← hK₀, ← hratio']
      field_simp
      ring

end SphericalRiesz
end
end

section

/-! The small-alpha Gaussian budget of a configuration on S²⁴ as a pair kernel.

`κ(x,y) = ∫_{(0,4]} α^(q-1) e^{-c α |x-y|²} dα` is symmetric, bounded by its constant diagonal
`4^q/q`, jointly measurable, and commutes with integration against finite measures.  The actual
budget of a configuration is `N H_q(X) = Σ_{i,j} κ(x_i,x_j) - N² β`.  No bound of the budget is
asserted here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

/-- Weighted Gaussian kernel of the small-alpha budget. -/
def smallBudgetKernel2 (c q : ℝ) (x y : SphereD 2) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*sphereGaussianKernel2 (c*α) x y

theorem rpow_sub_one_integrableOn_IocS2 {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun α : ℝ => α^(q-1)) (Ioc 0 4) :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1) (a := 0) (b := 4)).1

theorem rpow_sub_one_integral_IocS2 {q : ℝ} (hq : 0 < q) :
    ∫ α in Ioc (0:ℝ) 4, α^(q-1) = 4^q/q := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 4),
    integral_rpow (Or.inl (by linarith))]
  rw [show q-1+1 = q by ring, Real.zero_rpow hq.ne']
  ring

theorem smallBudgetIntegrand2_measurable (c q : ℝ) (x y : SphereD 2) :
    Measurable (fun α : ℝ => α^(q-1)*sphereGaussianKernel2 (c*α) x y) := by
  unfold sphereGaussianKernel2
  exact (measurable_id.pow_const (q-1)).mul (by fun_prop)

theorem smallBudgetIntegrand2_integrableOn {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (x y : SphereD 2) :
    IntegrableOn (fun α : ℝ => α^(q-1)*sphereGaussianKernel2 (c*α) x y) (Ioc 0 4) := by
  refine Integrable.mono' (rpow_sub_one_integrableOn_IocS2 hq)
    (smallBudgetIntegrand2_measurable c q x y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hα.1.le _),
    abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianKernel2_le_one (mul_nonneg hc hα.1.le) x y)

theorem smallBudgetKernel2_symm (c q : ℝ) (x y : SphereD 2) :
    smallBudgetKernel2 c q x y = smallBudgetKernel2 c q y x := by
  unfold smallBudgetKernel2 sphereGaussianKernel2
  simp_rw [dist_comm x y]

theorem smallBudgetKernel2_nonneg (c q : ℝ) (x y : SphereD 2) :
    0 ≤ smallBudgetKernel2 c q x y :=
  setIntegral_nonneg measurableSet_Ioc fun _α hα =>
    mul_nonneg (Real.rpow_nonneg hα.1.le _) (sphereGaussianKernel2_nonneg _ _ _)

theorem smallBudgetKernel2_self (c : ℝ) {q : ℝ} (hq : 0 < q) (x : SphereD 2) :
    smallBudgetKernel2 c q x x = 4^q/q := by
  unfold smallBudgetKernel2
  simp only [sphereGaussianKernel2_self, mul_one]
  exact rpow_sub_one_integral_IocS2 hq

theorem smallBudgetKernel2_le {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x y : SphereD 2) :
    smallBudgetKernel2 c q x y ≤ 4^q/q := by
  rw [← rpow_sub_one_integral_IocS2 hq]
  refine setIntegral_mono_on (smallBudgetIntegrand2_integrableOn hc hq x y)
    (rpow_sub_one_integrableOn_IocS2 hq) measurableSet_Ioc ?_
  intro α hα
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianKernel2_le_one (mul_nonneg hc hα.1.le) x y)

theorem smallBudgetJoint2_measurable (c q : ℝ) :
    Measurable (fun z : (SphereD 2 × SphereD 2) × ℝ =>
      z.2^(q-1)*sphereGaussianKernel2 (c*z.2) z.1.1 z.1.2) := by
  unfold sphereGaussianKernel2
  apply Measurable.mul (measurable_snd.pow_const (q-1))
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.mul (measurable_const.mul measurable_snd)
  exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
    (continuous_snd.comp continuous_fst))).measurable).pow_const 2

theorem smallBudgetKernel2_measurable (c q : ℝ) :
    StronglyMeasurable (fun p : SphereD 2 × SphereD 2 => smallBudgetKernel2 c q p.1 p.2) :=
  (smallBudgetJoint2_measurable c q).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) 4))

theorem smallBudgetKernel2_row_measurable (c q : ℝ) (x : SphereD 2) :
    StronglyMeasurable (fun y : SphereD 2 => smallBudgetKernel2 c q x y) := by
  have hf : StronglyMeasurable (fun z : SphereD 2 × ℝ =>
      z.2^(q-1)*sphereGaussianKernel2 (c*z.2) x z.1) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel2
    apply Measurable.mul (measurable_snd.pow_const (q-1))
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 4))

/-- The kernel is bounded, hence integrable against every finite measure on pairs. -/
theorem smallBudgetKernel2_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (ρ : Measure (SphereD 2 × SphereD 2)) [IsFiniteMeasure ρ] :
    Integrable (fun p : SphereD 2 × SphereD 2 => smallBudgetKernel2 c q p.1 p.2) ρ := by
  refine Integrable.of_bound (smallBudgetKernel2_measurable c q).aestronglyMeasurable (4^q/q) ?_
  refine Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (smallBudgetKernel2_nonneg c q _ _)]
  exact smallBudgetKernel2_le hc hq _ _

theorem smallBudgetKernel2_row_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 2)
    (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] :
    Integrable (fun y : SphereD 2 => smallBudgetKernel2 c q x y) μ := by
  refine Integrable.of_bound (smallBudgetKernel2_row_measurable c q x).aestronglyMeasurable
    (4^q/q) ?_
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (smallBudgetKernel2_nonneg c q _ _)]
  exact smallBudgetKernel2_le hc hq _ _

theorem sphereGaussianKernel2_integrable_finite {t : ℝ} (ht : 0 ≤ t)
    (ρ : Measure (SphereD 2 × SphereD 2)) [IsFiniteMeasure ρ] :
    Integrable (fun p : SphereD 2 × SphereD 2 => sphereGaussianKernel2 t p.1 p.2) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel2; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact sphereGaussianKernel2_le_one ht p.1 p.2

theorem sphereGaussianKernel2_row_integrable_finite {t : ℝ} (ht : 0 ≤ t) (x : SphereD 2)
    (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] :
    Integrable (fun y : SphereD 2 => sphereGaussianKernel2 t x y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel2; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact sphereGaussianKernel2_le_one ht x y

/-- Joint integrability of the weighted Gaussian in the pair and the scale. -/
theorem smallBudgetJoint2_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (ρ : Measure (SphereD 2 × SphereD 2)) [IsFiniteMeasure ρ] :
    Integrable (fun z : (SphereD 2 × SphereD 2) × ℝ =>
      z.2^(q-1)*sphereGaussianKernel2 (c*z.2) z.1.1 z.1.2)
      (ρ.prod (volume.restrict (Ioc (0:ℝ) 4))) := by
  refine Integrable.mono' (Integrable.comp_snd (rpow_sub_one_integrableOn_IocS2 hq) ρ)
    (smallBudgetJoint2_measurable c q).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
    with z hz
  have hz0 : 0 ≤ z.2 := hz.1.le
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hz0 _),
    abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hz0 _)
    (sphereGaussianKernel2_le_one (mul_nonneg hc hz0) _ _)

theorem smallBudget_pair_integral_eqS2 {c q : ℝ} (hc : 0 ≤ c) (μ₁ μ₂ : Measure (SphereD 2))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {α : ℝ} (hα : 0 ≤ α) :
    (∫ p : SphereD 2 × SphereD 2, α^(q-1)*sphereGaussianKernel2 (c*α) p.1 p.2 ∂μ₁.prod μ₂) =
      α^(q-1)*∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁ := by
  rw [integral_const_mul, integral_prod _
    (sphereGaussianKernel2_integrable_finite (mul_nonneg hc hα) (μ₁.prod μ₂))]

/-- The weighted scale integral commutes with integration against two finite measures. -/
theorem smallBudgetKernel2_integral_swap {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (μ₁ μ₂ : Measure (SphereD 2)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    ∫ x, ∫ y, smallBudgetKernel2 c q x y ∂μ₂ ∂μ₁ =
      ∫ α in Ioc (0:ℝ) 4, α^(q-1)*∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁ := by
  have hκ := smallBudgetKernel2_integrable hc hq (μ₁.prod μ₂)
  rw [← integral_prod _ hκ]
  have hswap := integral_integral_swap
    (f := fun (p : SphereD 2 × SphereD 2) (α : ℝ) =>
      α^(q-1)*sphereGaussianKernel2 (c*α) p.1 p.2)
    (smallBudgetJoint2_integrable hc hq (μ₁.prod μ₂))
  calc (∫ p : SphereD 2 × SphereD 2, smallBudgetKernel2 c q p.1 p.2 ∂μ₁.prod μ₂)
      = ∫ α in Ioc (0:ℝ) 4, ∫ p : SphereD 2 × SphereD 2,
          α^(q-1)*sphereGaussianKernel2 (c*α) p.1 p.2 ∂μ₁.prod μ₂ := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioc fun α hα =>
      smallBudget_pair_integral_eqS2 hc μ₁ μ₂ hα.1.le

/-- Integrability in the scale of the weighted pair integral against two finite measures. -/
theorem smallBudgetScale_integrableOnS2 {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (μ₁ μ₂ : Measure (SphereD 2)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    IntegrableOn (fun α : ℝ => α^(q-1)*∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁)
      (Ioc 0 4) := by
  have h := (smallBudgetJoint2_integrable hc hq (μ₁.prod μ₂)).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  exact smallBudget_pair_integral_eqS2 hc μ₁ μ₂ hα.1.le

theorem smallBudgetScale_row_integrableOnS2 {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 2)
    (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] :
    IntegrableOn (fun α : ℝ => α^(q-1)*∫ y, sphereGaussianKernel2 (c*α) x y ∂μ) (Ioc 0 4) := by
  have h := smallBudgetScale_integrableOnS2 hc hq (Measure.dirac x) μ
  simpa only [integral_dirac] using h

theorem smallBudgetKernel2_row_integral {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 2)
    (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] :
    ∫ y, smallBudgetKernel2 c q x y ∂μ =
      ∫ α in Ioc (0:ℝ) 4, α^(q-1)*∫ y, sphereGaussianKernel2 (c*α) x y ∂μ := by
  have h := smallBudgetKernel2_integral_swap hc hq (Measure.dirac x) μ
  simpa only [integral_dirac] using h

/-- Background of the small-alpha budget at the density scale of `N` points. -/
def smallBudgetBackground2 (N : ℕ) (q : ℝ) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α)

theorem sphereGaussianBackground2_scale_measurable (c : ℝ) :
    StronglyMeasurable (fun α : ℝ => sphereGaussianBackground2 (c*α)) := by
  have hf : StronglyMeasurable (fun z : ℝ × (SphereD 2 × SphereD 2) =>
      sphereGaussianKernel2 (c*z.1) z.2.1 z.2.2) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel2
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_fst)
    exact ((continuous_dist.comp (continuous_fst.comp continuous_snd |>.prodMk
      (continuous_snd.comp continuous_snd))).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := (sphereProbabilityD 2).prod (sphereProbabilityD 2))

theorem smallBudgetBackground2_integrableOn {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α)) (Ioc 0 4) := by
  have hc := sphereGaussianDensityFactor2_pos hN
  refine Integrable.mono' (rpow_sub_one_integrableOn_IocS2 hq)
    (((measurable_id.pow_const (q-1)).aestronglyMeasurable).mul
      (sphereGaussianBackground2_scale_measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hα.1.le _),
    abs_of_nonneg (sphereGaussianBackground2_nonneg _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianBackground2_le_one (mul_nonneg hc.le hα.1.le))

/-- The actual small-alpha budget of a configuration in kernel form. -/
theorem sphereGaussianSmallBudget2_eq_kernel {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 < q)
    (X : ConfigurationD 2 N) :
    (N:ℝ)*sphereGaussianSmallBudget2 q X =
      (∑ i, ∑ j, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (X i) (X j))-
        (N:ℝ)^2*smallBudgetBackground2 N q := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc0 : 0 ≤ sphereGaussianDensityFactor2 N := (sphereGaussianDensityFactor2_pos hN).le
  have hK : ∀ i j, IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (X i) (X j)) (Ioc 0 4) :=
    fun i j => smallBudgetIntegrand2_integrableOn hc0 hq _ _
  have hB := smallBudgetBackground2_integrableOn hN hq
  have hpoint : ∀ α : ℝ, α^(q-1)*(sphereGaussianCenteredScaled2 α X+1) =
      (N:ℝ)⁻¹*(∑ i, ∑ j, α^(q-1)*
        sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (X i) (X j))-
        (N:ℝ)*(α^(q-1)*sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α)) := by
    intro α
    unfold sphereGaussianCenteredScaled2
    rw [sphereGaussianScale2_eq_factor]
    simp only [← Finset.mul_sum]
    field_simp
    ring
  have hA : Integrable (fun α : ℝ => (N:ℝ)⁻¹*(∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (X i) (X j)))
      (volume.restrict (Ioc 0 4)) :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hK i j).const_mul _
  unfold sphereGaussianSmallBudget2
  simp_rw [hpoint]
  rw [integral_sub hA (hB.const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hK i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hK _ j)]
  unfold smallBudgetKernel2 smallBudgetBackground2
  field_simp

end SphericalRiesz
end
end

section

/-! Small-alpha budget of a foreground family with the smooth residual background.

In kernel form the neutralized Gaussian energy of the mixed measure (foreground points plus
`N σ` on the residual region `R`) is

`Σ_{i,j} K(x_i,x_j) + 2N Σ_i ∫_R K(x_i,·) dσ + N² ∫_R∫_R K dσ dσ - N² B(t)`

whenever the total charge is `N`.  Integrating against `α^(q-1)` on `(0,4]` and using the
twelfth-order profile gives a budget whose family-dependent part vanishes under refinement.
The residual points themselves are not chosen here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- Integral against the mixed measure of a bounded measurable function. -/
theorem mixedForegroundMeasure2_integral {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) (g : AmbientD 2 → ℝ) (hg : StronglyMeasurable g) (C : ℝ)
    (hC : ∀ y, |g y| ≤ C) :
    ∫ y, g y ∂(mixedForegroundMeasure2 x N R) =
      (∑ i, g (x i : AmbientD 2))+
        (N:ℝ)*∫ y in R, g (y : AmbientD 2) ∂(sphereProbabilityD 2) := by
  have hI : ∀ (μ : Measure (AmbientD 2)) [IsFiniteMeasure μ], Integrable g μ := fun μ _ =>
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)
  unfold mixedForegroundMeasure2
  rw [integral_add_measure (hI _) (hI _), finitePointMeasure_integral,
    integral_smul_nnreal_measure, integral_map (by fun_prop) hg.aestronglyMeasurable,
    NNReal.smul_def, NNReal.coe_natCast, smul_eq_mul]

theorem gaussianKernel_ambient_stronglyMeasurableS2 (t : ℝ) :
    StronglyMeasurable (fun p : AmbientD 2 × AmbientD 2 => gaussianKernel t p.1 p.2) :=
  (by unfold gaussianKernel; fun_prop :
    Continuous fun p : AmbientD 2 × AmbientD 2 => gaussianKernel t p.1 p.2).stronglyMeasurable

theorem gaussianKernel_potential_measurableS2 (t : ℝ) (μ : Measure (AmbientD 2))
    [IsFiniteMeasure μ] :
    StronglyMeasurable (fun w : AmbientD 2 => ∫ y, gaussianKernel t w y ∂μ) :=
  (gaussianKernel_ambient_stronglyMeasurableS2 t).integral_prod_right' (ν := μ)

theorem gaussianKernel_row_integrableS2 {t : ℝ} (ht : 0 ≤ t) (w : AmbientD 2)
    (μ : Measure (AmbientD 2)) [IsFiniteMeasure μ] :
    Integrable (fun y => gaussianKernel t w y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold gaussianKernel; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianKernel_nonneg _ _ _)]
  exact gaussianKernel_le_one ht _ _

theorem gaussianKernel_potential_abs_leS2 {t : ℝ} (ht : 0 ≤ t) (μ : Measure (AmbientD 2))
    [IsFiniteMeasure μ] (w : AmbientD 2) :
    |∫ y, gaussianKernel t w y ∂μ| ≤ μ.real univ := by
  rw [abs_of_nonneg (integral_nonneg fun y => gaussianKernel_nonneg _ _ _)]
  calc ∫ y, gaussianKernel t w y ∂μ ≤ ∫ _y, (1:ℝ) ∂μ :=
        integral_mono (gaussianKernel_row_integrableS2 ht w μ) (integrable_const 1)
          (fun y => gaussianKernel_le_one ht w y)
    _ = μ.real univ := by simp

theorem mixedForeground_kernel_rowS2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) {t : ℝ} (ht : 0 ≤ t) (w : AmbientD 2) :
    ∫ y, gaussianKernel t w y ∂(mixedForegroundMeasure2 x N R) =
      (∑ j, gaussianKernel t w (x j : AmbientD 2))+
        (N:ℝ)*∫ y in R, gaussianKernel t w (y : AmbientD 2) ∂(sphereProbabilityD 2) :=
  mixedForegroundMeasure2_integral x N R (fun y => gaussianKernel t w y)
    (by unfold gaussianKernel; fun_prop :
      Continuous fun y : AmbientD 2 => gaussianKernel t w y).stronglyMeasurable 1
    (fun y => by
      rw [abs_of_nonneg (gaussianKernel_nonneg _ _ _)]
      exact gaussianKernel_le_one ht _ _)

/-- Pair energy of the mixed measure against the sphere probability. -/
theorem mixedForeground_pair_sphereS2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) {t : ℝ} (ht : 0 ≤ t) :
    gaussianMeasurePair t (mixedForegroundMeasure2 x N R) ambientSphereProbability2 =
      ((Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 2).real R)*
        sphereGaussianBackground2 t := by
  have hpot : ∀ y : SphereD 2,
      (∫ y', gaussianKernel t (y : AmbientD 2) y' ∂ambientSphereProbability2) =
        sphereGaussianBackground2 t := fun y => by
    rw [ambientSphereProbability2_kernel_integral, ← sphereGaussianBackground2_eq_potential ht y]
  rw [gaussianMeasurePair_iterated ht,
    mixedForegroundMeasure2_integral x N R
      (fun w => ∫ y, gaussianKernel t w y ∂ambientSphereProbability2)
      (gaussianKernel_potential_measurableS2 t ambientSphereProbability2) 1
      (fun w => by simpa using gaussianKernel_potential_abs_leS2 ht ambientSphereProbability2 w)]
  simp_rw [hpot]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, setIntegral_const, smul_eq_mul]
  ring

theorem sphereGaussianKernel2_comm (t : ℝ) (x y : SphereD 2) :
    sphereGaussianKernel2 t x y = sphereGaussianKernel2 t y x := by
  unfold sphereGaussianKernel2
  rw [dist_comm]

/-- Pair energy of the mixed measure with itself, in kernel form. -/
theorem mixedForeground_pair_selfS2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) {t : ℝ} (ht : 0 ≤ t) :
    gaussianMeasurePair t (mixedForegroundMeasure2 x N R) (mixedForegroundMeasure2 x N R) =
      (∑ i, ∑ j, sphereGaussianKernel2 t (x i) (x j))+
      2*(N:ℝ)*(∑ i, ∫ y in R, sphereGaussianKernel2 t (x i) y ∂(sphereProbabilityD 2))+
      (N:ℝ)^2*(∫ y in R, ∫ y' in R, sphereGaussianKernel2 t y y' ∂(sphereProbabilityD 2)
        ∂(sphereProbabilityD 2)) := by
  have h1 : gaussianMeasurePair t (mixedForegroundMeasure2 x N R)
      (mixedForegroundMeasure2 x N R) =
      (∑ i, ∫ y, gaussianKernel t (x i : AmbientD 2) y ∂(mixedForegroundMeasure2 x N R))+
        (N:ℝ)*∫ y' in R, (∫ y, gaussianKernel t (y' : AmbientD 2) y
          ∂(mixedForegroundMeasure2 x N R)) ∂(sphereProbabilityD 2) := by
    rw [gaussianMeasurePair_iterated ht]
    exact mixedForegroundMeasure2_integral x N R
      (fun w => ∫ y, gaussianKernel t w y ∂(mixedForegroundMeasure2 x N R))
      (gaussianKernel_potential_measurableS2 t _) ((mixedForegroundMeasure2 x N R).real univ)
      (gaussianKernel_potential_abs_leS2 ht _)
  have h2 : ∀ w : SphereD 2,
      (∫ y, gaussianKernel t (w : AmbientD 2) y ∂(mixedForegroundMeasure2 x N R)) =
      (∑ j, sphereGaussianKernel2 t w (x j))+
        (N:ℝ)*∫ y in R, sphereGaussianKernel2 t w y ∂(sphereProbabilityD 2) := by
    intro w
    rw [mixedForeground_kernel_rowS2 x N R ht]
    simp_rw [← sphereGaussianKernel2_eq_ambient]
  have hI1 : Integrable (fun y' : SphereD 2 => ∑ j, sphereGaussianKernel2 t y' (x j))
      ((sphereProbabilityD 2).restrict R) :=
    integrable_finsetSum _ fun j _ =>
      (sphereGaussianKernel2_row_integrable_finite ht (x j) _).congr
        (Filter.Eventually.of_forall fun y' => sphereGaussianKernel2_comm t (x j) y')
  have hI2 : Integrable (fun y' : SphereD 2 =>
      ∫ y in R, sphereGaussianKernel2 t y' y ∂(sphereProbabilityD 2))
      ((sphereProbabilityD 2).restrict R) :=
    (sphereGaussianKernel2_integrable_finite ht
      (((sphereProbabilityD 2).restrict R).prod ((sphereProbabilityD 2).restrict R))).integral_prod_left
  have hsym : ∀ j, (∫ y' in R, sphereGaussianKernel2 t y' (x j) ∂(sphereProbabilityD 2)) =
      ∫ y in R, sphereGaussianKernel2 t (x j) y ∂(sphereProbabilityD 2) := fun j =>
    integral_congr_ae (Filter.Eventually.of_forall fun y' => sphereGaussianKernel2_comm t y' (x j))
  rw [h1]
  simp_rw [h2]
  rw [integral_add hI1 (hI2.const_mul _), integral_finsetSum _ (fun j _ =>
      (sphereGaussianKernel2_row_integrable_finite ht (x j) _).congr
        (Filter.Eventually.of_forall fun y' => sphereGaussianKernel2_comm t (x j) y')),
    integral_const_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [hsym]
  ring

/-- Neutralized Gaussian defect of the mixed measure in kernel form, at total charge `N`. -/
theorem mixedForeground_defect_eq_kernelS2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2))
    (hmass : (Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 2).real R = N) {t : ℝ}
    (ht : 0 ≤ t) :
    gaussianMeasureDefect t (N:ℝ) (mixedForegroundMeasure2 x N R) ambientSphereProbability2 =
      (∑ i, ∑ j, sphereGaussianKernel2 t (x i) (x j))+
      2*(N:ℝ)*(∑ i, ∫ y in R, sphereGaussianKernel2 t (x i) y ∂(sphereProbabilityD 2))+
      (N:ℝ)^2*(∫ y in R, ∫ y' in R, sphereGaussianKernel2 t y y' ∂(sphereProbabilityD 2)
        ∂(sphereProbabilityD 2))-
      (N:ℝ)^2*sphereGaussianBackground2 t := by
  unfold gaussianMeasureDefect
  rw [mixedForeground_pair_selfS2 x N R ht, mixedForeground_pair_sphereS2 x N R ht, hmass,
    ambientSphereProbability2_kernel_pair]
  ring

/-- Small-alpha budget of the foreground with smooth residual background, in kernel form. -/
def mixedSmallBudget2 {ι : Type*} [Fintype ι] (x : ι → SphereD 2) (N : ℕ)
    (R : Set (SphereD 2)) (q : ℝ) : ℝ :=
  (∑ i, ∑ j, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (x i) (x j))+
    2*(N:ℝ)*(∑ i, ∫ y in R, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (x i) y
      ∂(sphereProbabilityD 2))+
    (N:ℝ)^2*(∫ y in R, ∫ y' in R, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q y y'
      ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))-
    (N:ℝ)^2*smallBudgetBackground2 N q

/-- The kernel form is the weighted scale integral of the neutralized defects. -/
theorem mixedSmallBudget2_eq_integral {ι : Type*} [Fintype ι] (x : ι → SphereD 2) {N : ℕ}
    (hN : 0 < N) (R : Set (SphereD 2))
    (hmass : (Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 2).real R = N) {q : ℝ}
    (hq : 0 < q) :
    mixedSmallBudget2 x N R q = (∫ α in Ioc (0:ℝ) 4, α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor2 N*α) (N:ℝ)
        (mixedForegroundMeasure2 x N R) ambientSphereProbability2) ∧
    IntegrableOn (fun α : ℝ => α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor2 N*α) (N:ℝ)
        (mixedForegroundMeasure2 x N R) ambientSphereProbability2) (Ioc 0 4) := by
  have hc : 0 ≤ sphereGaussianDensityFactor2 N := (sphereGaussianDensityFactor2_pos hN).le
  have hf₁ : ∀ i j, IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j)) (Ioc 0 4) :=
    fun i j => smallBudgetIntegrand2_integrableOn hc hq _ _
  have hf₂ : ∀ i, IntegrableOn (fun α : ℝ => α^(q-1)*
      ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
        ∂(sphereProbabilityD 2)) (Ioc 0 4) :=
    fun i => smallBudgetScale_row_integrableOnS2 hc hq (x i) _
  have hf₃ : IntegrableOn (fun α : ℝ => α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
        ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)) (Ioc 0 4) :=
    smallBudgetScale_integrableOnS2 hc hq _ _
  have hf₄ := smallBudgetBackground2_integrableOn hN hq
  have hS₁ : IntegrableOn (fun α : ℝ => ∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j)) (Ioc 0 4) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf₁ i j
  have hS₂ : IntegrableOn (fun α : ℝ => ∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
        ∂(sphereProbabilityD 2)) (Ioc 0 4) :=
    integrable_finsetSum _ fun i _ => hf₂ i
  have hkey : EqOn (fun α : ℝ => α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor2 N*α) (N:ℝ)
        (mixedForegroundMeasure2 x N R) ambientSphereProbability2)
      (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
            ∂(sphereProbabilityD 2))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
            ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))-
        (N:ℝ)^2*(α^(q-1)*sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α)))
      (Ioc 0 4) := by
    intro α hα
    simp only
    rw [mixedForeground_defect_eq_kernelS2 x N R hmass (mul_nonneg hc hα.1.le)]
    simp only [← Finset.mul_sum]
    ring
  have hT₂ : IntegrableOn (fun α : ℝ => 2*(N:ℝ)*(∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
        ∂(sphereProbabilityD 2))) (Ioc 0 4) := hS₂.const_mul _
  have hT₃ : IntegrableOn (fun α : ℝ => (N:ℝ)^2*(α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
        ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))) (Ioc 0 4) := hf₃.const_mul _
  have hT₄ : IntegrableOn (fun α : ℝ => (N:ℝ)^2*(α^(q-1)*
      sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α))) (Ioc 0 4) :=
    hf₄.const_mul _
  have hT₁₂ : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
            ∂(sphereProbabilityD 2))) (Ioc 0 4) := hS₁.add hT₂
  have hT₁₂₃ : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
            ∂(sphereProbabilityD 2))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
            ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))) (Ioc 0 4) := hT₁₂.add hT₃
  have hRint : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
            ∂(sphereProbabilityD 2))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
            ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))-
        (N:ℝ)^2*(α^(q-1)*sphereGaussianBackground2 (sphereGaussianDensityFactor2 N*α)))
      (Ioc 0 4) := hT₁₂₃.sub hT₄
  have e₁ : (∫ α in Ioc (0:ℝ) 4, ∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) (x j)) =
      ∑ i, ∑ j, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (x i) (x j) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hf₁ i j)]
    simp_rw [integral_finsetSum _ (fun j _ => hf₁ _ j)]
    rfl
  have e₂ : (∫ α in Ioc (0:ℝ) 4, ∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) (x i) y
        ∂(sphereProbabilityD 2)) =
      ∑ i, ∫ y in R, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (x i) y
        ∂(sphereProbabilityD 2) := by
    rw [integral_finsetSum _ (fun i _ => hf₂ i)]
    exact Finset.sum_congr rfl fun i _ =>
      (smallBudgetKernel2_row_integral hc hq (x i) _).symm
  have e₃ : (∫ α in Ioc (0:ℝ) 4, α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α) y y'
        ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)) =
      ∫ y in R, ∫ y' in R, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q y y'
        ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2) :=
    (smallBudgetKernel2_integral_swap hc hq _ _).symm
  refine ⟨?_, hRint.congr_fun hkey.symm measurableSet_Ioc⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hkey, integral_sub hT₁₂₃ hT₄,
    integral_add hT₁₂ hT₃, integral_add hS₁ hT₂, integral_const_mul, integral_const_mul,
    integral_const_mul, e₁, e₂, e₃]
  rfl

/-- Small-alpha budget of a twelfth-order foreground family with smooth residual background. -/
theorem hexPatchFamily_mixedSmallBudget_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m),
      ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℝ)+
        (((d*m)^2:ℕ):ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
          (((d*m)^2:ℕ):ℝ)) →
      ∀ q : ℝ, 0 < q → q ≤ 2 →
      mixedSmallBudget2 (hexFamilyNodes2 P (a*m) hn) ((d*m)^2) (hexFamilyUnion2 P)ᶜ q ≤
        (((d*m)^2:ℕ):ℝ)*(hexForegroundProfileConst2*(4^q/q)+
          hexForegroundProfileGain2 q*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-q)*(4^(q/2)/(q/2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := hexPatchFamily_mixed_defect_profile
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn hmass q hq hqmax
  have hNpos : 0 < (d*m)^2 := by positivity
  obtain ⟨heq, hint⟩ := mixedSmallBudget2_eq_integral (hexFamilyNodes2 P (a*m) hn) hNpos
    (hexFamilyUnion2 P)ᶜ hmass hq
  rw [heq]
  set G := hexForegroundProfileGain2 q*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-q) with hG
  set C₀ := hexForegroundProfileConst2 with hC₀
  have hq2 : 0 < q/2 := by positivity
  have hpt : ∀ α ∈ Ioc (0:ℝ) 4, α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor2 ((d*m)^2)*α) (((d*m)^2:ℕ):ℝ)
        (mixedForegroundMeasure2 (hexFamilyNodes2 P (a*m) hn) ((d*m)^2)
          (hexFamilyUnion2 P)ᶜ) ambientSphereProbability2 ≤
      (((d*m)^2:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1)) := by
    intro α hα
    have h := hb P hv hε hdisj a d m hd hm hratio hn q hq hqmax α hα
    rw [sphereGaussianScale2_eq_factor] at h
    have hαq : 0 ≤ α^(q-1) := Real.rpow_nonneg hα.1.le _
    have hpow : α^(q-1)*α^(-(q/2)) = α^(q/2-1) := by
      rw [← Real.rpow_add hα.1]
      congr 1
      ring
    calc _ ≤ α^(q-1)*((((d*m)^2:ℕ):ℝ)*(C₀+G*α^(-(q/2)))) :=
          mul_le_mul_of_nonneg_left h hαq
      _ = (((d*m)^2:ℕ):ℝ)*(C₀*α^(q-1)+G*(α^(q-1)*α^(-(q/2)))) := by ring
      _ = _ := by rw [hpow]
  have hI₁ := rpow_sub_one_integrableOn_IocS2 hq
  have hI₂ := rpow_sub_one_integrableOn_IocS2 hq2
  have hR : IntegrableOn (fun α : ℝ => (((d*m)^2:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1))) (Ioc 0 4) :=
    ((hI₁.const_mul C₀).add (hI₂.const_mul G)).const_mul _
  calc _ ≤ ∫ α in Ioc (0:ℝ) 4, (((d*m)^2:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1)) :=
        setIntegral_mono_on hint hR measurableSet_Ioc hpt
    _ = _ := by
      rw [integral_const_mul, integral_add (hI₁.const_mul C₀) (hI₂.const_mul G),
        integral_const_mul, integral_const_mul, rpow_sub_one_integral_IocS2 hq,
        rpow_sub_one_integral_IocS2 hq2]

end SphericalRiesz
end
end

section

/-! One joint residual choice on S²⁴ for the small-alpha budget, the short-range tail and one
Gaussian window.

The residual region is the union of measurable pairwise disjoint cells of probability `1/N`.
One point is chosen in every cell, injectively and away from the foreground points, so that the
weighted sum of three centered quantities is at most `n (4^q/q + w₃)`:

* the small-alpha budget kernel, with the residual/foreground cross pairs, centered by its
  smooth mean `2N Σ_i ∫_R κ(X_i,·) dσ + N² ∫_R∫_R κ`;
* the short-range kernel, with the cross pairs, centered by the bound `(2M+n)/(-p)`;
* one Gaussian window among the residual points, centered by the bound `n N B(t₀)`.

No foreground estimate, configuration or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

/-- Residual pair sum plus twice the residual/foreground cross sum. -/
def residualCrossSumS2 {E : Type*} (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ}
    (z : Fin n → E) : ℝ :=
  cellPairSum k z+2*(∑ j, ∑ i, k (z j) (X i))

theorem residualCentered_eq_crossSumS2 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ} (z : Fin n → E) :
    residualCentered μ k X z = residualCrossSumS2 k X z-
      (2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i))+(n:ℝ)^2*residualBackground μ k) := by
  unfold residualCentered residualCrossSumS2 residualPairEnergy cellPairSum
  ring

theorem residualCrossSum_nonnegS2 {E : Type*} (k : E → E → ℝ) (hpos : ∀ x y, 0 ≤ k x y)
    {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ} (z : Fin n → E) :
    0 ≤ residualCrossSumS2 k X z := by
  unfold residualCrossSumS2 cellPairSum
  have h1 : 0 ≤ ∑ i, ∑ j, k (z i) (z j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpos _ _
  have h2 : 0 ≤ ∑ j, ∑ i, k (z j) (X i) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hpos _ _
  linarith

/-- One joint residual choice for three kernels on S²⁴. -/
theorem exists_hex_joint_residual2 {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {q p t₀ w₂ w₃ : ℝ} (hq : 0 < q) (hp0 : -1 ≤ p) (hp : p < 0) (ht₀ : 0 ≤ t₀)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    {ι : Type*} [Fintype ι] (X : ι → SphereD 2)
    (C : Fin n → Set (SphereD 2)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → SphereD 2, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧
      (∀ j, z j ∉ range X) ∧
      (residualCrossSumS2 (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q) X z-
        (2*(N:ℝ)*(∑ i, ∫ y in ⋃ j, C j,
            smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (X i) y
              ∂(sphereProbabilityD 2))+
          (N:ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
            smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q y y'
              ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))))+
      w₂*(residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z-
        (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p))+
      w₃*(cellPairSum (sphereGaussianKernel2 t₀) z-
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀)) ≤
      (n:ℝ)*(4^q/q+w₃) := by
  classical
  have hc : 0 < sphereGaussianDensityFactor2 N := sphereGaussianDensityFactor2_pos hN
  have hRm : MeasurableSet (⋃ j, C j) := MeasurableSet.iUnion hCm
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (N:ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h11 : 0 < -p := by linarith
  have h11ne : -p ≠ 0 := h11.ne'
  have hnne : (n:ℝ) ≠ 0 := hnR.ne'
  have hNne : (N:ℝ) ≠ 0 := hNR.ne'
  have hσR : (sphereProbabilityD 2) (⋃ j, C j) = (n:ℝ≥0∞)*(N:ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hR0 : (sphereProbabilityD 2) (⋃ j, C j) ≠ 0 := by
    rw [hσR]
    exact mul_ne_zero hn0 (ENNReal.inv_ne_zero.mpr hNt)
  have hinv : ((sphereProbabilityD 2) (⋃ j, C j))⁻¹ = (N:ℝ≥0∞)*(n:ℝ≥0∞)⁻¹ := by
    rw [hσR, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm]
  have htoReal : (((sphereProbabilityD 2) (⋃ j, C j))⁻¹).toReal = (N:ℝ)/(n:ℝ) := by
    rw [hinv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  -- the residual probability measure, as a variable with its defining equation
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (SphereD 2), μ = sphereRestrictedProbability2 (⋃ j, C j) :=
    ⟨_, rfl⟩
  have hμP : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact sphereRestrictedProbability2_probability _ hR0
  have hμA : NullSingletonClass μ := by
    rw [hμdef]
    infer_instance
  have hμC : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    have hsub : C j ∩ ⋃ i, C i = C j := inter_eq_left.mpr (subset_iUnion C j)
    rw [hμdef]
    simp only [sphereRestrictedProbability2, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), hsub, hCmass j, hinv, mul_comm (N:ℝ≥0∞) _, mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, mul_one]
  have hcover : μ (⋃ j, C j)ᶜ = 0 := by
    rw [hμdef]
    exact sphereRestrictedProbability2_compl _ hRm
  have hB : μ (range X) = 0 := (finite_range X).measure_zero μ
  have hint_eq : ∀ f : SphereD 2 → ℝ,
      (∫ y, f y ∂μ) = (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, f y ∂(sphereProbabilityD 2) := by
    intro f
    rw [hμdef]
    simp only [sphereRestrictedProbability2]
    rw [integral_smul_measure, smul_eq_mul, htoReal]
  -- integrability of the three kernels
  have hκprod : Integrable (Function.uncurry
      (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q)) (μ.prod μ) :=
    smallBudgetKernel2_integrable hc.le hq (μ.prod μ)
  have hκk : ∀ x, Integrable (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q x) μ :=
    fun x => smallBudgetKernel2_row_integrable hc.le hq x μ
  have hκV : Integrable (residualRowPotential μ
      (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q)) μ := hκprod.integral_prod_left
  have hTk : ∀ x, Integrable (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x) μ := by
    intro x
    rw [hμdef]
    exact shortRangeKernel2_restricted_integrable hc hp _ x
  have hTV : Integrable (residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) μ := by
    rw [hμdef]
    exact shortRangeKernel2_restricted_rowPotential_integrable hc hp _ hR0
  have hTprod : Integrable (Function.uncurry
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry
        (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) (μ.prod μ) :=
      (shortRangeKernel2_measurable (sphereGaussianDensityFactor2 N) p).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).mpr ⟨Filter.Eventually.of_forall fun x => hTk x, ?_⟩
    refine hTV.congr (Filter.Eventually.of_forall fun x => ?_)
    unfold residualRowPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y =
      ‖shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y‖
    rw [Real.norm_eq_abs, abs_of_nonneg (shortRangeKernel2_nonneg _ _ _ _)]
  have hGprod : Integrable (Function.uncurry (sphereGaussianKernel2 t₀)) (μ.prod μ) :=
    sphereGaussianKernel2_integrable_finite ht₀ (μ.prod μ)
  have hGk : ∀ x, Integrable (sphereGaussianKernel2 t₀ x) μ :=
    fun x => sphereGaussianKernel2_row_integrable_finite ht₀ x μ
  have hGV : Integrable (residualRowPotential μ (sphereGaussianKernel2 t₀)) μ :=
    hGprod.integral_prod_left
  -- the joint choice
  obtain ⟨z, hinj, hzC, hzB, hjoint⟩ := exists_stratified_joint_three μ
    (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q)
    (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)
    (sphereGaussianKernel2 t₀) (4^q/q) 0 1 hw₂ hw₃
    (smallBudgetKernel2_symm _ q) (shortRangeKernel2_symm _ p) (sphereGaussianKernel2_comm t₀)
    (smallBudgetKernel2_self _ hq) (shortRangeKernel2_self _ hp0)
    (sphereGaussianKernel2_self t₀)
    (smallBudgetKernel2_nonneg _ q) (shortRangeKernel2_nonneg _ p)
    (sphereGaussianKernel2_nonneg t₀)
    hκk hTk hGk hκV hTV hGV hκprod hTprod hGprod X X (Fin.elim0 : Fin 0 → SphereD 2)
    hn C hCm hCd hcover hμC (range X) hB
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  -- the budget kernel: exact smooth mean
  have hκU : ∀ x, residualRowPotential μ (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q) x =
      (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q x y
        ∂(sphereProbabilityD 2) := fun x => hint_eq _
  have hκbg : residualBackground μ (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q) =
      (N:ℝ)/(n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
        smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q y y'
          ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)) := by
    unfold residualBackground
    rw [hint_eq]
    simp_rw [hκU]
    rw [integral_const_mul]
  have hc₁ : residualCentered μ (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q) X z =
      residualCrossSumS2 (smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q) X z-
        (2*(N:ℝ)*(∑ i, ∫ y in ⋃ j, C j,
            smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q (X i) y
              ∂(sphereProbabilityD 2))+
          (N:ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
            smallBudgetKernel2 (sphereGaussianDensityFactor2 N) q y y'
              ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))) := by
    rw [residualCentered_eq_crossSumS2, hκbg]
    simp_rw [hκU]
    rw [← Finset.mul_sum]
    field_simp
    try ring
  -- the short-range kernel: bounded smooth mean
  have hTrow : ∀ x, (n:ℝ)*residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x ≤ 1/(-p) := by
    intro x
    have h := shortRangeKernel2_cell_rows_le hN hp C hCm hCd hCmass x
    rw [sphereRestrictedProbability2_sum_integral C hCm hCd hCmass
      (shortRangeKernel2_row_integrable (sphereGaussianScale2_pos hN zero_lt_one) hp x)] at h
    unfold residualRowPotential
    rw [hint_eq]
    calc (n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y ∂(sphereProbabilityD 2))
        = (N:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y
            ∂(sphereProbabilityD 2) := by field_simp
      _ ≤ 1/(-p) := h
  have hTU : ∀ x, residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x ≤ 1/((n:ℝ)*(-p)) := by
    intro x
    have h := hTrow x
    rw [le_div_iff₀ (mul_pos hnR h11)]
    calc _ = ((n:ℝ)*residualRowPotential μ
          (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x)*(-p) := by ring
      _ ≤ 1/(-p)*(-p) := mul_le_mul_of_nonneg_right h h11.le
      _ = 1 := by field_simp [hp.ne]
  have hTbg : residualBackground μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) ≤
      1/((n:ℝ)*(-p)) := by
    unfold residualBackground
    calc _ ≤ ∫ _x, 1/((n:ℝ)*(-p)) ∂μ := integral_mono hTV (integrable_const _) hTU
      _ = _ := by simp
  have hTsum : (n:ℝ)*(∑ i, residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) (X i)) ≤
      (Fintype.card ι:ℝ)/(-p) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _i : ι, 1/(-p) := Finset.sum_le_sum fun i _ => hTrow (X i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hTbgn : (n:ℝ)^2*residualBackground μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) ≤ (n:ℝ)/(-p) := by
    calc _ ≤ (n:ℝ)^2*(1/((n:ℝ)*(-p))) := mul_le_mul_of_nonneg_left hTbg (by positivity)
      _ = _ := by field_simp
  have hc₂ : residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z-
      (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p) ≤
      residualCentered μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z := by
    rw [residualCentered_eq_crossSumS2]
    have he : (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p) =
        2*((Fintype.card ι:ℝ)/(-p))+(n:ℝ)/(-p) := by ring
    rw [he]
    linarith
  -- the Gaussian window: bounded smooth mean
  have hGU : ∀ x, residualRowPotential μ (sphereGaussianKernel2 t₀) x ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    intro x
    unfold residualRowPotential
    rw [hint_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∫ y in ⋃ j, C j, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2))
        ≤ ∫ y, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2) :=
          setIntegral_le_integral (sphereGaussianKernel2_integrable ht₀ x)
            (Filter.Eventually.of_forall fun y => sphereGaussianKernel2_nonneg _ _ _)
      _ = sphereGaussianBackground2 t₀ := (sphereGaussianBackground2_eq_potential ht₀ x).symm
  have hGbg : residualBackground μ (sphereGaussianKernel2 t₀) ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    unfold residualBackground
    calc _ ≤ ∫ _x, (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ ∂μ :=
          integral_mono hGV (integrable_const _) hGU
      _ = _ := by simp
  have hc₃ : cellPairSum (sphereGaussianKernel2 t₀) z-
      (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) ≤
      residualCentered μ (sphereGaussianKernel2 t₀) (Fin.elim0 : Fin 0 → SphereD 2) z := by
    have hbgn : (n:ℝ)^2*residualBackground μ (sphereGaussianKernel2 t₀) ≤
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) := by
      calc _ ≤ (n:ℝ)^2*((N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀) :=
            mul_le_mul_of_nonneg_left hGbg (by positivity)
        _ = _ := by field_simp
    unfold residualCentered residualPairEnergy cellPairSum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, sub_zero,
      add_zero]
    linarith
  rw [hc₁] at hjoint
  have hm₂ := mul_le_mul_of_nonneg_left hc₂ hw₂
  have hm₃ := mul_le_mul_of_nonneg_left hc₃ hw₃
  have hrhs : (n:ℝ)*(4^q/q+w₂*0+w₃*1) = (n:ℝ)*(4^q/q+w₃) := by ring
  rw [hrhs] at hjoint
  linarith

end SphericalRiesz
end
end

section

/-! Common Gaussian budgets of an actual configuration on S²⁴.

A twelfth-order foreground family of one common scale and one point in every residual cell form
an actual configuration of `N = (d m)^2` distinct points.  One joint residual choice gives

* the small-alpha budget `N H_q(Z) ≤ B`,
* the weighted residual and residual/foreground short-range cost `w₂ (…) ≤ B`,
* the weighted Gaussian window among the residual points `w₃ (…) ≤ B`,

with the common explicit right side `B = N·Fg + n (4^q/q + w₃) + w₂ (2M+n)/(-p) + w₃ n N B(t₀)`.
The foreground part `Fg` consists of a family-independent constant and a term which vanishes
under refinement.  The foreground short-range cost, the sharp foreground profile, the family
itself and the attaining sequence are not constructed here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz
open Boundary

theorem hexFamilyNodes2_injective {K : ℕ} (P : Fin K → SmallHexCubePatch2)
    (hdisj : Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
      (smallHexSpherePatch2 (P j)))) (n : ℕ) (hn : 74 ≤ n) :
    Function.Injective (hexFamilyNodes2 P n hn) := by
  rintro ⟨i,u⟩ ⟨j,w⟩ h
  change smallHexPatchNodes2 (P i) n hn u = smallHexPatchNodes2 (P j) n hn w at h
  have hij : i = j := by
    by_contra hne
    have hi := smallHexPatchNodes2_mem (P i) n hn u
    have hj := smallHexPatchNodes2_mem (P j) n hn w
    rw [← h] at hj
    exact Set.disjoint_left.mp (hdisj hne) hi hj
  subst hij
  rw [smallHexPatchNodes2_injective (P i) n hn h]

/-- Foreground and residual points as one configuration of `N` points. -/
def combinedConfiguration2 {ι : Type*} [Fintype ι] {n N : ℕ} (x : ι → SphereD 2)
    (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N) (hx : Function.Injective x)
    (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x) : ConfigurationD 2 N where
  toFun i := Sum.elim x z ((Fintype.equivFinOfCardEq
    (show Fintype.card (ι ⊕ Fin n) = N by
      rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm i)
  inj' := (Function.Injective.sumElim hx hz (fun a b h => havoid b ⟨a, h⟩)).comp
    (Equiv.injective _)

/-- Pair sums of a combined configuration split into foreground, cross and residual pairs. -/
theorem combinedConfiguration2_sum {ι : Type*} [Fintype ι] {n N : ℕ} (x : ι → SphereD 2)
    (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N) (hx : Function.Injective x)
    (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    (k : SphereD 2 → SphereD 2 → ℝ) (hs : ∀ a b, k a b = k b a) :
    (∑ i, ∑ j, k (combinedConfiguration2 x z hcard hx hz havoid i)
      (combinedConfiguration2 x z hcard hx hz havoid j)) =
      (∑ a, ∑ b, k (x a) (x b))+residualCrossSumS2 k x z := by
  set e := (Fintype.equivFinOfCardEq
    (show Fintype.card (ι ⊕ Fin n) = N by
      rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm with he
  have h1 : ∀ f : ι ⊕ Fin n → ℝ, (∑ i : Fin N, f (e i)) = ∑ a, f a :=
    fun f => Equiv.sum_comp e f
  have h2 : (∑ i, ∑ j, k (combinedConfiguration2 x z hcard hx hz havoid i)
      (combinedConfiguration2 x z hcard hx hz havoid j)) =
      ∑ a : ι ⊕ Fin n, ∑ b : ι ⊕ Fin n, k (Sum.elim x z a) (Sum.elim x z b) :=
    (Finset.sum_congr rfl fun i _ =>
      h1 (fun b => k (Sum.elim x z (e i)) (Sum.elim x z b))).trans
      (h1 (fun a => ∑ b : ι ⊕ Fin n, k (Sum.elim x z a) (Sum.elim x z b)))
  rw [h2]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  have hsw : (∑ a, ∑ j, k (x a) (z j)) = ∑ j, ∑ a, k (z j) (x a) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => hs _ _
  unfold residualCrossSumS2 cellPairSum
  rw [hsw]
  ring

/-- Foreground part of the small-alpha budget of one refinement. -/
def hexForegroundBudget2 (a d m : ℕ) (q : ℝ) : ℝ :=
  hexForegroundProfileConst2*(4^q/q)+
    hexForegroundProfileGain2 q*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-q)*(4^(q/2)/(q/2))

/-- The common right side of the three joint residual bounds. -/
def hexJointBound2 (N n : ℕ) (M Fg q p t₀ w₂ w₃ : ℝ) : ℝ :=
  (N:ℝ)*Fg+(n:ℝ)*(4^q/q+w₃)+w₂*((2*M+(n:ℝ))/(-p))+
    w₃*((n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀))

/-- One joint residual choice: the actual configuration has a common small-alpha budget, a
common residual short-range cost and a controlled residual Gaussian window. -/
theorem exists_hex_common_budget2 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      ∀ (hdisj : Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j)))) (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) {n : ℕ}, 0 < n →
      ∀ (hcard : Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m)))+n = (d*m)^2)
        (C : Fin n → Set (SphereD 2)), (∀ i, MeasurableSet (C i)) →
        Pairwise (fun i j => Disjoint (C i) (C j)) →
        (∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹) →
        (⋃ j, C j) = (hexFamilyUnion2 P)ᶜ →
      ∀ {q p t₀ w₂ w₃ : ℝ}, 0 < q → q ≤ 2 → -1 ≤ p → p < 0 → 0 ≤ t₀ → 0 ≤ w₂ → 0 ≤ w₃ →
      ∃ (z : Fin n → SphereD 2) (hz : Function.Injective z)
        (havoid : ∀ j, z j ∉ range (hexFamilyNodes2 P (a*m) hn)),
        (∀ j, z j ∈ C j) ∧
        (((d*m)^2:ℕ):ℝ)*sphereGaussianSmallBudget2 q
          (combinedConfiguration2 (hexFamilyNodes2 P (a*m) hn) z hcard
            (hexFamilyNodes2_injective P hdisj (a*m) hn) hz havoid) ≤
          hexJointBound2 ((d*m)^2) n
            (Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))))
            (hexForegroundBudget2 a d m q) q p t₀ w₂ w₃ ∧
        w₂*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
          (hexFamilyNodes2 P (a*m) hn) z ≤
          hexJointBound2 ((d*m)^2) n
            (Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))))
            (hexForegroundBudget2 a d m q) q p t₀ w₂ w₃ ∧
        w₃*cellPairSum (sphereGaussianKernel2 t₀) z ≤
          hexJointBound2 ((d*m)^2) n
            (Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))))
            (hexForegroundBudget2 a d m q) q p t₀ w₂ w₃ := by
  obtain ⟨ρ,hρ,hρ1,hfg⟩ := hexPatchFamily_mixedSmallBudget_le
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn n hnpos hcard C hCm hCd hCmass hCcover
    q p t₀ w₂ w₃ hq hq2 hp0 hp ht₀ hw₂ hw₃
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (((d*m)^2:ℕ):ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- exact mass of the residual region
  have hσR : (sphereProbabilityD 2) (⋃ j, C j) = (n:ℝ≥0∞)*(((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hσreal : (sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
      (n:ℝ)/(((d*m)^2:ℕ):ℝ) := by
    rw [← hCcover, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]
  have hcardR : ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hcard
  have hmass : (Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℝ)+
      (((d*m)^2:ℕ):ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
        (((d*m)^2:ℕ):ℝ) := by
    rw [hσreal, mul_div_cancel₀ _ hNR]
    exact hcardR
  have hFg := hfg P hv hε hdisj a d m hd hm hratio hn hmass q hq hq2
  obtain ⟨z, hinj, hzC, hzB, hjoint⟩ := exists_hex_joint_residual2 hNpos hnpos hq hp0 hp ht₀
    hw₂ hw₃ (hexFamilyNodes2 P (a*m) hn) C hCm hCd hCmass
  refine ⟨z, hinj, hzB, hzC, ?_⟩
  have hbud := sphereGaussianSmallBudget2_eq_kernel hNpos hq
    (combinedConfiguration2 (hexFamilyNodes2 P (a*m) hn) z hcard
      (hexFamilyNodes2_injective P hdisj (a*m) hn) hinj hzB)
  rw [combinedConfiguration2_sum (hexFamilyNodes2 P (a*m) hn) z hcard
    (hexFamilyNodes2_injective P hdisj (a*m) hn) hinj hzB
    (smallBudgetKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) q)
    (smallBudgetKernel2_symm _ q)] at hbud
  have hmix : mixedSmallBudget2 (hexFamilyNodes2 P (a*m) hn) ((d*m)^2)
      (hexFamilyUnion2 P)ᶜ q =
      (∑ i, ∑ j, smallBudgetKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) q
        (hexFamilyNodes2 P (a*m) hn i) (hexFamilyNodes2 P (a*m) hn j))+
      (2*(((d*m)^2:ℕ):ℝ)*(∑ i, ∫ y in ⋃ j, C j,
          smallBudgetKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) q
            (hexFamilyNodes2 P (a*m) hn i) y ∂(sphereProbabilityD 2))+
        (((d*m)^2:ℕ):ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
          smallBudgetKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) q y y'
            ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)))-
      (((d*m)^2:ℕ):ℝ)^2*smallBudgetBackground2 ((d*m)^2) q := by
    unfold mixedSmallBudget2
    rw [← hCcover]
    ring
  have hH0 : 0 ≤ (((d*m)^2:ℕ):ℝ)*sphereGaussianSmallBudget2 q
      (combinedConfiguration2 (hexFamilyNodes2 P (a*m) hn) z hcard
        (hexFamilyNodes2_injective P hdisj (a*m) hn) hinj hzB) :=
    mul_nonneg (Nat.cast_nonneg _) (sphereGaussianSmallBudget2_nonneg hNpos q _)
  have hT0 : 0 ≤ residualCrossSumS2
      (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodes2 P (a*m) hn) z :=
    residualCrossSum_nonnegS2 _ (shortRangeKernel2_nonneg _ _) _ _
  have hG0 : 0 ≤ cellPairSum (sphereGaussianKernel2 t₀) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel2_nonneg _ _ _
  have h2 := mul_nonneg hw₂ hT0
  have h3 := mul_nonneg hw₃ hG0
  rw [hmix] at hFg
  unfold hexJointBound2 hexForegroundBudget2
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

end SphericalRiesz
end
end

section

/-! Reduction of the Gaussian window of a combined configuration to its foreground.

Gaussian kernels are positive definite, so for every `ε > 0`

`Σ_{all} K_t ≤ (1+ε) Σ_{fg,fg} K_t + (1+1/ε) Σ_{res,res} K_t`.

The residual pair sum is nonincreasing in the scale.  Hence one residual Gaussian window at a
small scale `t₀` controls the residual part of every window `t ≥ t₀`, and no
residual/foreground cross estimate is needed for the sharp windows.  The sharp foreground
profile itself is not proved here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

/-- Positive definiteness: the full Gaussian sum of a combined configuration is controlled by
the foreground sum and the residual sum. -/
theorem combinedConfiguration2_gaussian_young {ι : Type*} [Fintype ι] {n N : ℕ}
    (x : ι → SphereD 2) (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    (∑ i, ∑ j, sphereGaussianKernel2 t (combinedConfiguration2 x z hcard hx hz havoid i)
      (combinedConfiguration2 x z hcard hx hz havoid j)) ≤
      (1+ε)*(∑ a, ∑ b, sphereGaussianKernel2 t (x a) (x b))+
        (1+1/ε)*cellPairSum (sphereGaussianKernel2 t) z := by
  rw [combinedConfiguration2_sum x z hcard hx hz havoid (sphereGaussianKernel2 t)
    (sphereGaussianKernel2_comm t)]
  have hpsd := gaussianMeasureDefect_nonneg ht (1/ε)
    (finitePointMeasure (fun a => (x a : AmbientD 2)))
    (finitePointMeasure (fun j => (z j : AmbientD 2)))
  have hff : gaussianMeasurePair t (finitePointMeasure (fun a => (x a : AmbientD 2)))
      (finitePointMeasure (fun a => (x a : AmbientD 2))) =
      ∑ a, ∑ b, sphereGaussianKernel2 t (x a) (x b) := by
    rw [gaussianMeasurePair_finite_both ht]
    simp_rw [← sphereGaussianKernel2_eq_ambient]
  have hrr : gaussianMeasurePair t (finitePointMeasure (fun j => (z j : AmbientD 2)))
      (finitePointMeasure (fun j => (z j : AmbientD 2))) =
      cellPairSum (sphereGaussianKernel2 t) z := by
    rw [gaussianMeasurePair_finite_both ht]
    simp_rw [← sphereGaussianKernel2_eq_ambient]
    rfl
  have hfr : gaussianMeasurePair t (finitePointMeasure (fun a => (x a : AmbientD 2)))
      (finitePointMeasure (fun j => (z j : AmbientD 2))) =
      ∑ j, ∑ a, sphereGaussianKernel2 t (z j) (x a) := by
    rw [gaussianMeasurePair_finite_left ht]
    simp_rw [finitePointMeasure_integral, ← sphereGaussianKernel2_eq_ambient]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      sphereGaussianKernel2_comm t _ _
  unfold gaussianMeasureDefect at hpsd
  rw [hff, hrr, hfr] at hpsd
  have hmul := mul_nonneg hε.le hpsd
  have he : ε*((∑ a, ∑ b, sphereGaussianKernel2 t (x a) (x b))-
      2*(1/ε)*(∑ j, ∑ a, sphereGaussianKernel2 t (z j) (x a))+
      (1/ε)^2*cellPairSum (sphereGaussianKernel2 t) z) =
      ε*(∑ a, ∑ b, sphereGaussianKernel2 t (x a) (x b))-
      2*(∑ j, ∑ a, sphereGaussianKernel2 t (z j) (x a))+
      (1/ε)*cellPairSum (sphereGaussianKernel2 t) z := by
    have h1 : ε*(1/ε) = 1 := mul_one_div_cancel hε.ne'
    calc _ = ε*(∑ a, ∑ b, sphereGaussianKernel2 t (x a) (x b))-
          2*(ε*(1/ε))*(∑ j, ∑ a, sphereGaussianKernel2 t (z j) (x a))+
          (ε*(1/ε))*(1/ε)*cellPairSum (sphereGaussianKernel2 t) z := by ring
      _ = _ := by rw [h1]; ring
  rw [he] at hmul
  unfold residualCrossSumS2
  linarith

/-- The residual Gaussian pair sum is nonincreasing in the scale. -/
theorem cellPairSum_gaussian_antiS2 {n : ℕ} (z : Fin n → SphereD 2) {t₀ t : ℝ} (h : t₀ ≤ t) :
    cellPairSum (sphereGaussianKernel2 t) z ≤ cellPairSum (sphereGaussianKernel2 t₀) z := by
  unfold cellPairSum
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  unfold sphereGaussianKernel2
  apply Real.exp_le_exp.mpr
  have hd : 0 ≤ dist (z i) (z j)^2 := sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hd]

/-- Full scaled Gaussian profile of a combined configuration: the foreground profile with a
factor `1+ε`, plus the residual window at any smaller scale with a factor `1+1/ε`. -/
theorem combinedConfiguration2_fullScaled_le {ι : Type*} [Fintype ι] {n N : ℕ} (hN : 0 < N)
    (x : ι → SphereD 2) (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {α α₀ ε : ℝ} (hα₀ : 0 ≤ α₀) (hα : α₀ ≤ α) (hε : 0 < ε) :
    sphereGaussianFullScaled2 α (combinedConfiguration2 x z hcard hx hz havoid) ≤
      (1+ε)*((∑ a, ∑ b, sphereGaussianKernel2 (sphereGaussianScale2 N α) (x a) (x b))/(N:ℝ))+
        (1+1/ε)*(cellPairSum (sphereGaussianKernel2 (sphereGaussianScale2 N α₀)) z/(N:ℝ)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hc := sphereGaussianDensityFactor2_pos hN
  have hs0 : 0 ≤ sphereGaussianScale2 N α := by
    rw [sphereGaussianScale2_eq_factor]
    exact mul_nonneg hc.le (hα₀.trans hα)
  have hmono : sphereGaussianScale2 N α₀ ≤ sphereGaussianScale2 N α := by
    rw [sphereGaussianScale2_eq_factor, sphereGaussianScale2_eq_factor]
    exact mul_le_mul_of_nonneg_left hα hc.le
  have hy := combinedConfiguration2_gaussian_young x z hcard hx hz havoid hs0 hε
  have ha := cellPairSum_gaussian_antiS2 z hmono
  have h1ε : 0 ≤ 1+1/ε := by positivity
  unfold sphereGaussianFullScaled2
  rw [show (1+ε)*((∑ a, ∑ b, sphereGaussianKernel2 (sphereGaussianScale2 N α) (x a) (x b))/
        (N:ℝ))+(1+1/ε)*(cellPairSum (sphereGaussianKernel2 (sphereGaussianScale2 N α₀)) z/
        (N:ℝ)) =
      ((1+ε)*(∑ a, ∑ b, sphereGaussianKernel2 (sphereGaussianScale2 N α) (x a) (x b))+
        (1+1/ε)*cellPairSum (sphereGaussianKernel2 (sphereGaussianScale2 N α₀)) z)/(N:ℝ) by
    ring]
  exact div_le_div_of_nonneg_right
    (hy.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ha h1ε))) hNR.le

end SphericalRiesz
end
end

section

/-! Short-range cost of a twelfth-order foreground family of one common scale.

Inside one patch the cost is the computed rational-density budget.  Two nodes of different
patches are separated by a fixed positive distance `δ`, and the short-range kernel at
separation `δ` is at most `e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`.  Hence

`Σ_{fg,fg} T ≤ M B + M² e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`,  `M = K n²⁴`.

The residual points and the full configuration are not part of this statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Bound of the short-range kernel at separation at least `δ`. -/
def separatedShortRangeBound2 (c p δ : ℝ) : ℝ :=
  Real.exp (-(c*δ^2/2))*((1/(c*δ^2/2))^(p+1)*Real.Gamma (p+1))

theorem separatedShortRangeBound2_nonneg {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p)
    (hδ : 0 < δ) : 0 ≤ separatedShortRangeBound2 c p δ := by
  have hg : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  unfold separatedShortRangeBound2
  positivity

/-- The short-range kernel of two points at distance at least `δ`. -/
theorem shortRangeKernel2_le_of_separated {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p)
    (hδ : 0 < δ) {x y : SphereD 2} (hxy : δ ≤ dist x y) :
    shortRangeKernel2 c p x y ≤ separatedShortRangeBound2 c p δ := by
  have hne : x ≠ y := by
    intro h
    rw [h, dist_self] at hxy
    linarith
  have hi : IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel2 (c*α) x y) (Ioi 1) := by
    simpa only [show 2*(p+1)/2-1=p by ring] using
      sphereGaussianPair2_scaled_tail_integrable (s := 2*(p+1)) hc (by linarith) zero_le_one hne
  unfold shortRangeKernel2 separatedShortRangeBound2
  set r := c*δ^2/2 with hr
  have hr0 : 0 < r := by positivity
  have hGval : (∫ α in Ioi (0:ℝ), α^p*Real.exp (-(r*α))) =
      (1/r)^(p+1)*Real.Gamma (p+1) := by
    simpa only [show p+1-1=p by ring] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p+1) (r := r) (by linarith) hr0
  have hG : IntegrableOn (fun α : ℝ => α^p*Real.exp (-(r*α))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hGval]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith))).ne'
  calc
    _ ≤ ∫ α in Ioi (1:ℝ), Real.exp (-r)*(α^p*Real.exp (-(r*α))) := by
      apply setIntegral_mono_on hi ((hG.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _)
        measurableSet_Ioi
      intro α hα
      have hα1 : (1:ℝ) < α := hα
      have hk : sphereGaussianKernel2 (c*α) x y ≤ Real.exp (-r)*Real.exp (-(r*α)) := by
        unfold sphereGaussianKernel2
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hd2 : δ^2 ≤ dist x y^2 := pow_le_pow_left₀ hδ.le hxy 2
        have h1 : c*α*δ^2 ≤ c*α*dist x y^2 := mul_le_mul_of_nonneg_left hd2 (by positivity)
        have h2 : c*α*δ^2 = 2*r*α := by rw [hr]; ring
        have h3 : r ≤ r*α := by nlinarith
        linarith
      calc α^p*sphereGaussianKernel2 (c*α) x y ≤ α^p*(Real.exp (-r)*Real.exp (-(r*α))) :=
            mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg (by linarith) _)
        _ = _ := by ring
    _ ≤ ∫ α in Ioi (0:ℝ), Real.exp (-r)*(α^p*Real.exp (-(r*α))) := by
      apply setIntegral_mono_set (hG.const_mul _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (Real.rpow_nonneg (le_of_lt hα) _) (Real.exp_pos _).le)
      · exact (Ioi_subset_Ioi zero_le_one).eventuallyLE
    _ = _ := by rw [integral_const_mul, hGval]

/-- Short-range cost of a separated twelfth-order foreground family. -/
theorem hexPatchFamily_shortRange_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (p : ℝ), -1 < p →
      (∑ q, ∑ q', shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p
          (hexFamilyNodes2 P (a*m) hn q) (hexFamilyNodes2 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^2*
          hexGaussianTailBudget2
            (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p+
        ((K:ℝ)*((a*m:ℕ):ℝ)^2)^2*
          separatedShortRangeBound2 (sphereGaussianDensityFactor2 ((d*m)^2)) p δ := by
  classical
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaHexTwelfth2_rational_density_budget
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn p hp
  have hc0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2) :=
    sphereGaussianDensityFactor2_pos (by positivity)
  set c := sphereGaussianDensityFactor2 ((d*m)^2) with hc
  set τ := separatedShortRangeBound2 c p δ with hτ
  have hτ0 : 0 ≤ τ := separatedShortRangeBound2_nonneg hc0 hp hδ
  set B := hexGaussianTailBudget2
    (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p with hB
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hcardNodes : (Fintype.card (Fin 2 → TwelveNodeIndex (a*m)) : ℝ) = n^2 := by
    rw [twelveCubeNode_card 2 (a*m) hn]
    exact Nat.cast_pow _ _
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, shortRangeKernel2 c p
      (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P i) (a*m) hn w)) ≤
      n^2*B := by
    intro i
    have h := hb (P i).g (P i).v (P i).c (hv i) (P i).c_mem (P i).ε (P i).ε_pos (hε i)
      (P i).small hexUnitDensityRadius2 p hexUnitDensityRadius2_pos hp a d m ha hd hm
      (hratio i) hn
    have h' := (div_le_iff₀ (pow_pos hn0 2)).mp h
    calc _ ≤ B*n^2 := h'
      _ = _ := mul_comm _ _
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, shortRangeKernel2 c p
      (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P j) (a*m) hn w) ≤ τ :=
    fun i j hij u w => shortRangeKernel2_le_of_separated hc0 hp hδ
      (hsep i j hij _ (smallHexPatchNodes2_mem (P i) _ hn u) _
        (smallHexPatchNodes2_mem (P j) _ hn w))
  have hrow : ∀ i u, (∑ j, ∑ w, shortRangeKernel2 c p
      (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P j) (a*m) hn w)) ≤
      (∑ w, shortRangeKernel2 c p (smallHexPatchNodes2 (P i) (a*m) hn u)
        (smallHexPatchNodes2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, shortRangeKernel2 c p
        (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P j) (a*m) hn w)) ≤
        (if j = i then ∑ w, shortRangeKernel2 c p (smallHexPatchNodes2 (P i) (a*m) hn u)
          (smallHexPatchNodes2 (P i) (a*m) hn w) else 0)+n^2*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 2).le hτ0)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 2 → TwelveNodeIndex (a*m), τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = n^2*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, shortRangeKernel2 c p
            (smallHexPatchNodes2 (P i) (a*m) hn u)
            (smallHexPatchNodes2 (P i) (a*m) hn w) else 0)+n^2*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- all pairs
  have hsplit : (∑ q, ∑ q', shortRangeKernel2 c p
      (hexFamilyNodes2 P (a*m) hn q) (hexFamilyNodes2 P (a*m) hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, shortRangeKernel2 c p
        (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P j) (a*m) hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, shortRangeKernel2 c p (smallHexPatchNodes2 (P i) (a*m) hn u)
          (smallHexPatchNodes2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, shortRangeKernel2 c p (smallHexPatchNodes2 (P i) (a*m) hn u)
          (smallHexPatchNodes2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*((K:ℝ)*(n^2*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ ≤ (∑ _i : Fin K, n^2*B)+(K:ℝ)*(n^2*((K:ℝ)*(n^2*τ))) :=
      add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end SphericalRiesz
end
end

section

/-! Sharp Gaussian window of a twelfth-order foreground family at exact mass.

Inside one patch the nodes of the uncorrected middle block are lattice midpoints, so their
mutual Gaussian rows are Hex theta rows with the factor `(1-η)²` of the near-flat chart.  All
other nodes keep the conservative theta row.  A symmetric nonnegative pair sum is at most the
pair sum of a core plus twice the full rows outside the core, and the number of nodes outside
the middle block is `n²⁴ - (n-74)²⁴`.  Two patches are separated by a positive distance.  At the
exact-mass rational allocation the two theta arguments do not depend on the refinement:

`Σ_{fg,fg} G_t ≤ M (Θ(α(1-η)²) + 2 (1-(1-74/n)²⁴) Θ(κα)) + M² e^{-tδ²}`,  `M = K n²⁴`.

The residual points, the limit in the refinement and the attaining sequence are not part of
this file. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The Hex theta function is nonincreasing on the positive axis. -/
theorem hexGaussianThetaReal2_anti {β₁ β₂ : ℝ} (h₁ : 0 < β₁) (h : β₁ ≤ β₂) :
    hexGaussianThetaReal2 β₂ ≤ hexGaussianThetaReal2 β₁ := by
  have hs : ∀ β : ℝ, 0 < β → Summable (fun x : hexLattice =>
      Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2))) := fun β hβ =>
    (Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hβ)).summable
  unfold hexGaussianThetaReal2
  refine Summable.tsum_le_tsum (fun x => ?_) (hs β₂ (h₁.trans_le h)) (hs β₁ h₁)
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ Real.pi*‖(x : HexAmbient)‖^2 := by positivity
  nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]

/-- A symmetric nonnegative pair sum is at most the pair sum of a core plus twice the full rows
outside the core. -/
theorem pairSum_le_core_add_restS2 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (f : ι → ι → ℝ) (hf : ∀ u w, 0 ≤ f u w) (hs : ∀ u w, f u w = f w u) :
    (∑ u, ∑ w, f u w) ≤ (∑ u ∈ S, ∑ w ∈ S, f u w)+2*(∑ u ∈ Sᶜ, ∑ w, f u w) := by
  have h1 : (∑ u, ∑ w, f u w) = (∑ u ∈ S, ∑ w, f u w)+∑ u ∈ Sᶜ, ∑ w, f u w :=
    (Finset.sum_add_sum_compl S fun u => ∑ w, f u w).symm
  have h2 : (∑ u ∈ S, ∑ w, f u w) =
      (∑ u ∈ S, ∑ w ∈ S, f u w)+∑ u ∈ S, ∑ w ∈ Sᶜ, f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S fun w => f u w).symm
  have h3 : (∑ u ∈ S, ∑ w ∈ Sᶜ, f u w) ≤ ∑ w ∈ Sᶜ, ∑ u, f w u := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun w _ => ?_
    calc (∑ u ∈ S, f u w) = ∑ u ∈ S, f w u := Finset.sum_congr rfl fun u _ => hs u w
      _ ≤ ∑ u, f w u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun u _ _ => hf w u
  rw [h1, h2]
  linarith

/-- Indices of the uncorrected middle block of the twelfth-order tensor rule. -/
def twelveMiddleCubeS2 (n : ℕ) : (Fin 2 → Fin (n-74)) ↪ (Fin 2 → TwelveNodeIndex n) where
  toFun u := fun i => Sum.inr (Sum.inl (u i))
  inj' := by
    intro u w h
    funext i
    exact Sum.inl_injective (Sum.inr_injective (congrFun h i))

theorem twelveCubeNode_middleS2 (n : ℕ) (u : Fin 2 → Fin (n-74)) (i : Fin 2) :
    twelveCubeNode 2 n (twelveMiddleCubeS2 n u) i = ((u i:ℝ)+37+1/2)/(n:ℝ) := rfl

/-- Middle nodes are lattice midpoints: their flat distances are lattice distances at scale
`1/n`. -/
theorem twelveMiddleCube_flat_distanceS2 (n : ℕ) (u w : Fin 2 → Fin (n-74)) :
    dist (WithLp.toLp 2 (hexMap (twelveCubeNode 2 n (twelveMiddleCubeS2 n u))) : HexAmbient)
      (WithLp.toLp 2 (hexMap (twelveCubeNode 2 n (twelveMiddleCubeS2 n w)))) =
      (n:ℝ)⁻¹*‖((hexGridLattice2 (n-74) w-hexGridLattice2 (n-74) u : hexLattice) :
        HexAmbient)‖ := by
  have he : twelveCubeNode 2 n (twelveMiddleCubeS2 n u)-twelveCubeNode 2 n (twelveMiddleCubeS2 n w) =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, twelveCubeNode_middleS2, div_eq_mul_inv]
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
theorem smallHexPatch_middle_row {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 2 → Fin (n-74),
      (∑ w, sphereGaussianKernel2 t
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n w))) ≤
      hexGaussianThetaReal2 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaHexPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x : (Fin 2 → Fin (n-74)) → UnitCube 2 := fun w =>
    ⟨twelveCubeNode 2 n (twelveMiddleCubeS2 n w), fun i =>
      ⟨(twelveCubeNode_mem_open 2 n hn (twelveMiddleCubeS2 n w) i).1.le,
        (twelveCubeNode_mem_open 2 n hn (twelveMiddleCubeS2 n w) i).2.le⟩⟩
  have hrow := hb p.g p.v p.c hv p.c_mem p.ε p.ε_pos hε p.small (hexGridLattice2 (n-74)) x
    (n:ℝ)⁻¹ (inv_pos.mpr hnR) (fun i j => twelveMiddleCube_flat_distanceS2 n i j) t ht u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n w))) ≤
      hexGaussianThetaReal2 (t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n w))) =
      sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n w)) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
      (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n w))) (Finset.mem_univ u)).symm
  have hθ : t*((1-η)*p.ε/(n:ℝ))^2/Real.pi = t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi := by
    rw [div_eq_mul_inv ((1-η)*p.ε) (n:ℝ)]
  rw [hsplit, sphereGaussianKernel2_self t, hθ]
  linarith

/-- The fraction of the density scale kept by the conservative rows of corrected nodes. -/
def hexConservativeRowFactor2 : ℝ := (patchChartLower2/(2*‖equalAreaFlatDerivative2‖))^2

theorem hexConservativeRowFactor2_pos : 0 < hexConservativeRowFactor2 := by
  have hD := equalAreaFlatDerivative2_norm_pos
  have hL := patchChartLower2_pos
  unfold hexConservativeRowFactor2
  positivity

/-- All nodes of a small patch: conservative theta rows, uniformly in the refinement. -/
theorem smallHexPatch_all_row :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 2 → TwelveNodeIndex n,
      (∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn w)) ≤
      hexGaussianThetaReal2
        (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedHexPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hrow := equalAreaHexTwelfth2_gaussian_row hn p.g p.v p.c p.c_mem p.ε_pos p.small
    patchChartLower2_pos ht
    (fun x hx y hy => hgeom p.v hv p.ε p.ε_pos hε p.g p.c p.c_mem x hx y hy) u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn u) (smallHexPatchNodes2 p n hn w)) ≤
      hexGaussianThetaReal2
        (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
      (smallHexPatchNodes2 p n hn w)) =
      sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn u)+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn w) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn u) (smallHexPatchNodes2 p n hn w))
      (Finset.mem_univ u)).symm
  rw [hsplit, sphereGaussianKernel2_self t]
  linarith

/-- The full Gaussian pair sum of one small patch: sharp theta rows on the middle block and
conservative rows for the `n²⁴-(n-74)²⁴` other nodes. -/
theorem smallHexPatch_pairSum_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallHexCubePatch2), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t →
      (∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn w)) ≤
      (n:ℝ)^2*hexGaussianThetaReal2 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi)+
        2*((n:ℝ)^2-((n:ℝ)-74)^2)*hexGaussianThetaReal2
          (t*(p.ε*patchChartLower2/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi) := by
  obtain ⟨ρ₁,hρ₁,hρ₁',hsharp⟩ := smallHexPatch_middle_row hη hη1
  obtain ⟨ρ₂,hρ₂,_,hall⟩ := smallHexPatch_all_row
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
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 2 → TwelveNodeIndex n),
      S = Finset.univ.map (twelveMiddleCubeS2 n) := ⟨_, rfl⟩
  have h74 : ((n-74 : ℕ) : ℝ) = (n:ℝ)-74 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hcardS : (S.card : ℝ) = ((n:ℝ)-74)^2 := by
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
      Nat.cast_pow, h74]
  have hcardT : (Fintype.card (Fin 2 → TwelveNodeIndex n) : ℝ) = (n:ℝ)^2 := by
    rw [twelveCubeNode_card 2 n hn]
    exact Nat.cast_pow _ _
  have hcardC : (Sᶜ.card : ℝ) = (n:ℝ)^2-((n:ℝ)-74)^2 := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ S), hcardT, hcardS]
  have hsplit : (∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
      (smallHexPatchNodes2 p n hn w)) ≤
      (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn w))+
      2*(∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
        (smallHexPatchNodes2 p n hn w)) :=
    pairSum_le_core_add_restS2 S (fun u w => sphereGaussianKernel2 t
      (smallHexPatchNodes2 p n hn u) (smallHexPatchNodes2 p n hn w))
      (fun u w => sphereGaussianKernel2_nonneg _ _ _)
      (fun u w => sphereGaussianKernel2_comm t _ _)
  have hcore : (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
      (smallHexPatchNodes2 p n hn w)) ≤ (n:ℝ)^2*θs := by
    have hrows : ∀ u : Fin 2 → Fin (n-74), (∑ w ∈ S, sphereGaussianKernel2 t
        (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
        (smallHexPatchNodes2 p n hn w)) ≤ θs := by
      intro u
      rw [hS, Finset.sum_map, hθs]
      exact hsharp p hv₁ hε₁ n hn t ht u
    have hpow : ((n:ℝ)-74)^2 ≤ (n:ℝ)^2 := by
      have h0 : 0 ≤ (n:ℝ)-74 := by
        rw [← h74]
        exact Nat.cast_nonneg _
      exact pow_le_pow_left₀ h0 (by linarith) 2
    calc (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
          (smallHexPatchNodes2 p n hn w))
        = ∑ u : Fin 2 → Fin (n-74), ∑ w ∈ S, sphereGaussianKernel2 t
            (smallHexPatchNodes2 p n hn (twelveMiddleCubeS2 n u))
            (smallHexPatchNodes2 p n hn w) := by
          rw [hS, Finset.sum_map]
      _ ≤ ∑ _u : Fin 2 → Fin (n-74), θs := Finset.sum_le_sum fun u _ => hrows u
      _ = ((n:ℝ)-74)^2*θs := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
            Fintype.card_fin, Nat.cast_pow, h74]
      _ ≤ (n:ℝ)^2*θs := mul_le_mul_of_nonneg_right hpow hθs0
  have hrest : (∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 p n hn u)
      (smallHexPatchNodes2 p n hn w)) ≤ ((n:ℝ)^2-((n:ℝ)-74)^2)*θc := by
    calc _ ≤ ∑ _u ∈ Sᶜ, θc := Finset.sum_le_sum fun u _ => by
            rw [hθc]
            exact hall p hv₂ hε₂ n hn t ht u
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardC]
  calc _ ≤ _ := hsplit
    _ ≤ (n:ℝ)^2*θs+2*(((n:ℝ)^2-((n:ℝ)-74)^2)*θc) :=
        add_le_add hcore (mul_le_mul_of_nonneg_left hrest (by norm_num))
    _ = _ := by rw [mul_assoc]

/-- Pair sum of a separated family: the patch sums plus the squared cardinality times the cross
bound. -/
theorem hexFamily_pairSum_le_patches {K : ℕ} (P : Fin K → SmallHexCubePatch2) (n : ℕ)
    (hn : 74 ≤ n) (k : SphereD 2 → SphereD 2 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i j, i ≠ j → ∀ u w, k (smallHexPatchNodes2 (P i) n hn u)
      (smallHexPatchNodes2 (P j) n hn w) ≤ τ) :
    (∑ q, ∑ q', k (hexFamilyNodes2 P n hn q) (hexFamilyNodes2 P n hn q')) ≤
      (∑ i, ∑ u, ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
        (smallHexPatchNodes2 (P i) n hn w))+((K:ℝ)*(n:ℝ)^2)^2*τ := by
  classical
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcardNodes : (Fintype.card (Fin 2 → TwelveNodeIndex n) : ℝ) = (n:ℝ)^2 := by
    rw [twelveCubeNode_card 2 n hn]
    exact Nat.cast_pow _ _
  have hrow : ∀ i u, (∑ j, ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
      (smallHexPatchNodes2 (P j) n hn w)) ≤
      (∑ w, k (smallHexPatchNodes2 (P i) n hn u) (smallHexPatchNodes2 (P i) n hn w))+
        (K:ℝ)*((n:ℝ)^2*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, k (smallHexPatchNodes2 (P i) n hn u)
        (smallHexPatchNodes2 (P j) n hn w)) ≤
        (if j = i then ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
          (smallHexPatchNodes2 (P i) n hn w) else 0)+(n:ℝ)^2*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 2).le hτ)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 2 → TwelveNodeIndex n, τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = (n:ℝ)^2*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
            (smallHexPatchNodes2 (P i) n hn w) else 0)+(n:ℝ)^2*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit : (∑ q, ∑ q', k (hexFamilyNodes2 P n hn q) (hexFamilyNodes2 P n hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
        (smallHexPatchNodes2 (P j) n hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, k (smallHexPatchNodes2 (P i) n hn u)
          (smallHexPatchNodes2 (P i) n hn w))+(K:ℝ)*((n:ℝ)^2*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, k (smallHexPatchNodes2 (P i) n hn u)
          (smallHexPatchNodes2 (P i) n hn w))+(K:ℝ)*((n:ℝ)^2*((K:ℝ)*((n:ℝ)^2*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ = _ := by ring

/-- Gaussian window of a separated twelfth-order foreground family at exact mass. -/
theorem hexPatchFamily_gaussianWindow_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (α : ℝ), 0 < α →
      (∑ q, ∑ q', sphereGaussianKernel2 (sphereGaussianScale2 ((d*m)^2) α)
          (hexFamilyNodes2 P (a*m) hn q) (hexFamilyNodes2 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
          2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
            hexGaussianThetaReal2 (α*hexConservativeRowFactor2))+
        ((K:ℝ)*((a*m:ℕ):ℝ)^2)^2*
          Real.exp (-(sphereGaussianScale2 ((d*m)^2) α*δ^2)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallHexPatch_pairSum_le hη hη1
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
  have hsub : n^2-(n-74)^2 = n^2*(1-(1-74/n)^2) := by
    have h74 : n-74 = n*(1-74/n) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hn0']
    rw [h74, mul_pow]
    ring
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, sphereGaussianKernel2 t
      (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P i) (a*m) hn w)) ≤
      n^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
        2*(1-(1-74/n)^2)*hexGaussianThetaReal2 (α*hexConservativeRowFactor2)) := by
    intro i
    have h := hb (P i) (hv i) (hε i) (a*m) hn t ht
    rw [← hndef, hsharp i, hcons i, hsub] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, sphereGaussianKernel2 t
      (smallHexPatchNodes2 (P i) (a*m) hn u) (smallHexPatchNodes2 (P j) (a*m) hn w) ≤
      Real.exp (-(t*δ^2)) := by
    intro i j hij u w
    have hdist := hsep i j hij _ (smallHexPatchNodes2_mem (P i) _ hn u) _
      (smallHexPatchNodes2_mem (P j) _ hn w)
    unfold sphereGaussianKernel2
    apply Real.exp_le_exp.mpr
    have hsq : δ^2 ≤ dist (smallHexPatchNodes2 (P i) (a*m) hn u)
        (smallHexPatchNodes2 (P j) (a*m) hn w)^2 := pow_le_pow_left₀ hδ.le hdist 2
    have hmul := mul_le_mul_of_nonneg_left hsq ht.le
    linarith
  have hfam := hexFamily_pairSum_le_patches P (a*m) hn (sphereGaussianKernel2 t)
    (Real.exp_pos (-(t*δ^2))).le hcross
  rw [← hndef] at hfam
  calc _ ≤ (∑ i, ∑ u, ∑ w, sphereGaussianKernel2 t (smallHexPatchNodes2 (P i) (a*m) hn u)
          (smallHexPatchNodes2 (P i) (a*m) hn w))+((K:ℝ)*n^2)^2*Real.exp (-(t*δ^2)) := hfam
    _ ≤ (∑ _i : Fin K, n^2*(hexGaussianThetaReal2 (α*(1-η)^2)+
          2*(1-(1-74/n)^2)*hexGaussianThetaReal2 (α*hexConservativeRowFactor2)))+
          ((K:ℝ)*n^2)^2*Real.exp (-(t*δ^2)) :=
        add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end SphericalRiesz
end
end

section

/-! # Sharp upper bound of the Riesz energy on `S²` at every large `N`, `0 < s < 2` (stage S2-4)

Dimension-2 port of `LeechSharpUpper24`: the unit sphere `S² ⊂ ℝ³` and the triangular lattice of
covolume one (the `Hex…` objects) in place of `S²⁴` and the Leech lattice.  Three parts.

* `HexPatchFamily`: near-full separated rational patch families of the triangular lattice as
  families of small cube patches, and the residual cells of a refinement (`n = (d m)² - K (a m)²`
  cells of probability `1/N` whose union is the complement of the family).
* `HexBlock`: for a tolerance index `L ≥ 2` and every sufficiently large refinement, an actual
  configuration of `(d m)²` points with a common small-alpha budget, a common short-range cost
  and a Gaussian window bound which tends to the theta profile of the triangular lattice as
  `L → ∞`.
* `HexSharpUpper`: a diagonal choice over `L` gives one configuration of size `M(N) ≥ N`,
  `M(N)/N → 1`, for every large `N`; the Gaussian-only bridge bounds its normalized Riesz energy
  by the regularized-theta coefficient, and a subconfiguration of `N` points keeps the normalized
  energy up to the factor `(N/M)^(1-s/2) → 1`.

Exponents of dimension two.  The budgets are those of the bridge
`sphere2_riesz_upper_of_gaussian_budgets`: the small budget at `q = s/4` (in `(0, 1/2)`) and the
short-range cost at `p = s/4 - 1/2` (in `(-1/2, 0)`; it is `s/4 + (d-4)/4` in dimension `d`, that
is `s/4 + 5` on `S²⁴`), with the centring bound `(2M+n)/(-p)` of the short-range kernel
(`(2M+n)/(d/2-1-p)` in dimension `d`).  The background of the window at the scale `α₀ = 1/L` is at
most `α₀⁻¹ = L` (`α₀^(-d/2)`; `L¹²` on `S²⁴`) and the window weight is `L²`, so the residual
fraction of a block is taken below `L⁻³` (`L^(-(2+d/2))`; `L⁻¹⁴` on `S²⁴`).

The upper bound uses no Gaussian certificate and no CKMRV input.  The two-sided statements at
the end assume all-scale contact certificates of the triangular lattice for their lower half.  The
coefficient is the regularized theta Mellin integral `sphereRieszCoefficient2`; the last two
statements give it as the continued Epstein zeta value `A^(-s/2) ζ_Λ(s)`, `A = 4π` the area of
`S²` (`sphereRieszCoefficient2_eq_epstein`, part `HexEpsteinSphere2`). -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

section HexPatchFamily
open Set MeasureTheory
open scoped ENNReal
open Boundary

/-! ### HexPatchFamily

Near-full rational patch families of the triangular lattice on S² and the residual cells of a
refinement.

For every smallness radius `ρ` and every residual fraction `b` there is a finite family of small
cube patches of the triangular lattice of one common rational scale `ε d = r₀ a` which is pairwise
disjoint, separated by a positive distance, of exact probability `K (a/d)² > 1-b`, with
`K a² < d²`.

For every refinement `m` the complement of the family has probability exactly `n/N`,
`N = (d m)²`, `n = N - K (a m)² > 0`, and it splits into `n` measurable pairwise disjoint
cells of probability `1/N`.  These are the premises of the common Gaussian budget.  No point
choice, budget or attaining sequence is asserted here. -/

/-- A near-full separated family of small cube patches of the triangular lattice of one rational
scale on S². -/
theorem exists_hex_patch_family2 (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ (K : ℕ) (P : Fin K → SmallHexCubePatch2) (a d : ℕ) (δ : ℝ),
      0 < a ∧ 0 < d ∧ 0 < δ ∧
      (∀ i, ‖(P i).v‖ ≤ ρ) ∧ (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) ∧
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) ∧
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) ∧
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) ∧
      (sphereProbabilityD 2).real (hexFamilyUnion2 P) = (K:ℝ)*((a:ℝ)/d)^2 ∧
      1-b < (K:ℝ)*((a:ℝ)/d)^2 ∧ K*a^2 < d^2 := by
  obtain ⟨K,g,v,p,q,hp,hq,ℓ,hℓ,hℓdef,hscale,hcell,hd,⟨δ,hδ,hsep⟩,hlower,_,hmass,_,hbudget⟩ :=
    sphere2_near_full_rational_affine_cubes ρ b hρ hb
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hratio : ℓ*(q:ℝ) = hexUnitDensityRadius2*(p:ℝ) := by
    rw [hℓdef, equalAreaHexNormalizedScale2, mul_assoc, div_mul_cancel₀ _ hqR]
  refine ⟨K, fun i => ⟨g i, v i, cubeMidpoint2, ℓ, hℓ, cubeMidpoint2_mem_unitCube,
    (hcell i).2.1⟩, p, q, δ, hp, hq, hδ, fun i => (hcell i).1, fun _ => hscale,
    fun _ => hratio, hd, ?_, hmass, ?_, hbudget⟩
  · intro i j hij x hx y hy
    exact (hsep i j hij x hx y hy).le
  · rw [← hmass]
    exact hlower

/-- Residual cells of a refinement: `n = (d m)² - K (a m)² > 0` cells of probability `1/N`
whose union is the complement of the family. -/
theorem exists_hex_refinement_cells2 {K : ℕ} (P : Fin K → SmallHexCubePatch2) (a d : ℕ)
    (hd : 0 < d)
    (hmassP : (sphereProbabilityD 2).real (hexFamilyUnion2 P) = (K:ℝ)*((a:ℝ)/d)^2)
    (hbudget : K*a^2 < d^2) (m : ℕ) (hm : 0 < m) (hn : 74 ≤ a*m) :
    ∃ n : ℕ, 0 < n ∧
      Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m)))+n = (d*m)^2 ∧
      (n:ℝ)/(((d*m)^2:ℕ):ℝ) = 1-(K:ℝ)*((a:ℝ)/d)^2 ∧
      ∃ C : Fin n → Set (SphereD 2), (∀ i, MeasurableSet (C i)) ∧
        Pairwise (fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹) ∧
        (⋃ j, C j) = (hexFamilyUnion2 P)ᶜ := by
  have hcardM : Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) = K*(a*m)^2 := by
    rw [Fintype.card_prod, Fintype.card_fin, twelveCubeNode_card 2 (a*m) hn]
  have hlt : K*(a*m)^2 < (d*m)^2 := by
    have h1 : K*(a*m)^2 = K*a^2*m^2 := by rw [mul_pow, mul_assoc]
    have h2 : (d*m)^2 = d^2*m^2 := mul_pow d m 2
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hbudget (pow_pos hm 2)
  have hNpos : 0 < (d*m)^2 := by positivity
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
  obtain ⟨C, hCm, hCd, hCu, hCmass⟩ := exists_sphere2_equal_mass_cells hNpos
    (Nat.sub_pos_of_lt hlt) (hexFamilyUnion2_measurable P).compl hres
  refine ⟨(d*m)^2-K*(a*m)^2, Nat.sub_pos_of_lt hlt, ?_, hfrac, C, hCm, hCd, hCmass, hCu⟩
  rw [hcardM]
  exact Nat.add_sub_of_le hlt.le

end HexPatchFamily

section HexBlock
open Set MeasureTheory Filter
open scoped ENNReal Topology
open Boundary

/-! ### HexBlock

One block of the S² upper construction: an actual configuration with three Gaussian
controls.

For a tolerance index `L ≥ 2` take `η = α₀ = ε = 1/L`, the window weight `L²` and a near-full
rational family of the triangular lattice of residual fraction below `L⁻³`.  For every
sufficiently large refinement `m` the foreground nodes and one joint residual choice form an
actual configuration `X` of `N = (d m)²` points with

* the small-alpha budget `H_{s/4}(X) ≤ B_s`,
* the short-range cost `Σ T_{s/4-1/2}(X)/N ≤ D_s`,
* the window `Full_α(X) ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) B_s/L²` for every `α ≥ 1/L`,

where `B_s` and `D_s` depend only on `s`.  The exponent `p = s/4 - 1/2` is the one of the bridge
`sphere2_riesz_upper_of_gaussian_budgets`; it lies in `(-1/2, 0)`, inside the range `-1 ≤ p < 0`
of the joint residual choice.  The fraction `L⁻³` is fixed by the residual window: its centring
bound `w₃ n (N B(t₀))` with `w₃ = L²` and `N B(t₀) ≤ α₀⁻¹ = L`
(`sphereGaussianBackground2_scaled_cap`) is at most `N` when `n ≤ L⁻³ N`.  No limit in `L`, no
attaining sequence and no Riesz energy bound is asserted here. -/

/-- The joint bound is at most `N` times a constant when the residual fraction is at most
`λ⁻³`, the window weight is `λ²` and the window background is at most `λ` (in dimension `d` the
three powers are `λ^(-(2+d/2))`, `λ²`, `λ^(d/2)`; the short-range exponent is `p < d/2-1 = 0`). -/
theorem hexJointBound2_le {N n : ℕ} {M Fg Fb q p t₀ lam : ℝ}
    (hM0 : 0 ≤ M) (hMn : M+(n:ℝ) = (N:ℝ)) (hFg : Fg ≤ Fb) (hq : 0 < q) (hp : p < 0)
    (hlam : 1 ≤ lam) (hn : (n:ℝ) ≤ 1/lam^3*(N:ℝ))
    (hB : (N:ℝ)*sphereGaussianBackground2 t₀ ≤ lam) :
    hexJointBound2 N n M Fg q p t₀ 1 (lam^2) ≤ (N:ℝ)*(Fb+4^q/q+3/(-p)+2) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hnN : (n:ℝ) ≤ N := by linarith
  have hMN : M ≤ N := by linarith
  have hp' : 0 < -p := by linarith
  have h4q : 0 ≤ (4:ℝ)^q/q := div_nonneg (Real.rpow_nonneg (by norm_num) q) hq.le
  have hpow : lam^2*lam = lam^3 := by ring
  have hc3 : 1/lam^3*lam^2*lam = 1 := by
    rw [mul_assoc, hpow, one_div_mul_cancel (pow_ne_zero 3 hlam0.ne')]
  have hc2 : 1/lam^3*lam^2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (pow_pos hlam0 3)]
    exact pow_le_pow_right₀ hlam (by norm_num)
  have t1 : (N:ℝ)*Fg ≤ (N:ℝ)*Fb := mul_le_mul_of_nonneg_left hFg hN0
  have t2a : (n:ℝ)*((4:ℝ)^q/q) ≤ (N:ℝ)*((4:ℝ)^q/q) := mul_le_mul_of_nonneg_right hnN h4q
  have t2b : (n:ℝ)*lam^2 ≤ (N:ℝ) := by
    calc (n:ℝ)*lam^2 ≤ 1/lam^3*(N:ℝ)*lam^2 := mul_le_mul_of_nonneg_right hn (sq_nonneg lam)
      _ = (N:ℝ)*(1/lam^3*lam^2) := by ring
      _ ≤ (N:ℝ)*1 := mul_le_mul_of_nonneg_left hc2 hN0
      _ = N := mul_one _
  have t3 : (2*M+(n:ℝ))/(-p) ≤ (N:ℝ)*(3/(-p)) := by
    rw [div_le_iff₀ hp']
    calc 2*M+(n:ℝ) ≤ (N:ℝ)*3 := by linarith
      _ = (N:ℝ)*(3/(-p))*(-p) := by rw [mul_assoc, div_mul_cancel₀ _ hp'.ne']
  have t4 : lam^2*((n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀)) ≤ (N:ℝ) := by
    calc lam^2*((n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀))
        ≤ lam^2*((n:ℝ)*lam) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hn0) (sq_nonneg lam)
      _ ≤ lam^2*(1/lam^3*(N:ℝ)*lam) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn hlam0.le) (sq_nonneg lam)
      _ = (N:ℝ)*(1/lam^3*lam^2*lam) := by ring
      _ = N := by rw [hc3, mul_one]
  unfold hexJointBound2
  have e2 : (n:ℝ)*((4:ℝ)^q/q+lam^2) = (n:ℝ)*((4:ℝ)^q/q)+(n:ℝ)*lam^2 := by ring
  have e3 : (N:ℝ)*(Fb+(4:ℝ)^q/q+3/(-p)+2) =
      (N:ℝ)*Fb+(N:ℝ)*((4:ℝ)^q/q)+(N:ℝ)*(3/(-p))+(N:ℝ)+(N:ℝ) := by ring
  rw [e2, e3, one_mul]
  linarith

/-- Arithmetic of the short-range cost of a block. -/
theorem hexBlock_tail_arith {N M TB sep S rCS JB Bs : ℝ} (hN : 0 < N) (hM0 : 0 ≤ M)
    (hMN : M ≤ N) (hTB : 0 ≤ TB) (hsep : 0 ≤ sep) (hNsep : N*sep ≤ 1)
    (hS : S ≤ M*TB+M^2*sep) (hr : 1*rCS ≤ JB) (hJB : JB ≤ N*Bs) : (S+rCS)/N ≤ TB+1+Bs := by
  rw [div_le_iff₀ hN]
  have h1 : M*TB ≤ N*TB := mul_le_mul_of_nonneg_right hMN hTB
  have h2 : M^2*sep ≤ N := by
    calc M^2*sep = M*(M*sep) := by ring
      _ ≤ N*(N*sep) := mul_le_mul hMN (mul_le_mul_of_nonneg_right hMN hsep)
          (mul_nonneg hM0 hsep) hN.le
      _ ≤ N*1 := mul_le_mul_of_nonneg_left hNsep hN.le
      _ = N := mul_one N
  have h3 : rCS ≤ N*Bs := by linarith
  linarith

/-- Arithmetic of the foreground window of a block. -/
theorem hexBlock_window_arith {N M A R E E₀ c S : ℝ} (hN : 0 < N) (hM0 : 0 ≤ M) (hMN : M ≤ N)
    (hA : 0 ≤ A) (hR0 : 0 ≤ R) (hR : R ≤ c) (hE0 : 0 ≤ E) (hE : E ≤ E₀) (hNE : N*E₀ ≤ c)
    (hS : S ≤ M*(A+R)+M^2*E) : S/N ≤ A+2*c := by
  rw [div_le_iff₀ hN]
  have h1 : M*(A+R) ≤ N*(A+c) := mul_le_mul hMN (by linarith) (by linarith) hN.le
  have h2 : M^2*E ≤ N*c := by
    calc M^2*E = M*(M*E) := by ring
      _ ≤ N*(N*E₀) := mul_le_mul hMN (mul_le_mul hMN hE hE0 hN.le) (mul_nonneg hM0 hE0) hN.le
      _ ≤ N*c := mul_le_mul_of_nonneg_left hNE hN.le
  linarith

/-- Common small-alpha constant of the blocks (`q = s/4`, `p = s/4-1/2`; finite for
`0 < s < 2`, where `-p = (2-s)/4 > 0`). -/
def hexBlockSmallConst2 (s : ℝ) : ℝ :=
  hexForegroundProfileConst2*(4^(s/4)/(s/4))+
    hexForegroundProfileGain2 (s/4)*(4^(s/4/2)/(s/4/2))+4^(s/4)/(s/4)+3/(-(s/4-1/2))+2

/-- Common short-range constant of the blocks, at the exponent `p = s/4-1/2`. -/
def hexBlockTailConst2 (s : ℝ) : ℝ :=
  hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2)
    (s/4-1/2)+1+hexBlockSmallConst2 s

/-- One block: explicit conditions on the family and on the refinement give an actual
configuration with the three Gaussian controls. -/
theorem exists_hex_block_configuration2 {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {L : ℕ}
    (hL : 2 ≤ L) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      (sphereProbabilityD 2).real (hexFamilyUnion2 P) = (K:ℝ)*((a:ℝ)/d)^2 →
      1-1/(L:ℝ)^3 < (K:ℝ)*((a:ℝ)/d)^2 → K*a^2 < d^2 →
      ∀ m : ℕ, 0 < m → 74 ≤ a*m →
      ((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4)) ≤ 1 →
      (((d*m)^2:ℕ):ℝ)*separatedShortRangeBound2
        (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2) δ ≤ 1 →
      2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) ≤ 1/(L:ℝ) →
      (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      ∃ X : ConfigurationD 2 ((d*m)^2),
        sphereGaussianSmallBudget2 (s/4) X ≤ hexBlockSmallConst2 s ∧
        cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2)) X/
          (((d*m)^2:ℕ):ℝ) ≤ hexBlockTailConst2 s ∧
        ∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(hexBlockSmallConst2 s/(L:ℝ)^2) := by
  have hq : 0 < s/4 := by linarith
  have hq2 : s/4 ≤ 2 := by linarith
  have hp0 : -1 ≤ s/4-1/2 := by linarith
  have hp1 : -1 < s/4-1/2 := by linarith
  have hp : s/4-1/2 < 0 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := hexConservativeRowFactor2_pos
  obtain ⟨ρ₁,hρ₁,_,hbudget⟩ := exists_hex_common_budget2
  obtain ⟨ρ₂,hρ₂,_,htail⟩ := hexPatchFamily_shortRange_le
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := hexPatchFamily_gaussianWindow_le hη hη1
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep hmassP hcov hKad m hm hn he2 he3 he4 he5
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₂ : ∀ i, ‖(P i).v‖ ≤ ρ₂ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₁ := fun i =>
    (hε i).trans (min_le_left _ _)
  have hε₂ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₂ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₃ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the residual cells of the refinement
  obtain ⟨n, hnpos, hcard, hfrac, C, hCm, hCd, hCmass, hCu⟩ :=
    exists_hex_refinement_cells2 P a d hd hmassP hKad m hm hn
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2) := sphereGaussianDensityFactor2_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)) :=
    (sphereGaussianScale2_pos hNpos hη).le
  -- one joint residual choice
  obtain ⟨z, hz, havoid, _, hH, hT, hG⟩ := hbudget P hv₁ hε₁ hdisj a d m hd hm hratio hn hnpos
    hcard C hCm hCd hCmass hCu hq hq2 hp0 hp ht₀ (zero_le_one : (0:ℝ) ≤ 1) (sq_nonneg (L:ℝ))
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hcard
  have hMN : ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^2:ℕ):ℝ) := by
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hMK : ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^2 := by
    rw [Fintype.card_prod, Fintype.card_fin, twelveCubeNode_card 2 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the joint bound is at most N B_s
  have hFg : hexForegroundBudget2 a d m (s/4) ≤
      hexForegroundProfileConst2*(4^(s/4)/(s/4))+
        hexForegroundProfileGain2 (s/4)*(4^(s/4/2)/(s/4/2)) := by
    unfold hexForegroundBudget2
    have hG0 := hexForegroundProfileGain2_nonneg (s/4)
    have hZ0 : 0 ≤ (4:ℝ)^(s/4/2)/(s/4/2) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have h1 : hexForegroundProfileGain2 (s/4)*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4))*
        ((4:ℝ)^(s/4/2)/(s/4/2)) ≤ hexForegroundProfileGain2 (s/4)*((4:ℝ)^(s/4/2)/(s/4/2)) := by
      calc hexForegroundProfileGain2 (s/4)*((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4))*
            ((4:ℝ)^(s/4/2)/(s/4/2))
          = hexForegroundProfileGain2 (s/4)*(((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4)))*
            ((4:ℝ)^(s/4/2)/(s/4/2)) := by ring
        _ ≤ hexForegroundProfileGain2 (s/4)*1*((4:ℝ)^(s/4/2)/(s/4/2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hG0) hZ0
        _ = _ := by rw [mul_one]
    linarith
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^3*(((d*m)^2:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^2:ℕ):ℝ) < 1/(L:ℝ)^3 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  have hBcap : (((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) ≤ (L:ℝ) := by
    have h := sphereGaussianBackground2_scaled_cap hNpos hη
    have e : (1/(L:ℝ))⁻¹ = (L:ℝ) := by rw [one_div, inv_inv]
    rw [e] at h
    exact h
  have hJB : hexJointBound2 ((d*m)^2) n
      ((Fintype.card (Fin K × (Fin 2 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)
      (hexForegroundBudget2 a d m (s/4)) (s/4) (s/4-1/2)
      (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) 1 ((L:ℝ)^2) ≤
      (((d*m)^2:ℕ):ℝ)*hexBlockSmallConst2 s :=
    hexJointBound2_le hM0 hMn hFg hq hp hL1 hnfrac hBcap
  refine ⟨combinedConfiguration2 (hexFamilyNodes2 P (a*m) hn) z hcard
    (hexFamilyNodes2_injective P hdisj (a*m) hn) hz havoid, ?_, ?_, ?_⟩
  · -- the small-alpha budget
    exact le_of_mul_le_mul_left (hH.trans hJB) hNR
  · -- the short-range cost
    have hsumT := combinedConfiguration2_sum (hexFamilyNodes2 P (a*m) hn) z hcard
      (hexFamilyNodes2_injective P hdisj (a*m) hn) hz havoid
      (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2))
      (shortRangeKernel2_symm _ _)
    have htailP := htail P hv₂ hε₂ hδ hsep a d m ha hd hm hratio hn (s/4-1/2) hp1
    rw [← hMK] at htailP
    have hTB0 : 0 ≤ hexGaussianTailBudget2
        (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) (s/4-1/2) :=
      hexGaussianTailBudget2_nonneg
        (hexCorrectedDensityBudgetScale2_pos hexUnitDensityRadius2_pos) hp1
    have hsep0 : 0 ≤ separatedShortRangeBound2
        (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2) δ :=
      separatedShortRangeBound2_nonneg hc0 hp1 hδ
    unfold cellPairSum hexBlockTailConst2
    rw [hsumT]
    exact hexBlock_tail_arith hNR hM0 hMN hTB0 hsep0 he3 htailP hT hJB
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration2_fullScaled_le hNpos (hexFamilyNodes2 P (a*m) hn) z
      hcard (hexFamilyNodes2_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    -- the three small quantities
    have hθ : hexGaussianThetaReal2 (α*hexConservativeRowFactor2) ≤
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) :=
      hexGaussianThetaReal2_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h74 : (74:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-74/((a*m:ℕ):ℝ))^2 := by
      have h1 : 74/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h74
      have h2 : 0 ≤ 74/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-74/((a*m:ℕ):ℝ))^2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
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
        hexBlockSmallConst2 s/(L:ℝ)^2 := by
      rw [div_le_div_iff₀ hNR (pow_pos hL0 2)]
      have h := hG.trans hJB
      linarith
    have h2L : hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))

/-- The explicit conditions of a block hold for every sufficiently large refinement. -/
theorem hexBlock_conditions_eventually {s : ℝ} (hs : 0 < s) {L : ℕ} (hL : 2 ≤ L) (a d : ℕ)
    (ha : 0 < a) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 74 ≤ a*m ∧
      ((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4)) ≤ 1 ∧
      (((d*m)^2:ℕ):ℝ)*separatedShortRangeBound2
        (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2) δ ≤ 1 ∧
      2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) ≤ 1/(L:ℝ) ∧
      (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hΓ : 0 < Real.Gamma (s/4-1/2+1) := Real.Gamma_pos_of_pos (by linarith)
  have hδ2 : 0 < δ^2 := pow_pos hδ 2
  -- sizes
  have hdm : Tendsto (fun m : ℕ => d*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hd) tendsto_id
  have ham : Tendsto (fun m : ℕ => a*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id
  have hNt0 : Tendsto (fun m : ℕ => (d*m)^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^2 := fun m => by positivity
  -- the gain of the small-alpha profile
  have h2 : Tendsto (fun m : ℕ => ((d:ℝ)/(a:ℝ))^2*((d*m:ℕ):ℝ)^(-(s/4))) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((d*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hdm
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < s/4)).comp hcast).const_mul
      (((d:ℝ)/(a:ℝ))^2)
    simpa only [mul_zero, Function.comp_apply] using h
  have e2 := (tendsto_order.mp h2).2 1 one_pos
  -- the separated short-range bound
  have h3 : Tendsto (fun m : ℕ => (((d*m)^2:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (sphereGaussianScale2_separated_tendsto hNt hNp (by norm_num : (0:ℝ) < 1/2) hδ)
  have h3g : Tendsto (fun m : ℕ => (((d*m)^2:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2))*Real.Gamma (s/4-1/2+1))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using h3.mul_const (Real.Gamma (s/4-1/2+1))
  have e3a := (tendsto_order.mp h3g).2 1 one_pos
  have e3b := (tendsto_atTop.mp
    (sphereGaussianScale2_tendsto hNt0 (by norm_num : (0:ℝ) < 1/2))) (1/δ^2)
  -- the corrected fraction
  have h4 : Tendsto (fun m : ℕ => 2*(1-(1-74/((a*m:ℕ):ℝ))^2)*
      hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((a*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp ham
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h74 : Tendsto (fun _ : ℕ => (74:ℝ)) atTop (𝓝 74) := tendsto_const_nhds
    have hx : Tendsto (fun m : ℕ => (74:ℝ)/((a*m:ℕ):ℝ)) atTop (𝓝 0) := h74.div_atTop hcast
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
  filter_upwards [eventually_ge_atTop 74, e2, e3a, e3b, e4, e5] with m hm1 hm2 hm3a hm3b hm4 hm5
  refine ⟨by omega, hm1.trans (Nat.le_mul_of_pos_left m ha), hm2.le, ?_, hm4.le, hm5.le⟩
  have hx : sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2 =
      sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by
    rw [sphereGaussianScale2_eq_factor]
    ring
  have hx1 : 1 ≤ sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by
    rw [← hx]
    exact (div_le_iff₀ hδ2).mp hm3b
  have hx0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by linarith
  have hpow : (1/(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))^(s/4-1/2+1) ≤ 1 :=
    Real.rpow_le_one (one_div_nonneg.mpr hx0.le) ((div_le_one hx0).mpr hx1) (by linarith)
  rw [hx] at hm3a
  unfold separatedShortRangeBound2
  calc (((d*m)^2:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        ((1/(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))^(s/4-1/2+1)*Real.Gamma (s/4-1/2+1)))
      ≤ (((d*m)^2:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        (1*Real.Gamma (s/4-1/2+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hΓ.le) (Real.exp_pos _).le) (Nat.cast_nonneg _)
    _ = (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        Real.Gamma (s/4-1/2+1) := by ring
    _ ≤ 1 := hm3a.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a block configuration. -/
theorem exists_hex_block2 {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 2 ((d*m)^2),
      sphereGaussianSmallBudget2 (s/4) X ≤ hexBlockSmallConst2 s ∧
      cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2)) X/
        (((d*m)^2:ℕ):ℝ) ≤ hexBlockTailConst2 s ∧
      ∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
        (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(hexBlockSmallConst2 s/(L:ℝ)^2) := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_hex_block_configuration2 hs hs2 hL
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_hex_patch_family2 ρ (1/(L:ℝ)^3) hρ (one_div_pos.mpr (pow_pos hL0 3))
  refine ⟨d, hd, ?_⟩
  filter_upwards [hexBlock_conditions_eventually hs hL a d ha hd hδ] with m hm
  obtain ⟨hm0, hn, he2, he3, he4, he5⟩ := hm
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep hmassP hcov hKad m hm0 hn he2 he3 he4 he5

end HexBlock

section HexSharpUpper
open Set MeasureTheory Filter
open scoped Topology

/-! ### HexSharpUpper

Sharp upper bound for the Riesz energy on S² at every large `N`, for all `0 < s < 2`.

For every tolerance index the block construction gives actual configurations at all rational
sizes `(d m)²` with common Gaussian budgets and a window bound which tends to the theta profile
of the triangular lattice.  A diagonal choice over the tolerance index gives one configuration of
size `M(N) ≥ N`, `M(N)/N → 1`, for every large `N` (`M(N) = rationalSizeCeiling2 d N`, the least
`(d m)² ≥ N`); the Gaussian-only bridge bounds its normalized Riesz energy by the
regularized-theta coefficient.  A subconfiguration of `N` points keeps the normalized energy up to
the factor `(N/M)^(1-s/2) → 1`.

No Gaussian certificate, no lower bound and no CKMRV input is used in the upper half.  The
coefficient is the regularized theta Mellin integral `sphereRieszCoefficient2`; the statements
`…_epstein` give it as the continued Epstein zeta value of the triangular lattice. -/

/-- The ordered off-diagonal Riesz energy as a full pair sum with zero diagonal. -/
theorem energyRpowD_eq_orderedPair2 (s : ℝ) {d N : ℕ} (X : ConfigurationD d N) :
    energyRpowD s X =
      finiteOrderedPair (fun i j : Fin N => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) := by
  unfold energyRpowD finiteOrderedPair
  refine Finset.sum_congr rfl fun i _ => ?_
  show (∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s)) =
    ∑ j : Fin N, (if i = j then (0:ℝ) else (dist (X i) (X j))^(-s))
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin N => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) (Finset.mem_univ i),
    ite_eq_left rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj).symm]

theorem energyRpowD_nonneg2 (s : ℝ) {d N : ℕ} (X : ConfigurationD d N) :
    0 ≤ energyRpowD s X := by
  unfold energyRpowD
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg _

/-- A subconfiguration of `N` points whose Riesz energy is at most `(N/M)²` times the energy of
the whole configuration. -/
theorem energyRpowD_exists_subconfiguration2 (s : ℝ) {d : ℕ} (N M : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (X : ConfigurationD d M) :
    ∃ e : Fin N ↪ Fin M, energyRpowD s (e.trans X) ≤ ((N:ℝ)/(M:ℝ))^2*energyRpowD s X := by
  obtain ⟨e, he⟩ := finiteOrderedPair_exists_subembedding N M hN hNM
    (fun i j : Fin M => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s))
    (fun i j => by
      show (if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) =
        if j = i then (0:ℝ) else (dist (X j) (X i))^(-s)
      by_cases h : i = j
      · subst h
        rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), dist_comm])
    (fun i => ite_eq_left rfl)
  refine ⟨e, ?_⟩
  have hX := energyRpowD_eq_orderedPair2 s X
  have hY : energyRpowD s (e.trans X) = finiteOrderedPair (fun i j : Fin N =>
      if e i = e j then (0:ℝ) else (dist (X (e i)) (X (e j)))^(-s)) := by
    rw [energyRpowD_eq_orderedPair2]
    unfold finiteOrderedPair
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show (if i = j then (0:ℝ) else (dist ((e.trans X) i) ((e.trans X) j))^(-s)) =
      if e i = e j then (0:ℝ) else (dist (X (e i)) (X (e j)))^(-s)
    by_cases h : i = j
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · have h' : e i ≠ e j := fun he' => h (e.injective he')
      rw [ite_eq_right h, ite_eq_right h']
      rfl
  have he' : energyRpowD s (e.trans X)/((N:ℝ)*(N-1)) ≤ energyRpowD s X/((M:ℝ)*(M-1)) := by
    rw [hY, hX]
    exact he
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hnm : (N:ℝ) ≤ M := by exact_mod_cast hNM
  have hm : (0:ℝ) < M := by linarith
  have h1 : 0 < (N:ℝ)*(N-1) := mul_pos (by linarith) (by linarith)
  have h2 : 0 < (M:ℝ)*(M-1) := mul_pos hm (by linarith)
  have hE0 := energyRpowD_nonneg2 s X
  have hh := (div_le_iff₀ h1).mp he'
  have hcoef : ((N:ℝ)*(N-1))/((M:ℝ)*(M-1)) ≤ ((N:ℝ)/(M:ℝ))^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ h2 (sq_pos_of_pos hm)).mpr
    have hprod := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ N) hm.le) (sub_nonneg.mpr hnm)
    nlinarith
  calc energyRpowD s (e.trans X) ≤ energyRpowD s X/((M:ℝ)*(M-1))*((N:ℝ)*(N-1)) := hh
    _ = ((N:ℝ)*(N-1))/((M:ℝ)*(M-1))*energyRpowD s X := by ring
    _ ≤ ((N:ℝ)/(M:ℝ))^2*energyRpowD s X := mul_le_mul_of_nonneg_right hcoef hE0

/-- A subconfiguration of `N` points keeps the normalized Riesz energy on S² up to the factor
`(N/M)^(1-s/2)` (the energy scales by `(N/M)²` and the normalization is `N^(1+s/d)`, `d = 2`). -/
theorem normalizedEnergyRpow2_exists_subconfiguration (s : ℝ) (N M : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (X : ConfigurationD 2 M) :
    ∃ Y : ConfigurationD 2 N, normalizedEnergyRpow2 s Y ≤
      ((N:ℝ)/(M:ℝ))^(1-s/2)*normalizedEnergyRpow2 s X := by
  obtain ⟨e, he⟩ := energyRpowD_exists_subconfiguration2 s N M hN hNM X
  refine ⟨e.trans X, ?_⟩
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr : 0 < (N:ℝ)/(M:ℝ) := div_pos hn hm
  have hNp : 0 < (N:ℝ)^(1+s/2) := Real.rpow_pos_of_pos hn _
  have hMp : 0 < (M:ℝ)^(1+s/2) := Real.rpow_pos_of_pos hm _
  have hcancel : ((N:ℝ)/(M:ℝ))^2*(M:ℝ)^2 = (N:ℝ)^2 := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hm.ne')]
  have he' : energyRpowD s (e.trans X)-sphereRieszConst2 s*(N:ℝ)^2 ≤
      ((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst2 s*(M:ℝ)^2) := by
    have hexp : ((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst2 s*(M:ℝ)^2) =
        ((N:ℝ)/(M:ℝ))^2*energyRpowD s X-sphereRieszConst2 s*(((N:ℝ)/(M:ℝ))^2*(M:ℝ)^2) := by
      ring
    rw [hexp, hcancel]
    linarith
  have hNpow : (N:ℝ)^(1+s/2) = ((N:ℝ)/(M:ℝ))^(1+s/2)*(M:ℝ)^(1+s/2) := by
    rw [← Real.mul_rpow hr.le hm.le, div_mul_cancel₀ _ hm.ne']
  have hr2 : ((N:ℝ)/(M:ℝ))^(1-s/2)*((N:ℝ)/(M:ℝ))^(1+s/2) = ((N:ℝ)/(M:ℝ))^2 := by
    rw [← Real.rpow_add hr, show (1-s/2)+(1+s/2) = (2:ℝ) by ring]
    exact Real.rpow_two _
  have hpow : ((N:ℝ)/(M:ℝ))^2/(N:ℝ)^(1+s/2) =
      ((N:ℝ)/(M:ℝ))^(1-s/2)/(M:ℝ)^(1+s/2) := by
    rw [div_eq_div_iff hNp.ne' hMp.ne', hNpow, ← hr2]
    ring
  unfold normalizedEnergyRpow2
  calc (energyRpowD s (e.trans X)-sphereRieszConst2 s*(N:ℝ)^2)/(N:ℝ)^(1+s/2)
      ≤ (((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst2 s*(M:ℝ)^2))/(N:ℝ)^(1+s/2) :=
        div_le_div_of_nonneg_right he' hNp.le
    _ = ((N:ℝ)/(M:ℝ))^2/(N:ℝ)^(1+s/2)*(energyRpowD s X-sphereRieszConst2 s*(M:ℝ)^2) := by
        ring
    _ = ((N:ℝ)/(M:ℝ))^(1-s/2)*
        ((energyRpowD s X-sphereRieszConst2 s*(M:ℝ)^2)/(M:ℝ)^(1+s/2)) := by
        rw [hpow]
        ring

/-- The window bound of the blocks tends to the theta profile of the triangular lattice. -/
theorem hexBlockWindowBound_tendsto {α B : ℝ} (hα : 0 < α) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun k => (1+1/(L k:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L k:ℝ))^2)+2/(L k:ℝ))+
      (1+(L k:ℝ))*(B/(L k:ℝ)^2)) atTop (𝓝 (hexGaussianThetaReal2 α)) := by
  have hLR : Tendsto (fun k => (L k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hL
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hBc : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
  have hu : Tendsto (fun k => 1/(L k:ℝ)) atTop (𝓝 0) := hone.div_atTop hLR
  have h2u : Tendsto (fun k => 2/(L k:ℝ)) atTop (𝓝 0) := htwo.div_atTop hLR
  have hBL : Tendsto (fun k => B/(L k:ℝ)) atTop (𝓝 0) := hBc.div_atTop hLR
  have hBsq : Tendsto (fun k => B/(L k:ℝ)^2) atTop (𝓝 0) :=
    hBc.div_atTop ((tendsto_pow_atTop (two_ne_zero)).comp hLR)
  have harg : Tendsto (fun k => α*(1-1/(L k:ℝ))^2) atTop (𝓝 (α*(1-0)^2)) :=
    ((hone.sub hu).pow 2).const_mul α
  have hc : ContinuousAt hexGaussianThetaReal2 (α*(1-0)^2) :=
    hexGaussianThetaReal2_continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (by simpa using hα))
  have hθ : Tendsto (fun k => hexGaussianThetaReal2 (α*(1-1/(L k:ℝ))^2)) atTop
      (𝓝 (hexGaussianThetaReal2 (α*(1-0)^2))) := hc.tendsto.comp harg
  have hsum := ((hone.add hu).mul (hθ.add h2u)).add (hBsq.add hBL)
  have hlim : (1+0)*(hexGaussianThetaReal2 (α*(1-0)^2)+0)+((0:ℝ)+0) =
      hexGaussianThetaReal2 α := by norm_num
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with k hk
  have hLne : (L k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 : (L k:ℝ)*(B/(L k:ℝ)^2) = B/(L k:ℝ) := by
    rw [← mul_div_assoc, sq, mul_div_mul_left _ _ hLne]
  have h2 : (1+(L k:ℝ))*(B/(L k:ℝ)^2) = B/(L k:ℝ)^2+B/(L k:ℝ) := by
    rw [add_mul, one_mul, h1]
  rw [h2]

/-- Sharp upper bound on S² at every large `N`, for `0 < s < 2`: actual configurations whose
normalized Riesz energy `(E_s - I_s N²)/N^(1+s/2)` is at most the regularized-theta coefficient
of the triangular lattice plus `η`.  No hypothesis is used. -/
theorem sphere2_riesz_sharp_upper_allN {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      normalizedEnergyRpow2 s Y ≤ sphereRieszCoefficient2 s+η := by
  -- blocks for every tolerance index
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 2 ((d*m)^2),
        sphereGaussianSmallBudget2 (s/4) X ≤ hexBlockSmallConst2 s ∧
        cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/4-1/2)) X/
          (((d*m)^2:ℕ):ℝ) ≤ hexBlockTailConst2 s ∧
        ∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(hexBlockSmallConst2 s/((j+2:ℕ):ℝ)^2) :=
    fun j => exists_hex_block2 hs hs2 (L := j+2) (by omega)
  choose d hd hev using hblocks
  -- every tolerance index reaches every large N
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop,
      (rationalSizeCeiling2 (d j) N:ℝ)/(N:ℝ) ≤ 1+1/((j:ℝ)+1) ∧
      ∃ X : ConfigurationD 2 (rationalSizeCeiling2 (d j) N),
        sphereGaussianSmallBudget2 (s/4) X ≤ hexBlockSmallConst2 s ∧
        cellPairSum (shortRangeKernel2
          (sphereGaussianDensityFactor2 (rationalSizeCeiling2 (d j) N)) (s/4-1/2)) X/
          ((rationalSizeCeiling2 (d j) N:ℕ):ℝ) ≤ hexBlockTailConst2 s ∧
        ∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(hexBlockSmallConst2 s/((j+2:ℕ):ℝ)^2) := by
    intro j
    have h1 := (rationalSizeIndex2_tendsto (d j) (hd j)).eventually (hev j)
    have hgap : (1:ℝ) < 1+1/((j:ℝ)+1) := by
      have : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
      linarith
    have h2 := (tendsto_order.mp (rationalSizeCeiling2_ratio_tendsto (d j) (hd j))).2 _ hgap
    filter_upwards [h1, h2] with N hN1 hN2
    exact ⟨hN2.le, hN1⟩
  obtain ⟨J, hJt, hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hJ
  obtain ⟨N₂, hN₂1, hN₂2⟩ : ∃ N₂ : ℕ, N₁ ≤ N₂ ∧ 2 ≤ N₂ :=
    ⟨max N₁ 2, le_max_left _ _, le_max_right _ _⟩
  -- one configuration for every index k, of size M k ≥ N₂ + k
  have hQ := fun k : ℕ => hN₁ (N₂+k) (hN₂1.trans (Nat.le_add_right N₂ k))
  choose hratio Z hZ1 hZ2 hZ3 using hQ
  have hge : ∀ k : ℕ, N₂+k ≤ rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k) := fun k =>
    rationalSizeCeiling2_ge _ _ (hd _)
  have hMt : Tendsto (fun k : ℕ => rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₂).trans (hge k)) tendsto_id
  have hMpos : ∀ k : ℕ, 0 < rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k) := fun k =>
    lt_of_lt_of_le (by omega) (hge k)
  have hidx : Tendsto (fun k : ℕ => N₂+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₂) tendsto_id
  have hLt : Tendsto (fun k : ℕ => J (N₂+k)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₂+k)) 2) (hJt.comp hidx)
  -- the pointwise window
  have hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (Z k) ≤ hexGaussianThetaReal2 α+ε := by
    intro α hα ε hε
    have hΦ := hexBlockWindowBound_tendsto (B := hexBlockSmallConst2 s) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (hexGaussianThetaReal2 α+ε) (by linarith)
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hu : Tendsto (fun k : ℕ => 1/((J (N₂+k)+2:ℕ):ℝ)) atTop (𝓝 0) :=
      hone.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with k hk1 hk2
    exact (hZ3 k α hk2.le).trans hk1.le
  have hfin := sphere2_riesz_upper_of_gaussian_budgets hs hs2 hMt hMpos Z
    (hexBlockSmallConst2 s) (hexBlockTailConst2 s) hZ1 hZ2 hp (η/2) (half_pos hη)
  -- the size ratio tends to one
  have hNk : ∀ k : ℕ, (0:ℝ) < ((N₂+k:ℕ):ℝ) := fun k => by
    exact_mod_cast (show 0 < N₂+k by omega)
  have hratio_lower : ∀ k : ℕ, (1:ℝ) ≤
      (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)/((N₂+k:ℕ):ℝ) := fun k => by
    rw [le_div_iff₀ (hNk k), one_mul]
    exact_mod_cast hge k
  have hupper : Tendsto (fun k : ℕ => 1+1/((J (N₂+k):ℝ)+1)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hJR : Tendsto (fun k : ℕ => (J (N₂+k):ℝ)+1) atTop atTop :=
      tendsto_atTop_mono
        (fun k => (le_add_of_nonneg_right zero_le_one : (J (N₂+k):ℝ) ≤ (J (N₂+k):ℝ)+1))
        (tendsto_natCast_atTop_atTop.comp (hJt.comp hidx))
    have h := hone.add (hone.div_atTop hJR)
    rw [add_zero] at h
    exact h
  have hratio_t : Tendsto (fun k : ℕ =>
      (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)/((N₂+k:ℕ):ℝ)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hratio_lower hratio
  have hinv_t : Tendsto (fun k : ℕ =>
      ((N₂+k:ℕ):ℝ)/(rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio_t.inv₀ one_ne_zero
  have hpow_t : Tendsto (fun k : ℕ =>
      (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/2)) atTop (𝓝 1) := by
    have h := hinv_t.rpow_const (p := 1-s/2) (Or.inl one_ne_zero)
    rw [Real.one_rpow] at h
    exact h
  have hprod_t : Tendsto (fun k : ℕ =>
      (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/2)*
        (sphereRieszCoefficient2 s+η/2)) atTop (𝓝 (sphereRieszCoefficient2 s+η/2)) := by
    have h := hpow_t.mul_const (sphereRieszCoefficient2 s+η/2)
    rw [one_mul] at h
    exact h
  have e3 := (tendsto_order.mp hprod_t).2 (sphereRieszCoefficient2 s+η) (by linarith)
  -- subconfigurations of every large size
  have hall : ∀ᶠ k : ℕ in atTop, ∃ Y : ConfigurationD 2 (N₂+k),
      normalizedEnergyRpow2 s Y ≤ sphereRieszCoefficient2 s+η := by
    filter_upwards [hfin, e3] with k hk1 hk3
    obtain ⟨Y, hY⟩ := normalizedEnergyRpow2_exists_subconfiguration s (N₂+k)
      (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k)) (by omega) (hge k) (Z k)
    refine ⟨Y, hY.trans ?_⟩
    have hr0 : 0 ≤ (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/2) :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
    exact (mul_le_mul_of_nonneg_left hk1 hr0).trans hk3.le
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hall
  refine ⟨N₂+k₀, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = N₂+k := Nat.exists_eq_add_of_le (by omega)
  exact hk₀ k (by omega)

/-- The sharp upper bound at every large `N` in the original ordered-pair normalization, with
the actual uniform double integral.  No hypothesis is used. -/
theorem sphere2_riesz_sharp_upper_conjecture_form {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        sphereRieszCoefficient2 s+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere2_riesz_sharp_upper_allN hs hs2 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyRpow2, sphereRieszConst2_eq_pair_integral hs hs2] at hY

/-- Two-sided sharp asymptotics on S² for every `0 < s < 2`, with the regularized-theta Mellin
coefficient and the actual uniform double integral.  The lower half assumes all-scale contact
certificates of the triangular lattice (the CKMRV input); the upper half is unconditional. -/
theorem sphere2_riesz_sharp_asymptotic_all
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      sphereRieszCoefficient2 s-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        sphereRieszCoefficient2 s+η) :=
  ⟨sphere2_riesz_sharp_lower_conjecture_form hG2 hs hs2,
    sphere2_riesz_sharp_upper_conjecture_form hs hs2⟩

/-- The sharp upper bound at every large `N` with the Epstein coefficient `A^(-s/2) ζ_Λ(s)`,
`A = 4π` the area of S² and `ζ_Λ(s) = hexEpsteinZeta (s/2)` the continued Epstein zeta function
of the triangular lattice of covolume one.  No hypothesis is used. -/
theorem sphere2_riesz_sharp_upper_epstein {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η := by
  rw [← sphereRieszCoefficient2_eq_epstein hs hs2]
  exact sphere2_riesz_sharp_upper_conjecture_form hs hs2

/-- Two-sided sharp asymptotics on S² for every `0 < s < 2` with the Epstein coefficient
`A^(-s/2) ζ_Λ(s)` of the triangular lattice, `A = 4π` (the conjectured form of the second-order
term).  The lower half assumes all-scale contact certificates of the triangular lattice; the
upper half is unconditional. -/
theorem sphere2_riesz_sharp_asymptotic_epstein
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) :=
  ⟨sphere2_riesz_sharp_lower_epstein hG2 hs hs2, sphere2_riesz_sharp_upper_epstein hs hs2⟩

end HexSharpUpper

end SphericalRiesz
end
end

section

/-! Unconditional sharp positive-exponent asymptotics on the unit sphere S².
The triangular-lattice certificate is supplied by `hexGaussianContact_all`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- Both sharp bounds, with the actual continuous energy and continued Epstein coefficient.
The energy uses ordered pairs of distinct points. -/
theorem sphere2_riesz_sharp_asymptotic_unconditional
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) :=
  sphere2_riesz_sharp_asymptotic_epstein hexGaussianContact_all hs hs2

/-- The same sharp bounds with the sphere area written as `4π`. -/
theorem sphere2_riesz_sharp_asymptotic_explicit
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyRpowD s Y-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) ≤
        (4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re+η) := by
  simpa only [sphereArea2_univ_real] using sphere2_riesz_sharp_asymptotic_unconditional hs hs2

end SphericalRiesz
end
end
