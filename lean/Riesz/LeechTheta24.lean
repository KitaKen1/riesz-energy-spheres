import Riesz.LeechDual24
import Riesz.E8ThetaTransform

/-! # The Leech theta function and its `S`-transformation (stage P24-1)

`Θ_Λ(τ) = Σ_{x ∈ Λ₂₄} exp(π i |x|² τ)` converges for `Im τ > 0` (the lattice sum of `|x|^(-26)`
converges). By Poisson summation on the self-dual lattice of covolume one and the Gaussian
Fourier transform in dimension `24`, `Θ_Λ(-1/τ) = τ^12 Θ_Λ(τ)`; evenness gives
`Θ_Λ(τ + 1) = Θ_Λ(τ)`. The radial Schwartz profile of the `E8` development is reused: it is a
function of one real variable and does not depend on the dimension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology FourierTransform RealInnerProductSpace SchwartzMap
namespace SphericalRiesz

theorem leechLattice_summable_norm_rpow :
    Summable (fun x : leechLattice => ‖x‖ ^ (-26 : ℝ)) :=
  ZLattice.summable_norm_rpow leechLattice (-26) (by rw [leechLattice_rank]; norm_num)

def leechLatticeThetaTerm (τ : ℂ) (x : leechLattice) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖(x : LeechAmbient)‖^2 : ℝ)*τ)

theorem leechLatticeThetaTerm_norm (τ : ℂ) (x : leechLattice) :
    ‖leechLatticeThetaTerm τ x‖ = Real.exp (-Real.pi*‖(x : LeechAmbient)‖^2*τ.im) := by
  unfold leechLatticeThetaTerm
  rw [Complex.norm_exp]
  congr 1
  have he : (Real.pi : ℂ)*Complex.I*(‖(x : LeechAmbient)‖^2 : ℝ)*τ =
      ((Real.pi*‖(x : LeechAmbient)‖^2 : ℝ) : ℂ)*(τ*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.re_ofReal_mul, Complex.mul_I_re]
  ring

theorem leechLatticeThetaTerm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (leechLatticeThetaTerm τ) := by
  have hdecay : (fun t : ℝ => Real.exp (-Real.pi*τ.im*t^2)) =o[atTop]
      (fun t : ℝ => t^(-26 : ℝ)) := by
    have ha : -Real.pi*τ.im < 0 := by nlinarith [Real.pi_pos]
    simpa only [zero_mul, add_zero] using
      rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-26)
  obtain ⟨C, hC, hbound⟩ := hdecay.isBigO.exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound.bound
  have hfinite := leechLattice_finite_norm_lt R
  have hevent : ∀ᶠ x : leechLattice in cofinite,
      ‖leechLatticeThetaTerm τ x‖ ≤ C*‖x‖^(-26 : ℝ) := by
    apply eventually_cofinite.mpr
    apply hfinite.subset
    intro x hx
    by_contra hsmall
    have hlarge : R ≤ ‖(x : LeechAmbient)‖ := le_of_not_gt hsmall
    have h := hR ‖(x : LeechAmbient)‖ hlarge
    have hb : Real.exp (-Real.pi*τ.im*‖(x : LeechAmbient)‖^2) ≤
        C*‖(x : LeechAmbient)‖^(-26 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using h
    apply hx
    simpa only [leechLatticeThetaTerm_norm, Submodule.norm_coe,
      mul_assoc, mul_left_comm, mul_comm] using hb
  apply Summable.of_norm_bounded_eventually (leechLattice_summable_norm_rpow.mul_left C)
  filter_upwards [hevent] with x hx
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos hC,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx

/-- The theta function of the Leech lattice. -/
def leechTheta (τ : ℂ) : ℂ := ∑' x : leechLattice, leechLatticeThetaTerm τ x

theorem leechTheta_add_one (τ : ℂ) : leechTheta (τ+1) = leechTheta τ := by
  unfold leechTheta
  refine tsum_congr fun x => ?_
  obtain ⟨k, hk⟩ := leechLattice_even x
  unfold leechLatticeThetaTerm
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k, ?_⟩
  rw [hk]
  push_cast
  ring

def leechThetaKernel (τ : ℂ) (x : LeechAmbient) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖x‖^2 : ℝ)*τ)

theorem leechThetaKernel_lattice (τ : ℂ) (x : leechLattice) :
    leechThetaKernel τ x = leechLatticeThetaTerm τ x := rfl

theorem leechThetaKernel_gaussian (τ : ℂ) : leechThetaKernel τ =
    fun x : LeechAmbient => Complex.exp
      (-((Real.pi : ℂ)*(-Complex.I*τ))*(‖x‖ : ℂ)^2) := by
  funext x
  unfold leechThetaKernel
  congr 1
  push_cast
  ring

theorem leechThetaKernel_fourier_S {τ : ℂ} (hτ : 0 < τ.im) (w : LeechAmbient) :
    𝓕 (leechThetaKernel (-1/τ)) w = τ^12 * leechThetaKernel τ w := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simp [h] at hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let b : ℂ := (Real.pi : ℂ)*(-Complex.I*(-1/τ))
  have hb : 0 < b.re := by
    simpa [b] using mul_pos Real.pi_pos hS
  have hπ : (Real.pi : ℂ)/b = τ/Complex.I := by
    dsimp [b]
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
  have hI12 : Complex.I^12 = 1 := by
    rw [show (12:ℕ) = 4*3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  have hc : ((Real.pi : ℂ)/b)^((Module.finrank ℝ LeechAmbient : ℂ)/2) = τ^12 := by
    rw [hπ, finrank_euclideanSpace_fin]
    have h12 : ((24:ℕ):ℂ)/2 = ((12:ℕ):ℂ) := by norm_num
    rw [h12, Complex.cpow_natCast, div_pow, hI12, div_one]
  have he : -(Real.pi : ℂ)^2*(‖w‖ : ℂ)^2/b =
      (Real.pi : ℂ)*Complex.I*(‖w‖^2 : ℝ)*τ := by
    dsimp [b]
    push_cast
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  rw [leechThetaKernel_gaussian]
  change 𝓕 (fun x : LeechAmbient => Complex.exp (-b*(‖x‖ : ℂ)^2)) w = _
  rw [fourier_gaussian_innerProductSpace hb w, hc, he]
  rfl

noncomputable def leechThetaSchwartzKernel (τ : ℂ) (hτ : 0 < τ.im) : 𝓢(LeechAmbient, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg (F := LeechAmbient)
    (e8ThetaProfile τ) (e8ThetaProfile_contDiff τ) (e8ThetaProfile_decay (τ := τ) hτ)

theorem leechThetaSchwartzKernel_apply (τ : ℂ) (hτ : 0 < τ.im) (x : LeechAmbient) :
    leechThetaSchwartzKernel τ hτ x =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  simp [leechThetaSchwartzKernel, e8ThetaProfile, mul_assoc, mul_comm]

theorem leechThetaSchwartzKernel_eq (τ : ℂ) (hτ : 0 < τ.im) :
    (fun x : LeechAmbient => leechThetaSchwartzKernel τ hτ x) = leechThetaKernel τ := by
  funext x
  rw [leechThetaSchwartzKernel_apply]
  unfold leechThetaKernel
  congr 1
  ring

/-- The `S`-transformation of the Leech theta function (weight `12`). -/
theorem leechTheta_transform_S {τ : ℂ} (hτ : 0 < τ.im) :
    leechTheta (-1/τ) = τ^12 * leechTheta τ := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simp [h] at hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let f := leechThetaSchwartzKernel (-1/τ) hS
  have hp := SchwartzMap.poissonSummation_lattice (L := leechLattice) f 0
  have hd : SchwartzMap.dualLattice leechLattice = leechLattice := leechLattice_selfDual
  rw [hd] at hp
  have hf : (fun x : LeechAmbient => f x) = leechThetaKernel (-1/τ) :=
    leechThetaSchwartzKernel_eq (-1/τ) hS
  have hp' : (∑' x : leechLattice, leechThetaKernel (-1/τ) x) =
      ∑' x : leechLattice, 𝓕 (leechThetaKernel (-1/τ)) x := by
    simpa [leechLattice_covolume, hf] using hp
  unfold leechTheta
  change (∑' x : leechLattice, leechThetaKernel (-1/τ) x) =
    τ^12 * ∑' x : leechLattice, leechThetaKernel τ x
  rw [hp']
  simp_rw [leechThetaKernel_fourier_S hτ]
  exact tsum_mul_left

#print axioms leechLattice_summable_norm_rpow
#print axioms leechLatticeThetaTerm_norm
#print axioms leechLatticeThetaTerm_summable
#print axioms leechTheta_add_one
#print axioms leechThetaKernel_gaussian
#print axioms leechThetaKernel_fourier_S
#print axioms leechThetaSchwartzKernel_apply
#print axioms leechThetaSchwartzKernel_eq
#print axioms leechTheta_transform_S

end SphericalRiesz
