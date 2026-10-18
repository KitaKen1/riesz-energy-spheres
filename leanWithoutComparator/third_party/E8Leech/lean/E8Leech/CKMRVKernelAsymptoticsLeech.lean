import E8Leech.CKMRVGrowthLeechPlus

/-!
# CKMRV (4.38) for the Leech kernels

For fixed `τ`, as `Im z → ∞`,
`K₋⁽²⁴⁾(τ, z) = G₋(τ, z) + O(|z| e^{-π Im z})` and `K₊⁽²⁴⁾(τ, z) = G₊(τ, z) + O(|z|² e^{-π Im z})`,
where `G±` is a combination of `e^{2πikz} z^j` with `k ∈ {-1, 0}` and `j ∈ {0, 1}` (CKMRV (4.38)).

Write `Δ(z) = s² P(z)` with `s = e^{πiz}` and `P = 1 - 24 s² + O(s³)`, and
`D(z) = Δ(z) j(τ) - E₄(z)³ → -1`. Then
`K₋ = (2·1728π)⁻¹ (D Δ)⁻¹ (ℓ(z) N_ℓ(z) + N₀(z))` with `ℓ = πiz + 4 log 2`, and
`K₊ = (1728 c₊)⁻¹ s⁻² (z² M₂ + z M₁ + M₀)`. The functions `N_ℓ, N₀` and `M_k` have
second-order expansions in `s` (`HasExp3`) whose `s`-coefficients vanish, and `M₂ = O(|s|³)`:
these are the cancellations of the `e^{-πiz}` and `z² e^{-2πiz}`, `z²` terms.
The kernel identities are checked by `linear_combination` certificates computed by polynomial
division (`research/leech438_check.py` in the session notes).
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## `Δ = s² P` and the weights `s⁻²` -/

/-- `P = Δ / s² = (U J₂⁴ W)² / 256`, where `V = s J₂⁴`. -/
def discriminantCuspQuot (z : ℍ) : ℂ :=
  (thetaU z * jacobiTheta₂ ((z : ℂ) / 2) z ^ 4 * thetaW z) ^ 2 / 256

theorem discriminant_eq_cuspS_sq_mul (z : ℍ) :
    ModularForm.discriminant z = cuspS z ^ 2 * discriminantCuspQuot z := by
  have h := thetaProductSq_eq_discriminant z
  rw [thetaProductSq, thetaV_eq_cuspS_mul] at h
  rw [discriminantCuspQuot]
  linear_combination (-1 / 256 : ℂ) * h

theorem hasExp3_discriminantCuspQuot : HasExp3 discriminantCuspQuot 1 0 (-24) :=
  ((((hasExp3_thetaU.mul (hasExp3_jacobiTheta₂_half.pow.pow)).mul hasExp3_thetaW).pow).const_mul
    (1 / 256 : ℂ)).congr_fun (fun z => by rw [discriminantCuspQuot]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem norm_cuspS_sq_inv (z : ℍ) : ‖(cuspS z ^ 2)⁻¹‖ = Real.exp (2 * π * z.im) := by
  rw [norm_inv, norm_pow, norm_cuspS, ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  push_cast
  ring

theorem isBigO_cuspS_sq_inv :
    (fun z : ℍ => (cuspS z ^ 2)⁻¹) =O[atImInfty] fun z : ℍ => Real.exp (2 * π * z.im) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [norm_cuspS_sq_inv, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul])

/-- `s⁻² · O(w |s|³) = O(w e^{-π Im z})`. -/
theorem isBigO_cuspS_sq_inv_mul {f : ℍ → ℂ} {w : ℍ → ℝ}
    (hf : f =O[atImInfty] fun z : ℍ => w z * ‖cuspS z‖ ^ 3) :
    (fun z => (cuspS z ^ 2)⁻¹ * f z) =O[atImInfty] fun z : ℍ => w z * Real.exp (-π * z.im) :=
  (isBigO_cuspS_sq_inv.mul hf).congr_right fun z => by
    rw [norm_cuspS, mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring

theorem isBigO_le_norm_sq_mul (r : ℍ → ℝ) :
    r =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * r z :=
  ((isBigO_one_real_norm_coe.trans isBigO_norm_coe_sq).mul (isBigO_refl r atImInfty)).congr_left
    fun _ => one_mul _

/-! ## Expansions of the `z`-side factors -/

theorem hasExp3_eisensteinFourteen :
    HasExp3 (fun z : ℍ => ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) 1 0 (-24) :=
  (hasExp3_eisensteinFour.pow.mul hasExp3_eisensteinSix).congr_coeff (by norm_num) (by norm_num)
    (by norm_num)

theorem hasExp3_eisensteinTen :
    HasExp3 (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z) 1 0 (-264) :=
  (hasExp3_eisensteinFour.mul hasExp3_eisensteinSix).congr_coeff (by norm_num) (by norm_num)
    (by norm_num)

theorem hasExp3_thetaU_sq_sub_thetaV_sq :
    HasExp3 (fun z : ℍ => thetaU z ^ 2 - thetaV z ^ 2) 1 16 (-144) :=
  (hasExp3_thetaU.pow.sub hasExp3_thetaV.pow).congr_coeff (by norm_num) (by norm_num)
    (by norm_num)

theorem hasExp3_eightMinusDenZ (τ : ℍ) :
    HasExp3 (fun z => eightMinusDenZ τ z) (-1) 0 (kleinModularJ τ - 720) :=
  ((hasExp3_discriminant.mul (HasExp3.const (kleinModularJ τ))).sub
    (hasExp3_eisensteinFour.pow.mul hasExp3_eisensteinFour)).congr_fun
    (fun z => by simp only [eightMinusDenZ]; ring) |>.congr_coeff (by ring) (by ring) (by ring)

/-- `(D P)⁻¹ = -1 + (696 - j(τ)) s² + O(|s|³)`. -/
theorem hasExp3_leechDenInv (τ : ℍ) :
    HasExp3 (fun z => (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹) (-1) 0
      (696 - kleinModularJ τ) :=
  (((hasExp3_eightMinusDenZ τ).mul hasExp3_discriminantCuspQuot).inv (by norm_num)).congr_coeff
    (by ring) (by ring) (by ring)

theorem hasExp3_discriminantCuspQuot_inv :
    HasExp3 (fun z => (discriminantCuspQuot z)⁻¹) 1 0 24 :=
  (hasExp3_discriminantCuspQuot.inv one_ne_zero).congr_coeff (by norm_num) (by norm_num)
    (by norm_num)

/-! ## The Leech minus kernel as `Im z → ∞` -/

/-- `α = a₁ - a₂`, the difference of the last two row constants. -/
def leechMinusAlpha (τ : ℍ) : ℂ :=
  ckmrvPsiBasis τ 1 * (ModularForm.E₄ τ * ModularForm.E₆ τ) -
    ckmrvPsiBasis τ 2 * ModularForm.E₄ τ ^ 2

def leechMinusBeta (τ : ℍ) : ℂ := 2 * leechMinusAlpha τ - 2 * 1728 * ModularForm.discriminant τ

def leechMinusGamma (τ : ℍ) : ℂ :=
  kleinModularJ τ * leechMinusAlpha τ + 1728 * (ckmrvPsiBasis τ 2 * ModularForm.E₄ τ ^ 2)

/-- `N_ℓ(z) = -3456 Δ(τ) E₁₄(z)`, the coefficient of `ℓ(z) = πiz + 4 log 2`. -/
def leechMinusNEll (τ z : ℍ) : ℂ :=
  -(2 * 1728) * ModularForm.discriminant τ * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z)

/-- `N₀(z)`, the part of the numerator without `ℓ(z)`. -/
def leechMinusNZero (τ z : ℍ) : ℂ :=
  -(2 * 1728) * ModularForm.discriminant τ *
      (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * (ckmrvL z - π * I * z - 4 * Real.log 2)) +
    thetaW z * eightMinusDenZ τ z * leechMinusBeta τ +
    ModularForm.discriminant z * thetaW z * leechMinusGamma τ -
    leechMinusAlpha τ * (ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2))

/-- The `s²`-coefficient of `N₀`. -/
def leechMinusNZeroC (τ : ℍ) : ℂ :=
  12 * (-(2 * 1728) * ModularForm.discriminant τ) + (kleinModularJ τ - 744) * leechMinusBeta τ +
    leechMinusGamma τ + 408 * leechMinusAlpha τ

theorem ckmrvLeechMinusKernel_eq_z (τ z : ℍ) :
    ckmrvLeechMinusKernel τ z = ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ *
      (ModularForm.discriminant z)⁻¹ * (ckmrvEll z * leechMinusNEll τ z + leechMinusNZero τ z) := by
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hu : ModularForm.discriminant z * (ModularForm.discriminant z)⁻¹ = 1 := mul_inv_cancel₀ hΔ
  have hJz : kleinModularJ z = ModularForm.E₄ z ^ 3 * (ModularForm.discriminant z)⁻¹ := by
    rw [kleinModularJ, div_eq_mul_inv]
  have hD : eightMinusDenZ τ z =
      ModularForm.discriminant z * kleinModularJ τ - ModularForm.E₄ z ^ 3 := rfl
  have hinv : (kleinModularJ τ - kleinModularJ z)⁻¹ =
      ModularForm.discriminant z * (eightMinusDenZ τ z)⁻¹ := by
    have h : kleinModularJ τ - kleinModularJ z =
        eightMinusDenZ τ z / ModularForm.discriminant z := by
      rw [eq_div_iff hΔ, hD, hJz]
      linear_combination (-(ModularForm.E₄ z ^ 3)) * hu
    rw [h, inv_div, div_eq_mul_inv]
  have h2 : ckmrvModularFactor z 2 =
      ModularForm.E₄ z ^ 2 * ModularForm.E₆ z / ModularForm.discriminant z := by
    rw [← eisensteinFourteen_eq_four_sq_mul_six]
    rfl
  have h1 : ckmrvModularFactor z 1 = 1 := rfl
  have h0 : ckmrvModularFactor z 0 =
      ModularForm.E₄ z * ModularForm.E₆ z / ModularForm.discriminant z := by
    rw [← eisensteinTen_eq_four_mul_six]
    rfl
  obtain ⟨e0, e1, e2⟩ := leechMinusTauCoeff_expand τ z
  rw [ckmrvLeechMinusKernel_eq_sum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, h2, h1, h0, e0, e1, e2, ckmrvTildePsiBasis,
    leechMinusNEll, leechMinusNZero, leechMinusBeta, leechMinusGamma, leechMinusAlpha, ckmrvEll]
  linear_combination
      (-3456*(kleinModularJ τ)*(thetaW z)*(ModularForm.discriminant τ)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) - 3*(kleinModularJ τ)*(thetaW z)*(ModularForm.E₄ τ)^2*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) + 3*(kleinModularJ τ)*(thetaW z)*(ModularForm.E₄ τ)*(ModularForm.E₆ τ)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹) + 3456*(kleinModularJ z)*(thetaW z)*(ModularForm.discriminant τ)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) + 2*(kleinModularJ z)*(thetaW z)*(ModularForm.E₄ τ)^2*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) - 2*(kleinModularJ z)*(thetaW z)*(ModularForm.E₄ τ)*(ModularForm.E₆ τ)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹) - 3456*(ckmrvL z)*(ModularForm.discriminant τ)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹)^2 + (thetaU z)^2*(ModularForm.E₄ τ)^2*(ModularForm.E₄ z)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹)^2 - (thetaU z)^2*(ModularForm.E₄ τ)*(ModularForm.E₄ z)*(ModularForm.E₆ τ)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹)^2 - (thetaV z)^2*(ModularForm.E₄ τ)^2*(ModularForm.E₄ z)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹)^2 + (thetaV z)^2*(ModularForm.E₄ τ)*(ModularForm.E₄ z)*(ModularForm.E₆ τ)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹)^2 + 1728*(thetaW z)*(ModularForm.E₄ τ)^2*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹)) * hinv +
      (3456*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.discriminant τ)*(ModularForm.discriminant z)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) + 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.discriminant z)*(ModularForm.E₄ τ)^2*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) - 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.discriminant z)*(ModularForm.E₄ τ)*(ModularForm.E₆ τ)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹)) * hJz +
      (3456*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.discriminant τ)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) + 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.E₄ τ)^2*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) - 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.E₄ τ)*(ModularForm.E₆ τ)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹)) * hD +
      (-3456*((eightMinusDenZ τ z)⁻¹)*(ckmrvL z)*(ModularForm.discriminant τ)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) + ((eightMinusDenZ τ z)⁻¹)*(thetaU z)^2*(ModularForm.E₄ τ)^2*(ModularForm.E₄ z)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) - ((eightMinusDenZ τ z)⁻¹)*(thetaU z)^2*(ModularForm.E₄ τ)*(ModularForm.E₄ z)*(ModularForm.E₆ τ)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹) - ((eightMinusDenZ τ z)⁻¹)*(thetaV z)^2*(ModularForm.E₄ τ)^2*(ModularForm.E₄ z)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) + ((eightMinusDenZ τ z)⁻¹)*(thetaV z)^2*(ModularForm.E₄ τ)*(ModularForm.E₄ z)*(ModularForm.E₆ τ)*(ModularForm.E₆ z)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹) + 3456*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.discriminant τ)*(ModularForm.E₄ z)^3*(ckmrvMinusScale⁻¹)*((ModularForm.discriminant z)⁻¹) + 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.E₄ τ)^2*(ModularForm.E₄ z)^3*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 2)*((ModularForm.discriminant z)⁻¹) - 2*((eightMinusDenZ τ z)⁻¹)*(thetaW z)*(ModularForm.E₄ τ)*(ModularForm.E₄ z)^3*(ModularForm.E₆ τ)*(ckmrvMinusScale⁻¹)*(ckmrvPsiBasis τ 1)*((ModularForm.discriminant z)⁻¹)) * hu

theorem hasExp3_leechMinusNEll_div (τ : ℍ) :
    HasExp3 (fun z => leechMinusNEll τ z * (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹)
      (2 * 1728 * ModularForm.discriminant τ) 0
      (-(2 * 1728) * ModularForm.discriminant τ * (720 - kleinModularJ τ)) :=
  ((hasExp3_eisensteinFourteen.const_mul (-(2 * 1728) * ModularForm.discriminant τ)).mul
    (hasExp3_leechDenInv τ)).congr_fun (fun z => rfl) |>.congr_coeff (by ring) (by ring) (by ring)

theorem hasExp3_leechMinusNZero (τ : ℍ) :
    HasExp3 (fun z => leechMinusNZero τ z) (-leechMinusBeta τ - leechMinusAlpha τ) 0
      (leechMinusNZeroC τ) :=
  (((((hasExp3_eisensteinFourteen.mul hasExp3_ckmrvL_sub).const_mul
      (-(2 * 1728) * ModularForm.discriminant τ)).add
    ((hasExp3_thetaW.mul (hasExp3_eightMinusDenZ τ)).mul (HasExp3.const (leechMinusBeta τ)))).add
    ((hasExp3_discriminant.mul hasExp3_thetaW).mul (HasExp3.const (leechMinusGamma τ)))).sub
    ((hasExp3_eisensteinTen.mul hasExp3_thetaU_sq_sub_thetaV_sq).const_mul
      (leechMinusAlpha τ))).congr_fun (fun z => rfl)
    |>.congr_coeff (by ring) (by simp only [leechMinusBeta]; ring)
      (by simp only [leechMinusNZeroC]; ring)

theorem hasExp3_leechMinusNZero_div (τ : ℍ) :
    HasExp3 (fun z => leechMinusNZero τ z * (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹)
      (leechMinusBeta τ + leechMinusAlpha τ) 0
      ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) - leechMinusNZeroC τ) :=
  ((hasExp3_leechMinusNZero τ).mul (hasExp3_leechDenInv τ)).congr_coeff (by ring) (by ring)
    (by ring)

/-- The cusp term `G₋^{(24)}(τ, z)` (CKMRV (4.38)): `e^{-2πiz}` times a linear function of `z`,
plus a linear function of `z`. -/
def ckmrvLeechMinusG (τ z : ℍ) : ℂ :=
  ckmrvMinusScale⁻¹ *
    ((cuspS z ^ 2)⁻¹ * (ckmrvEll z * (2 * 1728 * ModularForm.discriminant τ) +
        (leechMinusBeta τ + leechMinusAlpha τ)) +
      ckmrvEll z * (-(2 * 1728) * ModularForm.discriminant τ * (720 - kleinModularJ τ)) +
      ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) - leechMinusNZeroC τ))

/-- **CKMRV (4.38), Leech minus kernel.** For fixed `τ`,
`K₋(τ, z) - G₋(τ, z) = O(|z| e^{-π Im z})` as `Im z → ∞`. -/
theorem isBigO_ckmrvLeechMinusKernel_sub_G (τ : ℍ) :
    (fun z : ℍ => ckmrvLeechMinusKernel τ z - ckmrvLeechMinusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
  have hsum := (IsBigO.mul isBigO_ckmrvEll (hasExp3_leechMinusNEll_div τ)).add
    (IsBigO.trans (hasExp3_leechMinusNZero_div τ) (isBigO_le_norm_mul _))
  have h := (isBigO_cuspS_sq_inv_mul hsum).const_mul_left ckmrvMinusScale⁻¹
  refine h.congr_left fun z => ?_
  have hu : (ModularForm.discriminant z)⁻¹ = (cuspS z ^ 2)⁻¹ * (discriminantCuspQuot z)⁻¹ := by
    rw [discriminant_eq_cuspS_sq_mul, mul_inv]
  have hs : (cuspS z ^ 2)⁻¹ * cuspS z ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 (cuspS_ne_zero z))
  rw [ckmrvLeechMinusKernel_eq_z, ckmrvLeechMinusG, hu]
  linear_combination (-(ckmrvMinusScale⁻¹ *
    (ckmrvEll z * (-(2 * 1728) * ModularForm.discriminant τ * (720 - kleinModularJ τ)) +
      ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) -
        leechMinusNZeroC τ)))) * hs

/-! ## The Leech plus kernel as `Im z → ∞` -/

def leechPlusA0 (τ : ℍ) : ℂ := (τ : ℂ) * (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ)

def leechPlusA1 (τ : ℍ) : ℂ := ckmrvPhiBasis τ 1 * ModularForm.discriminant τ

def leechPlusA2 (τ : ℍ) : ℂ := ckmrvPhiBasis τ 2 * (ModularForm.E₄ τ * ModularForm.E₆ τ)

/-- The part of `c₀` without `(j(τ) - j(z))⁻¹`. -/
def leechPlusP0 (τ : ℍ) : ℂ :=
  6 * leechPlusA0 τ + (-12 * kleinModularJ τ + 5 * 1728) * leechPlusA1 τ + 6 * leechPlusA2 τ

/-- The part of `c₂` without `(j(τ) - j(z))⁻¹`. -/
def leechPlusP2 (τ : ℍ) : ℂ :=
  -6 * leechPlusA0 τ + (12 * kleinModularJ τ - 7 * 1728) * leechPlusA1 τ + -6 * leechPlusA2 τ

/-- The `Δ(z)⁻¹` part of the numerator. -/
def leechPlusAz (τ z : ℍ) : ℂ :=
  leechPlusP0 τ * ModularForm.E₄ z * (z : ℂ) ^ 2 + leechPlusP2 τ * ckmrvTildePhiBasis z 2

/-- The `(D Δ)(z)⁻¹` part of the numerator. -/
def leechPlusBz (τ z : ℍ) : ℂ :=
  1728 * leechPlusA2 τ * ModularForm.E₄ z * (z : ℂ) ^ 2 * ModularForm.discriminant z -
    2 * 1728 * leechPlusA1 τ * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) * ckmrvTildePhiBasis z 1 +
    1728 * leechPlusA0 τ * ckmrvTildePhiBasis z 2 * ModularForm.discriminant z

theorem ckmrvLeechPlusKernel_eq_z (τ z : ℍ) :
    ckmrvLeechPlusKernel τ z = (1728 * ckmrvPlusScale)⁻¹ *
      ((ModularForm.discriminant z)⁻¹ * leechPlusAz τ z +
        (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ * leechPlusBz τ z) := by
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hu : ModularForm.discriminant z * (ModularForm.discriminant z)⁻¹ = 1 := mul_inv_cancel₀ hΔ
  have hJz : kleinModularJ z = ModularForm.E₄ z ^ 3 * (ModularForm.discriminant z)⁻¹ := by
    rw [kleinModularJ, div_eq_mul_inv]
  have hinv : (kleinModularJ τ - kleinModularJ z)⁻¹ =
      ModularForm.discriminant z * (eightMinusDenZ τ z)⁻¹ := by
    have h : kleinModularJ τ - kleinModularJ z =
        eightMinusDenZ τ z / ModularForm.discriminant z := by
      rw [eq_div_iff hΔ, eightMinusDenZ, hJz]
      linear_combination (-(ModularForm.E₄ z ^ 3)) * hu
    rw [h, inv_div, div_eq_mul_inv]
  have h3 : ckmrvModularFactor z 3 = ModularForm.E₄ z := rfl
  have h2 : ckmrvModularFactor z 2 =
      ModularForm.E₄ z ^ 2 * ModularForm.E₆ z / ModularForm.discriminant z := by
    rw [← eisensteinFourteen_eq_four_sq_mul_six]
    rfl
  have h1 : ckmrvModularFactor z 1 = 1 := rfl
  obtain ⟨e0, e1, e2⟩ := leechPlusTauCoeff_expand τ z
  rw [ckmrvLeechPlusKernel_eq_sum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, h3, h2, h1, e0, e1, e2, ckmrvTildePhiBasis,
    leechPlusAz, leechPlusBz, leechPlusP0, leechPlusP2, leechPlusA0, leechPlusA1, leechPlusA2]
  linear_combination
      (12*(Complex.I)*(ModularForm.discriminant τ)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvPhiBasis τ 1)*((Real.pi : ℂ)⁻¹)*(ckmrvPlusScale⁻¹)*((ModularForm.discriminant z)⁻¹)^2*((z : ℂ)) - 12*(Complex.I)*(EisensteinSeries.E2 z)*(ModularForm.E₄ τ)^2*(ModularForm.E₆ τ)*((Real.pi : ℂ)⁻¹)*(ckmrvPlusScale⁻¹)*((τ : ℂ))*((ModularForm.discriminant z)⁻¹)*((z : ℂ)) - 2*(ModularForm.discriminant τ)*(EisensteinSeries.E2 z)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvPhiBasis τ 1)*(ckmrvPlusScale⁻¹)*((ModularForm.discriminant z)⁻¹)^2*((z : ℂ))^2 + (EisensteinSeries.E2 z)^2*(ModularForm.E₄ τ)^2*(ModularForm.E₆ τ)*(ckmrvPlusScale⁻¹)*((τ : ℂ))*((ModularForm.discriminant z)⁻¹)*((z : ℂ))^2 - 36*(ModularForm.E₄ τ)^2*(ModularForm.E₆ τ)*((Real.pi : ℂ)⁻¹)^2*(ckmrvPlusScale⁻¹)*((τ : ℂ))*((ModularForm.discriminant z)⁻¹) + (ModularForm.E₄ τ)*(ModularForm.E₄ z)*(ModularForm.E₆ τ)*(ckmrvPhiBasis τ 2)*(ckmrvPlusScale⁻¹)*((ModularForm.discriminant z)⁻¹)*((z : ℂ))^2) * hinv +
      (12*((eightMinusDenZ τ z)⁻¹)*(Complex.I)*(ModularForm.discriminant τ)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvPhiBasis τ 1)*((Real.pi : ℂ)⁻¹)*(ckmrvPlusScale⁻¹)*((ModularForm.discriminant z)⁻¹)*((z : ℂ)) - 2*((eightMinusDenZ τ z)⁻¹)*(ModularForm.discriminant τ)*(EisensteinSeries.E2 z)*(ModularForm.E₄ z)^2*(ModularForm.E₆ z)*(ckmrvPhiBasis τ 1)*(ckmrvPlusScale⁻¹)*((ModularForm.discriminant z)⁻¹)*((z : ℂ))^2) * hu

/-- The `z²`-coefficient `M₂ = P⁻¹ A₂ + (D P)⁻¹ B₂`. -/
def leechPlusM2 (τ z : ℍ) : ℂ :=
  (discriminantCuspQuot z)⁻¹ *
      (leechPlusP0 τ * ModularForm.E₄ z + leechPlusP2 τ * EisensteinSeries.E2 z ^ 2) +
    (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹ *
      (1728 * leechPlusA2 τ * (ModularForm.E₄ z * ModularForm.discriminant z) -
        2 * 1728 * leechPlusA1 τ *
          (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * EisensteinSeries.E2 z) +
        1728 * leechPlusA0 τ * (EisensteinSeries.E2 z ^ 2 * ModularForm.discriminant z))

/-- The `z`-coefficient `M₁`. -/
def leechPlusM1 (τ z : ℍ) : ℂ :=
  (discriminantCuspQuot z)⁻¹ *
      (leechPlusP2 τ * (-(12 * I / (π : ℂ))) * EisensteinSeries.E2 z) +
    (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹ *
      (2 * 1728 * leechPlusA1 τ * (6 * I / (π : ℂ)) *
          (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) -
        1728 * leechPlusA0 τ * (12 * I / (π : ℂ)) *
          (EisensteinSeries.E2 z * ModularForm.discriminant z))

/-- The constant coefficient `M₀`. -/
def leechPlusM0 (τ z : ℍ) : ℂ :=
  (discriminantCuspQuot z)⁻¹ * (leechPlusP2 τ * (-(36 / (π : ℂ) ^ 2))) +
    (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹ *
      (1728 * leechPlusA0 τ * (-(36 / (π : ℂ) ^ 2)) * ModularForm.discriminant z)

theorem ckmrvLeechPlusKernel_eq_M (τ z : ℍ) :
    ckmrvLeechPlusKernel τ z = (1728 * ckmrvPlusScale)⁻¹ *
      ((cuspS z ^ 2)⁻¹ * ((z : ℂ) ^ 2 * leechPlusM2 τ z + (z : ℂ) * leechPlusM1 τ z +
        leechPlusM0 τ z)) := by
  have hu : (ModularForm.discriminant z)⁻¹ = (cuspS z ^ 2)⁻¹ * (discriminantCuspQuot z)⁻¹ := by
    rw [discriminant_eq_cuspS_sq_mul, mul_inv]
  rw [ckmrvLeechPlusKernel_eq_z, hu]
  simp only [leechPlusAz, leechPlusBz, leechPlusM2, leechPlusM1, leechPlusM0, ckmrvTildePhiBasis,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

theorem hasExp3_leechPlusM2 (τ : ℍ) : HasExp3 (fun z => leechPlusM2 τ z) 0 0 0 :=
  ((hasExp3_discriminantCuspQuot_inv.mul ((hasExp3_eisensteinFour.const_mul (leechPlusP0 τ)).add
      (hasExp3_eisensteinTwo.pow.const_mul (leechPlusP2 τ)))).add
    ((hasExp3_leechDenInv τ).mul
      ((((hasExp3_eisensteinFour.mul hasExp3_discriminant).const_mul (1728 * leechPlusA2 τ)).sub
        ((hasExp3_eisensteinFourteen.mul hasExp3_eisensteinTwo).const_mul
          (2 * 1728 * leechPlusA1 τ))).add
        ((hasExp3_eisensteinTwo.pow.mul hasExp3_discriminant).const_mul
          (1728 * leechPlusA0 τ))))).congr_fun (fun z => rfl)
    |>.congr_coeff (by simp only [leechPlusP0, leechPlusP2]; ring) (by ring)
      (by simp only [leechPlusP0, leechPlusP2]; ring)

def leechPlusM1a (τ : ℍ) : ℂ :=
  leechPlusP2 τ * (-(12 * I / (π : ℂ))) - 2 * 1728 * leechPlusA1 τ * (6 * I / (π : ℂ))

def leechPlusM1c (τ : ℍ) : ℂ :=
  2 * 1728 * leechPlusA1 τ * (6 * I / (π : ℂ)) * (24 + (696 - kleinModularJ τ)) +
    1728 * leechPlusA0 τ * (12 * I / (π : ℂ))

theorem hasExp3_leechPlusM1 (τ : ℍ) :
    HasExp3 (fun z => leechPlusM1 τ z) (leechPlusM1a τ) 0 (leechPlusM1c τ) :=
  ((hasExp3_discriminantCuspQuot_inv.mul
      (hasExp3_eisensteinTwo.const_mul (leechPlusP2 τ * (-(12 * I / (π : ℂ)))))).add
    ((hasExp3_leechDenInv τ).mul
      ((hasExp3_eisensteinFourteen.const_mul
          (2 * 1728 * leechPlusA1 τ * (6 * I / (π : ℂ)))).sub
        ((hasExp3_eisensteinTwo.mul hasExp3_discriminant).const_mul
          (1728 * leechPlusA0 τ * (12 * I / (π : ℂ))))))).congr_fun (fun z => rfl)
    |>.congr_coeff (by simp only [leechPlusM1a]; ring) (by ring) (by simp only [leechPlusM1c]; ring)

def leechPlusM0a (τ : ℍ) : ℂ := leechPlusP2 τ * (-(36 / (π : ℂ) ^ 2))

def leechPlusM0c (τ : ℍ) : ℂ :=
  24 * (leechPlusP2 τ * (-(36 / (π : ℂ) ^ 2))) -
    1728 * leechPlusA0 τ * (-(36 / (π : ℂ) ^ 2))

theorem hasExp3_leechPlusM0 (τ : ℍ) :
    HasExp3 (fun z => leechPlusM0 τ z) (leechPlusM0a τ) 0 (leechPlusM0c τ) :=
  ((hasExp3_discriminantCuspQuot_inv.mul (HasExp3.const (leechPlusP2 τ * (-(36 / (π : ℂ) ^ 2))))).add
    ((hasExp3_leechDenInv τ).mul (hasExp3_discriminant.const_mul
      (1728 * leechPlusA0 τ * (-(36 / (π : ℂ) ^ 2)))))).congr_fun (fun z => rfl)
    |>.congr_coeff (by simp only [leechPlusM0a]; ring) (by ring) (by simp only [leechPlusM0c]; ring)

/-- The cusp term `G₊^{(24)}(τ, z)` (CKMRV (4.38)). -/
def ckmrvLeechPlusG (τ z : ℍ) : ℂ :=
  (1728 * ckmrvPlusScale)⁻¹ *
    ((cuspS z ^ 2)⁻¹ * ((z : ℂ) * leechPlusM1a τ + leechPlusM0a τ) +
      (z : ℂ) * leechPlusM1c τ + leechPlusM0c τ)

/-- **CKMRV (4.38), Leech plus kernel.** For fixed `τ`,
`K₊(τ, z) - G₊(τ, z) = O(|z|² e^{-π Im z})` as `Im z → ∞`. -/
theorem isBigO_ckmrvLeechPlusKernel_sub_G (τ : ℍ) :
    (fun z : ℍ => ckmrvLeechPlusKernel τ z - ckmrvLeechPlusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-π * z.im) := by
  have hsum := ((IsBigO.mul isBigO_coe_sq (hasExp3_leechPlusM2 τ)).add
    (IsBigO.mul (isBigO_coe_norm.trans isBigO_norm_coe_sq) (hasExp3_leechPlusM1 τ))).add
    (IsBigO.trans (hasExp3_leechPlusM0 τ) (isBigO_le_norm_sq_mul _))
  have h := (isBigO_cuspS_sq_inv_mul hsum).const_mul_left (1728 * ckmrvPlusScale)⁻¹
  refine h.congr_left fun z => ?_
  have hs : (cuspS z ^ 2)⁻¹ * cuspS z ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 (cuspS_ne_zero z))
  rw [ckmrvLeechPlusKernel_eq_M, ckmrvLeechPlusG]
  linear_combination (-((1728 * ckmrvPlusScale)⁻¹ *
    ((z : ℂ) * leechPlusM1c τ + leechPlusM0c τ))) * hs

end E8Leech
