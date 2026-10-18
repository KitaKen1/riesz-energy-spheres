import E8Leech.LeechCuspParts
import E8Leech.CKMRVContourCauchy

/-!
# The integrands of the contour identity in dimension 24

For `τ = iy`, `E(z) = e^{πiρz}` and the cusp parts `P_{±1}` of `LeechCuspParts` (with `A, B` the
coefficients of the growing part of `𝒦⁽²⁴⁾(iy, ·)`):

* `leechHatF = 𝒦̂ E`, the integrand on the imaginary axis;
* `leechPlusF = (𝒦̂ − P₁) E` on the closed triangle `(0, 1, ∞)` and
  `leechMinusF = (𝒦̂ − P₋₁) E` on `(−1, 0, ∞)`;
* `leechFPlus`, `leechFMinus`: these minus the principal parts at the poles `Sτ ± 1`.

This file contains the definitions, the bounds at `i∞` (for `ρ > 2`) and the algebra of the final
assembly.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-- `𝒦̂⁽²⁴⁾(iy, ·) E`. -/
def leechHatF (y ρ : ℝ) (z : ℂ) : ℂ := rightC ckmrvLeechHatKernel (imagPt y) z * gaussE ρ z

/-- `(𝒦̂⁽²⁴⁾(iy, ·) − P₁) E`. -/
def leechPlusF (y ρ : ℝ) (z : ℂ) : ℂ :=
  (rightC ckmrvLeechHatKernel (imagPt y) z -
    cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z) * gaussE ρ z

/-- `(𝒦̂⁽²⁴⁾(iy, ·) − P₋₁) E`. -/
def leechMinusF (y ρ : ℝ) (z : ℂ) : ℂ :=
  (rightC ckmrvLeechHatKernel (imagPt y) z -
    cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z) * gaussE ρ z

/-- `c₊`, the residue of `𝒦̂ E` at `σ + 1`. -/
def leechCPlus (y ρ : ℝ) : ℂ := sigmaC y ^ 12 / (2 * (π : ℂ)) * gaussE ρ (sigmaC y + 1)

/-- `c₋`, the residue of `𝒦̂ E` at `σ − 1`. -/
def leechCMinus (y ρ : ℝ) : ℂ := -(sigmaC y ^ 12 / (2 * (π : ℂ))) * gaussE ρ (sigmaC y - 1)

/-- `F₊ = (𝒦̂ − P₁) E − c₊ k₊`. -/
def leechFPlus (y ρ : ℝ) (z : ℂ) : ℂ :=
  leechPlusF y ρ z - leechCPlus y ρ * principalK (sigmaC y + 1) z

/-- `F₋ = (𝒦̂ − P₋₁) E − c₋ k₋`. -/
def leechFMinus (y ρ : ℝ) (z : ℂ) : ℂ :=
  leechMinusF y ρ z - leechCMinus y ρ * principalK (sigmaC y - 1) z

theorem leechPlusF_eq (y ρ : ℝ) (z : ℂ) :
    leechPlusF y ρ z = leechHatF y ρ z -
      cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z * gaussE ρ z := by
  simp only [leechPlusF, leechHatF]
  ring

theorem leechMinusF_eq (y ρ : ℝ) (z : ℂ) :
    leechMinusF y ρ z = leechHatF y ρ z -
      cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z * gaussE ρ z := by
  simp only [leechMinusF, leechHatF]
  ring

/-! ## The algebra of the assembly -/

theorem leech_contour_algebra
    {LHS T1 T2 T3 F0 P0 P1 M0 M1 SG SH Kp Km Jp Jm cp cm eP eM C₀ Y A B Z1 Zm1 : ℂ}
    (e1 : LHS = 2 * T1 - T2 - T3) (e2 : 2 * T1 = 2 * F0 - eM * P1 - eP * M1)
    (e3 : T2 = I * eM * SG + eM * cp * Jm) (e4 : T3 = -(I * eP * SH) + eP * cm * Jp)
    (e5 : SG = I * P1 - I * P0) (e6 : SH = I * M0 - I * M1)
    (e7 : F0 = P0 + cp * Kp + Z1) (e8 : F0 = M0 + cm * Km + Zm1)
    (e9 : Kp - Km = -4 * A) (e10 : Jp - Jm = -4 * B)
    (e11 : eM * cp = C₀) (e11' : eP * cm = -C₀) (e13 : A + B = π / 2) (e14 : C₀ * (2 * π) = Y) :
    LHS + Y - (eM * Z1 + eP * Zm1) = (2 - eP - eM) * F0 := by
  linear_combination e1 + e2 - e3 - e4 - I * eM * e5 + I * eP * e6 +
    (eP * (M0 - M1) - eM * (P1 - P0)) * Complex.I_sq + (Kp - Jm) * e11 + (Km - Jp) * e11' +
    eM * e7 + eP * e8 + C₀ * e9 + C₀ * e10 - 4 * C₀ * e13 - e14

/-! ## Bounds at `i∞` -/

theorem norm_leechHatF (y ρ : ℝ) (z : ℂ) :
    ‖leechHatF y ρ z‖ =
      ‖rightC ckmrvLeechHatKernel (imagPt y) z‖ * Real.exp (-(π * ρ) * z.im) := by
  rw [leechHatF, norm_mul, norm_gaussE]

/-- For `ρ > 2`, `𝒦̂ E = O((1 + Im z)⁻²)` at `i∞` in the strip `|Re z| ≤ 1`. -/
theorem exists_bound_leechHatF_top (y : ℝ) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ M V : ℝ, ∀ z : ℂ, 0 < z.im → |z.re| ≤ 1 → V ≤ z.im →
      ‖leechHatF y ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_leechHatKernel_top y (R := 1) zero_le_one
  obtain ⟨K, hK, hKb⟩ := exists_pow_three_mul_exp_le (c := π * (ρ - 2))
    (mul_pos Real.pi_pos (by linarith))
  refine ⟨C * K, V, fun z hz hre hV => ?_⟩
  have hk := hb ⟨z, hz⟩ hV hre
  have e : rightC ckmrvLeechHatKernel (imagPt y) z = ckmrvLeechHatKernel (imagPt y) ⟨z, hz⟩ := by
    simp only [rightC]
    rw [ofComplex_apply_of_im_pos hz]
  have hk' : ‖ckmrvLeechHatKernel (imagPt y) ⟨z, hz⟩‖ ≤
      C * (1 + z.im) * Real.exp (2 * π * z.im) := hk
  rw [norm_leechHatF, e]
  have hv := hKb z.im hz.le
  have hpos : 0 < (1 + z.im) ^ 2 := by positivity
  have hexp : Real.exp (2 * π * z.im) * Real.exp (-(π * ρ) * z.im) =
      Real.exp (-(π * (ρ - 2) * z.im)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [le_div_iff₀ hpos]
  calc ‖ckmrvLeechHatKernel (imagPt y) ⟨z, hz⟩‖ * Real.exp (-(π * ρ) * z.im) * (1 + z.im) ^ 2
      ≤ C * (1 + z.im) * Real.exp (2 * π * z.im) * Real.exp (-(π * ρ) * z.im) *
          (1 + z.im) ^ 2 := by gcongr
    _ = C * ((1 + z.im) ^ 3 * (Real.exp (2 * π * z.im) * Real.exp (-(π * ρ) * z.im))) := by ring
    _ ≤ C * K := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_left hv hC

/-- `P₁ E = O((1 + Im z)⁻²)` at `i∞` in the strip `0 ≤ Re z ≤ 1`. -/
theorem exists_bound_cuspPartPlus_top (A B : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M : ℝ, ∀ z : ℂ, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
      ‖cuspPartPlus A B z * gaussE ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := exists_pow_twelve_mul_exp_le (c := π * ρ) (mul_pos Real.pi_pos hρ)
  refine ⟨Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) * K, fun z hz h0 h1 => ?_⟩
  have hv : 0 ≤ z.im := by linarith
  have hb := norm_cuspPartPlus_le_top A B hz h0 h1
  have hk := hKb z.im hv
  have hpos : 0 < (1 + z.im) ^ 2 := by positivity
  have hM : 0 ≤ Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) := by positivity
  have hexp : Real.exp (-(π * ρ) * z.im) = Real.exp (-(π * ρ * z.im)) := by ring_nf
  rw [norm_mul, norm_gaussE, le_div_iff₀ hpos, hexp]
  calc ‖cuspPartPlus A B z‖ * Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2
      ≤ (1 + z.im) ^ 10 * (Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖)) *
          Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2 := by gcongr
    _ = Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) *
          ((1 + z.im) ^ 12 * Real.exp (-(π * ρ * z.im))) := by ring
    _ ≤ Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) * K := mul_le_mul_of_nonneg_left hk hM

/-- `P₋₁ E = O((1 + Im z)⁻²)` at `i∞` in the strip `−1 ≤ Re z ≤ 0`. -/
theorem exists_bound_cuspPartMinus_top (A B : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M : ℝ, ∀ z : ℂ, 1 ≤ z.im → -1 ≤ z.re → z.re ≤ 0 →
      ‖cuspPartMinus A B z * gaussE ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := exists_pow_twelve_mul_exp_le (c := π * ρ) (mul_pos Real.pi_pos hρ)
  refine ⟨Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) * K, fun z hz h0 h1 => ?_⟩
  have hv : 0 ≤ z.im := by linarith
  have hb := norm_cuspPartMinus_le_top A B hz h0 h1
  have hk := hKb z.im hv
  have hpos : 0 < (1 + z.im) ^ 2 := by positivity
  have hM : 0 ≤ Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) := by positivity
  have hexp : Real.exp (-(π * ρ) * z.im) = Real.exp (-(π * ρ * z.im)) := by ring_nf
  rw [norm_mul, norm_gaussE, le_div_iff₀ hpos, hexp]
  calc ‖cuspPartMinus A B z‖ * Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2
      ≤ (1 + z.im) ^ 10 * (Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖)) *
          Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2 := by gcongr
    _ = Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) *
          ((1 + z.im) ^ 12 * Real.exp (-(π * ρ * z.im))) := by ring
    _ ≤ Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖) * K := mul_le_mul_of_nonneg_left hk hM

end E8Leech
