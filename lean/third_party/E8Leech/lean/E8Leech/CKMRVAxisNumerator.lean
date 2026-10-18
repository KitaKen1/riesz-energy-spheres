import E8Leech.E8UnitCostFinal
import E8Leech.CKMRVKernelReal
import SpherePacking.ModularForms.Lv1Lv2Identities

/-!
# The `d = 8` kernels on the imaginary axes as explicit real expressions

For `τ = iu`, `z = it` every building block of `K±⁽⁸⁾` is real, and `E₄, E₆, Δ` are polynomials in
`V = θ₂⁴`, `W = θ₄⁴` (`U = V + W`):
`E₄ = V² + VW + W²`, `E₆ = (V + 2W)(2V + W)(W − V)/2`, `Δ = (UVW)²/256`.
So `2 𝒦̂(iu, it) · Δ(iu)Δ(it)(j(iu) − j(it))` is an explicit real polynomial `axPhi` in
`E₂, V, W, L, L_S` at `iu`, `E₂, V, W, L` at `it`, and `u, t, π, 1/π, 1/t`, while
`Δ(iu)Δ(it)(j(iu) − j(it)) = axNu` is a polynomial in `V, W` at both points.

This is the starting point of the proof of the CKMRV inequality (6.4)(1):
off the singular curves `𝒦̂(iu, it) > 0` is the sign condition `axPhi · axNu > 0`.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

/-! ## `E₄`, `E₆`, `Δ` in theta form -/

theorem H₂_eq_thetaV (τ : ℍ) : H₂ τ = thetaV τ := by
  rw [H₂, Θ₂_as_jacobiTheta₂]
  rfl

theorem H₄_eq_thetaW (τ : ℍ) : H₄ τ = thetaW τ := by
  rw [H₄, Θ₄_as_jacobiTheta₂]
  rfl

theorem E4_eq_thetaVW (τ : ℍ) :
    ModularForm.E₄ τ = thetaV τ ^ 2 + thetaV τ * thetaW τ + thetaW τ ^ 2 := by
  have h := congrFun SpherePacking.ModularForms.E₄_eq_thetaE4 τ
  simp only [SpherePacking.ModularForms.thetaE4, Pi.add_apply, Pi.pow_apply, Pi.mul_apply,
    H₂_eq_thetaV, H₄_eq_thetaW] at h
  exact h

theorem E6_eq_thetaVW (τ : ℍ) :
    ModularForm.E₆ τ =
      (thetaV τ + 2 * thetaW τ) * (2 * thetaV τ + thetaW τ) * (thetaW τ - thetaV τ) / 2 := by
  have h := congrFun SpherePacking.ModularForms.E₆_eq_thetaE6 τ
  simp only [SpherePacking.ModularForms.thetaE6, Pi.smul_apply, Pi.add_apply, Pi.mul_apply,
    Pi.sub_apply, smul_eq_mul, H₂_eq_thetaV, H₄_eq_thetaW] at h
  have h' : ModularForm.E₆ τ = 1 / 2 * ((thetaV τ + 2 * thetaW τ) *
      ((2 * thetaV τ + thetaW τ) * (thetaW τ - thetaV τ))) := h
  rw [h']
  ring

theorem discriminant_eq_thetaUVW (τ : ℍ) :
    ModularForm.discriminant τ = (thetaU τ * thetaV τ * thetaW τ) ^ 2 / 256 := by
  have h := thetaProductSq_eq_discriminant τ
  rw [thetaProductSq] at h
  rw [h]
  ring

/-! ## The real polynomial model -/

/-- `E₄ = V² + VW + W²`. -/
def axE4 (V W : ℝ) : ℝ := V ^ 2 + V * W + W ^ 2

/-- `E₆ = (V + 2W)(2V + W)(W − V)/2`. -/
def axE6 (V W : ℝ) : ℝ := (V + 2 * W) * (2 * V + W) * (W - V) / 2

/-- `Δ = (UVW)²/256` with `U = V + W`. -/
def axDelta (V W : ℝ) : ℝ := ((V + W) * V * W) ^ 2 / 256

/-- `Δ(τ) N₊`: the plus numerator with the `τ`-side `Δ` cleared (`τ = iu`, `z = it`). -/
def axPlusNum (E2a Va Wa u E2b Vb Wb t : ℝ) : ℝ :=
  (axDelta Vb Wb * axE4 Va Wa ^ 3 - axDelta Va Wa * axE4 Vb Wb ^ 3) *
      (u * axE6 Va Wa - 2 * (u * E2a - 3 / π) * axE4 Va Wa) +
    axDelta Vb Wb * E2a * (u * E2a - 6 / π) * axE4 Va Wa ^ 2 * axE6 Va Wa +
    axDelta Va Wa * (-2 * (u * E2a - 3 / π) * axE4 Va Wa * axE4 Vb Wb * axE6 Vb Wb *
        (E2b - 6 / (π * t)) + u * axE6 Va Wa * axE4 Vb Wb ^ 2 * (E2b - 6 / (π * t)) ^ 2)

/-- `ψ₂ = (U + W)L − (U + V)L_S`. -/
def axPsiTwo (Va Wa La LSa : ℝ) : ℝ := (Va + Wa + Wa) * La - (Va + Wa + Va) * LSa

/-- `ψ₄ = (U² + W² − 2V²)L + (U² + V² − 2W²)L_S`. -/
def axPsiFour (Va Wa La LSa : ℝ) : ℝ :=
  ((Va + Wa) ^ 2 + Wa ^ 2 - 2 * Va ^ 2) * La + ((Va + Wa) ^ 2 + Va ^ 2 - 2 * Wa ^ 2) * LSa

/-- `Δ(τ) N₋`: the minus numerator with the `τ`-side `Δ` cleared. -/
def axMinusNum (Va Wa La LSa Vb Wb Lb : ℝ) : ℝ :=
  -3456 * axDelta Va Wa * axE4 Va Wa * (axE4 Vb Wb * axE6 Vb Wb * Lb) +
    axPsiTwo Va Wa La LSa * axE4 Va Wa ^ 2 * axE6 Va Wa *
      (axE4 Vb Wb ^ 2 * Wb - axE6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2)) +
    axPsiFour Va Wa La LSa * (1728 * axDelta Va Wa * (axE4 Vb Wb ^ 2 * Wb) +
      axE4 Va Wa ^ 3 * (axE6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2) - axE4 Vb Wb ^ 2 * Wb))

/-- `Φ' = Δ(τ)·2𝒦̂·Δ(z)(j(τ) − j(z))` on the axes. -/
def axPhi (E2a Va Wa La LSa u E2b Vb Wb Lb t : ℝ) : ℝ :=
  -(π ^ 2 * t ^ 2 / 36) * axPlusNum E2a Va Wa u E2b Vb Wb t -
    axMinusNum Va Wa La LSa Vb Wb Lb / (3456 * π)

/-- `Δ(τ)·2𝒦·Δ(z)(j(τ) − j(z))` on the axes. -/
def axPhiK (E2a Va Wa La LSa u E2b Vb Wb Lb t : ℝ) : ℝ :=
  -(π ^ 2 * t ^ 2 / 36) * axPlusNum E2a Va Wa u E2b Vb Wb t +
    axMinusNum Va Wa La LSa Vb Wb Lb / (3456 * π)

/-- `𝒩 = Δ(τ)Δ(z)(j(τ) − j(z)) = Δ(z)E₄(τ)³ − Δ(τ)E₄(z)³`. -/
def axNu (Va Wa Vb Wb : ℝ) : ℝ :=
  axDelta Vb Wb * axE4 Va Wa ^ 3 - axDelta Va Wa * axE4 Vb Wb ^ 3

/-! ## The generators on the imaginary axis -/

/-- `E₂(iu)`. -/
def axE2 (u : ℝ) : ℝ := (EisensteinSeries.E2 (imagPt u)).re

/-- `V(iu) = θ₂(iu)⁴`. -/
def axV (u : ℝ) : ℝ := (thetaV (imagPt u)).re

/-- `W(iu) = θ₄(iu)⁴`. -/
def axW (u : ℝ) : ℝ := (thetaW (imagPt u)).re

/-- `L(iu) = log λ(iu)`. -/
def axL (u : ℝ) : ℝ := (ckmrvL (imagPt u)).re

/-- `L_S(iu) = log(1 − λ(iu))`. -/
def axLS (u : ℝ) : ℝ := (ckmrvLS (imagPt u)).re

theorem ofReal_re_eq_of_mem {z : ℂ} (h : z ∈ realSubfield) : ((z.re : ℝ) : ℂ) = z := by
  apply Complex.ext
  · simp
  · simp [mem_realSubfield_iff.mp h]

section Axis

variable {u : ℝ} (hu : 0 < u)
include hu

theorem E2_imagPt_eq_axE2 : EisensteinSeries.E2 (imagPt u) = (axE2 u : ℂ) :=
  (ofReal_re_eq_of_mem (E2_imagPt_mem hu)).symm

theorem thetaV_imagPt_eq_axV : thetaV (imagPt u) = (axV u : ℂ) :=
  (ofReal_re_eq_of_mem (thetaV_imagPt_mem hu)).symm

theorem thetaW_imagPt_eq_axW : thetaW (imagPt u) = (axW u : ℂ) :=
  (ofReal_re_eq_of_mem (thetaW_imagPt_mem hu)).symm

theorem ckmrvL_imagPt_eq_axL : ckmrvL (imagPt u) = (axL u : ℂ) :=
  (ofReal_re_eq_of_mem (ckmrvL_imagPt_mem hu)).symm

theorem ckmrvLS_imagPt_eq_axLS : ckmrvLS (imagPt u) = (axLS u : ℂ) :=
  (ofReal_re_eq_of_mem (ckmrvLS_imagPt_mem hu)).symm

theorem thetaU_imagPt_eq_ax : thetaU (imagPt u) = ((axV u + axW u : ℝ) : ℂ) := by
  rw [thetaU_eq_add, thetaV_imagPt_eq_axV hu, thetaW_imagPt_eq_axW hu]
  push_cast
  ring

theorem E4_imagPt_eq_ax : ModularForm.E₄ (imagPt u) = (axE4 (axV u) (axW u) : ℂ) := by
  rw [E4_eq_thetaVW, thetaV_imagPt_eq_axV hu, thetaW_imagPt_eq_axW hu, axE4]
  push_cast
  ring

theorem E6_imagPt_eq_ax : ModularForm.E₆ (imagPt u) = (axE6 (axV u) (axW u) : ℂ) := by
  rw [E6_eq_thetaVW, thetaV_imagPt_eq_axV hu, thetaW_imagPt_eq_axW hu, axE6]
  push_cast
  ring

theorem discriminant_imagPt_eq_ax :
    ModularForm.discriminant (imagPt u) = (axDelta (axV u) (axW u) : ℂ) := by
  rw [discriminant_eq_thetaUVW, thetaU_imagPt_eq_ax hu, thetaV_imagPt_eq_axV hu,
    thetaW_imagPt_eq_axW hu, axDelta]
  push_cast
  ring

theorem axDelta_ne_zero : axDelta (axV u) (axW u) ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero (imagPt u)
  rw [discriminant_imagPt_eq_ax hu, h, ofReal_zero]

end Axis

/-! ## The plus kernel -/

/-- The contracted plus numerator `Σⱼ (factor·φ̃ⱼ)(z) · cⱼ(τ, z)`. -/
def ckmrvEightPlusContraction (τ z : ℍ) : ℂ :=
  ∑ j, (ckmrvModularFactor z (![7, 6, 5] j) * ckmrvTildePhiBasis z j) * eightPlusTauCoeff j τ z

/-- The contracted minus numerator. -/
def ckmrvEightMinusContraction (τ z : ℍ) : ℂ :=
  ∑ j, (ckmrvModularFactor z (![6, 5, 4] j) * ckmrvTildePsiBasis z j) * eightMinusTauCoeff j τ

theorem ckmrvEightPlusKernel_eq_contraction (τ z : ℍ) :
    ckmrvEightPlusKernel τ z = ckmrvEightPlusContraction τ z /
      (ckmrvPlusScale * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvEightPlusKernel_eq_sum, ckmrvEightPlusContraction, div_eq_mul_inv, Finset.sum_mul]
  simp only [Fin.sum_univ_three, mul_inv]
  ring

theorem ckmrvEightMinusKernel_eq_contraction (τ z : ℍ) :
    ckmrvEightMinusKernel τ z = ckmrvEightMinusContraction τ z /
      (ckmrvMinusScale * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvEightMinusKernel_eq_sum, ckmrvEightMinusContraction, div_eq_mul_inv, Finset.sum_mul]
  simp only [Fin.sum_univ_three, mul_inv]
  ring

/-- The plus contraction on the axes is `i` times this real number. -/
def axPlusContr (E2a Va Wa u E2b Vb Wb t : ℝ) : ℝ :=
  axDelta Vb Wb * (-t ^ 2) *
      ((axE4 Va Wa ^ 3 / axDelta Va Wa - axE4 Vb Wb ^ 3 / axDelta Vb Wb) *
          (u * (axE6 Va Wa - 2 * E2a * axE4 Va Wa + E2a ^ 2) + 6 / π * (axE4 Va Wa - E2a)) +
        E2a * (u * E2a - 6 / π) * (axE4 Vb Wb ^ 3 / axDelta Vb Wb -
          (axE4 Va Wa ^ 3 / axDelta Va Wa - axE4 Va Wa ^ 2 * axE6 Va Wa / axDelta Va Wa))) +
    axE4 Vb Wb * axE6 Vb Wb * (-t ^ 2 * (E2b - 6 / (π * t))) *
      (-2 * ((u * E2a - 3 / π) * axE4 Va Wa)) +
    axE4 Vb Wb ^ 2 * (-t ^ 2 * (E2b - 6 / (π * t)) ^ 2) * (u * axE6 Va Wa)

/-- The minus contraction on the axes. -/
def axMinusContr (Va Wa La LSa Vb Wb Lb : ℝ) : ℝ :=
  axE4 Vb Wb * axE6 Vb Wb * Lb * (-(2 * 1728) * axE4 Va Wa) +
    axE4 Vb Wb ^ 2 * Wb *
      ((axPsiTwo Va Wa La LSa - axPsiFour Va Wa La LSa) * (axE4 Va Wa ^ 3 / axDelta Va Wa) -
        axPsiTwo Va Wa La LSa * (axE4 Va Wa ^ 3 / axDelta Va Wa -
          axE4 Va Wa ^ 2 * axE6 Va Wa / axDelta Va Wa) + 1728 * axPsiFour Va Wa La LSa) +
    axE6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2) *
      (-((axPsiTwo Va Wa La LSa - axPsiFour Va Wa La LSa) * (axE4 Va Wa ^ 3 / axDelta Va Wa)) +
        axPsiTwo Va Wa La LSa * (axE4 Va Wa ^ 3 / axDelta Va Wa -
          axE4 Va Wa ^ 2 * axE6 Va Wa / axDelta Va Wa))

theorem axDelta_mul_axPlusContr {E2a Va Wa u E2b Vb Wb t : ℝ} (ha : axDelta Va Wa ≠ 0)
    (hb : axDelta Vb Wb ≠ 0) (ht : t ≠ 0) :
    axDelta Va Wa * axPlusContr E2a Va Wa u E2b Vb Wb t =
      -t ^ 2 * axPlusNum E2a Va Wa u E2b Vb Wb t := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axPlusContr, axPlusNum]
  field_simp
  ring

theorem axDelta_mul_axMinusContr {Va Wa La LSa Vb Wb Lb : ℝ} (ha : axDelta Va Wa ≠ 0) :
    axDelta Va Wa * axMinusContr Va Wa La LSa Vb Wb Lb = axMinusNum Va Wa La LSa Vb Wb Lb := by
  simp only [axMinusContr, axMinusNum]
  field_simp
  ring

theorem ckmrvEightPlusContraction_expand (τ z : ℍ) :
    ckmrvEightPlusContraction τ z =
      ModularForm.discriminant z * ckmrvTildePhiBasis z 0 * eightPlusTauCoeff 0 τ z +
        ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1 * eightPlusTauCoeff 1 τ z +
          ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2 * eightPlusTauCoeff 2 τ z := by
  rw [← eisensteinTen_eq_four_mul_six, ← eisensteinEight_eq_four_sq]
  simp only [ckmrvEightPlusContraction, Fin.sum_univ_three]
  rfl

theorem ckmrvEightMinusContraction_expand (τ z : ℍ) :
    ckmrvEightMinusContraction τ z =
      ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePsiBasis z 0 * eightMinusTauCoeff 0 τ +
        ModularForm.E₄ z ^ 2 * ckmrvTildePsiBasis z 1 * eightMinusTauCoeff 1 τ +
          ModularForm.E₆ z * ckmrvTildePsiBasis z 2 * eightMinusTauCoeff 2 τ := by
  rw [← eisensteinTen_eq_four_mul_six, ← eisensteinEight_eq_four_sq]
  simp only [ckmrvEightMinusContraction, Fin.sum_univ_three]
  rfl

theorem ckmrvEightHat_algebra (P M D J : ℂ) (pr mr db jr : ℝ) (hP : P = I * (pr : ℂ))
    (hM : M = (mr : ℂ)) (hD : D = (db : ℂ)) (hJ : J = (jr : ℂ)) (hdb : db ≠ 0) (hjr : jr ≠ 0) :
    (P / (36 * (π : ℂ) ^ (-2 : ℤ) * I * D * J) - M / (2 * 1728 * (π : ℂ) * D * J)) / 2 =
      (((π ^ 2 * pr / 36 - mr / (3456 * π)) / (db * jr) / 2 : ℝ) : ℂ) := by
  subst hP hM hD hJ
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπc : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdbc : (db : ℂ) ≠ 0 := ofReal_ne_zero.mpr hdb
  have hjrc : (jr : ℂ) ≠ 0 := ofReal_ne_zero.mpr hjr
  rw [zpow_neg, zpow_two]
  push_cast
  field_simp
  ring

section AxisKernel

variable {u t : ℝ}

theorem tildePhi0_axis (ht : 0 < t) : ckmrvTildePhiBasis (imagPt t) 0 = ((-t ^ 2 : ℝ) : ℂ) := by
  show ((imagPt t : ℍ) : ℂ) ^ 2 = _
  rw [coe_imagPt ht]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem tildePhi1_axis (ht : 0 < t) :
    ckmrvTildePhiBasis (imagPt t) 1 = ((-t ^ 2 * (axE2 t - 6 / (π * t)) : ℝ) : ℂ) := by
  show ((imagPt t : ℍ) : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) -
    6 * Complex.I / (Real.pi : ℂ) * ((imagPt t : ℍ) : ℂ) = _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [coe_imagPt ht, E2_imagPt_eq_axE2 ht]
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem tildePhi2_axis (ht : 0 < t) :
    ckmrvTildePhiBasis (imagPt t) 2 = ((-t ^ 2 * (axE2 t - 6 / (π * t)) ^ 2 : ℝ) : ℂ) := by
  show ((imagPt t : ℍ) : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) ^ 2 -
    12 * Complex.I / (Real.pi : ℂ) * ((imagPt t : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt t) -
      36 / (Real.pi : ℂ) ^ 2 = _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [coe_imagPt ht, E2_imagPt_eq_axE2 ht]
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem phi0_axis (hu : 0 < u) : ckmrvPhiBasis (imagPt u) 0 = I * (u : ℂ) := by
  show ((imagPt u : ℍ) : ℂ) = _
  rw [coe_imagPt hu]

theorem phi1_axis (hu : 0 < u) :
    ckmrvPhiBasis (imagPt u) 1 = I * ((u * axE2 u - 3 / π : ℝ) : ℂ) := by
  show ((imagPt u : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt u) - 3 * Complex.I / (Real.pi : ℂ) = _
  rw [coe_imagPt hu, E2_imagPt_eq_axE2 hu]
  push_cast
  ring

theorem phi2_axis (hu : 0 < u) :
    ckmrvPhiBasis (imagPt u) 2 = I * ((axE2 u * (u * axE2 u - 6 / π) : ℝ) : ℂ) := by
  show ((imagPt u : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt u) ^ 2 -
    6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 (imagPt u) = _
  rw [coe_imagPt hu, E2_imagPt_eq_axE2 hu]
  push_cast
  ring

theorem tildePsi0_axis (ht : 0 < t) : ckmrvTildePsiBasis (imagPt t) 0 = (axL t : ℂ) := by
  show ckmrvL (imagPt t) = _
  exact ckmrvL_imagPt_eq_axL ht

theorem tildePsi1_axis (ht : 0 < t) : ckmrvTildePsiBasis (imagPt t) 1 = (axW t : ℂ) := by
  show thetaW (imagPt t) = _
  exact thetaW_imagPt_eq_axW ht

theorem tildePsi2_axis (ht : 0 < t) :
    ckmrvTildePsiBasis (imagPt t) 2 = (((axV t + axW t) ^ 2 - axV t ^ 2 : ℝ) : ℂ) := by
  show thetaU (imagPt t) ^ 2 - thetaV (imagPt t) ^ 2 = _
  rw [thetaU_imagPt_eq_ax ht, thetaV_imagPt_eq_axV ht]
  push_cast
  ring

theorem psiBasis_one_axis (hu : 0 < u) :
    ckmrvPsiBasis (imagPt u) 1 = (axPsiTwo (axV u) (axW u) (axL u) (axLS u) : ℂ) := by
  show ckmrvXiTwo (imagPt u) * ckmrvL (imagPt u) + ckmrvXiTwoS (imagPt u) * ckmrvLS (imagPt u) = _
  rw [ckmrvXiTwo, ckmrvXiTwoS, thetaU_imagPt_eq_ax hu, thetaV_imagPt_eq_axV hu,
    thetaW_imagPt_eq_axW hu, ckmrvL_imagPt_eq_axL hu, ckmrvLS_imagPt_eq_axLS hu, axPsiTwo]
  push_cast
  ring

theorem psiBasis_two_axis (hu : 0 < u) :
    ckmrvPsiBasis (imagPt u) 2 = (axPsiFour (axV u) (axW u) (axL u) (axLS u) : ℂ) := by
  show ckmrvXiFour (imagPt u) * ckmrvL (imagPt u) + ckmrvXiFourS (imagPt u) * ckmrvLS (imagPt u) = _
  rw [ckmrvXiFour, ckmrvXiFourS, thetaU_imagPt_eq_ax hu, thetaV_imagPt_eq_axV hu,
    thetaW_imagPt_eq_axW hu, ckmrvL_imagPt_eq_axL hu, ckmrvLS_imagPt_eq_axLS hu, axPsiFour]
  push_cast
  ring

theorem kleinModularJ_imagPt_eq_ax (hu : 0 < u) :
    kleinModularJ (imagPt u) = ((axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) : ℝ) : ℂ) := by
  rw [kleinModularJ, E4_imagPt_eq_ax hu, discriminant_imagPt_eq_ax hu]
  push_cast
  ring

theorem plusContraction_axis (hu : 0 < u) (ht : 0 < t) :
    ckmrvEightPlusContraction (imagPt u) (imagPt t) =
      I * (axPlusContr (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t : ℂ) := by
  rw [ckmrvEightPlusContraction_expand, eightPlusTauCoeff_zero, eightPlusTauCoeff_one,
    eightPlusTauCoeff_two, ckmrvModularFactor_two_eq, tildePhi0_axis ht, tildePhi1_axis ht,
    tildePhi2_axis ht, phi1_axis hu, phi2_axis hu, coe_imagPt hu, kleinModularJ_imagPt_eq_ax hu,
    kleinModularJ_imagPt_eq_ax ht, E2_imagPt_eq_axE2 hu, E4_imagPt_eq_ax hu, E4_imagPt_eq_ax ht,
    E6_imagPt_eq_ax hu, E6_imagPt_eq_ax ht, discriminant_imagPt_eq_ax hu,
    discriminant_imagPt_eq_ax ht, axPlusContr]
  push_cast
  ring

theorem minusContraction_axis (hu : 0 < u) (ht : 0 < t) :
    ckmrvEightMinusContraction (imagPt u) (imagPt t) =
      (axMinusContr (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t) : ℂ) := by
  rw [ckmrvEightMinusContraction_expand, eightMinusTauCoeff_zero, eightMinusTauCoeff_one,
    eightMinusTauCoeff_two, ckmrvModularFactor_two_eq, tildePsi0_axis ht, tildePsi1_axis ht,
    tildePsi2_axis ht, psiBasis_one_axis hu, psiBasis_two_axis hu, kleinModularJ_imagPt_eq_ax hu,
    E4_imagPt_eq_ax hu, E4_imagPt_eq_ax ht, E6_imagPt_eq_ax hu, E6_imagPt_eq_ax ht,
    discriminant_imagPt_eq_ax hu, axMinusContr]
  push_cast
  ring

/-- **The hat kernel on the axes.** Off the singular curves,
`2 𝒦̂(iu, it) · 𝒩 = Φ'` with `𝒩 = Δ(iu)Δ(it)(j(iu) − j(it))`. -/
theorem ckmrvEightHatKernel_axis (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
        axNu (axV u) (axW u) (axV t) (axW t) =
      axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
  have hΔa := axDelta_ne_zero hu
  have hΔb := axDelta_ne_zero ht
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hJr : axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
      axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t) ≠ 0 := by
    intro h0
    apply hJ
    rw [kleinModularJ_imagPt_eq_ax hu, kleinModularJ_imagPt_eq_ax ht]
    exact congrArg ((↑) : ℝ → ℂ) (sub_eq_zero.mp h0)
  have hJeq : kleinModularJ (imagPt u) - kleinModularJ (imagPt t) =
      ((axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
        axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t) : ℝ) : ℂ) := by
    rw [kleinModularJ_imagPt_eq_ax hu, kleinModularJ_imagPt_eq_ax ht, ← ofReal_sub]
  have hK := ckmrvEightHat_algebra (ckmrvEightPlusContraction (imagPt u) (imagPt t))
    (ckmrvEightMinusContraction (imagPt u) (imagPt t)) (ModularForm.discriminant (imagPt t))
    (kleinModularJ (imagPt u) - kleinModularJ (imagPt t))
    (axPlusContr (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t)
    (axMinusContr (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t))
    (axDelta (axV t) (axW t)) _ (plusContraction_axis hu ht) (minusContraction_axis hu ht)
    (discriminant_imagPt_eq_ax ht) hJeq hΔb hJr
  rw [ckmrvEightHatKernel, ckmrvEightPlusKernel_eq_contraction,
    ckmrvEightMinusKernel_eq_contraction, ckmrvPlusScale, ckmrvMinusScale, hK, ofReal_re]
  have hplus := axDelta_mul_axPlusContr (E2a := axE2 u) (u := u) (E2b := axE2 t) hΔa hΔb ht.ne'
  have hminus := axDelta_mul_axMinusContr (La := axL u) (LSa := axLS u) (Lb := axL t)
    (Vb := axV t) (Wb := axW t) hΔa
  have hNu : axNu (axV u) (axW u) (axV t) (axW t) = axDelta (axV u) (axW u) *
      axDelta (axV t) (axW t) * (axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
        axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t)) := by
    simp only [axNu]
    field_simp
  have hN : axDelta (axV t) (axW t) * axE4 (axV u) (axW u) ^ 3 -
      axDelta (axV u) (axW u) * axE4 (axV t) (axW t) ^ 3 ≠ 0 := by
    have hEq : axDelta (axV t) (axW t) * axE4 (axV u) (axW u) ^ 3 -
        axDelta (axV u) (axW u) * axE4 (axV t) (axW t) ^ 3 =
          axDelta (axV u) (axW u) * axDelta (axV t) (axW t) *
            (axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
              axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t)) := by
      field_simp
    rw [hEq]
    exact mul_ne_zero (mul_ne_zero hΔa hΔb) hJr
  rw [hNu]
  calc _ = π ^ 2 * (axDelta (axV u) (axW u) *
          axPlusContr (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t) / 36 -
        (axDelta (axV u) (axW u) *
          axMinusContr (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t)) / (3456 * π) := by
        field_simp
    _ = _ := by
        rw [hplus, hminus]
        simp only [axPhi]
        ring

end AxisKernel

end E8Leech
