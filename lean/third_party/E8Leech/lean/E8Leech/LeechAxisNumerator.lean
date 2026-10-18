import E8Leech.CKMRVAxisNumerator
import E8Leech.CKMRVCombinedKernels

/-!
# The `d = 24` kernels on the imaginary axes as explicit real expressions

For `τ = iu`, `z = it` off the singular curves `j(iu) = j(it)`,

`𝒦̂⁽²⁴⁾(iu, it) = axLeechPhi / (3456 · Δ(it) · 𝒩(iu, it))`,

where `𝒩 = Δ(z) E₄(τ)³ − Δ(τ) E₄(z)³ = axNu` is the same polynomial in `V, W` as for `d = 8` and
`axLeechPhi` is an explicit real polynomial in `E₂, V, W, L, L_S` at `iu`, `E₂, V, W, L` at `it`
and `u, t, π, 1/π, 1/t` (from the polynomial numerators of `CKMRVPolynomialNumerators`).
Since `Δ(it) > 0`, the inequality (6.4)(1) for `d = 24` is the sign condition
`axLeechPhi · axNu > 0`, in the same form as for `d = 8` (`axPhi · axNu > 0`).
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

/-! ## The real polynomial model -/

/-- `R₊ = −i Σᵢⱼ φᵢ(τ) N₊ᵢⱼ(τ, z) φ̃ⱼ(z)` on the axes (`τ = iu`, `z = it`). -/
def axLeechPlusNum (E2a Va Wa u E2b Vb Wb t : ℝ) : ℝ :=
  u * (6 * axNu Va Wa Vb Wb * axE4 Va Wa ^ 2 * axE6 Va Wa * axE4 Vb Wb * (-t ^ 2) +
      (1728 * axDelta Va Wa * axDelta Vb Wb - 6 * axNu Va Wa Vb Wb) * axE4 Va Wa ^ 2 *
        axE6 Va Wa * (-t ^ 2 * (E2b - 6 / (π * t)) ^ 2)) +
    (u * E2a - 3 / π) *
      ((-12 * axE4 Va Wa ^ 3 + 5 * 1728 * axDelta Va Wa) * axNu Va Wa Vb Wb * axE4 Vb Wb *
          (-t ^ 2) +
        -2 * 1728 * axDelta Va Wa ^ 2 * axE4 Vb Wb ^ 2 * axE6 Vb Wb *
          (-t ^ 2 * (E2b - 6 / (π * t))) +
        (12 * axE4 Va Wa ^ 3 - 7 * 1728 * axDelta Va Wa) * axNu Va Wa Vb Wb *
          (-t ^ 2 * (E2b - 6 / (π * t)) ^ 2)) +
    E2a * (u * E2a - 6 / π) *
      ((1728 * axDelta Va Wa * axDelta Vb Wb + 6 * axNu Va Wa Vb Wb) * axE4 Va Wa * axE6 Va Wa *
          axE4 Vb Wb * (-t ^ 2) +
        -6 * axNu Va Wa Vb Wb * axE4 Va Wa * axE6 Va Wa * (-t ^ 2 * (E2b - 6 / (π * t)) ^ 2))

/-- `R₋ = Σᵢⱼ ψᵢ(τ) N₋ᵢⱼ(τ, z) ψ̃ⱼ(z)` on the axes. -/
def axLeechMinusNum (Va Wa La LSa Vb Wb Lb : ℝ) : ℝ :=
  (-2 * 1728 * axDelta Va Wa ^ 2 * axE4 Vb Wb ^ 2 * axE6 Vb Wb * Lb +
      -2 * 1728 * axDelta Va Wa * axNu Va Wa Vb Wb * Wb) +
    axPsiTwo Va Wa La LSa *
      ((axE4 Va Wa ^ 3 * axDelta Vb Wb + 2 * axNu Va Wa Vb Wb) * axE4 Va Wa * axE6 Va Wa * Wb +
        -axDelta Va Wa * axE4 Va Wa * axE6 Va Wa * axE4 Vb Wb * axE6 Vb Wb *
          ((Vb + Wb) ^ 2 - Vb ^ 2)) +
    axPsiFour Va Wa La LSa *
      ((1728 * axDelta Va Wa * axDelta Vb Wb - 2 * axNu Va Wa Vb Wb -
          axE4 Va Wa ^ 3 * axDelta Vb Wb) * axE4 Va Wa ^ 2 * Wb +
        axDelta Va Wa * axE4 Va Wa ^ 2 * axE4 Vb Wb * axE6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2))

/-- `Φ₂₄ = 3456 · Δ(z) 𝒩 · 𝒦̂⁽²⁴⁾` on the axes. -/
def axLeechPhi (E2a Va Wa La LSa u E2b Vb Wb Lb t : ℝ) : ℝ :=
  π ^ 2 / 36 * axLeechPlusNum E2a Va Wa u E2b Vb Wb t -
    axLeechMinusNum Va Wa La LSa Vb Wb Lb / (2 * π)

/-! ## The kernels with the denominator cleared -/

theorem ckmrvLeechPlusKernel_mul_den (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
        (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechPlusKernel τ z =
      (1728 * ckmrvPlusScale)⁻¹ * ckmrvCoreContraction (ckmrvPhiBasis τ) (ckmrvTildePhiBasis z)
        (ckmrvLeechPlusPolynomialNumerator τ z) := by
  have h := ckmrvLeechPlusCoefficientMatrix_polynomial τ z hg
  have hij : ∀ i j : Fin 3, (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechPlusCoefficientMatrix τ z i j =
      (1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator τ z i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  simp only [ckmrvLeechPlusKernel, ckmrvCoreContraction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (ckmrvPhiBasis τ i * ckmrvTildePhiBasis z j) * hij i j

theorem ckmrvLeechMinusKernel_mul_den (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
        (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechMinusKernel τ z =
      ckmrvMinusScale⁻¹ * ckmrvCoreContraction (ckmrvPsiBasis τ) (ckmrvTildePsiBasis z)
        (ckmrvLeechMinusPolynomialNumerator τ z) := by
  have h := ckmrvLeechMinusCoefficientMatrix_polynomial τ z hg
  have hij : ∀ i j : Fin 3, (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechMinusCoefficientMatrix τ z i j =
      ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator τ z i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  simp only [ckmrvLeechMinusKernel, ckmrvCoreContraction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (ckmrvPsiBasis τ i * ckmrvTildePsiBasis z j) * hij i j

/-! ## The contractions on the axes -/

section Axis

variable {u t : ℝ}

/-- The plus contraction on the axes is `i` times the real polynomial `R₊`. -/
theorem leechPlusContraction_axis (hu : 0 < u) (ht : 0 < t) :
    ckmrvCoreContraction (ckmrvPhiBasis (imagPt u)) (ckmrvTildePhiBasis (imagPt t))
        (ckmrvLeechPlusPolynomialNumerator (imagPt u) (imagPt t)) =
      I * ((axLeechPlusNum (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t : ℝ) : ℂ) := by
  simp only [ckmrvCoreContraction, Fin.sum_univ_three, ckmrvLeechPlusPolynomialNumerator,
    ckmrvKleinCrossDifference, phi0_axis hu, phi1_axis hu, phi2_axis hu, tildePhi0_axis ht,
    tildePhi1_axis ht, tildePhi2_axis ht, E4_imagPt_eq_ax hu, E6_imagPt_eq_ax hu,
    discriminant_imagPt_eq_ax hu, E4_imagPt_eq_ax ht, E6_imagPt_eq_ax ht,
    discriminant_imagPt_eq_ax ht, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
  simp only [axLeechPlusNum, axNu]
  push_cast
  ring

/-- The minus contraction on the axes is the real polynomial `R₋`. -/
theorem leechMinusContraction_axis (hu : 0 < u) (ht : 0 < t) :
    ckmrvCoreContraction (ckmrvPsiBasis (imagPt u)) (ckmrvTildePsiBasis (imagPt t))
        (ckmrvLeechMinusPolynomialNumerator (imagPt u) (imagPt t)) =
      ((axLeechMinusNum (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t) : ℝ) : ℂ) := by
  have hpsi0 : ckmrvPsiBasis (imagPt u) 0 = 1 := rfl
  simp only [ckmrvCoreContraction, Fin.sum_univ_three, ckmrvLeechMinusPolynomialNumerator,
    ckmrvKleinCrossDifference, hpsi0, psiBasis_one_axis hu, psiBasis_two_axis hu,
    tildePsi0_axis ht, tildePsi1_axis ht, tildePsi2_axis ht, E4_imagPt_eq_ax hu,
    E6_imagPt_eq_ax hu, discriminant_imagPt_eq_ax hu, E4_imagPt_eq_ax ht, E6_imagPt_eq_ax ht,
    discriminant_imagPt_eq_ax ht, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
  simp only [axLeechMinusNum, axNu]
  push_cast
  ring

/-- The common denominator on the axes: `Δ(τ) Δ(z)² (j(τ) − j(z)) = Δ(it) · 𝒩`. -/
theorem leechDenominator_axis (hu : 0 < u) (ht : 0 < t) :
    ModularForm.discriminant (imagPt u) * ModularForm.discriminant (imagPt t) ^ 2 *
        (kleinModularJ (imagPt u) - kleinModularJ (imagPt t)) =
      ((axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t) : ℝ) : ℂ) := by
  have hDu := axDelta_ne_zero hu
  have hDt := axDelta_ne_zero ht
  rw [kleinModularJ_imagPt_eq_ax hu, kleinModularJ_imagPt_eq_ax ht, discriminant_imagPt_eq_ax hu,
    discriminant_imagPt_eq_ax ht, axNu]
  push_cast
  have hDu' : (axDelta (axV u) (axW u) : ℂ) ≠ 0 := by exact_mod_cast hDu
  have hDt' : (axDelta (axV t) (axW t) : ℂ) ≠ 0 := by exact_mod_cast hDt
  field_simp

/-- **`𝒦̂⁽²⁴⁾(iu, it)` as an explicit real expression**, off the singular curves. -/
theorem ckmrvLeechHatKernel_axis (hu : 0 < u) (ht : 0 < t)
    (hreg : kleinModularJ (imagPt u) - kleinModularJ (imagPt t) ≠ 0) :
    ckmrvLeechHatKernel (imagPt u) (imagPt t) =
      ((axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t /
        (3456 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
  have hden := leechDenominator_axis hu ht
  have hp := ckmrvLeechPlusKernel_mul_den (imagPt u) (imagPt t) hreg
  have hm := ckmrvLeechMinusKernel_mul_den (imagPt u) (imagPt t) hreg
  rw [leechPlusContraction_axis hu ht, hden] at hp
  rw [leechMinusContraction_axis hu ht, hden] at hm
  have hd0 : ((axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t) : ℝ) : ℂ) ≠ 0 := by
    rw [← hden]
    exact mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _))) hreg
  have hd0' : axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t) ≠ 0 := by
    exact_mod_cast hd0
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hD : (axDelta (axV t) (axW t) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hd0').1
  have hN : (axNu (axV u) (axW u) (axV t) (axW t) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hd0').2
  have hpl : ckmrvLeechPlusKernel (imagPt u) (imagPt t) =
      ((π ^ 2 * axLeechPlusNum (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t /
        (1728 * 36 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
    have hsc : (1728 * ckmrvPlusScale)⁻¹ * I = (π : ℂ) ^ 2 / (1728 * 36) := by
      rw [ckmrvPlusScale, zpow_neg, zpow_two]
      field_simp
    rw [← mul_assoc, hsc] at hp
    apply mul_left_cancel₀ hd0
    rw [hp]
    push_cast
    field_simp
  have hmi : ckmrvLeechMinusKernel (imagPt u) (imagPt t) =
      ((axLeechMinusNum (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t) /
        (2 * 1728 * π * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hd0
    rw [hm, ckmrvMinusScale]
    push_cast
    field_simp
  rw [ckmrvLeechHatKernel, hpl, hmi, axLeechPhi]
  push_cast
  field_simp
  ring

end Axis

end E8Leech
