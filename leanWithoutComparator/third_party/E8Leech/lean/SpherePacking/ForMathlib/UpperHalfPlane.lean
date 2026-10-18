-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


/-!
# Upper half-plane

This file proves results such as `ModularGroup.modular_S_sq`.
-/

open UpperHalfPlane

/-- Coercion of the `S`-action on `ℍ`: `(S • z : ℂ) = -1 / z`. -/
public theorem ModularGroup.coe_S_smul (z : UpperHalfPlane) :
    (↑(S • z) : ℂ) = (-1 : ℂ) / (z : ℂ) := by
  simpa [div_eq_mul_inv] using congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (z := z))

/-- The `S` matrix squares to `-1` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.modular_S_sq : S * S = -1 := by
  decide

/-- Explicit matrix for `S * T` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.S_mul_T :
    S * T = ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]

/-- Coercion of the `(S * T)`-action on `ℍ`: `((S * T) • z : ℂ) = -1 / (z + 1)`. -/
public theorem ModularGroup.coe_ST_smul (z : UpperHalfPlane) :
    (↑((S * T) • z) : ℂ) = (-1 : ℂ) / ((z : ℂ) + 1) := by
  simpa [ModularGroup.S_mul_T] using coe_specialLinearGroup_apply (g := S * T) (z := z)
