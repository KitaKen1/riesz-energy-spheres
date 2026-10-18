-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import SpherePacking.ForMathlib.ScalarOneForm

/-!
# Symmetry of `fderiv` for scalar one-forms

This file proves symmetry lemmas for `fderiv`/`fderivWithin` of `MagicFunction.scalarOneForm`.
They are used to discharge the `dω = 0` hypothesis in Poincaré-lemma based contour deformation
arguments.
-/

namespace SpherePacking.ForMathlib

open MagicFunction

noncomputable section

/-- The `fderiv` of `scalarOneForm f` is symmetric in its two tangent arguments. -/
public lemma fderiv_scalarOneForm_symm {f : ℂ → ℂ} {x u v : ℂ}
    (hfdiff : DifferentiableAt ℂ f x) :
    fderiv ℝ (scalarOneForm f) x u v = fderiv ℝ (scalarOneForm f) x v u := by
  let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) := (ContinuousLinearMap.mul ℂ ℂ).flip
  have hEq : scalarOneForm f = fun z => L (f z) := by
    rfl
  have hωF :
      HasFDerivAt (𝕜 := ℝ) (scalarOneForm f)
        ((ContinuousLinearMap.toSpanSingleton ℂ (L (deriv f x))).restrictScalars ℝ) x := by
    simpa [hEq] using
      ((hasDerivAt_const x L).clm_apply hfdiff.hasDerivAt).hasFDerivAt.restrictScalars ℝ
  rw [hωF.fderiv]
  simp [L, mul_left_comm, mul_comm]

/-- `fderivWithin`-version of `fderiv_scalarOneForm_symm` on an open set. -/
public lemma fderivWithin_scalarOneForm_symm_of_isOpen
    {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {u v : ℂ} (hfdiff : DifferentiableAt ℂ f x) :
    fderivWithin ℝ (scalarOneForm f) s x u v = fderivWithin ℝ (scalarOneForm f) s x v u := by
  simpa [fderivWithin_of_mem_nhds (f := scalarOneForm f) (hs.mem_nhds hx)] using
    (fderiv_scalarOneForm_symm (f := f) (x := x) (u := u) (v := v) hfdiff)

end

end SpherePacking.ForMathlib
