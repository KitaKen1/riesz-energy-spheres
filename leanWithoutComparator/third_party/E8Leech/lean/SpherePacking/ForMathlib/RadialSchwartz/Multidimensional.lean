/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.

module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus


/-!
# Multidimensional

This file defines `schwartzMap_multidimensional_of_schwartzMap_real` and proves results such as
`hasFDerivAt_norm_sq`, `differentiableAt_norm_sq`, and `differentiable_norm_sq`.
-/

section SchwartzMap_multidimensional_of_schwartzMap_real

open SchwartzMap Function RCLike

-- Credit to Heather for helping me golf these

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Fréchet derivative of `x ↦ ‖x‖ ^ 2` is `2 • innerSL ℝ x`. -/
public lemma hasFDerivAt_norm_sq {x : F} :
    HasFDerivAt (fun x ↦ ‖x‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt

/-- The function `x ↦ ‖x‖ ^ 2` is differentiable at every point. -/
public lemma differentiableAt_norm_sq {x : F} :
    DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2) x := hasFDerivAt_norm_sq.differentiableAt

/-- The function `x ↦ ‖x‖ ^ 2` is differentiable. -/
public lemma differentiable_norm_sq :
    Differentiable ℝ (fun (x : F) ↦ ‖x‖ ^ 2) := fun _ => differentiableAt_norm_sq

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

/-- Lift a Schwartz function on `ℝ` to a Schwartz function on `F` by composing with `‖x‖ ^ 2`. -/
@[expose, simps!]
public noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

@[simp] lemma schwartzMap_multidimensional_of_schwartzMap_real_apply (x : F) :
    schwartzMap_multidimensional_of_schwartzMap_real (F := F) f x = f (‖x‖ ^ 2) := by
  simp [schwartzMap_multidimensional_of_schwartzMap_real]

end SchwartzMap_multidimensional_of_schwartzMap_real
