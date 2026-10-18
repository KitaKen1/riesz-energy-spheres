-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Tactic.FunProp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `fun_prop` extensions

This file extends Mathlib's `fun_prop` lemma database with instances/closure lemmas that occur
frequently in this repository:

* `MDifferentiable` (incl. a `pow` rule and a numeral leaf-rule),
* `Summable`,
* `HasSum`,
* `MeasureTheory.Integrable`.

The goal is that "plumbing" proofs can often be replaced by:

```
by fun_prop
```
-/

open scoped Manifold

/-! ### `MDifferentiable` -/

attribute [fun_prop] MDifferentiable mdifferentiable_id mdifferentiable_const MDifferentiable.comp
  MDifferentiable.add MDifferentiable.sub MDifferentiable.neg MDifferentiable.mul
  MDifferentiable.const_smul

section MDifferentiablePow

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type*} [NormedRing E'] [NormedAlgebra 𝕜 E']
variable {f : M → E'}

/--
`fun_prop` leaf-rule: numerals (as constant functions) are `MDifferentiable`.

Without this, `fun_prop` can get stuck on goals like `MDifferentiable ... fun x => 3 x`,
whose head symbol is `OfNat.ofNat` (for the `OfNat (M → E') 3` instance).
-/
public theorem mdifferentiable_ofNat (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, E') (OfNat.ofNat (α := M → E') n) := by
  exact (mdifferentiable_const :
    MDifferentiable I 𝓘(𝕜, E') (fun _ : M => (OfNat.ofNat (α := E') n)))

/- `fun_prop` rule: pointwise powers preserve `MDifferentiable`. -/
attribute [fun_prop] mdifferentiable_ofNat MDifferentiable.pow

end MDifferentiablePow

/-! ### `Summable` -/

attribute [fun_prop] Summable Summable.add Summable.sub Summable.neg Summable.const_smul
  Summable.smul_const Summable.mul_left Summable.mul_right

/-! ### `HasSum` -/

attribute [fun_prop] HasSum HasSum.add HasSum.sub HasSum.neg HasSum.const_smul HasSum.smul_const
  HasSum.mul_left HasSum.mul_right

/-! ### `MeasureTheory.Integrable` -/

attribute [fun_prop] MeasureTheory.Integrable
  MeasureTheory.Integrable.add
  MeasureTheory.Integrable.sub
  MeasureTheory.Integrable.neg
  MeasureTheory.Integrable.smul
  MeasureTheory.Integrable.smul_const
  MeasureTheory.Integrable.const_mul
  MeasureTheory.Integrable.mul_const
  MeasureTheory.Integrable.norm
  MeasureTheory.Integrable.comp_measurable
