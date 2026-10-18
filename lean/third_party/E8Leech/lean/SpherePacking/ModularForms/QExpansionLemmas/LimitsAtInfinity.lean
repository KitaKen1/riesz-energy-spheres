-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.CompletePartialOrder


/-!
# Limits at infinity

For modular forms, the value at the cusp `∞` is a genuine limit as `im τ → ∞`.

## Main statements
* `modularForm_tendsto_atImInfty`
* `qExpansion_mul_coeff`
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

/-- The cusp function at `0` is a (punctured) limit along the inverse `q`-parameter. -/
public theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k]
    [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hcont : ContinuousAt (Function.Periodic.cuspFunction (n : ℝ) (⇑f ∘ (↑ofComplex : ℂ → ℍ)))
      0 := by
    simpa [UpperHalfPlane.cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos
        (by simp [CongruenceSubgroup.strictPeriods_Gamma])).continuousAt
  simpa [UpperHalfPlane.cuspFunction, Function.comp] using
    (Function.Periodic.tendsto_nhds_zero (h := (n : ℝ)) (f := ⇑f ∘ (↑ofComplex : ℂ → ℍ)) hcont)


/-- A modular form converges to its `valueAtInfty` as `im τ → ∞` (for `Γ(n)`). -/
public theorem modularForm_tendsto_atImInfty {k : ℤ} (n : ℕ) (f : ModularForm Γ(n) k)
    [NeZero n] :
    Tendsto (fun τ : ℍ => f τ) atImInfty (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have ht :
      Tendsto (fun τ : ℍ => cuspFunction (n : ℝ) f (Periodic.qParam (n : ℝ) τ)) atImInfty
        (𝓝 (cuspFunction (n : ℝ) f 0)) := by
    exact ((ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hmem).continuousAt.tendsto.comp
        (UpperHalfPlane.qParam_tendsto_atImInfty hn_pos))
  have hzero : cuspFunction (n : ℝ) f 0 = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) := by
    exact UpperHalfPlane.cuspFunction_apply_zero hn_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hmem)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hmem)
  have ht' :
      Tendsto (fun τ : ℍ => cuspFunction (n : ℝ) f (Periodic.qParam (n : ℝ) τ)) atImInfty
        (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
    simpa [hzero] using ht
  refine ht'.congr fun τ ↦ ?_
  simpa [UpperHalfPlane.cuspFunction, Periodic.qParam] using
    (SlashInvariantFormClass.eq_cuspFunction (f := f) (h := (n : ℝ)) τ hmem hn_ne)

/-- The `qExpansion` of a product is the product of the `qExpansion`s (coeffwise). -/
public lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [hn : NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g :=
  ModularForm.qExpansion_mul (Γ := Γ(n)) (h := (n : ℝ)) (Nat.cast_pos.mpr (NeZero.pos n))
    (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f g
