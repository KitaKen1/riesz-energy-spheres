-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
import SpherePacking.ModularForms.QExpansionLemmas.LimitsAtInfinity

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.CompletePartialOrder


/-!
# Algebra of `qExpansion`

This file records basic algebraic properties of `qExpansion`, mostly for comparing `qExpansion`s of
functions that are definitionally equal and for interacting with subtraction, scalar multiplication
and powers.

## Main statements
* `qExpansion_ext2`
* `qExpansion_sub1`
* `qExpansion_smul2`
* `qExpansion_pow`
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

lemma cuspFunction_congr_funLike
    {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (h : ℝ) (f : α) (g : β) (hf : ⇑f = ⇑g) :
    cuspFunction h f = cuspFunction h g := by
  ext z
  by_cases hz : z = 0 <;> simp [cuspFunction, Periodic.cuspFunction, hf, hz]

/-- If two `FunLike` objects have the same underlying function, then their `qExpansion`s agree. -/
public lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β)
    (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  ext m
  simp [qExpansion_coeff, cuspFunction_congr_funLike (h := (1 : ℝ)) (f := f) (g := g) h]

/-- On `Γ(1)`, `qExpansion` commutes with subtraction. -/
public lemma qExpansion_sub1 {a b : ℤ} (f : ModularForm Γ(1) a) (g : ModularForm Γ(1) b) :
    qExpansion 1 (f - g) = qExpansion 1 f - qExpansion 1 g := by
  simpa using
    (ModularForm.qExpansion_sub (Γ := Γ(1)) (h := (1 : ℝ)) (by norm_num)
      (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f g)

/-- `qExpansion` commutes with scalar multiplication. -/
public lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [hn : NeZero n] :
    a • qExpansion n f = qExpansion n (a • f) := by
  simpa using
    (ModularForm.qExpansion_smul (Γ := Γ(n)) (h := (n : ℝ)) (Nat.cast_pos.mpr (NeZero.pos n))
      (by
        simp [CongruenceSubgroup.strictPeriods_Gamma]) a f).symm

/-- The `qExpansion` of a power agrees with the power of the `qExpansion`. -/
public lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
    qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) =
      (qExpansion 1 f) ^ n := by
  simpa using
    (qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℝ)) (k := k) (by norm_num)
      (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f n)
