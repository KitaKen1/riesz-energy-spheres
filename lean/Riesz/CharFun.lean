/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see third_party/TauCeti/LICENSE.
Authors: The Tau Ceti contributors

Adapted from TauCeti/Analysis/Bochner/CharFun/PosDef.lean,
commit 98962476aaba1de05b4a883df5af0562247cb501.
Only the finite quadratic-form part is included; namespace and imports adapted.
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate
open scoped ComplexOrder

namespace SphericalRiesz.Fourier

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

private theorem integrable_innerProbChar (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ := by
  have h : (fun y => exp (⟪y, a⟫ * I)) = ⇑(innerProbChar a) := by
    ext y; rw [innerProbChar_apply]
  rw [h]; exact (innerProbChar a).integrable (μ := μ)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem exp_mul_conj_exp_inner (y a b : E) :
    exp (⟪y, a⟫ * I) * conj (exp (⟪y, b⟫ * I)) = exp (⟪y, a - b⟫ * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [inner_sub_right, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem normSq_finset_sum_exp_eq_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (t : ι → E) (y : E) : ((normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) := by
  have hconj : conj (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I))
      = ∑ j ∈ s, conj (c j) * conj (exp (⟪y, t j⟫ * I)) := by
    rw [map_sum]; simp only [map_mul]
  rw [← mul_conj, hconj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← exp_mul_conj_exp_inner y (t i) (t j)]
  ring

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` equals the integral of a
squared modulus. This is the engine behind positive-definiteness: the right-hand side is the
integral of a manifestly nonnegative function. -/
theorem charFun_sum_mul_conj_eq_integral {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j)
      = ((∫ y, normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) ∂μ : ℝ) : ℂ) := by
  -- integrability of the building blocks
  have hterm : ∀ i j : ι,
      Integrable (fun y => c i * conj (c j) * exp (⟪y, t i - t j⟫ * I)) μ :=
    fun i j => (integrable_innerProbChar (t i - t j)).const_mul _
  have hrow : ∀ i : ι,
      Integrable (fun y => ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I)) μ :=
    fun i => integrable_finsetSum s fun j _ => hterm i j
  calc ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j)
      = ∑ i ∈ s, ∑ j ∈ s, ∫ y, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [charFun_apply, integral_const_mul]
    _ = ∑ i ∈ s, ∫ y, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (integral_finsetSum s fun j _ => hterm i j).symm
    _ = ∫ y, ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ :=
        (integral_finsetSum s fun i _ => hrow i).symm
    _ = ∫ y, ((normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) : ℝ) : ℂ) ∂μ :=
        integral_congr_ae (.of_forall fun y => (normSq_finset_sum_exp_eq_sum s c t y).symm)
    _ = ((∫ y, normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) ∂μ : ℝ) : ℂ) := integral_complex_ofReal

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` is a nonnegative real:
`charFun μ` is a positive-definite function. This is `pd_quadratic_form_of_measure`. -/
theorem charFun_sum_mul_conj_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j) := by
  rw [charFun_sum_mul_conj_eq_integral, Complex.zero_le_real]
  exact integral_nonneg fun y => normSq_nonneg _

/-- The `Fintype`-indexed form of positive-definiteness: summing over all of a finite index
type. -/
theorem charFun_fintype_sum_mul_conj_nonneg {ι : Type*} [Fintype ι] (c : ι → ℂ) (t : ι → E) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * charFun μ (t i - t j) :=
  charFun_sum_mul_conj_nonneg Finset.univ c t

end SphericalRiesz.Fourier
