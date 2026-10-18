import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! Sequential first moments for the neutralized residual energy.
The kernel is symmetric with zero diagonal, as is the actual inverse-fourth
kernel. No positive-definiteness or iid product measure is used. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalRiesz
variable {E : Type*} [MeasurableSpace E]

def residualPairEnergy (k : E → E → ℝ) {n : ℕ} (X : Fin n → E) : ℝ :=
  ∑ i, ∑ j, k (X i) (X j)

def residualRowPotential (μ : Measure E) (k : E → E → ℝ) (x : E) : ℝ :=
  ∫ y, k x y ∂μ

def residualBackground (μ : Measure E) (k : E → E → ℝ) : ℝ :=
  ∫ x, residualRowPotential μ k x ∂μ

def residualSelectionPotential (μ : Measure E) (k : E → E → ℝ) (L : E → ℝ)
    {n : ℕ} (X : Fin n → E) : ℝ :=
  residualPairEnergy k X - 2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i)) +
    ((n:ℝ)^2+(n:ℝ))*residualBackground μ k + (∑ i, L (X i)) -
    (n:ℝ)*(∫ x, L x ∂μ)

def residualStep (μ : Measure E) (k : E → E → ℝ) (L : E → ℝ)
    {n : ℕ} (X : Fin n → E) (x : E) : ℝ :=
  residualSelectionPotential μ k L X + 2*(∑ i, k (X i) x) -
    2*(∑ i, residualRowPotential μ k (X i)) -
    2*((n:ℝ)+1)*residualRowPotential μ k x +
    2*((n:ℝ)+1)*residualBackground μ k + L x - (∫ y, L y ∂μ)

omit [MeasurableSpace E] in
theorem residualPairEnergy_cons (k : E → E → ℝ)
    (hs : ∀ x y, k x y = k y x) (h0 : ∀ x, k x x = 0)
    {n : ℕ} (X : Fin n → E) (x : E) :
    residualPairEnergy k (Fin.cons x X) = residualPairEnergy k X +
      2*(∑ i, k (X i) x) := by
  simp only [residualPairEnergy,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,h0,
    zero_add,Finset.sum_add_distrib]
  simp_rw [hs x]
  ring

theorem residualSelectionPotential_cons (μ : Measure E) (k : E → E → ℝ)
    (L : E → ℝ) (hs : ∀ x y, k x y = k y x) (h0 : ∀ x, k x x = 0)
    {n : ℕ} (X : Fin n → E) (x : E) :
    residualSelectionPotential μ k L (Fin.cons x X) = residualStep μ k L X x := by
  unfold residualStep residualSelectionPotential
  rw [residualPairEnergy_cons k hs h0]
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Nat.cast_add,Nat.cast_one]
  ring

variable {μ : Measure E} [IsProbabilityMeasure μ]

theorem residualStep_integrable (k : E → E → ℝ) (L : E → ℝ)
    (hk : ∀ x, Integrable (k x) μ)
    (hV : Integrable (residualRowPotential μ k) μ) (hL : Integrable L μ)
    {n : ℕ} (X : Fin n → E) : Integrable (residualStep μ k L X) μ := by
  have hsum : Integrable (fun x => ∑ i, k (X i) x) μ :=
    integrable_finsetSum _ (fun i _ => hk (X i))
  exact (((((integrable_const _).add (hsum.const_mul 2)).sub
    (integrable_const _)).sub (hV.const_mul _)).add (integrable_const _)).add hL
    |>.sub (integrable_const _)

theorem residualStep_integral (k : E → E → ℝ) (L : E → ℝ)
    (hk : ∀ x, Integrable (k x) μ)
    (hV : Integrable (residualRowPotential μ k) μ) (hL : Integrable L μ)
    {n : ℕ} (X : Fin n → E) :
    (∫ x, residualStep μ k L X x ∂μ) = residualSelectionPotential μ k L X := by
  have hsum : Integrable (fun x => ∑ i, k (X i) x) μ :=
    integrable_finsetSum _ (fun i _ => hk (X i))
  have h1 : Integrable (fun x => residualSelectionPotential μ k L X +
      2*(∑ i, k (X i) x)) μ := (integrable_const _).add
    (hsum.const_mul 2)
  have h2 : Integrable (fun x => residualSelectionPotential μ k L X +
      2*(∑ i, k (X i) x)-2*(∑ i, residualRowPotential μ k (X i))) μ :=
    h1.sub (integrable_const _)
  have h3 : Integrable (fun x => residualSelectionPotential μ k L X +
      2*(∑ i, k (X i) x)-2*(∑ i, residualRowPotential μ k (X i))-
      2*((n:ℝ)+1)*residualRowPotential μ k x) μ := h2.sub (hV.const_mul _)
  have h4 : Integrable (fun x => residualSelectionPotential μ k L X +
      2*(∑ i, k (X i) x)-2*(∑ i, residualRowPotential μ k (X i))-
      2*((n:ℝ)+1)*residualRowPotential μ k x+
      2*((n:ℝ)+1)*residualBackground μ k) μ := h3.add (integrable_const _)
  have h5 : Integrable (fun x => residualSelectionPotential μ k L X +
      2*(∑ i, k (X i) x)-2*(∑ i, residualRowPotential μ k (X i))-
      2*((n:ℝ)+1)*residualRowPotential μ k x+
      2*((n:ℝ)+1)*residualBackground μ k+L x) μ := h4.add hL
  unfold residualStep
  rw [integral_sub h5 (integrable_const _),integral_add h4 hL,
    integral_add h3 (integrable_const _),integral_sub h2 (hV.const_mul _),
    integral_sub h1 (integrable_const _),
    integral_add (integrable_const _) (hsum.const_mul 2)]
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul,
    integral_finsetSum _ (fun i _ => hk (X i)),residualRowPotential,residualBackground]
  ring

theorem exists_residualSelectionPotential_nonpos [NullSingletonClass μ]
    (k : E → E → ℝ) (L : E → ℝ)
    (hs : ∀ x y, k x y = k y x) (h0 : ∀ x, k x x = 0)
    (hk : ∀ x, Integrable (k x) μ)
    (hV : Integrable (residualRowPotential μ k) μ) (hL : Integrable L μ)
    (B : Set E) (hB : μ B = 0) (r : ℕ) :
    ∃ X : Fin r → E, Function.Injective X ∧ (∀ i, X i ∉ B) ∧
      residualSelectionPotential μ k L X ≤ 0 := by
  classical
  induction r with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · simp [residualSelectionPotential,residualPairEnergy]
  | succ r ih =>
    obtain ⟨X,hX,hXB,hP⟩ := ih
    have hR : μ (range X) = 0 := (finite_range X).measure_zero μ
    have hBR : μ (B ∪ range X) = 0 := measure_union_null hB hR
    obtain ⟨x,hx,hstep⟩ := exists_notMem_null_le_integral
      (residualStep_integrable k L hk hV hL X) hBR
    rw [residualStep_integral k L hk hV hL X] at hstep
    refine ⟨Fin.cons x X,Fin.cons_injective_of_injective
      (fun hxR => hx (Or.inr hxR)) hX,?_,?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact fun hxB => hx (Or.inl hxB)
      | succ j => exact hXB j
    · rw [residualSelectionPotential_cons μ k L hs h0]
      exact hstep.trans hP

def residualNeutralizedEnergy (μ : Measure E) (k : E → E → ℝ) (L : E → ℝ)
    {n : ℕ} (X : Fin n → E) : ℝ :=
  residualPairEnergy k X - 2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i)) +
    (n:ℝ)^2*residualBackground μ k + (∑ i, L (X i)) -
    (n:ℝ)*(∫ x, L x ∂μ)

omit [IsProbabilityMeasure μ] in
theorem residualNeutralizedEnergy_eq (k : E → E → ℝ) (L : E → ℝ)
    {n : ℕ} (X : Fin n → E) :
    residualNeutralizedEnergy μ k L X = residualSelectionPotential μ k L X -
      (n:ℝ)*residualBackground μ k := by
  unfold residualNeutralizedEnergy residualSelectionPotential
  ring

theorem exists_residualNeutralizedEnergy_nonpos [NullSingletonClass μ]
    (k : E → E → ℝ) (L : E → ℝ)
    (hs : ∀ x y, k x y = k y x) (h0 : ∀ x, k x x = 0)
    (hpos : ∀ x y, 0 ≤ k x y) (hk : ∀ x, Integrable (k x) μ)
    (hV : Integrable (residualRowPotential μ k) μ) (hL : Integrable L μ)
    (B : Set E) (hB : μ B = 0) (r : ℕ) :
    ∃ X : Fin r → E, Function.Injective X ∧ (∀ i, X i ∉ B) ∧
      residualNeutralizedEnergy μ k L X ≤ -(r:ℝ)*residualBackground μ k ∧
      residualNeutralizedEnergy μ k L X ≤ 0 := by
  obtain ⟨X,hX,hXB,hP⟩ := exists_residualSelectionPotential_nonpos
    k L hs h0 hk hV hL B hB r
  have hI : 0 ≤ residualBackground μ k := integral_nonneg
    (fun x => integral_nonneg (hpos x))
  refine ⟨X,hX,hXB,?_,?_⟩
  · rw [residualNeutralizedEnergy_eq]
    linarith
  · rw [residualNeutralizedEnergy_eq]
    nlinarith [mul_nonneg (Nat.cast_nonneg r) hI]

end SphericalRiesz
