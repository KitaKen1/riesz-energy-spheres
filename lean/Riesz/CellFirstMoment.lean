import Mathlib

/-! Per-cell first-moment selection (stage NEG, second half).

Points `z_0, …, z_{n-1}` are chosen one at a time, the `i`-th from its own probability measure
`ν_i` (typically the normalized restriction of the sphere probability to the `i`-th cell of a
stratification) and inside its own cell `C_i`. For a symmetric kernel `k` and a linear term `L`
the conditional expectation of `Σ_{i,j} k(z_i, z_j) + Σ_i L(z_i)` is a martingale along the
choices, so there is a deterministic choice whose value does not exceed the expectation
`Σ_i ∫ k(x,x) dν_i + 2 Σ_{i<j} ∫∫ k dν_i dν_j + Σ_i ∫ L dν_i` (here written recursively). This
generalizes the single-measure sequential selection: the variance terms of a stratified choice
only involve the diagonal and the cross means of *different* cells. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
variable {E : Type*} [MeasurableSpace E]

/-- The full double sum `Σ_{i,j} k(z_i, z_j)`. -/
def cellPairSum (k : E → E → ℝ) {n : ℕ} (z : Fin n → E) : ℝ :=
  ∑ i, ∑ j, k (z i) (z j)

/-- The cross mean `∫∫ k(x,y) dν(y) dμ(x)`. -/
def cellCross (k : E → E → ℝ) (μ ν : Measure E) : ℝ :=
  ∫ x, (∫ y, k x y ∂ν) ∂μ

/-- The expectation of the quadratic part, recursively over the cells. -/
def cellBoundK (k : E → E → ℝ) : (n : ℕ) → (Fin n → Measure E) → ℝ
  | 0, _ => 0
  | n+1, ν => (∫ x, k x x ∂(ν 0)) + 2*(∑ j : Fin n, cellCross k (ν 0) (ν j.succ)) +
      cellBoundK k n (fun j => ν j.succ)

omit [MeasurableSpace E] in
theorem cellPairSum_cons (k : E → E → ℝ) (hs : ∀ x y, k x y = k y x) {n : ℕ}
    (z : Fin n → E) (x : E) :
    cellPairSum k (Fin.cons x z : Fin (n+1) → E) =
      k x x+2*(∑ j, k x (z j))+cellPairSum k z := by
  simp only [cellPairSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_add_distrib]
  have h : ∑ i : Fin n, k (z i) x = ∑ i : Fin n, k x (z i) :=
    Finset.sum_congr rfl (fun i _ => hs _ _)
  rw [h]
  ring

/-- Per-cell first-moment selection. -/
theorem exists_cell_selection (k : E → E → ℝ) (hs : ∀ x y, k x y = k y x) :
    ∀ (n : ℕ) (ν : Fin n → Measure E) (C : Fin n → Set E) (L : E → ℝ) (B : Set E),
      (∀ i, IsProbabilityMeasure (ν i)) → (∀ i, NullSingletonClass (ν i)) →
      (∀ i, ν i (C i)ᶜ = 0) → (∀ i, ν i B = 0) →
      (∀ i x, Integrable (k x) (ν i)) →
      (∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i)) →
      (∀ i, Integrable (fun x => k x x) (ν i)) →
      (∀ i, Integrable L (ν i)) →
      ∃ z : Fin n → E, Function.Injective z ∧ (∀ i, z i ∈ C i) ∧ (∀ i, z i ∉ B) ∧
        cellPairSum k z+∑ i, L (z i) ≤ cellBoundK k n ν+∑ i, ∫ x, L x ∂(ν i) := by
  intro n
  induction n with
  | zero =>
    intro ν C L B _ _ _ _ _ _ _ _
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp [cellPairSum, cellBoundK]
  | succ n ih =>
    intro ν C L B hP hA hC hB hk hV hD hL
    have := hP 0
    -- the first point
    set V : E → ℝ := fun x => k x x+2*(∑ j : Fin n, ∫ y, k x y ∂(ν j.succ))+L x with hVdef
    have hVi : Integrable V (ν 0) :=
      ((hD 0).add ((integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun (j : Fin n) _ => hV 0 j.succ)).const_mul 2)).add (hL 0)
    have hVint : (∫ x, V x ∂(ν 0)) = (∫ x, k x x ∂(ν 0))+
        2*(∑ j : Fin n, cellCross k (ν 0) (ν j.succ))+∫ x, L x ∂(ν 0) := by
      have h1 := (hD 0)
      have h2 : Integrable (fun x => 2*(∑ j : Fin n, ∫ y, k x y ∂(ν j.succ))) (ν 0) :=
        (integrable_finsetSum (Finset.univ : Finset (Fin n))
          (fun (j : Fin n) _ => hV 0 j.succ)).const_mul (2:ℝ)
      have h12 : Integrable (fun x => k x x+2*(∑ j : Fin n, ∫ y, k x y ∂(ν j.succ))) (ν 0) :=
        h1.add h2
      change (∫ x, (k x x+2*(∑ j : Fin n, ∫ y, k x y ∂(ν j.succ))+L x) ∂(ν 0)) = _
      rw [integral_add h12 (hL 0), integral_add h1 h2, integral_const_mul,
        integral_finsetSum (Finset.univ : Finset (Fin n)) (fun (j : Fin n) _ => hV 0 j.succ)]
      rfl
    have hnull : ν 0 (B ∪ (C 0)ᶜ) = 0 := measure_union_null (hB 0) (hC 0)
    obtain ⟨x₀, hx₀, hVx⟩ := exists_notMem_null_le_integral hVi hnull
    have hx₀B : x₀ ∉ B := fun h => hx₀ (Or.inl h)
    have hx₀C : x₀ ∈ C 0 := by
      by_contra h
      exact hx₀ (Or.inr h)
    -- the remaining points
    obtain ⟨z', hinj, hzC, hzB, hz⟩ := ih (fun j => ν j.succ) (fun j => C j.succ)
      (fun y => L y+2*k x₀ y) (B ∪ {x₀}) (fun j => hP j.succ) (fun j => hA j.succ)
      (fun j => hC j.succ)
      (fun j => by
        have := hA j.succ
        exact measure_union_null (hB j.succ) (measure_singleton x₀))
      (fun j x => hk j.succ x) (fun i j => hV i.succ j.succ) (fun j => hD j.succ)
      (fun j => (hL j.succ).add ((hk j.succ x₀).const_mul 2))
    refine ⟨Fin.cons x₀ z', Fin.cons_injective_of_injective (fun hm => ?_) hinj, ?_, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := hm
      exact hzB j (Or.inr (by simp [hj]))
    · intro i
      cases i using Fin.cases with
      | zero => exact hx₀C
      | succ j => exact hzC j
    · intro i
      cases i using Fin.cases with
      | zero => exact hx₀B
      | succ j => exact fun h => hzB j (Or.inl h)
    · have hLint : ∀ j : Fin n, (∫ y, (L y+2*k x₀ y) ∂(ν j.succ)) =
          (∫ y, L y ∂(ν j.succ))+2*∫ y, k x₀ y ∂(ν j.succ) := by
        intro j
        rw [integral_add (hL j.succ) ((hk j.succ x₀).const_mul 2), integral_const_mul]
      simp only [hLint, Finset.sum_add_distrib, ← Finset.mul_sum] at hz
      rw [cellPairSum_cons k hs, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      have hbound : cellBoundK k (n+1) ν = (∫ x, k x x ∂(ν 0))+
          2*(∑ j : Fin n, cellCross k (ν 0) (ν j.succ))+cellBoundK k n (fun j => ν j.succ) := rfl
      rw [hbound]
      have hV0 : V x₀ = k x₀ x₀+2*(∑ j : Fin n, ∫ y, k x₀ y ∂(ν j.succ))+L x₀ := rfl
      rw [hVint] at hVx
      linarith

/-- Closed form of the expectation for a symmetric family of cross means:
`Σ_i ∫ k(x,x) dν_i + Σ_{i,j} ⟨ν_i, k ν_j⟩ - Σ_i ⟨ν_i, k ν_i⟩`. -/
theorem cellBoundK_eq_sum (k : E → E → ℝ) :
    ∀ (n : ℕ) (ν : Fin n → Measure E),
      (∀ i j, cellCross k (ν i) (ν j) = cellCross k (ν j) (ν i)) →
      cellBoundK k n ν = (∑ i, ∫ x, k x x ∂(ν i))+(∑ i, ∑ j, cellCross k (ν i) (ν j))-
        ∑ i, cellCross k (ν i) (ν i) := by
  intro n
  induction n with
  | zero => intro ν _; simp [cellBoundK]
  | succ n ih =>
    intro ν hsym
    have h := ih (fun j => ν j.succ) (fun i j => hsym i.succ j.succ)
    have hs0 : ∑ i : Fin n, cellCross k (ν i.succ) (ν 0) = ∑ i : Fin n, cellCross k (ν 0) (ν i.succ) :=
      Finset.sum_congr rfl (fun i _ => hsym i.succ 0)
    show (∫ x, k x x ∂(ν 0))+2*(∑ j : Fin n, cellCross k (ν 0) (ν j.succ))+
      cellBoundK k n (fun j => ν j.succ) = _
    rw [h]
    simp only [Fin.sum_univ_succ, Finset.sum_add_distrib]
    rw [hs0]
    ring

/-- The variance of a stratified choice: if `k(x,x) = κ₀` and `κ₀ - k(x,y) ≤ ω_i` on the `i`-th
cell, the expectation exceeds the smooth cross term `Σ_{i,j} ⟨ν_i, k ν_j⟩` by at most `Σ_i ω_i`. -/
theorem cellBoundK_le_cross_add (k : E → E → ℝ) (κ₀ : ℝ) (hdiag : ∀ x, k x x = κ₀) (n : ℕ)
    (ν : Fin n → Measure E) (C : Fin n → Set E) (ω : Fin n → ℝ)
    (hP : ∀ i, IsProbabilityMeasure (ν i)) (hC : ∀ i, ν i (C i)ᶜ = 0)
    (hω : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, κ₀-k x y ≤ ω i)
    (hk : ∀ i x, Integrable (k x) (ν i))
    (hV : ∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i))
    (hsym : ∀ i j, cellCross k (ν i) (ν j) = cellCross k (ν j) (ν i)) :
    cellBoundK k n ν ≤ (∑ i, ∑ j, cellCross k (ν i) (ν j))+∑ i, ω i := by
  rw [cellBoundK_eq_sum k n ν hsym]
  have hself : ∀ i, κ₀-ω i ≤ cellCross k (ν i) (ν i) := by
    intro i
    have := hP i
    have hae : ∀ᵐ x ∂(ν i), x ∈ C i := by
      rw [ae_iff]
      simpa [Set.compl_def] using hC i
    have hin : ∀ᵐ x ∂(ν i), κ₀-ω i ≤ ∫ y, k x y ∂(ν i) := by
      filter_upwards [hae] with x hx
      have h := integral_mono_ae (integrable_const (κ₀-ω i) (μ := ν i)) (hk i x)
        (by
          filter_upwards [hae] with y hy
          linarith [hω i x hx y hy])
      simpa using h
    have h := integral_mono_ae (integrable_const (κ₀-ω i) (μ := ν i)) (hV i i) hin
    simpa [cellCross] using h
  have hd : ∀ i, (∫ x, k x x ∂(ν i)) = κ₀ := by
    intro i
    have := hP i
    simp [hdiag]
  simp only [hd]
  have hsum : (∑ i : Fin n, (κ₀-ω i)) ≤ ∑ i, cellCross k (ν i) (ν i) :=
    Finset.sum_le_sum (fun i _ => hself i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum ⊢
  linarith

/-- Stratified selection: one point per cell, value at most the smooth cross term plus the
linear means plus the cell variances `Σ_i ω_i`. -/
theorem exists_stratified_selection (k : E → E → ℝ) (hs : ∀ x y, k x y = k y x) (κ₀ : ℝ)
    (hdiag : ∀ x, k x x = κ₀) (n : ℕ) (ν : Fin n → Measure E) (C : Fin n → Set E)
    (ω : Fin n → ℝ) (L : E → ℝ) (B : Set E)
    (hP : ∀ i, IsProbabilityMeasure (ν i)) (hA : ∀ i, NullSingletonClass (ν i))
    (hC : ∀ i, ν i (C i)ᶜ = 0) (hB : ∀ i, ν i B = 0)
    (hω : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, κ₀-k x y ≤ ω i)
    (hk : ∀ i x, Integrable (k x) (ν i))
    (hV : ∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i))
    (hsym : ∀ i j, cellCross k (ν i) (ν j) = cellCross k (ν j) (ν i))
    (hL : ∀ i, Integrable L (ν i)) :
    ∃ z : Fin n → E, Function.Injective z ∧ (∀ i, z i ∈ C i) ∧ (∀ i, z i ∉ B) ∧
      cellPairSum k z+∑ i, L (z i) ≤
        (∑ i, ∑ j, cellCross k (ν i) (ν j))+(∑ i, ∫ x, L x ∂(ν i))+∑ i, ω i := by
  have hD : ∀ i, Integrable (fun x => k x x) (ν i) := by
    intro i
    have := hP i
    simp only [hdiag]
    exact integrable_const κ₀
  obtain ⟨z, h1, h2, h3, h4⟩ := exists_cell_selection k hs n ν C L B hP hA hC hB hk hV hD hL
  have h5 := cellBoundK_le_cross_add k κ₀ hdiag n ν C ω hP hC hω hk hV hsym
  exact ⟨z, h1, h2, h3, by linarith⟩

#print axioms cellPairSum_cons
#print axioms exists_cell_selection
#print axioms cellBoundK_eq_sum
#print axioms cellBoundK_le_cross_add
#print axioms exists_stratified_selection

end SphericalRiesz
