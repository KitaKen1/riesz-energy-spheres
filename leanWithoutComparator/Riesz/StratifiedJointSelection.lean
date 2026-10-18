import Riesz.StratifiedResidualEnergy
import Riesz.ResidualJointSelection

/-! Joint stratified selection for three kernels with constant diagonals.

For a probability measure `μ`, equal-mass cells and a symmetric kernel `k` with constant
diagonal `κ₀`, one point per cell can be chosen with neutralized energy at most `Σ_j ω_j`, where
`ω_j` bounds `κ₀ - k` on the `j`-th cell.  With the linear term
`L(y) = 2 Σ_i k(y, X_i) + 2 n U_μ k(y)` the neutralized energy is the centered sum

`Σ_{j,l} k(z_j,z_l) + 2 Σ_{j,i} k(z_j,X_i) - 2 n Σ_i U_μ k(X_i) - n² ∫∫ k dμ dμ`

of the residual pairs and the residual/foreground cross pairs.  The neutralized energy is linear
in the kernel and in the linear term, so one choice of residual points controls the weighted sum
of three centered sums.  The theorem is independent of the dimension and of the sphere. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz
variable {E : Type*} [MeasurableSpace E]

/-- Stratified residual selection for a kernel with constant diagonal: `NE ≤ Σ_j ω_j`. -/
theorem exists_stratified_residualNeutralizedEnergy_le_diag (μ : Measure E)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (k : E → E → ℝ) (L : E → ℝ)
    (hs : ∀ x y, k x y = k y x) (κ₀ : ℝ) (hdiag : ∀ x, k x x = κ₀) {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set E) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : μ (⋃ j, C j)ᶜ = 0) (hmass : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹)
    (ω : Fin n → ℝ) (hω : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, κ₀-k x y ≤ ω j)
    (hk : ∀ x, Integrable (k x) μ) (hV : Integrable (residualRowPotential μ k) μ)
    (hprod : Integrable (Function.uncurry k) (μ.prod μ)) (hL : Integrable L μ)
    (B : Set E) (hB : μ B = 0) :
    ∃ z : Fin n → E, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧ (∀ j, z j ∉ B) ∧
      residualNeutralizedEnergy μ k L z ≤ ∑ j, ω j := by
  set ν : Fin n → Measure E := fun j => (n:ℝ≥0∞) • μ.restrict (C j) with hνdef
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hP : ∀ j, IsProbabilityMeasure (ν j) := by
    intro j
    constructor
    simp only [hνdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hmass j]
    exact ENNReal.mul_inv_cancel hn0 hnt
  have hA : ∀ j, NullSingletonClass (ν j) := by
    intro j
    constructor
    intro x
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply' (hCm j),
      measure_mono_null inter_subset_left (measure_singleton x), mul_zero]
  have hCc : ∀ j, ν j (C j)ᶜ = 0 := by
    intro j
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j).compl, compl_inter_self, measure_empty, mul_zero]
  have hBν : ∀ j, ν j B = 0 := by
    intro j
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply' (hCm j), measure_mono_null inter_subset_left hB, mul_zero]
  have hI : ∀ f : E → ℝ, Integrable f μ → ∀ j, Integrable f (ν j) :=
    fun f hf j => hf.restrict.smul_measure hnt
  have hprodν : ∀ i j, Integrable (Function.uncurry k) ((ν i).prod (ν j)) := by
    intro i j
    simp only [hνdef]
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict]
    exact (hprod.restrict.smul_measure hnt).smul_measure hnt
  have hk' : ∀ j x, Integrable (k x) (ν j) := fun j x => hI _ (hk x) j
  have hV' : ∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i) := by
    intro i j
    have := hP i; have := hP j
    exact (hprodν i j).integral_prod_left
  have hsym : ∀ i j, cellCross k (ν i) (ν j) = cellCross k (ν j) (ν i) := by
    intro i j
    have := hP i; have := hP j
    unfold cellCross
    rw [integral_integral_swap (hprodν i j)]
    congr 1
    funext y
    congr 1
    funext x
    exact hs x y
  set L' : E → ℝ := fun x => L x-2*(n:ℝ)*residualRowPotential μ k x with hL'def
  have hL'μ : Integrable L' μ := hL.sub (hV.const_mul _)
  obtain ⟨z, hinj, hzC, hzB, hsel⟩ := exists_stratified_selection k hs κ₀ hdiag n ν C ω L' B hP hA
    hCc hBν hω hk' hV' hsym (fun j => hI _ hL'μ j)
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ j, C j := mem_ae_iff.mpr hcover
  have hsum_int : ∀ f : E → ℝ, Integrable f μ →
      (∑ j, ∫ x, f x ∂(ν j)) = (n:ℝ)*∫ x, f x ∂μ := by
    intro f hf
    have hν : ∀ j, (∫ x, f x ∂(ν j)) = (n:ℝ)*∫ x in C j, f x ∂μ := by
      intro j
      simp only [hνdef]
      rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]
    simp_rw [hν]
    rw [← Finset.mul_sum]
    congr 1
    conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
    rw [integral_iUnion hCm (fun i j hij => hdisj hij) hf.integrableOn, tsum_fintype]
  have hcross : (∑ i, ∑ j, cellCross k (ν i) (ν j)) = (n:ℝ)^2*residualBackground μ k := by
    have hinner : ∀ i, (∑ j, cellCross k (ν i) (ν j)) =
        ∫ x, (n:ℝ)*residualRowPotential μ k x ∂(ν i) := by
      intro i
      unfold cellCross
      rw [← integral_finsetSum _ (fun j _ => hV' i j)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact hsum_int (k x) (hk x)
    simp_rw [hinner]
    rw [hsum_int (fun x => (n:ℝ)*residualRowPotential μ k x) (hV.const_mul _), integral_const_mul]
    unfold residualBackground
    ring
  have hlin : (∑ j, ∫ x, L' x ∂(ν j)) =
      (n:ℝ)*(∫ x, L x ∂μ)-2*(n:ℝ)^2*residualBackground μ k := by
    rw [hsum_int L' hL'μ]
    simp only [hL'def]
    rw [integral_sub hL (hV.const_mul _), integral_const_mul]
    unfold residualBackground
    ring
  have hLz : (∑ j, L' (z j)) = (∑ j, L (z j))-2*(n:ℝ)*∑ j, residualRowPotential μ k (z j) := by
    simp only [hL'def, Finset.sum_sub_distrib, Finset.mul_sum]
  have hpe : residualPairEnergy k z = cellPairSum k z := rfl
  rw [hcross, hlin, hLz] at hsel
  unfold residualNeutralizedEnergy
  rw [hpe]
  linarith

/-- The linear term which turns the neutralized energy into the centered pair-plus-cross sum. -/
def residualCrossLinear (μ : Measure E) (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E)
    (n : ℕ) (y : E) : ℝ :=
  2*(∑ i, k y (X i))+2*(n:ℝ)*residualRowPotential μ k y

/-- Residual pairs and residual/foreground cross pairs, centered by their smooth means. -/
def residualCentered (μ : Measure E) (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E)
    {n : ℕ} (z : Fin n → E) : ℝ :=
  residualPairEnergy k z+2*(∑ j, ∑ i, k (z j) (X i))-
    2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i))-(n:ℝ)^2*residualBackground μ k

theorem residualCrossLinear_integrable {μ : Measure E} (k : E → E → ℝ)
    (hs : ∀ x y, k x y = k y x) {ι : Type*} [Fintype ι] (X : ι → E)
    (hk : ∀ x, Integrable (k x) μ) (hV : Integrable (residualRowPotential μ k) μ) (n : ℕ) :
    Integrable (residualCrossLinear μ k X n) μ := by
  have hcol : ∀ i, Integrable (fun y => k y (X i)) μ := fun i =>
    (hk (X i)).congr (Filter.Eventually.of_forall fun y => hs (X i) y)
  exact ((integrable_finsetSum _ fun i _ => hcol i).const_mul 2).add (hV.const_mul _)

/-- Closed form of the neutralized energy with the cross linear term. -/
theorem residualNeutralizedEnergy_crossLinear {μ : Measure E} (k : E → E → ℝ)
    (hs : ∀ x y, k x y = k y x) {ι : Type*} [Fintype ι] (X : ι → E)
    (hk : ∀ x, Integrable (k x) μ) (hV : Integrable (residualRowPotential μ k) μ)
    {n : ℕ} (z : Fin n → E) :
    residualNeutralizedEnergy μ k (residualCrossLinear μ k X n) z = residualCentered μ k X z := by
  have hcol : ∀ i, Integrable (fun y => k y (X i)) μ := fun i =>
    (hk (X i)).congr (Filter.Eventually.of_forall fun y => hs (X i) y)
  have hcolint : ∀ i, (∫ y, k y (X i) ∂μ) = residualRowPotential μ k (X i) := by
    intro i
    unfold residualRowPotential
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hs y (X i))
  have hint : (∫ y, residualCrossLinear μ k X n y ∂μ) =
      2*(∑ i, residualRowPotential μ k (X i))+2*(n:ℝ)*residualBackground μ k := by
    unfold residualCrossLinear
    rw [integral_add ((integrable_finsetSum _ fun i _ => hcol i).const_mul 2) (hV.const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ (fun i _ => hcol i)]
    simp_rw [hcolint]
    rfl
  have hsum : (∑ j, residualCrossLinear μ k X n (z j)) =
      2*(∑ j, ∑ i, k (z j) (X i))+2*(n:ℝ)*(∑ j, residualRowPotential μ k (z j)) := by
    unfold residualCrossLinear
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold residualNeutralizedEnergy residualCentered
  rw [hint, hsum]
  ring

/-- A nonnegative kernel: the centered sum is at least minus its smooth means. -/
theorem residualCentered_ge_of_nonneg {μ : Measure E} (k : E → E → ℝ)
    (hpos : ∀ x y, 0 ≤ k x y) {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ} (z : Fin n → E) :
    -(2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i))+(n:ℝ)^2*residualBackground μ k) ≤
      residualCentered μ k X z := by
  have hp : 0 ≤ residualPairEnergy k z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpos _ _
  have hc : 0 ≤ ∑ j, ∑ i, k (z j) (X i) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hpos _ _
  unfold residualCentered
  linarith

/-- Joint stratified selection: one choice of residual points controls three centered sums. -/
theorem exists_stratified_joint_three (μ : Measure E) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (k₁ k₂ k₃ : E → E → ℝ) (κ₁ κ₂ κ₃ : ℝ) {w₂ w₃ : ℝ}
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hs₁ : ∀ x y, k₁ x y = k₁ y x) (hs₂ : ∀ x y, k₂ x y = k₂ y x)
    (hs₃ : ∀ x y, k₃ x y = k₃ y x)
    (hd₁ : ∀ x, k₁ x x = κ₁) (hd₂ : ∀ x, k₂ x x = κ₂) (hd₃ : ∀ x, k₃ x x = κ₃)
    (hpos₁ : ∀ x y, 0 ≤ k₁ x y) (hpos₂ : ∀ x y, 0 ≤ k₂ x y) (hpos₃ : ∀ x y, 0 ≤ k₃ x y)
    (hk₁ : ∀ x, Integrable (k₁ x) μ) (hk₂ : ∀ x, Integrable (k₂ x) μ)
    (hk₃ : ∀ x, Integrable (k₃ x) μ)
    (hV₁ : Integrable (residualRowPotential μ k₁) μ)
    (hV₂ : Integrable (residualRowPotential μ k₂) μ)
    (hV₃ : Integrable (residualRowPotential μ k₃) μ)
    (hprod₁ : Integrable (Function.uncurry k₁) (μ.prod μ))
    (hprod₂ : Integrable (Function.uncurry k₂) (μ.prod μ))
    (hprod₃ : Integrable (Function.uncurry k₃) (μ.prod μ))
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (X₁ : ι₁ → E) (X₂ : ι₂ → E) (X₃ : ι₃ → E)
    {n : ℕ} (hn : 0 < n) (C : Fin n → Set E) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : μ (⋃ j, C j)ᶜ = 0) (hmass : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹)
    (B : Set E) (hB : μ B = 0) :
    ∃ z : Fin n → E, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧ (∀ j, z j ∉ B) ∧
      residualCentered μ k₁ X₁ z+w₂*residualCentered μ k₂ X₂ z+w₃*residualCentered μ k₃ X₃ z ≤
        (n:ℝ)*(κ₁+w₂*κ₂+w₃*κ₃) := by
  set L₁ := residualCrossLinear μ k₁ X₁ n with hL₁def
  set L₂ := residualCrossLinear μ k₂ X₂ n with hL₂def
  set L₃ := residualCrossLinear μ k₃ X₃ n with hL₃def
  have hL₁ : Integrable L₁ μ := residualCrossLinear_integrable k₁ hs₁ X₁ hk₁ hV₁ n
  have hL₂ : Integrable L₂ μ := residualCrossLinear_integrable k₂ hs₂ X₂ hk₂ hV₂ n
  have hL₃ : Integrable L₃ μ := residualCrossLinear_integrable k₃ hs₃ X₃ hk₃ hV₃ n
  set k₁₂ : E → E → ℝ := fun x y => k₁ x y+w₂*k₂ x y with hk₁₂def
  set L₁₂ : E → ℝ := fun x => L₁ x+w₂*L₂ x with hL₁₂def
  have hk₁₂ : ∀ x, Integrable (k₁₂ x) μ := fun x => (hk₁ x).add ((hk₂ x).const_mul w₂)
  have hV₁₂ : Integrable (residualRowPotential μ k₁₂) μ :=
    residualRowPotential_add_smul_integrable k₁ k₂ w₂ hk₁ hk₂ hV₁ hV₂
  have hL₁₂ : Integrable L₁₂ μ := hL₁.add (hL₂.const_mul w₂)
  set k : E → E → ℝ := fun x y => k₁₂ x y+w₃*k₃ x y with hkdef
  set L : E → ℝ := fun x => L₁₂ x+w₃*L₃ x with hLdef
  have hk : ∀ x, Integrable (k x) μ := fun x => (hk₁₂ x).add ((hk₃ x).const_mul w₃)
  have hV : Integrable (residualRowPotential μ k) μ :=
    residualRowPotential_add_smul_integrable k₁₂ k₃ w₃ hk₁₂ hk₃ hV₁₂ hV₃
  have hL : Integrable L μ := hL₁₂.add (hL₃.const_mul w₃)
  have hprod : Integrable (Function.uncurry k) (μ.prod μ) :=
    (hprod₁.add (hprod₂.const_mul w₂)).add (hprod₃.const_mul w₃)
  have hpos : ∀ x y, 0 ≤ k x y := fun x y =>
    add_nonneg (add_nonneg (hpos₁ x y) (mul_nonneg hw₂ (hpos₂ x y))) (mul_nonneg hw₃ (hpos₃ x y))
  obtain ⟨z, hinj, hzC, hzB, hne⟩ := exists_stratified_residualNeutralizedEnergy_le_diag μ k L
    (fun x y => by simp only [hkdef, hk₁₂def]; rw [hs₁ x y, hs₂ x y, hs₃ x y])
    (κ₁+w₂*κ₂+w₃*κ₃) (fun x => by simp only [hkdef, hk₁₂def]; rw [hd₁ x, hd₂ x, hd₃ x])
    hn C hCm hdisj hcover hmass (fun _ => κ₁+w₂*κ₂+w₃*κ₃)
    (fun j x _ y _ => by linarith [hpos x y]) hk hV hprod hL B hB
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  have h₁ := residualNeutralizedEnergy_add_smul k₁₂ k₃ L₁₂ L₃ w₃ hk₁₂ hk₃ hV₁₂ hV₃ hL₁₂ hL₃ z
  have h₂ := residualNeutralizedEnergy_add_smul k₁ k₂ L₁ L₂ w₂ hk₁ hk₂ hV₁ hV₂ hL₁ hL₂ z
  have hc₁ := residualNeutralizedEnergy_crossLinear k₁ hs₁ X₁ hk₁ hV₁ z
  have hc₂ := residualNeutralizedEnergy_crossLinear k₂ hs₂ X₂ hk₂ hV₂ z
  have hc₃ := residualNeutralizedEnergy_crossLinear k₃ hs₃ X₃ hk₃ hV₃ z
  have hsum : (∑ _j : Fin n, (κ₁+w₂*κ₂+w₃*κ₃)) = (n:ℝ)*(κ₁+w₂*κ₂+w₃*κ₃) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hne
  rw [← hc₁, ← hc₂, ← hc₃, ← h₂, ← h₁]
  exact hne

end SphericalRiesz
