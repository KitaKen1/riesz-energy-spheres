import Riesz.CellFirstMoment
import Riesz.ResidualFirstMoment

/-! Stratified residual selection in neutralized form (stage NEG, second half).

For a probability measure `μ` and cells `C_0, …, C_{n-1}` of mass exactly `1/n` covering
`μ`-almost everything, one point per cell chosen from `n μ|_{C_j}` (per-cell first moment with the
linear term `L - 2n U_μ`) satisfies `residualNeutralizedEnergy μ k L z ≤ Σ_j ω_j`, where `ω_j`
bounds `-k(x,y)` on `C_j` (`k` symmetric with zero diagonal, `U_μ` its row potential). For a
nonnegative kernel all `ω_j = 0`: the stratified choice has the same `NE ≤ 0` as the sequential
i.i.d. choice, so it can replace it in the joint residual assemblies of the `s = 4` route, while
for the subtracted macroscopic kernel the `ω_j` are the cell variances `c d_j² w^(p+2)/(p+2)`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz
variable {E : Type*} [MeasurableSpace E]

/-- Stratified residual selection: `NE ≤ Σ_j ω_j`. -/
theorem exists_stratified_residualNeutralizedEnergy_le (μ : Measure E) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (k : E → E → ℝ) (L : E → ℝ) (hs : ∀ x y, k x y = k y x)
    (h0 : ∀ x, k x x = 0) {n : ℕ} (hn : 0 < n) (C : Fin n → Set E)
    (hCm : ∀ j, MeasurableSet (C j)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : μ (⋃ j, C j)ᶜ = 0) (hmass : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹)
    (ω : Fin n → ℝ) (hω : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, 0-k x y ≤ ω j)
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
  -- integrability transfers from `μ` to the cell measures
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
  -- the linear term
  set L' : E → ℝ := fun x => L x-2*(n:ℝ)*residualRowPotential μ k x with hL'def
  have hL'μ : Integrable L' μ := hL.sub (hV.const_mul _)
  obtain ⟨z, hinj, hzC, hzB, hsel⟩ := exists_stratified_selection k hs 0 h0 n ν C ω L' B hP hA
    hCc hBν hω hk' hV' hsym (fun j => hI _ hL'μ j)
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  -- identify the expectation
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

/-- For a nonnegative kernel with zero diagonal the stratified choice has `NE ≤ 0`. -/
theorem exists_stratified_residualNeutralizedEnergy_nonpos (μ : Measure E)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (k : E → E → ℝ) (L : E → ℝ)
    (hs : ∀ x y, k x y = k y x) (h0 : ∀ x, k x x = 0) (hpos : ∀ x y, 0 ≤ k x y) {n : ℕ}
    (hn : 0 < n) (C : Fin n → Set E) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hcover : μ (⋃ j, C j)ᶜ = 0)
    (hmass : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹) (hk : ∀ x, Integrable (k x) μ)
    (hV : Integrable (residualRowPotential μ k) μ)
    (hprod : Integrable (Function.uncurry k) (μ.prod μ)) (hL : Integrable L μ)
    (B : Set E) (hB : μ B = 0) :
    ∃ z : Fin n → E, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧ (∀ j, z j ∉ B) ∧
      residualNeutralizedEnergy μ k L z ≤ 0 := by
  obtain ⟨z, h1, h2, h3, h4⟩ := exists_stratified_residualNeutralizedEnergy_le μ k L hs h0 hn C
    hCm hdisj hcover hmass (fun _ => 0) (fun j x _ y _ => by linarith [hpos x y]) hk hV hprod hL
    B hB
  exact ⟨z, h1, h2, h3, by simpa using h4⟩

#print axioms exists_stratified_residualNeutralizedEnergy_le
#print axioms exists_stratified_residualNeutralizedEnergy_nonpos

end SphericalRiesz
