import Riesz.StratifiedJointSelection
import Riesz.LeechForegroundBudget24

/-! One joint residual choice on S²⁴ for the small-alpha budget, the short-range tail and one
Gaussian window.

The residual region is the union of measurable pairwise disjoint cells of probability `1/N`.
One point is chosen in every cell, injectively and away from the foreground points, so that the
weighted sum of three centered quantities is at most `n (4^q/q + w₃)`:

* the small-alpha budget kernel, with the residual/foreground cross pairs, centered by its
  smooth mean `2N Σ_i ∫_R κ(X_i,·) dσ + N² ∫_R∫_R κ`;
* the short-range kernel, with the cross pairs, centered by the bound `(2M+n)/(11-p)`;
* one Gaussian window among the residual points, centered by the bound `n N B(t₀)`.

No foreground estimate, configuration or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

/-- Residual pair sum plus twice the residual/foreground cross sum. -/
def residualCrossSum {E : Type*} (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ}
    (z : Fin n → E) : ℝ :=
  cellPairSum k z+2*(∑ j, ∑ i, k (z j) (X i))

theorem residualCentered_eq_crossSum {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (k : E → E → ℝ) {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ} (z : Fin n → E) :
    residualCentered μ k X z = residualCrossSum k X z-
      (2*(n:ℝ)*(∑ i, residualRowPotential μ k (X i))+(n:ℝ)^2*residualBackground μ k) := by
  unfold residualCentered residualCrossSum residualPairEnergy cellPairSum
  ring

theorem residualCrossSum_nonneg {E : Type*} (k : E → E → ℝ) (hpos : ∀ x y, 0 ≤ k x y)
    {ι : Type*} [Fintype ι] (X : ι → E) {n : ℕ} (z : Fin n → E) :
    0 ≤ residualCrossSum k X z := by
  unfold residualCrossSum cellPairSum
  have h1 : 0 ≤ ∑ i, ∑ j, k (z i) (z j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpos _ _
  have h2 : 0 ≤ ∑ j, ∑ i, k (z j) (X i) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hpos _ _
  linarith

/-- One joint residual choice for three kernels on S²⁴. -/
theorem exists_leech_joint_residual24 {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {q p t₀ w₂ w₃ : ℝ} (hq : 0 < q) (hp0 : -1 ≤ p) (hp : p < 11) (ht₀ : 0 ≤ t₀)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    {ι : Type*} [Fintype ι] (X : ι → SphereD 24)
    (C : Fin n → Set (SphereD 24)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → SphereD 24, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧
      (∀ j, z j ∉ range X) ∧
      (residualCrossSum (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q) X z-
        (2*(N:ℝ)*(∑ i, ∫ y in ⋃ j, C j,
            smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (X i) y
              ∂(sphereProbabilityD 24))+
          (N:ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
            smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q y y'
              ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))))+
      w₂*(residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z-
        (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p))+
      w₃*(cellPairSum (sphereGaussianKernel24 t₀) z-
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀)) ≤
      (n:ℝ)*(4^q/q+w₃) := by
  classical
  have hc : 0 < sphereGaussianDensityFactor24 N := sphereGaussianDensityFactor24_pos hN
  have hRm : MeasurableSet (⋃ j, C j) := MeasurableSet.iUnion hCm
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (N:ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h11 : 0 < 11-p := by linarith
  have h11ne : (11:ℝ)-p ≠ 0 := h11.ne'
  have hnne : (n:ℝ) ≠ 0 := hnR.ne'
  have hNne : (N:ℝ) ≠ 0 := hNR.ne'
  have hσR : (sphereProbabilityD 24) (⋃ j, C j) = (n:ℝ≥0∞)*(N:ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hR0 : (sphereProbabilityD 24) (⋃ j, C j) ≠ 0 := by
    rw [hσR]
    exact mul_ne_zero hn0 (ENNReal.inv_ne_zero.mpr hNt)
  have hinv : ((sphereProbabilityD 24) (⋃ j, C j))⁻¹ = (N:ℝ≥0∞)*(n:ℝ≥0∞)⁻¹ := by
    rw [hσR, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm]
  have htoReal : (((sphereProbabilityD 24) (⋃ j, C j))⁻¹).toReal = (N:ℝ)/(n:ℝ) := by
    rw [hinv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  -- the residual probability measure, as a variable with its defining equation
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (SphereD 24), μ = sphereRestrictedProbability24 (⋃ j, C j) :=
    ⟨_, rfl⟩
  haveI hμP : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact sphereRestrictedProbability24_probability _ hR0
  haveI hμA : NullSingletonClass μ := by
    rw [hμdef]
    infer_instance
  have hμC : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    have hsub : C j ∩ ⋃ i, C i = C j := inter_eq_left.mpr (subset_iUnion C j)
    rw [hμdef]
    simp only [sphereRestrictedProbability24, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), hsub, hCmass j, hinv, mul_comm (N:ℝ≥0∞) _, mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, mul_one]
  have hcover : μ (⋃ j, C j)ᶜ = 0 := by
    rw [hμdef]
    exact sphereRestrictedProbability24_compl _ hRm
  have hB : μ (range X) = 0 := (finite_range X).measure_zero μ
  have hint_eq : ∀ f : SphereD 24 → ℝ,
      (∫ y, f y ∂μ) = (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, f y ∂(sphereProbabilityD 24) := by
    intro f
    rw [hμdef]
    simp only [sphereRestrictedProbability24]
    rw [integral_smul_measure, smul_eq_mul, htoReal]
  -- integrability of the three kernels
  have hκprod : Integrable (Function.uncurry
      (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q)) (μ.prod μ) :=
    smallBudgetKernel24_integrable hc.le hq (μ.prod μ)
  have hκk : ∀ x, Integrable (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q x) μ :=
    fun x => smallBudgetKernel24_row_integrable hc.le hq x μ
  have hκV : Integrable (residualRowPotential μ
      (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q)) μ := hκprod.integral_prod_left
  have hTk : ∀ x, Integrable (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x) μ := by
    intro x
    rw [hμdef]
    exact shortRangeKernel24_restricted_integrable hc hp _ x
  have hTV : Integrable (residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) μ := by
    rw [hμdef]
    exact shortRangeKernel24_restricted_rowPotential_integrable hc hp _ hR0
  have hTprod : Integrable (Function.uncurry
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry
        (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) (μ.prod μ) :=
      (shortRangeKernel24_measurable (sphereGaussianDensityFactor24 N) p).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).mpr ⟨Filter.Eventually.of_forall fun x => hTk x, ?_⟩
    refine hTV.congr (Filter.Eventually.of_forall fun x => ?_)
    unfold residualRowPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y =
      ‖shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y‖
    rw [Real.norm_eq_abs, abs_of_nonneg (shortRangeKernel24_nonneg _ _ _ _)]
  have hGprod : Integrable (Function.uncurry (sphereGaussianKernel24 t₀)) (μ.prod μ) :=
    sphereGaussianKernel24_integrable_finite ht₀ (μ.prod μ)
  have hGk : ∀ x, Integrable (sphereGaussianKernel24 t₀ x) μ :=
    fun x => sphereGaussianKernel24_row_integrable_finite ht₀ x μ
  have hGV : Integrable (residualRowPotential μ (sphereGaussianKernel24 t₀)) μ :=
    hGprod.integral_prod_left
  -- the joint choice
  obtain ⟨z, hinj, hzC, hzB, hjoint⟩ := exists_stratified_joint_three μ
    (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q)
    (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)
    (sphereGaussianKernel24 t₀) (4^q/q) 0 1 hw₂ hw₃
    (smallBudgetKernel24_symm _ q) (shortRangeKernel24_symm _ p) (sphereGaussianKernel24_comm t₀)
    (smallBudgetKernel24_self _ hq) (shortRangeKernel24_self _ hp0)
    (sphereGaussianKernel24_self t₀)
    (smallBudgetKernel24_nonneg _ q) (shortRangeKernel24_nonneg _ p)
    (sphereGaussianKernel24_nonneg t₀)
    hκk hTk hGk hκV hTV hGV hκprod hTprod hGprod X X (Fin.elim0 : Fin 0 → SphereD 24)
    hn C hCm hCd hcover hμC (range X) hB
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  -- the budget kernel: exact smooth mean
  have hκU : ∀ x, residualRowPotential μ (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q) x =
      (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q x y
        ∂(sphereProbabilityD 24) := fun x => hint_eq _
  have hκbg : residualBackground μ (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q) =
      (N:ℝ)/(n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
        smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q y y'
          ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24)) := by
    unfold residualBackground
    rw [hint_eq]
    simp_rw [hκU]
    rw [integral_const_mul]
  have hc₁ : residualCentered μ (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q) X z =
      residualCrossSum (smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q) X z-
        (2*(N:ℝ)*(∑ i, ∫ y in ⋃ j, C j,
            smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (X i) y
              ∂(sphereProbabilityD 24))+
          (N:ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
            smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q y y'
              ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))) := by
    rw [residualCentered_eq_crossSum, hκbg]
    simp_rw [hκU]
    rw [← Finset.mul_sum]
    field_simp
    try ring
  -- the short-range kernel: bounded smooth mean
  have hTrow : ∀ x, (n:ℝ)*residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x ≤ 1/(11-p) := by
    intro x
    have h := shortRangeKernel24_cell_rows_le hN hp C hCm hCd hCmass x
    rw [sphereRestrictedProbability24_sum_integral C hCm hCd hCmass
      (shortRangeKernel24_row_integrable (sphereGaussianScale24_pos hN zero_lt_one) hp x)] at h
    unfold residualRowPotential
    rw [hint_eq]
    calc (n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y ∂(sphereProbabilityD 24))
        = (N:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y
            ∂(sphereProbabilityD 24) := by field_simp
      _ ≤ 1/(11-p) := h
  have hTU : ∀ x, residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x ≤ 1/((n:ℝ)*(11-p)) := by
    intro x
    have h := hTrow x
    rw [le_div_iff₀ (mul_pos hnR h11)]
    calc _ = ((n:ℝ)*residualRowPotential μ
          (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x)*(11-p) := by ring
      _ ≤ 1/(11-p)*(11-p) := mul_le_mul_of_nonneg_right h h11.le
      _ = 1 := by field_simp
  have hTbg : residualBackground μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) ≤
      1/((n:ℝ)*(11-p)) := by
    unfold residualBackground
    calc _ ≤ ∫ _x, 1/((n:ℝ)*(11-p)) ∂μ := integral_mono hTV (integrable_const _) hTU
      _ = _ := by simp
  have hTsum : (n:ℝ)*(∑ i, residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) (X i)) ≤
      (Fintype.card ι:ℝ)/(11-p) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _i : ι, 1/(11-p) := Finset.sum_le_sum fun i _ => hTrow (X i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hTbgn : (n:ℝ)^2*residualBackground μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) ≤ (n:ℝ)/(11-p) := by
    calc _ ≤ (n:ℝ)^2*(1/((n:ℝ)*(11-p))) := mul_le_mul_of_nonneg_left hTbg (by positivity)
      _ = _ := by field_simp
  have hc₂ : residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z-
      (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p) ≤
      residualCentered μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z := by
    rw [residualCentered_eq_crossSum]
    have he : (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p) =
        2*((Fintype.card ι:ℝ)/(11-p))+(n:ℝ)/(11-p) := by ring
    rw [he]
    linarith
  -- the Gaussian window: bounded smooth mean
  have hGU : ∀ x, residualRowPotential μ (sphereGaussianKernel24 t₀) x ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ := by
    intro x
    unfold residualRowPotential
    rw [hint_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∫ y in ⋃ j, C j, sphereGaussianKernel24 t₀ x y ∂(sphereProbabilityD 24))
        ≤ ∫ y, sphereGaussianKernel24 t₀ x y ∂(sphereProbabilityD 24) :=
          setIntegral_le_integral (sphereGaussianKernel24_integrable ht₀ x)
            (Filter.Eventually.of_forall fun y => sphereGaussianKernel24_nonneg _ _ _)
      _ = sphereGaussianBackground24 t₀ := (sphereGaussianBackground24_eq_potential ht₀ x).symm
  have hGbg : residualBackground μ (sphereGaussianKernel24 t₀) ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ := by
    unfold residualBackground
    calc _ ≤ ∫ _x, (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ ∂μ :=
          integral_mono hGV (integrable_const _) hGU
      _ = _ := by simp
  have hc₃ : cellPairSum (sphereGaussianKernel24 t₀) z-
      (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀) ≤
      residualCentered μ (sphereGaussianKernel24 t₀) (Fin.elim0 : Fin 0 → SphereD 24) z := by
    have hbgn : (n:ℝ)^2*residualBackground μ (sphereGaussianKernel24 t₀) ≤
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀) := by
      calc _ ≤ (n:ℝ)^2*((N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀) :=
            mul_le_mul_of_nonneg_left hGbg (by positivity)
        _ = _ := by field_simp
    unfold residualCentered residualPairEnergy cellPairSum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, sub_zero,
      add_zero]
    linarith
  rw [hc₁] at hjoint
  have hm₂ := mul_le_mul_of_nonneg_left hc₂ hw₂
  have hm₃ := mul_le_mul_of_nonneg_left hc₃ hw₃
  have hrhs : (n:ℝ)*(4^q/q+w₂*0+w₃*1) = (n:ℝ)*(4^q/q+w₃) := by ring
  rw [hrhs] at hjoint
  linarith

end SphericalRiesz
