import Riesz.SphereNegMacroBlock8

/-! The residual part of the negative-exponent macroscopic end, given a stratification
(stage NEG, second half).

Let `S` be split into measurable disjoint cells `C_j` of probability exactly `1/N` and diameter at
most `d_j`. Choosing one point in each cell by the stratified first-moment selection with the
subtracted macroscopic kernel `K'` (zero diagonal, cell variance `≤ c d_j² w^(p+2)/(p+2)`) and the
linear term `-2N ∫_S K'(·,y) dσ(y)`, the expectation of the neutralized block is exactly the sum of
the cell variances (the cross means add up to `N² ∫_S∫_S K'`). Hence
`block_{K'}(z; S, N) ≤ Σ_j c d_j² w^(p+2)/(p+2)`: cells at the density scale contribute `O(w^(p+2))`
each in units of `N`, small as `w → 0`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace SphericalRiesz

theorem negMacroKernel8_abs_le {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w) (x y : Sphere8) :
    |negMacroKernel8 c p w x y| ≤ 4*c*(w^(p+2)/(p+2)) := by
  have h1 := negMacroKernel8_nonpos (p := p) (δ := w) hc x y
  have h2 := negMacroKernel8_variance hc hp hw x y
  have hd := sphere8_dist_le_two x y
  have hd0 := dist_nonneg (x := x) (y := y)
  have hd2 : (dist x y)^2 ≤ 4 := by nlinarith
  have hW : 0 ≤ w^(p+2)/(p+2) := div_nonneg (Real.rpow_nonneg hw _) (by linarith)
  rw [abs_of_nonpos h1]
  calc -negMacroKernel8 c p w x y = 0-negMacroKernel8 c p w x y := by ring
    _ ≤ c*(dist x y)^2*(w^(p+2)/(p+2)) := h2
    _ ≤ c*4*(w^(p+2)/(p+2)) := by
        apply mul_le_mul_of_nonneg_right _ hW
        exact mul_le_mul_of_nonneg_left hd2 hc
    _ = 4*c*(w^(p+2)/(p+2)) := by ring

theorem negMacroKernel8_measurable (c p w : ℝ) :
    StronglyMeasurable (fun q : Sphere8 × Sphere8 => negMacroKernel8 c p w q.1 q.2) := by
  have hf : StronglyMeasurable (fun z : (Sphere8 × Sphere8) × ℝ =>
      z.2^p*(sphereGaussianKernel8 (c*z.2) z.1.1 z.1.2-1)) :=
    ((negMacro_integrand_measurable c p).comp (measurable_snd.prodMk measurable_fst)).stronglyMeasurable
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc 0 w))

/-- The residual part of the macroscopic end for a given stratification. -/
theorem negMacro_stratified_residual {n : ℕ} {N : ℝ} (hN : 0 < N) {c p w : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hw : 0 ≤ w) (S : Set Sphere8) (C : Fin n → Set Sphere8)
    (hCm : ∀ j, MeasurableSet (C j)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hunion : (⋃ j, C j) = S) (hmass : ∀ j, sphereProbability8 (C j) = ENNReal.ofReal (1/N))
    (dm : Fin n → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j)
    (B : Set Sphere8) (hB : sphereProbability8 B = 0) :
    ∃ z : Fin n → Sphere8, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧ (∀ j, z j ∉ B) ∧
      kernelBlock8 (negMacroKernel8 c p w) z S N ≤ ∑ j, c*(dm j)^2*(w^(p+2)/(p+2)) := by
  set k := negMacroKernel8 c p w with hkdef
  set Mb := 4*c*(w^(p+2)/(p+2)) with hMbdef
  have hkb : ∀ x y, |k x y| ≤ Mb := fun x y => negMacroKernel8_abs_le hc hp hw x y
  have hkm := negMacroKernel8_measurable c p w
  set ν : Fin n → Measure Sphere8 := fun j => ENNReal.ofReal N • sphereProbability8.restrict (C j)
    with hνdef
  have hNinv : ENNReal.ofReal N*ENNReal.ofReal (1/N) = 1 := by
    rw [← ENNReal.ofReal_mul hN.le, mul_one_div_cancel hN.ne', ENNReal.ofReal_one]
  have hP : ∀ j, IsProbabilityMeasure (ν j) := by
    intro j
    constructor
    simp only [hνdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hmass j, hNinv]
  have hA : ∀ j, NullSingletonClass (ν j) := by
    intro j
    constructor
    intro x
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    have : sphereProbability8 ({x} ∩ C j) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton x)
    rw [this, mul_zero]
  have hCc : ∀ j, ν j (C j)ᶜ = 0 := by
    intro j
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j).compl, compl_inter_self, measure_empty, mul_zero]
  have hBν : ∀ j, ν j B = 0 := by
    intro j
    simp only [hνdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply' (hCm j)]
    rw [measure_mono_null inter_subset_left hB, mul_zero]
  have hfin : ∀ j, IsFiniteMeasure (ν j) := fun j => by have := hP j; infer_instance
  have hrow : ∀ (μ : Measure Sphere8) [IsFiniteMeasure μ] (x : Sphere8), Integrable (k x) μ := by
    intro μ _ x
    refine (integrable_const Mb).mono' ?_ (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hkb x y)
    exact (hkm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hpotm : ∀ (μ : Measure Sphere8) [SFinite μ],
      StronglyMeasurable (fun x => ∫ y, k x y ∂μ) := by
    intro μ _
    exact hkm.integral_prod_right' (ν := μ)
  have hpotb : ∀ (μ : Measure Sphere8) [IsProbabilityMeasure μ] (x : Sphere8),
      |∫ y, k x y ∂μ| ≤ Mb := by
    intro μ _ x
    calc |∫ y, k x y ∂μ| = ‖∫ y, k x y ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ Mb*μ.real univ := norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hkb x y)
      _ = Mb := by simp
  have hV : ∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i) := by
    intro i j
    have := hP i; have := hP j
    exact (integrable_const Mb).mono' (hpotm (ν j)).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpotb (ν j) x)
  have hk : ∀ j x, Integrable (k x) (ν j) := fun j x => by have := hfin j; exact hrow (ν j) x
  -- symmetry of the cross means (Fubini)
  have hsym : ∀ i j, cellCross k (ν i) (ν j) = cellCross k (ν j) (ν i) := by
    intro i j
    have := hP i; have := hP j
    unfold cellCross
    have hint : Integrable (Function.uncurry fun x y => k x y) ((ν i).prod (ν j)) := by
      refine (integrable_const Mb).mono' hkm.aestronglyMeasurable
        (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hkb q.1 q.2)
    rw [integral_integral_swap hint]
    congr 1
    funext y
    congr 1
    funext x
    exact negMacroKernel8_symm c p w x y
  -- the linear term
  set pot : Sphere8 → ℝ := kernelPotential8 k S with hpotdef
  set L : Sphere8 → ℝ := fun x => -2*N*pot x with hLdef
  have hpotS : StronglyMeasurable pot := hpotm (sphereProbability8.restrict S)
  have hpotSb : ∀ x, |pot x| ≤ Mb := by
    intro x
    simp only [hpotdef, kernelPotential8]
    calc |∫ y in S, k x y ∂sphereProbability8| = ‖∫ y in S, k x y ∂sphereProbability8‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ Mb*(sphereProbability8.restrict S).real univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]; exact hkb x y)
      _ ≤ Mb*1 := by
          have hM0 : 0 ≤ Mb := (abs_nonneg _).trans (hkb x x)
          apply mul_le_mul_of_nonneg_left _ hM0
          rw [measureReal_restrict_apply_univ]
          exact measureReal_le_one
      _ = Mb := mul_one Mb
  have hL : ∀ j, Integrable L (ν j) := by
    intro j
    have := hfin j
    refine ((integrable_const Mb).mono' hpotS.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpotSb x)).const_mul (-2*N)
  -- the variance bound on each cell
  have hω : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, 0-k x y ≤ c*(dm j)^2*(w^(p+2)/(p+2)) := by
    intro j x hx y hy
    refine (negMacroKernel8_variance hc hp hw x y).trans ?_
    have hW : 0 ≤ w^(p+2)/(p+2) := div_nonneg (Real.rpow_nonneg hw _) (by linarith)
    apply mul_le_mul_of_nonneg_right _ hW
    apply mul_le_mul_of_nonneg_left _ hc
    have h0 : 0 ≤ dist x y := dist_nonneg
    exact pow_le_pow_left₀ h0 (hdiam j x hx y hy) 2
  obtain ⟨z, hinj, hzC, hzB, hsel⟩ := exists_stratified_selection k
    (fun x y => negMacroKernel8_symm c p w x y) 0 (fun x => negMacroKernel8_self c p w x) n ν C
    (fun j => c*(dm j)^2*(w^(p+2)/(p+2))) L B hP hA hCc hBν hω hk hV hsym hL
  refine ⟨z, hinj, hzC, hzB, ?_⟩
  -- identify the expectation
  have hsum_int : ∀ f : Sphere8 → ℝ, Integrable f (sphereProbability8.restrict S) →
      (∑ j, ∫ x, f x ∂(ν j)) = N*∫ x in S, f x ∂sphereProbability8 := by
    intro f hf
    have hν : ∀ j, (∫ x, f x ∂(ν j)) = N*∫ x in C j, f x ∂sphereProbability8 := by
      intro j
      simp only [hνdef]
      rw [integral_smul_measure, ENNReal.toReal_ofReal hN.le, smul_eq_mul]
    simp_rw [hν]
    rw [← Finset.mul_sum]
    congr 1
    rw [← hunion] at hf ⊢
    rw [integral_iUnion hCm (fun i j hij => hdisj hij) hf, tsum_fintype]
  have hpotSi : Integrable pot (sphereProbability8.restrict S) :=
    (integrable_const Mb).mono' hpotS.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpotSb x)
  have hcross : (∑ i, ∑ j, cellCross k (ν i) (ν j)) = N^2*kernelBackground8 k S S := by
    have hinner : ∀ i, (∑ j, cellCross k (ν i) (ν j)) = ∫ x, N*pot x ∂(ν i) := by
      intro i
      unfold cellCross
      rw [← integral_finsetSum _ (fun j _ => hV i j)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact hsum_int (k x) (hrow _ x)
    simp_rw [hinner]
    rw [hsum_int (fun x => N*pot x) (hpotSi.const_mul N), integral_const_mul]
    unfold kernelBackground8
    ring
  have hlin : (∑ j, ∫ x, L x ∂(ν j)) = -2*N^2*kernelBackground8 k S S := by
    rw [hsum_int L (hpotSi.const_mul (-2*N))]
    simp only [hLdef]
    rw [integral_const_mul]
    unfold kernelBackground8
    ring
  have hLz : (∑ j, L (z j)) = -2*N*∑ j, pot (z j) := by
    simp only [hLdef]
    rw [Finset.mul_sum]
  rw [hcross, hlin, hLz] at hsel
  unfold kernelBlock8
  change cellPairSum k z-2*N*(∑ i, kernelPotential8 k S (z i))+N^2*kernelBackground8 k S S ≤ _
  simp only [hpotdef] at hsel
  linarith

#print axioms negMacroKernel8_abs_le
#print axioms negMacroKernel8_measurable
#print axioms negMacro_stratified_residual

end SphericalRiesz
