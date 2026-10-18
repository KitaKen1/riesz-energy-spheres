import Riesz.StratifiedResidualEnergy
import Riesz.SphereShortRangeResidual8
import Riesz.NegMacroStratified8
import Riesz.GaussianBlockUnion8

/-! Stratified joint residual selection for the negative-exponent construction (stage NEG).

On a residual region `A` cut into `n` cells of probability exactly `σ(A)/n`, one point per cell
can be chosen so that the `s = 4` residual neutralized energy, plus `w` times the short-range
one, plus `λ` times the residual neutralized energy of the subtracted macroscopic kernel `K'`, is
at most `λ Σ_j c' d_j² δ^(p'+2)/(p'+2)`: the `s = 4` and short-range kernels are nonnegative with
zero diagonal, so only `K'` contributes cell variances. With exact mass the `K'` part is the
block of `K'` against `M σ|_A`, which is nonnegative. This gives the two bounds of the HP joint
assembly (the `s = 4` block of patches + residual, now with the extra cost `λ Ω`) together with a
bound on the residual macroscopic end by the deviation `block(X) - block(X ∪ Z)`, which the
universal `s = 4` lower bound controls. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

theorem restrictedProbability8_prod_integrable {f : Sphere8 → Sphere8 → ℝ} (A : Set Sphere8)
    (hA0 : sphereProbability8 A ≠ 0)
    (hf : Integrable (fun q : Sphere8 × Sphere8 => f q.1 q.2)
      (sphereProbability8.prod sphereProbability8)) :
    Integrable (Function.uncurry f)
      ((sphereRestrictedProbability8 A).prod (sphereRestrictedProbability8 A)) := by
  have hne : (sphereProbability8 A)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  unfold sphereRestrictedProbability8
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict]
  exact (hf.restrict.smul_measure hne).smul_measure hne

theorem shortRangeKernel8_pair_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 3) :
    Integrable (fun q : Sphere8 × Sphere8 => shortRangeKernel8 c p q.1 q.2)
      (sphereProbability8.prod sphereProbability8) := by
  apply (integrable_prod_iff (shortRangeKernel8_measurable c p).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => shortRangeKernel8_row_integrable hc hp x), ?_⟩
  have hm : StronglyMeasurable (fun x : Sphere8 =>
      ∫ y, ‖shortRangeKernel8 c p x y‖ ∂sphereProbability8) :=
    (shortRangeKernel8_measurable c p).norm.integral_prod_right'
  refine (integrable_const ((105/32)/c^4/(3-p))).mono' hm.aestronglyMeasurable ?_
  filter_upwards [] with x
  show ‖∫ y, ‖shortRangeKernel8 c p x y‖ ∂sphereProbability8‖ ≤ (105/32)/c^4/(3-p)
  have he : (∫ y, ‖shortRangeKernel8 c p x y‖ ∂sphereProbability8) =
      ∫ y, shortRangeKernel8 c p x y ∂sphereProbability8 := by
    congr 1
    funext y
    rw [Real.norm_eq_abs, abs_of_nonneg (shortRangeKernel8_nonneg c p x y)]
  rw [he, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun y => shortRangeKernel8_nonneg c p x y)]
  exact shortRangeKernel8_row_integral_le hc hp x

/-- Stratified joint selection for the `s = 4` kernel, the short-range kernel and `K'`. -/
theorem sphere8_exists_stratified_residual_joint {q : ℕ} (X : Fin q → Sphere8)
    (A S : Set Sphere8) (hA : MeasurableSet A) (hA0 : sphereProbability8 A ≠ 0) (M : ℝ)
    {n : ℕ} (hn : 0 < n) (C : Fin n → Set Sphere8) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hunion : (⋃ j, C j) = A)
    (hmass : ∀ j, sphereProbability8 (C j) = sphereProbability8 A/n)
    {c p w : ℝ} (hc : 0 < c) (hp1 : -1 ≤ p) (hp : p < 3) (hw : 0 ≤ w)
    {c' p' δ lam : ℝ} (hc' : 0 ≤ c') (hp' : -2 < p') (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (dm : Fin n → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ Z : Fin n → Sphere8, Function.Injective Z ∧ (∀ j, Z j ∈ C j ∧ Z j ∉ range X) ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 A) sphereKernel4
          (sphereResidualCrossRow8 X S M) Z +
        w*residualNeutralizedEnergy (sphereRestrictedProbability8 A) (shortRangeKernel8 c p)
          (shortRangeCrossRow8 c p X) Z +
        lam*residualNeutralizedEnergy (sphereRestrictedProbability8 A) (negMacroKernel8 c' p' δ)
          (fun _ => 0) Z ≤
      lam*∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)) := by
  have := sphereRestrictedProbability8_probability A hA0
  set Mb := 4*c'*(δ^(p'+2)/(p'+2)) with hMbdef
  have hkb : ∀ x y, |negMacroKernel8 c' p' δ x y| ≤ Mb :=
    fun x y => negMacroKernel8_abs_le hc' hp' hδ x y
  have hkm := negMacroKernel8_measurable c' p' δ
  -- integrability of the three kernels, rows and linear terms
  have hk₁ : ∀ x, Integrable (sphereKernel4 x) (sphereRestrictedProbability8 A) :=
    sphereKernel4_restricted_probability_integrable A
  have hk₂ : ∀ x, Integrable (shortRangeKernel8 c p x) (sphereRestrictedProbability8 A) :=
    shortRangeKernel8_restricted_integrable hc hp A
  have hk₃ : ∀ x, Integrable (negMacroKernel8 c' p' δ x) (sphereRestrictedProbability8 A) := by
    intro x
    refine (integrable_const Mb).mono'
      (hkm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs]
    exact hkb x y
  have hV₁ := sphereRestrictedProbability8_row_integrable A
  have hV₂ := shortRangeKernel8_restricted_rowPotential_integrable hc hp A hA0
  have hV₃ : Integrable (residualRowPotential (sphereRestrictedProbability8 A)
      (negMacroKernel8 c' p' δ)) (sphereRestrictedProbability8 A) := by
    have hm : StronglyMeasurable (residualRowPotential (sphereRestrictedProbability8 A)
        (negMacroKernel8 c' p' δ)) :=
      hkm.integral_prod_right' (ν := sphereRestrictedProbability8 A)
    refine (integrable_const Mb).mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    unfold residualRowPotential
    calc |∫ y, negMacroKernel8 c' p' δ x y ∂sphereRestrictedProbability8 A|
        = ‖∫ y, negMacroKernel8 c' p' δ x y ∂sphereRestrictedProbability8 A‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ Mb*(sphereRestrictedProbability8 A).real univ :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]; exact hkb x y)
      _ = Mb := by simp
  have hL₁ := sphereResidualCrossRow8_integrable X A S M
  have hL₂ := shortRangeCrossRow8_integrable hc hp X A
  have hL₃ : Integrable (fun _ : Sphere8 => (0:ℝ)) (sphereRestrictedProbability8 A) :=
    integrable_const 0
  have hk12 : ∀ x, Integrable (fun y => sphereKernel4 x y+w*shortRangeKernel8 c p x y)
      (sphereRestrictedProbability8 A) := fun x => (hk₁ x).add ((hk₂ x).const_mul w)
  have hV12 := residualRowPotential_add_smul_integrable sphereKernel4 (shortRangeKernel8 c p) w
    hk₁ hk₂ hV₁ hV₂
  have hL12 : Integrable (fun x => sphereResidualCrossRow8 X S M x+w*shortRangeCrossRow8 c p X x)
      (sphereRestrictedProbability8 A) := hL₁.add (hL₂.const_mul w)
  have hk : ∀ x, Integrable (fun y => sphereKernel4 x y+w*shortRangeKernel8 c p x y+
      lam*negMacroKernel8 c' p' δ x y) (sphereRestrictedProbability8 A) :=
    fun x => (hk12 x).add ((hk₃ x).const_mul lam)
  have hV := residualRowPotential_add_smul_integrable
    (fun x y => sphereKernel4 x y+w*shortRangeKernel8 c p x y) (negMacroKernel8 c' p' δ) lam
    hk12 hk₃ hV12 hV₃
  have hL : Integrable (fun x => sphereResidualCrossRow8 X S M x+w*shortRangeCrossRow8 c p X x+
      lam*0) (sphereRestrictedProbability8 A) := hL12.add (hL₃.const_mul lam)
  have hprod₁ := restrictedProbability8_prod_integrable A hA0 sphereKernel4_pair_integrable
  have hprod₂ := restrictedProbability8_prod_integrable A hA0 (shortRangeKernel8_pair_integrable hc hp)
  have hprod₃ : Integrable (Function.uncurry (negMacroKernel8 c' p' δ))
      ((sphereRestrictedProbability8 A).prod (sphereRestrictedProbability8 A)) := by
    refine (integrable_const Mb).mono' hkm.aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact hkb z.1 z.2
  have hprod : Integrable (Function.uncurry (fun x y => sphereKernel4 x y+
      w*shortRangeKernel8 c p x y+lam*negMacroKernel8 c' p' δ x y))
      ((sphereRestrictedProbability8 A).prod (sphereRestrictedProbability8 A)) :=
    (hprod₁.add (hprod₂.const_mul w)).add (hprod₃.const_mul lam)
  -- cells
  have hsub : ∀ j, C j ⊆ A := fun j => hunion ▸ subset_iUnion C j
  have hmass' : ∀ j, sphereRestrictedProbability8 A (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    simp only [sphereRestrictedProbability8, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), inter_eq_left.mpr (hsub j), hmass j, div_eq_mul_inv,
      ← mul_assoc, ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _), one_mul]
  have hcover : sphereRestrictedProbability8 A (⋃ j, C j)ᶜ = 0 := by
    rw [hunion]
    exact sphereRestrictedProbability8_compl A hA
  have hω : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j,
      0-(sphereKernel4 x y+w*shortRangeKernel8 c p x y+lam*negMacroKernel8 c' p' δ x y) ≤
        lam*(c'*(dm j)^2*(δ^(p'+2)/(p'+2))) := by
    intro j x hx y hy
    have h1 := sphereKernel4_nonneg x y
    have h2 := mul_nonneg hw (shortRangeKernel8_nonneg c p x y)
    have hW : 0 ≤ δ^(p'+2)/(p'+2) := div_nonneg (Real.rpow_nonneg hδ _) (by linarith)
    have hd : (dist x y)^2 ≤ (dm j)^2 :=
      pow_le_pow_left₀ dist_nonneg (hdiam j x hx y hy) 2
    have h3 : 0-negMacroKernel8 c' p' δ x y ≤ c'*(dm j)^2*(δ^(p'+2)/(p'+2)) :=
      (negMacroKernel8_variance hc' hp' hδ x y).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hc') hW)
    have h4 := mul_le_mul_of_nonneg_left h3 hlam
    linarith
  have hB : sphereRestrictedProbability8 A (range X) = 0 := (finite_range X).measure_zero _
  obtain ⟨Z, hZ, hZC, hZB, hsel⟩ := exists_stratified_residualNeutralizedEnergy_le
    (sphereRestrictedProbability8 A)
    (fun x y => sphereKernel4 x y+w*shortRangeKernel8 c p x y+lam*negMacroKernel8 c' p' δ x y)
    (fun x => sphereResidualCrossRow8 X S M x+w*shortRangeCrossRow8 c p X x+lam*0)
    (fun x y => by
      rw [sphereKernel4_symm x y, shortRangeKernel8_symm c p x y, negMacroKernel8_symm c' p' δ x y])
    (fun x => by
      rw [sphereKernel4_diagonal, shortRangeKernel8_self c hp1, negMacroKernel8_self]
      ring)
    hn C hCm hdisj hcover hmass' (fun j => lam*(c'*(dm j)^2*(δ^(p'+2)/(p'+2)))) hω hk hV hprod hL
    (range X) hB
  have e1 := residualNeutralizedEnergy_add_smul (μ := sphereRestrictedProbability8 A)
    sphereKernel4 (shortRangeKernel8 c p) (sphereResidualCrossRow8 X S M)
    (shortRangeCrossRow8 c p X) w hk₁ hk₂ hV₁ hV₂ hL₁ hL₂ Z
  have e2 := residualNeutralizedEnergy_add_smul (μ := sphereRestrictedProbability8 A)
    (fun x y => sphereKernel4 x y+w*shortRangeKernel8 c p x y) (negMacroKernel8 c' p' δ)
    (fun x => sphereResidualCrossRow8 X S M x+w*shortRangeCrossRow8 c p X x) (fun _ => 0) lam
    hk12 hk₃ hV12 hV₃ hL12 hL₃ Z
  beta_reduce at e2
  have hsum : (∑ j, lam*(c'*(dm j)^2*(δ^(p'+2)/(p'+2)))) =
      lam*∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)) := (Finset.mul_sum _ _ _).symm
  refine ⟨Z, hZ, fun j => ⟨hZC j, hZB j⟩, ?_⟩
  linarith

/-- With exact mass the residual neutralized energy (zero linear term) is the block against
`M σ|_A`. -/
theorem residualNE_eq_kernelBlock8 {k : Sphere8 → Sphere8 → ℝ} (A : Set Sphere8)
    (hA0 : sphereProbability8 A ≠ 0) {n : ℕ} (Z : Fin n → Sphere8) (M : ℝ)
    (hr : (n:ℝ) = M*sphereProbability8.real A) :
    residualNeutralizedEnergy (sphereRestrictedProbability8 A) k (fun _ => 0) Z =
      kernelBlock8 k Z A M := by
  have hm := sphereRestrictedProbability8_mass_match A hA0 n M hr
  unfold residualNeutralizedEnergy kernelBlock8 kernelPair8 residualPairEnergy
  simp_rw [kernel_restricted_row, kernel_restricted_background]
  simp only [Finset.sum_const_zero, integral_zero, mul_zero, add_zero, sub_zero]
  rw [← Finset.mul_sum, ← hm]
  ring

/-- With exact mass the block of the subtracted macroscopic kernel is nonnegative. -/
theorem negMacroBlock8_nonneg_of_mass {ι : Type*} [Fintype ι] {c p δ : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hδ : 0 ≤ δ) (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ)
    (hmass : (Fintype.card ι:ℝ) = M*sphereProbability8.real S) :
    0 ≤ kernelBlock8 (negMacroKernel8 c p δ) X S M := by
  rw [negMacroBlock8_eq_of_mass hc hp hδ X S M hmass]
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  apply mul_nonneg (Real.rpow_nonneg hα.1.le _)
  rw [gaussianBlock8_eq_defect (mul_nonneg hc hα.1.le)]
  exact gaussianMeasureDefect_nonneg (mul_nonneg hc hα.1.le) M _ _

/-- The NEG joint residual assembly: stratified residual points `Z` in `Sᶜ` with
(1) the `s = 4` block of `X ∪ Z` at most the block of `X` plus the short-range cost plus `λ Ω`,
(2) the residual block of `K'` at most `Ω` plus the deviation `block(X) - block(X ∪ Z)` and the
short-range cost, divided by `λ`. -/
theorem sphere8_neg_joint_residual_assembly {q n : ℕ} (X : Fin q → Sphere8) (S : Set Sphere8)
    (hS : MeasurableSet S) (hA0 : sphereProbability8 Sᶜ ≠ 0) (M : ℝ)
    (hr : (n:ℝ) = M*sphereProbability8.real Sᶜ) (hn : 0 < n) (C : Fin n → Set Sphere8)
    (hCm : ∀ j, MeasurableSet (C j)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hunion : (⋃ j, C j) = Sᶜ) (hmass : ∀ j, sphereProbability8 (C j) = sphereProbability8 Sᶜ/n)
    {c p w : ℝ} (hc : 0 < c) (hp1 : -1 ≤ p) (hp : p < 3) (hw : 0 < w)
    {c' p' δ lam : ℝ} (hc' : 0 ≤ c') (hp' : -2 < p') (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (dm : Fin n → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ Z : Fin n → Sphere8, Function.Injective Z ∧ (∀ j, Z j ∈ C j ∧ Z j ∉ range X) ∧
      sphereFiniteBlock4 (Sum.elim X Z) univ M ≤ sphereFiniteBlock4 X S M+
        w*(2*(n:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))+
          (n:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))))+
        lam*∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)) ∧
      kernelBlock8 (negMacroKernel8 c' p' δ) Z Sᶜ M ≤ (∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)))+
        ((sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)+
          w*(2*(n:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))+
            (n:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p))))))/lam := by
  set R := ((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)) with hR
  set Ω := ∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)) with hΩ
  obtain ⟨Z, hZ, hZC, hjoint⟩ := sphere8_exists_stratified_residual_joint X Sᶜ S hS.compl hA0 M
    hn C hCm hdisj hunion hmass hc hp1 hp hw.le hc' hp' hδ hlam.le dm hdiam
  have hassm := sphereFiniteBlock4_residual_assembly X Z S hS hA0 M hr
  let := sphereRestrictedProbability8_probability Sᶜ hA0
  have hrow : ∀ x, residualRowPotential (sphereRestrictedProbability8 Sᶜ) (shortRangeKernel8 c p) x ≤ R :=
    fun x => shortRangeKernel8_restricted_row_le hc hp Sᶜ x
  have hint : ∫ z, shortRangeCrossRow8 c p X z ∂sphereRestrictedProbability8 Sᶜ ≤ 2*(q:ℝ)*R :=
    shortRangeCrossRow8_integral_le hc hp X Sᶜ
  have hlow := residualNeutralizedEnergy_ge_of_nonneg (μ := sphereRestrictedProbability8 Sᶜ)
    (shortRangeKernel8 c p) (shortRangeCrossRow8 c p X) (shortRangeKernel8_nonneg c p)
    (shortRangeCrossRow8_nonneg c p X) hrow hint Z
  have hNE3 := residualNE_eq_kernelBlock8 (k := negMacroKernel8 c' p' δ) Sᶜ hA0 Z M hr
  have hpos3 : 0 ≤ kernelBlock8 (negMacroKernel8 c' p' δ) Z Sᶜ M :=
    negMacroBlock8_nonneg_of_mass hc' hp' hδ Z Sᶜ M (by simpa using hr)
  rw [hNE3] at hjoint
  have hw2 := mul_le_mul_of_nonneg_left hlow hw.le
  have hl3 := mul_nonneg hlam.le hpos3
  refine ⟨Z, hZ, hZC, ?_, ?_⟩
  · rw [hassm]
    nlinarith
  · have h : lam*kernelBlock8 (negMacroKernel8 c' p' δ) Z Sᶜ M ≤ lam*Ω+
        ((sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)+
          w*(2*(n:ℝ)^2*R+(n:ℝ)*(2*(q:ℝ)*R))) := by
      rw [hassm]
      nlinarith
    rw [add_div' _ _ _ hlam.ne', le_div_iff₀ hlam]
    linarith

#print axioms restrictedProbability8_prod_integrable
#print axioms shortRangeKernel8_pair_integrable
#print axioms sphere8_exists_stratified_residual_joint
#print axioms residualNE_eq_kernelBlock8
#print axioms negMacroBlock8_nonneg_of_mass
#print axioms sphere8_neg_joint_residual_assembly

end SphericalRiesz
