import Riesz.SphereResidualAssembly8

/-! Residual assembly for a bounded measurable symmetric kernel on the actual sphere.

For points `X` with background `M σ|_S`, residual points `Z` with background `M σ|_{Sᶜ}` and
`r = M σ(Sᶜ)`, the neutralized block of `X ∪ Z` against `M σ` is the block of `X` plus the
residual neutralized energy (sequential first-moment form) with cross row
`2(Σᵢ k(Xᵢ,·) - M ∫_S k(y,·) dσ)`.  This is the algebra of `sphereFiniteBlock4_residual_assembly`
for any bounded kernel (the diagonal is kept in the pair sums). -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

section
variable (k : Sphere8 → Sphere8 → ℝ)

def kernelPotential8 (A : Set Sphere8) (x : Sphere8) : ℝ :=
  ∫ y in A, k x y ∂sphereProbability8

def kernelBackground8 (S T : Set Sphere8) : ℝ :=
  ∫ x in S, kernelPotential8 k T x ∂sphereProbability8

def kernelPair8 {ι : Type*} [Fintype ι] (X : ι → Sphere8) : ℝ :=
  ∑ i, ∑ j, k (X i) (X j)

def kernelBlock8 {ι : Type*} [Fintype ι] (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) : ℝ :=
  kernelPair8 k X-2*M*(∑ i, kernelPotential8 k S (X i))+M^2*kernelBackground8 k S S

def kernelCrossRow8 {p : ℕ} (X : Fin p → Sphere8) (S : Set Sphere8) (M : ℝ) (z : Sphere8) : ℝ :=
  2*((∑ i, k (X i) z)-M*kernelPotential8 k S z)

end

section
variable {k : Sphere8 → Sphere8 → ℝ} {B : ℝ}
  (hk : StronglyMeasurable (fun q : Sphere8 × Sphere8 => k q.1 q.2))
  (hb : ∀ x y, |k x y| ≤ B)

include hk hb in
theorem kernel_row_integrable (μ : Measure Sphere8) [IsFiniteMeasure μ] (x : Sphere8) :
    Integrable (k x) μ := by
  have hm : StronglyMeasurable (k x) :=
    hk.comp_measurable (measurable_const.prodMk measurable_id)
  exact (integrable_const B).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb x y)

include hk in
theorem kernelPotential8_stronglyMeasurable (A : Set Sphere8) :
    StronglyMeasurable (kernelPotential8 k A) :=
  hk.integral_prod_right'

include hb in
theorem kernelPotential8_abs_le (A : Set Sphere8) (x : Sphere8) :
    |kernelPotential8 k A x| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb x x)
  unfold kernelPotential8
  calc |∫ y in A, k x y ∂sphereProbability8| = ‖∫ y in A, k x y ∂sphereProbability8‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ B*(sphereProbability8.restrict A).real univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hb x y)
    _ ≤ B*1 := by
        apply mul_le_mul_of_nonneg_left _ hB
        rw [measureReal_restrict_apply_univ]
        exact measureReal_le_one
    _ = B := mul_one B

include hk hb in
theorem kernelPotential8_integrable (μ : Measure Sphere8) [IsFiniteMeasure μ] (A : Set Sphere8) :
    Integrable (kernelPotential8 k A) μ :=
  (integrable_const B).mono' (kernelPotential8_stronglyMeasurable hk A).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact kernelPotential8_abs_le hb A x)

include hk hb in
theorem kernelPotential8_add_compl (S : Set Sphere8) (hS : MeasurableSet S) (x : Sphere8) :
    kernelPotential8 k S x+kernelPotential8 k Sᶜ x = kernelPotential8 k univ x := by
  unfold kernelPotential8
  rw [integral_add_compl hS (kernel_row_integrable hk hb _ x), setIntegral_univ]

include hk hb in
theorem kernel_pair_integrable (S T : Set Sphere8) :
    Integrable (fun q : Sphere8 × Sphere8 => k q.1 q.2)
      ((sphereProbability8.restrict S).prod (sphereProbability8.restrict T)) :=
  (integrable_const B).mono' hk.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hb q.1 q.2)

include hk hb in
theorem kernelBackground8_symm (hs : ∀ x y, k x y = k y x) (S T : Set Sphere8) :
    kernelBackground8 k S T = kernelBackground8 k T S := by
  unfold kernelBackground8 kernelPotential8
  rw [integral_integral_swap (kernel_pair_integrable hk hb S T)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => integral_congr_ae
    (Filter.Eventually.of_forall (fun x => hs x y)))

include hk hb in
theorem kernelBackground8_add_compl (A S : Set Sphere8) (hS : MeasurableSet S) :
    kernelBackground8 k A S+kernelBackground8 k A Sᶜ = kernelBackground8 k A univ := by
  unfold kernelBackground8
  rw [← integral_add (kernelPotential8_integrable hk hb _ S)
    (kernelPotential8_integrable hk hb _ Sᶜ)]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun x => kernelPotential8_add_compl hk hb S hS x))

include hk hb in
theorem kernelBackground8_compl_left (A S : Set Sphere8) (hA : MeasurableSet A) :
    kernelBackground8 k A S+kernelBackground8 k Aᶜ S = kernelBackground8 k univ S := by
  unfold kernelBackground8
  rw [integral_add_compl hA (kernelPotential8_integrable hk hb _ S), setIntegral_univ]

include hk hb in
theorem kernelBackground8_split (hs : ∀ x y, k x y = k y x) (S : Set Sphere8)
    (hS : MeasurableSet S) :
    kernelBackground8 k univ univ = kernelBackground8 k S S+2*kernelBackground8 k Sᶜ S+
      kernelBackground8 k Sᶜ Sᶜ := by
  have h1 := kernelBackground8_add_compl hk hb S S hS
  have h2 := kernelBackground8_add_compl hk hb Sᶜ S hS
  have h3 := kernelBackground8_compl_left hk hb S univ hS
  rw [kernelBackground8_symm hk hb hs S Sᶜ] at h1
  linarith

theorem kernel_restricted_row (A : Set Sphere8) (x : Sphere8) :
    residualRowPotential (sphereRestrictedProbability8 A) k x =
      ((sphereProbability8 A)⁻¹).toReal*kernelPotential8 k A x := by
  simp only [residualRowPotential, sphereRestrictedProbability8, integral_smul_measure,
    smul_eq_mul, kernelPotential8]

theorem kernel_restricted_background (A : Set Sphere8) :
    residualBackground (sphereRestrictedProbability8 A) k =
      (((sphereProbability8 A)⁻¹).toReal)^2*kernelBackground8 k A A := by
  unfold residualBackground
  simp_rw [kernel_restricted_row]
  rw [sphereRestrictedProbability8, integral_smul_measure, integral_const_mul]
  simp only [smul_eq_mul, kernelBackground8]
  ring

include hk hb in
theorem kernelCrossRow8_integral {p : ℕ} (X : Fin p → Sphere8) (A S : Set Sphere8) (M : ℝ)
    (hA : sphereProbability8 A ≠ 0) :
    (∫ x, kernelCrossRow8 k X S M x ∂sphereRestrictedProbability8 A) =
      2*((∑ i, residualRowPotential (sphereRestrictedProbability8 A) k (X i))-
        M*((sphereProbability8 A)⁻¹).toReal*kernelBackground8 k A S) := by
  let := sphereRestrictedProbability8_probability A hA
  have hsym : ∀ i, (fun x => k (X i) x) = k (X i) := fun i => rfl
  have hk' : Integrable (fun x => ∑ i, k (X i) x) (sphereRestrictedProbability8 A) :=
    integrable_finsetSum _ (fun i _ => kernel_row_integrable hk hb _ (X i))
  unfold kernelCrossRow8
  rw [integral_const_mul, integral_sub hk' ((kernelPotential8_integrable hk hb _ S).const_mul M),
    integral_const_mul, integral_finsetSum _ (fun i _ => kernel_row_integrable hk hb _ (X i))]
  unfold residualRowPotential
  rw [sphereRestrictedProbability8, integral_smul_measure]
  simp only [smul_eq_mul, kernelBackground8]
  ring

include hk hb in
/-- The residual assembly for a bounded symmetric kernel. -/
theorem kernelBlock8_residual_assembly (hs : ∀ x y, k x y = k y x) {p r : ℕ}
    (X : Fin p → Sphere8) (Z : Fin r → Sphere8) (S : Set Sphere8) (hS : MeasurableSet S)
    (hA : sphereProbability8 Sᶜ ≠ 0) (M : ℝ) (hr : (r:ℝ) = M*sphereProbability8.real Sᶜ) :
    kernelBlock8 k (Sum.elim X Z) univ M = kernelBlock8 k X S M +
      residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) k (kernelCrossRow8 k X S M) Z := by
  have hm := sphereRestrictedProbability8_mass_match Sᶜ hA r M hr
  have hrow : ∀ x, (r:ℝ)*residualRowPotential (sphereRestrictedProbability8 Sᶜ) k x =
      M*kernelPotential8 k Sᶜ x := by
    intro x
    rw [kernel_restricted_row, ← mul_assoc, hm]
  have hbg : (r:ℝ)^2*residualBackground (sphereRestrictedProbability8 Sᶜ) k =
      M^2*kernelBackground8 k Sᶜ Sᶜ := by
    rw [kernel_restricted_background, ← mul_assoc, ← mul_pow, hm]
  have hcross : (r:ℝ)*(∫ x, kernelCrossRow8 k X S M x ∂sphereRestrictedProbability8 Sᶜ) =
      2*M*(∑ i, kernelPotential8 k Sᶜ (X i))-2*M^2*kernelBackground8 k Sᶜ S := by
    rw [kernelCrossRow8_integral hk hb X Sᶜ S M hA]
    simp_rw [kernel_restricted_row]
    rw [← Finset.mul_sum]
    calc _ = 2*((r:ℝ)*((sphereProbability8 Sᶜ)⁻¹).toReal)*
          (∑ i, kernelPotential8 k Sᶜ (X i))-
          2*M*((r:ℝ)*((sphereProbability8 Sᶜ)⁻¹).toReal)*kernelBackground8 k Sᶜ S := by ring
      _ = _ := by rw [hm]; ring
  have hL : (∑ j, kernelCrossRow8 k X S M (Z j)) =
      2*(∑ j, ∑ i, k (X i) (Z j))-2*M*(∑ j, kernelPotential8 k S (Z j)) := by
    simp only [kernelCrossRow8, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hpair : kernelPair8 k (Sum.elim X Z) = kernelPair8 k X+kernelPair8 k Z+
      2*(∑ j, ∑ i, k (X i) (Z j)) := by
    have hcomm : (∑ i, ∑ j, k (X i) (Z j)) = ∑ j, ∑ i, k (X i) (Z j) := Finset.sum_comm
    have hrev : (∑ j, ∑ i, k (Z j) (X i)) = ∑ j, ∑ i, k (X i) (Z j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_congr rfl (fun i _ => hs (Z j) (X i))
    unfold kernelPair8
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
    rw [hcomm, hrev]
    ring
  have hpot : ∀ x, kernelPotential8 k univ x = kernelPotential8 k S x+kernelPotential8 k Sᶜ x :=
    fun x => (kernelPotential8_add_compl hk hb S hS x).symm
  unfold residualNeutralizedEnergy
  change _ = _+(kernelPair8 k Z-2*(r:ℝ)*(∑ j, residualRowPotential
    (sphereRestrictedProbability8 Sᶜ) k (Z j))+
    (r:ℝ)^2*residualBackground (sphereRestrictedProbability8 Sᶜ) k+
    (∑ j, kernelCrossRow8 k X S M (Z j))-
    (r:ℝ)*(∫ x, kernelCrossRow8 k X S M x ∂sphereRestrictedProbability8 Sᶜ))
  rw [mul_assoc 2 (r:ℝ), Finset.mul_sum]
  simp_rw [hrow]
  rw [hbg, hL, hcross]
  unfold kernelBlock8
  rw [hpair, kernelBackground8_split hk hb hs S hS]
  simp_rw [hpot]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

end

end SphericalRiesz
