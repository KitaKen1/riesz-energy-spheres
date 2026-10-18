import Riesz.SphereAtomless8
import Riesz.ResidualFirstMoment
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual inverse-fourth residual points in an arbitrary positive-measure
sphere subset. The cross row uses actual fixed nodes and actual sphere
background restrictions. All analytic premises of sequential selection are
discharged here, rather than postulated in the physical conclusion. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalRiesz

def sphereRestrictedProbability8 (A : Set Sphere8) : Measure Sphere8 :=
  (sphereProbability8 A)⁻¹ • sphereProbability8.restrict A

theorem sphereRestrictedProbability8_probability (A : Set Sphere8)
    (hA : sphereProbability8 A ≠ 0) :
    IsProbabilityMeasure (sphereRestrictedProbability8 A) := by
  refine ⟨?_⟩
  simp only [sphereRestrictedProbability8,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top _ _)

instance sphereRestrictedProbability8_nullSingleton (A : Set Sphere8) :
    NullSingletonClass (sphereRestrictedProbability8 A) := by
  refine ⟨fun p => ?_⟩
  simp [sphereRestrictedProbability8,Measure.smul_apply]

theorem sphereRestrictedProbability8_compl (A : Set Sphere8) (hA : MeasurableSet A) :
    sphereRestrictedProbability8 A Aᶜ = 0 := by
  simp [sphereRestrictedProbability8,Measure.smul_apply,Measure.restrict_apply hA.compl]

theorem sphereKernel4_symm (x y : Sphere8) : sphereKernel4 x y = sphereKernel4 y x := by
  simp only [sphereKernel4,dist_comm]

theorem sphereKernel4_diagonal (x : Sphere8) : sphereKernel4 x x = 0 := by
  simp [sphereKernel4]

theorem sphereKernel4_pair_offDiagonal {r : ℕ} (Z : Fin r → Sphere8) :
    residualPairEnergy sphereKernel4 Z =
      ∑ i, ∑ j ∈ Finset.univ.erase i, sphereKernel4 (Z i) (Z j) := by
  classical
  unfold residualPairEnergy
  apply Finset.sum_congr rfl
  intro i _
  have h := Finset.sum_erase_add Finset.univ (fun j => sphereKernel4 (Z i) (Z j))
    (Finset.mem_univ i)
  simpa only [sphereKernel4_diagonal,add_zero] using h.symm

def sphereRestrictedPotential4 (A : Set Sphere8) (x : Sphere8) : ℝ :=
  ∫ y in A, sphereKernel4 x y ∂sphereProbability8

theorem sphereRestrictedPotential4_nonneg (A : Set Sphere8) (x : Sphere8) :
    0 ≤ sphereRestrictedPotential4 A x := integral_nonneg (sphereKernel4_nonneg x)

theorem sphereRestrictedPotential4_le (A : Set Sphere8) (x : Sphere8) :
    sphereRestrictedPotential4 A x ≤ spherePotential4 northPole8 := by
  calc
    _ ≤ spherePotential4 x := setIntegral_le_integral (sphereKernel4_integrable x)
      (Filter.Eventually.of_forall (sphereKernel4_nonneg x))
    _ = _ := spherePotential4_constant x northPole8

theorem sphereRestrictedPotential4_integrable (A : Set Sphere8) :
    Integrable (sphereRestrictedPotential4 A) sphereProbability8 := by
  have hm : StronglyMeasurable (sphereRestrictedPotential4 A) :=
    sphereKernel4_pair_measurable.stronglyMeasurable.integral_prod_right'
  apply (integrable_const (spherePotential4 northPole8)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sphereRestrictedPotential4_nonneg A x)]
    exact sphereRestrictedPotential4_le A x)

theorem sphereKernel4_restricted_probability_integrable (A : Set Sphere8) (x : Sphere8) :
    Integrable (sphereKernel4 x) (sphereRestrictedProbability8 A) := by
  simpa only [sphereRestrictedProbability8,Measure.restrict_apply_univ] using
    (sphereKernel4_integrable x).restrict (s := A) |>.to_average

theorem sphereRestrictedPotential4_restricted_probability_integrable
    (A S : Set Sphere8) :
    Integrable (sphereRestrictedPotential4 S) (sphereRestrictedProbability8 A) := by
  simpa only [sphereRestrictedProbability8,Measure.restrict_apply_univ] using
    (sphereRestrictedPotential4_integrable S).restrict (s := A) |>.to_average

theorem sphereRestrictedProbability8_row (A : Set Sphere8) (x : Sphere8) :
    residualRowPotential (sphereRestrictedProbability8 A) sphereKernel4 x =
      ((sphereProbability8 A)⁻¹).toReal * sphereRestrictedPotential4 A x := by
  simp only [residualRowPotential,sphereRestrictedProbability8,integral_smul_measure,
    smul_eq_mul,sphereRestrictedPotential4]

theorem sphereRestrictedProbability8_row_integrable (A : Set Sphere8) :
    Integrable (residualRowPotential (sphereRestrictedProbability8 A) sphereKernel4)
      (sphereRestrictedProbability8 A) := by
  have he : residualRowPotential (sphereRestrictedProbability8 A) sphereKernel4 =
      fun x => ((sphereProbability8 A)⁻¹).toReal * sphereRestrictedPotential4 A x :=
    funext (sphereRestrictedProbability8_row A)
  rw [he]
  exact (sphereRestrictedPotential4_restricted_probability_integrable A A).const_mul _

def sphereResidualCrossRow8 {p : ℕ} (X : Fin p → Sphere8) (S : Set Sphere8)
    (M : ℝ) (x : Sphere8) : ℝ :=
  2*((∑ i, sphereKernel4 (X i) x)-M*sphereRestrictedPotential4 S x)

theorem sphereResidualCrossRow8_integrable {p : ℕ} (X : Fin p → Sphere8)
    (A S : Set Sphere8) (M : ℝ) :
    Integrable (sphereResidualCrossRow8 X S M) (sphereRestrictedProbability8 A) := by
  have hsum : Integrable (fun x => ∑ i, sphereKernel4 (X i) x)
      (sphereRestrictedProbability8 A) := integrable_finsetSum _
    (fun i _ => sphereKernel4_restricted_probability_integrable A (X i))
  exact (hsum.sub ((sphereRestrictedPotential4_restricted_probability_integrable A S).const_mul M)).const_mul 2

theorem sphere8_exists_residual_points {p : ℕ} (X : Fin p → Sphere8)
    (A S B : Set Sphere8) (hA : MeasurableSet A) (hA0 : sphereProbability8 A ≠ 0)
    (hB : B.Finite) (M : ℝ) (r : ℕ) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧
      (∀ i, Z i ∈ A ∧ Z i ∉ B ∧ Z i ∉ range X) ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 A) sphereKernel4
        (sphereResidualCrossRow8 X S M) Z ≤
          -(r:ℝ)*residualBackground (sphereRestrictedProbability8 A) sphereKernel4 ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 A) sphereKernel4
        (sphereResidualCrossRow8 X S M) Z ≤ 0 := by
  let := sphereRestrictedProbability8_probability A hA0
  have hF : sphereRestrictedProbability8 A (B ∪ range X) = 0 :=
    (hB.union (finite_range X)).measure_zero _
  have hbad : sphereRestrictedProbability8 A (Aᶜ ∪ (B ∪ range X)) = 0 :=
    measure_union_null (sphereRestrictedProbability8_compl A hA) hF
  obtain ⟨Z,hZ,havoid,hbound,hzero⟩ := exists_residualNeutralizedEnergy_nonpos
    sphereKernel4 (sphereResidualCrossRow8 X S M) sphereKernel4_symm sphereKernel4_diagonal
    sphereKernel4_nonneg (sphereKernel4_restricted_probability_integrable A)
    (sphereRestrictedProbability8_row_integrable A)
    (sphereResidualCrossRow8_integrable X A S M) (Aᶜ ∪ (B ∪ range X)) hbad r
  refine ⟨Z,hZ,?_,hbound,hzero⟩
  intro i
  have hi := havoid i
  exact ⟨not_not.mp (fun h => hi (Or.inl h)),
    (fun h => hi (Or.inr (Or.inl h))),(fun h => hi (Or.inr (Or.inr h)))⟩

theorem sphere8_exists_residual_points_physical {p : ℕ} (X : Fin p → Sphere8)
    (A S B : Set Sphere8) (hA : MeasurableSet A) (hA0 : sphereProbability8 A ≠ 0)
    (hB : B.Finite) (M : ℝ) (r : ℕ) :
    let ν := (sphereProbability8 A)⁻¹ • sphereProbability8.restrict A
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧
      (∀ i, Z i ∈ A ∧ Z i ∉ B ∧ Z i ∉ range X) ∧
      (∑ i, ∑ j ∈ Finset.univ.erase i, sphereKernel4 (Z i) (Z j))-
      2*(r:ℝ)*(∑ i, ∫ y, sphereKernel4 (Z i) y ∂ν)+
      (r:ℝ)^2*(∫ x, ∫ y, sphereKernel4 x y ∂ν ∂ν)+
      2*(∑ i, ((∑ j, sphereKernel4 (X j) (Z i))-
        M*(∫ y in S, sphereKernel4 (Z i) y ∂sphereProbability8)))-
      2*(r:ℝ)*(∫ x, ((∑ j, sphereKernel4 (X j) x)-
        M*(∫ y in S, sphereKernel4 x y ∂sphereProbability8)) ∂ν) ≤ 0 := by
  dsimp only
  obtain ⟨Z,hZ,havoid,_,hzero⟩ := sphere8_exists_residual_points X A S B hA hA0 hB M r
  refine ⟨Z,hZ,havoid,?_⟩
  unfold residualNeutralizedEnergy at hzero
  rw [sphereKernel4_pair_offDiagonal] at hzero
  simp only [residualRowPotential,residualBackground,sphereResidualCrossRow8,
    sphereRestrictedPotential4,← Finset.mul_sum,integral_const_mul] at hzero
  unfold sphereRestrictedProbability8 at hzero
  convert hzero using 1 <;> ring

end SphericalRiesz
