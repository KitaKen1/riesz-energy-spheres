import Riesz.SphereResidual8
import Riesz.SphereValue8

/-! Exact splitting and normalization of the actual sphere backgrounds.
All kernel integrability used for Fubini comes from the actual inverse-fourth
kernel, rather than a supplied background-integrability hypothesis. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

def sphereBackgroundPair4 (S T : Set Sphere8) : ℝ :=
  ∫ x in S, sphereRestrictedPotential4 T x ∂sphereProbability8

theorem sphereRestrictedPotential4_add_compl (S : Set Sphere8)
    (hS : MeasurableSet S) (x : Sphere8) :
    sphereRestrictedPotential4 S x + sphereRestrictedPotential4 Sᶜ x = 7/16 := by
  rw [sphereRestrictedPotential4,sphereRestrictedPotential4,
    integral_add_compl hS (sphereKernel4_integrable x)]
  exact spherePotential4_value x

theorem sphereKernel4_restricted_pair_integrable (S T : Set Sphere8) :
    Integrable (fun xy : Sphere8 × Sphere8 => sphereKernel4 xy.1 xy.2)
      ((sphereProbability8.restrict S).prod (sphereProbability8.restrict T)) := by
  rw [Measure.prod_restrict]
  exact sphereKernel4_pair_integrable.restrict

theorem sphereBackgroundPair4_symm (S T : Set Sphere8) :
    sphereBackgroundPair4 S T = sphereBackgroundPair4 T S := by
  unfold sphereBackgroundPair4 sphereRestrictedPotential4
  rw [integral_integral_swap (sphereKernel4_restricted_pair_integrable S T)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => integral_congr_ae
    (Filter.Eventually.of_forall (fun x => sphereKernel4_symm x y)))

theorem sphereBackgroundPair4_add_compl (A S : Set Sphere8) (hS : MeasurableSet S) :
    sphereBackgroundPair4 A S + sphereBackgroundPair4 A Sᶜ =
      sphereProbability8.real A * (7/16) := by
  unfold sphereBackgroundPair4
  rw [← integral_add (sphereRestrictedPotential4_integrable S).restrict
    (sphereRestrictedPotential4_integrable Sᶜ).restrict]
  have h : (∫ x in A, sphereRestrictedPotential4 S x + sphereRestrictedPotential4 Sᶜ x
      ∂sphereProbability8) = ∫ _x in A, (7/16:ℝ) ∂sphereProbability8 :=
    integral_congr_ae (Filter.Eventually.of_forall (sphereRestrictedPotential4_add_compl S hS))
  rw [h,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

theorem sphereBackgroundPair4_split (S : Set Sphere8) (hS : MeasurableSet S) :
    sphereBackgroundPair4 S S + 2*sphereBackgroundPair4 Sᶜ S +
      sphereBackgroundPair4 Sᶜ Sᶜ = 7/16 := by
  have h1 := sphereBackgroundPair4_add_compl S S hS
  have h2 := sphereBackgroundPair4_add_compl Sᶜ S hS
  have hm := probReal_add_probReal_compl (μ := sphereProbability8) hS
  rw [sphereBackgroundPair4_symm S Sᶜ] at h1
  nlinarith

theorem sphereRestrictedProbability8_background (A : Set Sphere8) :
    residualBackground (sphereRestrictedProbability8 A) sphereKernel4 =
      (((sphereProbability8 A)⁻¹).toReal)^2 * sphereBackgroundPair4 A A := by
  unfold residualBackground
  simp_rw [sphereRestrictedProbability8_row]
  rw [sphereRestrictedProbability8,integral_smul_measure,integral_const_mul]
  simp only [smul_eq_mul,sphereBackgroundPair4]
  ring

theorem sphereRestrictedProbability8_mass_match (A : Set Sphere8)
    (hA : sphereProbability8 A ≠ 0) (r M : ℝ)
    (hr : r = M*sphereProbability8.real A) :
    r*((sphereProbability8 A)⁻¹).toReal = M := by
  have ha : sphereProbability8.real A ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hA,measure_ne_top _ _⟩
  rw [hr,ENNReal.toReal_inv]
  change M*sphereProbability8.real A*(sphereProbability8.real A)⁻¹ = M
  rw [mul_assoc,mul_inv_cancel₀ ha,mul_one]

theorem sphereRestrictedProbability8_row_mass_match (A : Set Sphere8)
    (hA : sphereProbability8 A ≠ 0) (r M : ℝ)
    (hr : r = M*sphereProbability8.real A) (x : Sphere8) :
    r*residualRowPotential (sphereRestrictedProbability8 A) sphereKernel4 x =
      M*sphereRestrictedPotential4 A x := by
  rw [sphereRestrictedProbability8_row,← mul_assoc,
    sphereRestrictedProbability8_mass_match A hA r M hr]

theorem sphereRestrictedProbability8_background_mass_match (A : Set Sphere8)
    (hA : sphereProbability8 A ≠ 0) (r M : ℝ)
    (hr : r = M*sphereProbability8.real A) :
    r^2*residualBackground (sphereRestrictedProbability8 A) sphereKernel4 =
      M^2*sphereBackgroundPair4 A A := by
  rw [sphereRestrictedProbability8_background,← mul_assoc,← mul_pow,
    sphereRestrictedProbability8_mass_match A hA r M hr]

theorem sphereResidualCrossRow8_integral {p : ℕ} (X : Fin p → Sphere8)
    (A S : Set Sphere8) (M : ℝ) :
    (∫ x, sphereResidualCrossRow8 X S M x ∂sphereRestrictedProbability8 A) =
      2*((∑ i, residualRowPotential (sphereRestrictedProbability8 A) sphereKernel4 (X i))-
        M*((sphereProbability8 A)⁻¹).toReal*sphereBackgroundPair4 A S) := by
  have hk : Integrable (fun x => ∑ i, sphereKernel4 (X i) x)
      (sphereRestrictedProbability8 A) := integrable_finsetSum _
    (fun i _ => sphereKernel4_restricted_probability_integrable A (X i))
  unfold sphereResidualCrossRow8
  rw [integral_const_mul,integral_sub hk
    ((sphereRestrictedPotential4_restricted_probability_integrable A S).const_mul M),
    integral_const_mul,integral_finsetSum _
      (fun i _ => sphereKernel4_restricted_probability_integrable A (X i))]
  unfold residualRowPotential
  rw [sphereRestrictedProbability8,integral_smul_measure]
  simp only [smul_eq_mul,sphereBackgroundPair4]
  ring

theorem sphereResidualCrossRow8_integral_mass_match {p : ℕ} (X : Fin p → Sphere8)
    (A S : Set Sphere8) (hA : sphereProbability8 A ≠ 0) (r M : ℝ)
    (hr : r = M*sphereProbability8.real A) :
    r*(∫ x, sphereResidualCrossRow8 X S M x ∂sphereRestrictedProbability8 A) =
      2*M*(∑ i, sphereRestrictedPotential4 A (X i))-
        2*M^2*sphereBackgroundPair4 A S := by
  rw [sphereResidualCrossRow8_integral]
  simp_rw [sphereRestrictedProbability8_row]
  rw [← Finset.mul_sum]
  have hm := sphereRestrictedProbability8_mass_match A hA r M hr
  calc
    _ = 2*(r*((sphereProbability8 A)⁻¹).toReal)*
        (∑ i, sphereRestrictedPotential4 A (X i))-
        2*M*(r*((sphereProbability8 A)⁻¹).toReal)*sphereBackgroundPair4 A S := by ring
    _ = _ := by rw [hm];ring

end SphericalRiesz
