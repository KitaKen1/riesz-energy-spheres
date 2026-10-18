import Riesz.SphereShortRangeKernel8
import Riesz.SphereResidualAssembly8

/-! Joint residual selection: the `s = 4` block and the weighted short-range sum.

The residual points are chosen by the sequential first moment for the combined kernel
`sphereKernel4 + w·k_φ` (with the combined cross rows).  Writing `NE₄`, `NE_φ` for the two
neutralized energies, the selection gives `NE₄ + w·NE_φ ≤ 0`; the background terms of the
nonnegative short-range kernel bound `NE_φ` from below by `-B`, so the `s = 4` block grows by at
most `w·B`, while the residual short-range sum is at most `(block gap)/w + B`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

/-- Cross row of the weighted short-range kernel with fixed nodes. -/
def shortRangeCrossRow8 (c p : ℝ) {q : ℕ} (X : Fin q → Sphere8) (z : Sphere8) : ℝ :=
  2*∑ i, shortRangeKernel8 c p (X i) z

theorem shortRangeCrossRow8_nonneg (c p : ℝ) {q : ℕ} (X : Fin q → Sphere8) (z : Sphere8) :
    0 ≤ shortRangeCrossRow8 c p X z :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => shortRangeKernel8_nonneg c p _ _)

theorem shortRangeCrossRow8_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 3) {q : ℕ}
    (X : Fin q → Sphere8) (A : Set Sphere8) :
    Integrable (shortRangeCrossRow8 c p X) (sphereRestrictedProbability8 A) :=
  (integrable_finsetSum _ fun i _ => shortRangeKernel8_restricted_integrable hc hp A (X i)).const_mul 2

theorem shortRangeCrossRow8_integral_le {c p : ℝ} (hc : 0 < c) (hp : p < 3) {q : ℕ}
    (X : Fin q → Sphere8) (A : Set Sphere8) :
    ∫ z, shortRangeCrossRow8 c p X z ∂sphereRestrictedProbability8 A ≤
      2*(q:ℝ)*(((sphereProbability8 A)⁻¹).toReal*((105/32)/c^4/(3-p))) := by
  unfold shortRangeCrossRow8
  rw [integral_const_mul, integral_finsetSum _
    (fun i _ => shortRangeKernel8_restricted_integrable hc hp A (X i))]
  have h : ∀ i, ∫ z, shortRangeKernel8 c p (X i) z ∂sphereRestrictedProbability8 A ≤
      ((sphereProbability8 A)⁻¹).toReal*((105/32)/c^4/(3-p)) :=
    fun i => shortRangeKernel8_restricted_row_le hc hp A (X i)
  calc 2*∑ i, ∫ z, shortRangeKernel8 c p (X i) z ∂sphereRestrictedProbability8 A
      ≤ 2*∑ _i : Fin q, ((sphereProbability8 A)⁻¹).toReal*((105/32)/c^4/(3-p)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by norm_num)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Sphere wrapper of the joint first-moment selection. -/
theorem sphere8_exists_residual_points_joint {q : ℕ} (X : Fin q → Sphere8)
    (A S B : Set Sphere8) (hA : MeasurableSet A) (hA0 : sphereProbability8 A ≠ 0)
    (hB : B.Finite) (M : ℝ) (r : ℕ) {c p w : ℝ} (hc : 0 < c) (hp1 : -1 ≤ p) (hp : p < 3)
    (hw : 0 ≤ w) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧
      (∀ i, Z i ∈ A ∧ Z i ∉ B ∧ Z i ∉ range X) ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 A) sphereKernel4
          (sphereResidualCrossRow8 X S M) Z +
        w*residualNeutralizedEnergy (sphereRestrictedProbability8 A) (shortRangeKernel8 c p)
          (shortRangeCrossRow8 c p X) Z ≤ 0 := by
  let := sphereRestrictedProbability8_probability A hA0
  have hF : sphereRestrictedProbability8 A (B ∪ range X) = 0 :=
    (hB.union (finite_range X)).measure_zero _
  have hbad : sphereRestrictedProbability8 A (Aᶜ ∪ (B ∪ range X)) = 0 :=
    measure_union_null (sphereRestrictedProbability8_compl A hA) hF
  obtain ⟨Z, hZ, havoid, hzero⟩ := exists_residualNeutralizedEnergy_joint
    sphereKernel4 (shortRangeKernel8 c p) (sphereResidualCrossRow8 X S M)
    (shortRangeCrossRow8 c p X) hw
    sphereKernel4_symm (shortRangeKernel8_symm c p) sphereKernel4_diagonal
    (fun x => shortRangeKernel8_self c hp1 x)
    sphereKernel4_nonneg (shortRangeKernel8_nonneg c p)
    (sphereKernel4_restricted_probability_integrable A)
    (fun x => shortRangeKernel8_restricted_integrable hc hp A x)
    (sphereRestrictedProbability8_row_integrable A)
    (shortRangeKernel8_restricted_rowPotential_integrable hc hp A hA0)
    (sphereResidualCrossRow8_integrable X A S M) (shortRangeCrossRow8_integrable hc hp X A)
    (Aᶜ ∪ (B ∪ range X)) hbad r
  refine ⟨Z, hZ, ?_, hzero⟩
  intro i
  have hi := havoid i
  exact ⟨not_not.mp (fun h => hi (Or.inl h)), (fun h => hi (Or.inr (Or.inl h))),
    (fun h => hi (Or.inr (Or.inr h)))⟩

/-- Joint residual assembly: the `s = 4` block grows by at most `w·B`, and the residual
short-range sum is at most `(block gap)/w + B`. -/
theorem sphere8_joint_residual_assembly {q r : ℕ} (X : Fin q → Sphere8) (S : Set Sphere8)
    (hS : MeasurableSet S) (hA0 : sphereProbability8 Sᶜ ≠ 0) (M : ℝ)
    (hr : (r:ℝ) = M*sphereProbability8.real Sᶜ) {c p w : ℝ} (hc : 0 < c) (hp1 : -1 ≤ p)
    (hp : p < 3) (hw : 0 < w) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧ (∀ i, Z i ∈ Sᶜ ∧ Z i ∉ range X) ∧
      sphereFiniteBlock4 (Sum.elim X Z) univ M ≤ sphereFiniteBlock4 X S M+
        w*(2*(r:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))+
          (r:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p))))) ∧
      residualPairEnergy (shortRangeKernel8 c p) Z+∑ i, shortRangeCrossRow8 c p X (Z i) ≤
        (sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)/w+
          (2*(r:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))+
            (r:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p))))) := by
  set R := ((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)) with hR
  let := sphereRestrictedProbability8_probability Sᶜ hA0
  obtain ⟨Z, hZ, havoid, hjoint⟩ := sphere8_exists_residual_points_joint X Sᶜ S ∅ hS.compl hA0
    finite_empty M r hc hp1 hp hw.le
  have hassm := sphereFiniteBlock4_residual_assembly X Z S hS hA0 M hr
  have hrow : ∀ x, residualRowPotential (sphereRestrictedProbability8 Sᶜ) (shortRangeKernel8 c p) x ≤ R :=
    fun x => shortRangeKernel8_restricted_row_le hc hp Sᶜ x
  have hint : ∫ z, shortRangeCrossRow8 c p X z ∂sphereRestrictedProbability8 Sᶜ ≤ 2*(q:ℝ)*R :=
    shortRangeCrossRow8_integral_le hc hp X Sᶜ
  have hlow := residualNeutralizedEnergy_ge_of_nonneg (μ := sphereRestrictedProbability8 Sᶜ)
    (shortRangeKernel8 c p) (shortRangeCrossRow8 c p X) (shortRangeKernel8_nonneg c p)
    (shortRangeCrossRow8_nonneg c p X) hrow hint Z
  have hup := residualPair_add_linear_le (μ := sphereRestrictedProbability8 Sᶜ)
    (shortRangeKernel8 c p) (shortRangeCrossRow8 c p X) (shortRangeKernel8_nonneg c p) hrow hint Z
  refine ⟨Z, hZ, fun i => ⟨(havoid i).1, (havoid i).2.2⟩, ?_, ?_⟩
  · rw [hassm]
    nlinarith [mul_le_mul_of_nonneg_left hlow hw.le, hjoint]
  · have hφ : residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) (shortRangeKernel8 c p)
        (shortRangeCrossRow8 c p X) Z ≤
        (sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)/w := by
      rw [le_div_iff₀ hw, hassm]
      linarith
    linarith

end SphericalRiesz
