import Riesz.SphereBackgroundSplit8

/-! Exact actual energy assembly after matching the residual integer count
to the sphere-complement mass. Finite equivalences only reindex actual nodes;
no replacement kernel or background is used. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

def sphereFinitePair4 {ι : Type*} [Fintype ι] (X : ι → Sphere8) : ℝ :=
  ∑ i, ∑ j, sphereKernel4 (X i) (X j)

def sphereFiniteBlock4 {ι : Type*} [Fintype ι] (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) : ℝ :=
  sphereFinitePair4 X - 2*M*(∑ i, sphereRestrictedPotential4 S (X i)) +
    M^2*sphereBackgroundPair4 S S

theorem sphereRestrictedPotential4_univ (x : Sphere8) :
    sphereRestrictedPotential4 univ x = 7/16 := by
  simpa only [sphereRestrictedPotential4,setIntegral_univ,spherePotential4] using
    spherePotential4_value x

theorem sphereBackgroundPair4_univ : sphereBackgroundPair4 univ univ = 7/16 := by
  unfold sphereBackgroundPair4
  simp_rw [sphereRestrictedPotential4_univ]
  simp

theorem sphereFinitePair4_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere8) :
    sphereFinitePair4 (X ∘ e) = sphereFinitePair4 X := by
  have hi (x : Sphere8) : (∑ j, sphereKernel4 x (X (e j))) = ∑ j, sphereKernel4 x (X j) :=
    e.sum_comp (fun j => sphereKernel4 x (X j))
  unfold sphereFinitePair4
  simp only [Function.comp_apply]
  simp_rw [hi]
  exact e.sum_comp (fun i => ∑ j, sphereKernel4 (X i) (X j))

theorem sphereFiniteBlock4_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere8) (S : Set Sphere8) (M : ℝ) :
    sphereFiniteBlock4 (X ∘ e) S M = sphereFiniteBlock4 X S M := by
  unfold sphereFiniteBlock4
  rw [sphereFinitePair4_reindex e X]
  have hs := e.sum_comp (fun i => sphereRestrictedPotential4 S (X i))
  simp only [Function.comp_apply]
  rw [hs]

theorem sphereFinitePair4_sum {p r : ℕ} (X : Fin p → Sphere8) (Z : Fin r → Sphere8) :
    sphereFinitePair4 (Sum.elim X Z) = sphereFinitePair4 X + sphereFinitePair4 Z +
      2*(∑ j, ∑ i, sphereKernel4 (X i) (Z j)) := by
  have hcross : (∑ i, ∑ j, sphereKernel4 (X i) (Z j)) =
      ∑ j, ∑ i, sphereKernel4 (X i) (Z j) := Finset.sum_comm
  have hrev : (∑ j, ∑ i, sphereKernel4 (Z j) (X i)) =
      ∑ j, ∑ i, sphereKernel4 (X i) (Z j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun i _ => sphereKernel4_symm (Z j) (X i))
  unfold sphereFinitePair4
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib]
  rw [hcross,hrev]
  ring

theorem residualNeutralizedEnergy_sphere_mass_match {p r : ℕ}
    (X : Fin p → Sphere8) (Z : Fin r → Sphere8) (A S : Set Sphere8)
    (hA : sphereProbability8 A ≠ 0) (M : ℝ)
    (hr : (r:ℝ) = M*sphereProbability8.real A) :
    residualNeutralizedEnergy (sphereRestrictedProbability8 A) sphereKernel4
      (sphereResidualCrossRow8 X S M) Z =
      sphereFinitePair4 Z - 2*M*(∑ j, sphereRestrictedPotential4 A (Z j)) +
      M^2*sphereBackgroundPair4 A A + 2*(∑ j, ∑ i, sphereKernel4 (X i) (Z j))-
      2*M*(∑ j, sphereRestrictedPotential4 S (Z j))-
      2*M*(∑ i, sphereRestrictedPotential4 A (X i))+
      2*M^2*sphereBackgroundPair4 A S := by
  have hrows : (r:ℝ)*(∑ j, residualRowPotential (sphereRestrictedProbability8 A)
      sphereKernel4 (Z j)) = M*(∑ j, sphereRestrictedPotential4 A (Z j)) := by
    simp_rw [sphereRestrictedProbability8_row]
    rw [← Finset.mul_sum,← mul_assoc,sphereRestrictedProbability8_mass_match A hA r M hr]
  have hL : (∑ j, sphereResidualCrossRow8 X S M (Z j)) =
      2*(∑ j, ∑ i, sphereKernel4 (X i) (Z j))-
      2*M*(∑ j, sphereRestrictedPotential4 S (Z j)) := by
    simp only [sphereResidualCrossRow8,mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  unfold residualNeutralizedEnergy
  change sphereFinitePair4 Z - 2*(r:ℝ)*(∑ j, residualRowPotential
    (sphereRestrictedProbability8 A) sphereKernel4 (Z j))+
    (r:ℝ)^2*residualBackground (sphereRestrictedProbability8 A) sphereKernel4+
    (∑ j, sphereResidualCrossRow8 X S M (Z j))-
    (r:ℝ)*(∫ x, sphereResidualCrossRow8 X S M x ∂sphereRestrictedProbability8 A) = _
  rw [mul_assoc 2 (r:ℝ),hrows,
    sphereRestrictedProbability8_background_mass_match A hA r M hr,hL,
    sphereResidualCrossRow8_integral_mass_match X A S hA r M hr]
  ring

theorem sphereFiniteBlock4_residual_assembly {p r : ℕ}
    (X : Fin p → Sphere8) (Z : Fin r → Sphere8) (S : Set Sphere8)
    (hS : MeasurableSet S) (hA : sphereProbability8 Sᶜ ≠ 0) (M : ℝ)
    (hr : (r:ℝ) = M*sphereProbability8.real Sᶜ) :
    sphereFiniteBlock4 (Sum.elim X Z) univ M = sphereFiniteBlock4 X S M +
      residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) sphereKernel4
        (sphereResidualCrossRow8 X S M) Z := by
  have hrow (x : Sphere8) : sphereRestrictedPotential4 univ x =
      sphereRestrictedPotential4 S x + sphereRestrictedPotential4 Sᶜ x := by
    rw [sphereRestrictedPotential4_univ,sphereRestrictedPotential4_add_compl S hS]
  rw [residualNeutralizedEnergy_sphere_mass_match X Z Sᶜ S hA M hr]
  unfold sphereFiniteBlock4
  rw [sphereFinitePair4_sum,sphereBackgroundPair4_univ,← sphereBackgroundPair4_split S hS]
  simp_rw [hrow]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib]
  ring

theorem sphereFiniteBlock4_eq_energy4 {N : ℕ} (Y : Configuration N) :
    sphereFiniteBlock4 Y univ (N:ℝ) = energy4 Y-(7/16:ℝ)*(N:ℝ)^2 := by
  have hp : sphereFinitePair4 Y = energy4 Y := sphereKernel4_pair_offDiagonal Y
  unfold sphereFiniteBlock4
  rw [hp,sphereBackgroundPair4_univ]
  simp_rw [sphereRestrictedPotential4_univ]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem sphereFiniteBlock4_residual_le {p r : ℕ}
    (X : Fin p → Sphere8) (Z : Fin r → Sphere8) (S : Set Sphere8)
    (hS : MeasurableSet S) (hA : sphereProbability8 Sᶜ ≠ 0) (M : ℝ)
    (hr : (r:ℝ) = M*sphereProbability8.real Sᶜ)
    (he : residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) sphereKernel4
      (sphereResidualCrossRow8 X S M) Z ≤ 0) :
    sphereFiniteBlock4 (Sum.elim X Z) univ M ≤ sphereFiniteBlock4 X S M := by
  rw [sphereFiniteBlock4_residual_assembly X Z S hS hA M hr]
  linarith

end SphericalRiesz
