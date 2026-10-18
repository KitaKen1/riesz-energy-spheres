import Riesz.RationalLongRangeResidual8

/-! Adding points to a configuration: the mass-split assembly.

For points `X` with background `M σ` and `r` added points `Z` with background `r σ`, the block of
`X ∪ Z` against `(M+r) σ` is the block of `X` plus the residual neutralized energy of `Z` for the
uniform probability, with cross row `2(Σ k(Xᵢ,·) - M ∫ k(y,·) dσ)`.  This holds for bounded
kernels and for the inverse-fourth kernel.  A joint first-moment choice of `Z` for
`sphereKernel4 + w·K⁰` then controls the `s = 4` energy and the long-range block of the enlarged
configuration, as in the residual selection.  Gaussian blocks of configurations against the full
background are `N (F + 1)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz
open Boundary

theorem sphereProbability8_univ_ne_zero : sphereProbability8 univ ≠ 0 := by
  rw [measure_univ]
  exact one_ne_zero

theorem sphereProbability8_univ_inv_toReal : ((sphereProbability8 univ)⁻¹).toReal = 1 := by
  rw [measure_univ, inv_one, ENNReal.toReal_one]

section
variable {k : Sphere8 → Sphere8 → ℝ} {B : ℝ}
  (hk : StronglyMeasurable (fun q : Sphere8 × Sphere8 => k q.1 q.2))
  (hb : ∀ x y, |k x y| ≤ B)

include hk hb in
/-- The mass-split assembly for a bounded symmetric kernel. -/
theorem kernelBlock8_mass_assembly (hs : ∀ x y, k x y = k y x) {q r : ℕ}
    (X : Fin q → Sphere8) (Z : Fin r → Sphere8) (M : ℝ) :
    kernelBlock8 k (Sum.elim X Z) univ (M+r) = kernelBlock8 k X univ M +
      residualNeutralizedEnergy (sphereRestrictedProbability8 univ) k
        (kernelCrossRow8 k X univ M) Z := by
  have hrow : ∀ x, residualRowPotential (sphereRestrictedProbability8 univ) k x =
      kernelPotential8 k univ x := by
    intro x
    rw [kernel_restricted_row, sphereProbability8_univ_inv_toReal, one_mul]
  have hbg : residualBackground (sphereRestrictedProbability8 univ) k =
      kernelBackground8 k univ univ := by
    rw [kernel_restricted_background, sphereProbability8_univ_inv_toReal, one_pow, one_mul]
  have hcross : (∫ x, kernelCrossRow8 k X univ M x ∂sphereRestrictedProbability8 univ) =
      2*((∑ i, kernelPotential8 k univ (X i))-M*kernelBackground8 k univ univ) := by
    rw [kernelCrossRow8_integral hk hb X univ univ M sphereProbability8_univ_ne_zero,
      sphereProbability8_univ_inv_toReal]
    simp_rw [hrow]
    ring
  have hL : (∑ j, kernelCrossRow8 k X univ M (Z j)) =
      2*(∑ j, ∑ i, k (X i) (Z j))-2*M*(∑ j, kernelPotential8 k univ (Z j)) := by
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
  unfold residualNeutralizedEnergy
  change _ = _+(kernelPair8 k Z-2*(r:ℝ)*(∑ j, residualRowPotential
    (sphereRestrictedProbability8 univ) k (Z j))+
    (r:ℝ)^2*residualBackground (sphereRestrictedProbability8 univ) k+
    (∑ j, kernelCrossRow8 k X univ M (Z j))-
    (r:ℝ)*(∫ x, kernelCrossRow8 k X univ M x ∂sphereRestrictedProbability8 univ))
  simp_rw [hrow]
  rw [hbg, hL, hcross]
  unfold kernelBlock8
  rw [hpair]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  ring

end

/-- The mass-split assembly for the inverse-fourth kernel. -/
theorem sphereFiniteBlock4_mass_assembly {q r : ℕ} (X : Fin q → Sphere8) (Z : Fin r → Sphere8)
    (M : ℝ) :
    sphereFiniteBlock4 (Sum.elim X Z) univ (M+r) = sphereFiniteBlock4 X univ M +
      residualNeutralizedEnergy (sphereRestrictedProbability8 univ) sphereKernel4
        (sphereResidualCrossRow8 X univ M) Z := by
  have hrow : ∀ x, residualRowPotential (sphereRestrictedProbability8 univ) sphereKernel4 x =
      7/16 := by
    intro x
    rw [sphereRestrictedProbability8_row, sphereProbability8_univ_inv_toReal, one_mul,
      sphereRestrictedPotential4_univ]
  have hbg : residualBackground (sphereRestrictedProbability8 univ) sphereKernel4 = 7/16 := by
    rw [sphereRestrictedProbability8_background, sphereProbability8_univ_inv_toReal, one_pow,
      one_mul, sphereBackgroundPair4_univ]
  have hcross : (∫ x, sphereResidualCrossRow8 X univ M x ∂sphereRestrictedProbability8 univ) =
      2*((q:ℝ)*(7/16)-M*(7/16)) := by
    rw [sphereResidualCrossRow8_integral, sphereProbability8_univ_inv_toReal, sphereBackgroundPair4_univ]
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hL : (∑ j, sphereResidualCrossRow8 X univ M (Z j)) =
      2*(∑ j, ∑ i, sphereKernel4 (X i) (Z j))-2*M*((r:ℝ)*(7/16)) := by
    simp only [sphereResidualCrossRow8, sphereRestrictedPotential4_univ, mul_sub,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold residualNeutralizedEnergy
  change _ = _+(sphereFinitePair4 Z-2*(r:ℝ)*(∑ j, residualRowPotential
    (sphereRestrictedProbability8 univ) sphereKernel4 (Z j))+
    (r:ℝ)^2*residualBackground (sphereRestrictedProbability8 univ) sphereKernel4+
    (∑ j, sphereResidualCrossRow8 X univ M (Z j))-
    (r:ℝ)*(∫ x, sphereResidualCrossRow8 X univ M x ∂sphereRestrictedProbability8 univ))
  simp_rw [hrow]
  rw [hbg, hL, hcross]
  unfold sphereFiniteBlock4
  rw [sphereFinitePair4_sum, sphereBackgroundPair4_univ]
  simp_rw [sphereRestrictedPotential4_univ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fintype.card_sum, Nat.cast_add]
  ring

/-- Gaussian blocks of a configuration against the full background. -/
theorem gaussianKernelBlock8_config {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (Y : Configuration N) :
    kernelBlock8 (sphereGaussianKernel8 (sphereGaussianScale8 N α)) (fun i => Y i) univ (N:ℝ) =
      (N:ℝ)*(sphereGaussianCenteredScaled8 α Y+1) := by
  have ht : 0 ≤ sphereGaussianScale8 N α := by
    unfold sphereGaussianScale8
    positivity
  have hpot : ∀ x, kernelPotential8 (sphereGaussianKernel8 (sphereGaussianScale8 N α)) univ x =
      sphereGaussianBackground8 (sphereGaussianScale8 N α) := by
    intro x
    unfold kernelPotential8
    rw [setIntegral_univ, sphereGaussianBackground8_eq_potential ht x]
    rfl
  have hbg : kernelBackground8 (sphereGaussianKernel8 (sphereGaussianScale8 N α)) univ univ =
      sphereGaussianBackground8 (sphereGaussianScale8 N α) := by
    unfold kernelBackground8
    simp_rw [hpot]
    rw [setIntegral_univ, integral_const, probReal_univ, one_smul]
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold kernelBlock8 kernelPair8 sphereGaussianCenteredScaled8
  simp_rw [hpot]
  rw [hbg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem longRangeKernel8_measurable_off (c p : ℝ) (μ : Measure Sphere8) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {hc : 0 ≤ c} {hp : -1 < p} :
    Integrable (residualRowPotential μ (longRangeOffKernel8 c p)) μ := by
  have hrow : residualRowPotential μ (longRangeOffKernel8 c p) =
      residualRowPotential μ (longRangeKernel8 c p) :=
    funext fun x => integral_congr_ae (longRangeOffKernel8_ae_eq c p _ x)
  rw [hrow]
  have hm : StronglyMeasurable (residualRowPotential μ (longRangeKernel8 c p)) :=
    (longRangeKernel8_measurable c p).integral_prod_right'
  refine (integrable_const (1/(p+1))).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  unfold residualRowPotential
  rw [Real.norm_eq_abs]
  calc |∫ y, longRangeKernel8 c p x y ∂μ| = ‖∫ y, longRangeKernel8 c p x y ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ 1/(p+1)*μ.real univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact longRangeKernel8_abs_le hc hp x y)
    _ = 1/(p+1) := by rw [probReal_univ, mul_one]

/-- Joint first-moment choice of added points. -/
theorem sphere8_joint_longRange_addition {q r : ℕ} (X : Fin q → Sphere8) (M : ℝ) {c p w : ℝ}
    (hc : 0 ≤ c) (hp : -1 < p) (hw : 0 < w) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧ (∀ i, Z i ∉ range X) ∧
      sphereFiniteBlock4 (Sum.elim X Z) univ (M+r) ≤ sphereFiniteBlock4 X univ M +
        w*(kernelBlock8 (longRangeKernel8 c p) X univ M+(r:ℝ)/(p+1)) ∧
      kernelBlock8 (longRangeKernel8 c p) (Sum.elim X Z) univ (M+r) ≤
        kernelBlock8 (longRangeKernel8 c p) X univ M +
          (sphereFiniteBlock4 X univ M-sphereFiniteBlock4 (Sum.elim X Z) univ (M+r))/w+
            (r:ℝ)/(p+1) := by
  let := sphereRestrictedProbability8_probability univ sphereProbability8_univ_ne_zero
  have hk := longRangeKernel8_measurable c p
  have hb : ∀ x y, |longRangeKernel8 c p x y| ≤ 1/(p+1) := longRangeKernel8_abs_le hc hp
  have hbad : sphereRestrictedProbability8 univ (range X) = 0 := (finite_range X).measure_zero _
  have hk2 : ∀ x, Integrable (longRangeOffKernel8 c p x) (sphereRestrictedProbability8 univ) :=
    fun x => (integrable_const (1/(p+1))).mono'
      (longRangeOffKernel8_row_measurable c p x).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (longRangeOffKernel8_nonneg c p x y)]
        exact longRangeOffKernel8_le hc hp x y)
  have hV2 := longRangeKernel8_measurable_off c p (sphereRestrictedProbability8 univ)
    (hc := hc) (hp := hp)
  have hL2 : Integrable (kernelCrossRow8 (longRangeKernel8 c p) X univ M)
      (sphereRestrictedProbability8 univ) := by
    unfold kernelCrossRow8
    exact ((integrable_finsetSum _ fun i _ => kernel_row_integrable hk hb _ (X i)).sub
      ((kernelPotential8_integrable hk hb _ univ).const_mul M)).const_mul 2
  obtain ⟨Z, hZ, hXB, hjoint⟩ := exists_residualNeutralizedEnergy_joint
    (μ := sphereRestrictedProbability8 univ) sphereKernel4 (longRangeOffKernel8 c p)
    (sphereResidualCrossRow8 X univ M) (kernelCrossRow8 (longRangeKernel8 c p) X univ M) hw.le
    sphereKernel4_symm (longRangeOffKernel8_symm c p) sphereKernel4_diagonal
    (longRangeOffKernel8_self c p) sphereKernel4_nonneg (longRangeOffKernel8_nonneg c p)
    (sphereKernel4_restricted_probability_integrable univ) hk2
    (sphereRestrictedProbability8_row_integrable univ) hV2
    (sphereResidualCrossRow8_integrable X univ univ M) hL2 (range X) hbad r
  have h4 := sphereFiniteBlock4_mass_assembly X Z M
  have hL := kernelBlock8_mass_assembly hk hb (longRangeKernel8_symm c p) X Z M
  have hoff := longRange_residual_off_eq (c := c) hp univ
    (kernelCrossRow8 (longRangeKernel8 c p) X univ M) Z hZ
  have hpsd := longRangeBlock8_nonneg hc hp (Sum.elim X Z) univ (M+r)
  refine ⟨Z, hZ, hXB, ?_, ?_⟩
  · have hlow : -(kernelBlock8 (longRangeKernel8 c p) X univ M+(r:ℝ)/(p+1)) ≤
        residualNeutralizedEnergy (sphereRestrictedProbability8 univ) (longRangeOffKernel8 c p)
          (kernelCrossRow8 (longRangeKernel8 c p) X univ M) Z := by
      rw [hoff]
      linarith
    have := mul_le_mul_of_nonneg_left hlow hw.le
    rw [h4]
    linarith
  · have hNE : residualNeutralizedEnergy (sphereRestrictedProbability8 univ)
        (longRangeOffKernel8 c p) (kernelCrossRow8 (longRangeKernel8 c p) X univ M) Z ≤
        (sphereFiniteBlock4 X univ M-sphereFiniteBlock4 (Sum.elim X Z) univ (M+r))/w := by
      rw [le_div_iff₀ hw, h4]
      linarith
    rw [hL]
    linarith

end SphericalRiesz
