import E8Leech.CKMRVPlusKernels

/-!
# Finite unshifted diagonal limits of the actual plus formulas

The contracted polynomial numerator vanishes on the diagonal. Divide its
normalized holomorphic form by the actual j difference, whose derivative is
nonzero when E4 and E6 are nonzero. This proves a finite punctured limit and
a continuous extension obtained by updating the diagonal value. It does not
assert continuity of Lean's totalized quotient at its original diagonal value,
or handle elliptic points, the minus kernel, or all global kernel identities.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open UpperHalfPlane Filter Function
open scoped Manifold Topology BigOperators

theorem tendsto_removable_quotient {f g : ℂ → ℂ} {x df dg : ℂ}
    (hf : HasDerivAt f df x) (hf0 : f x = 0)
    (hg : HasDerivAt g dg x) (hne : dg ≠ 0) :
    Tendsto (fun w => f w / (g w - g x)) (𝓝[≠] x) (𝓝 (df / dg)) := by
  have h := hf.tendsto_slope.div hg.tendsto_slope hne
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hx : w - x ≠ 0 := sub_ne_zero.mpr hw
  simp only [Pi.div_apply, slope_def_field, hf0, sub_zero]
  rw [div_div_div_cancel_right₀ hx]

def ckmrvEightPlusNormalizedNumerator (τ z : UpperHalfPlane) : ℂ :=
  (ckmrvPlusScale⁻¹ * ckmrvCoreContraction (ckmrvPhiBasis τ) (ckmrvTildePhiBasis z)
    (ckmrvEightPlusPolynomialNumerator τ z)) /
      (ModularForm.discriminant τ * ModularForm.discriminant z)

def ckmrvLeechPlusNormalizedNumerator (τ z : UpperHalfPlane) : ℂ :=
  ((1728 * ckmrvPlusScale)⁻¹ *
    ckmrvCoreContraction (ckmrvPhiBasis τ) (ckmrvTildePhiBasis z)
      (ckmrvLeechPlusPolynomialNumerator τ z)) /
        (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2)

theorem ckmrvEightPlusNormalizedNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvEightPlusNormalizedNumerator z z = 0 := by
  simp only [ckmrvEightPlusNormalizedNumerator,
    ckmrvEightPlusPolynomialNumerator_diagonal, ckmrvCoreContraction_smul,
    ckmrvPlusResidue_contract_self, mul_zero, zero_div]

theorem ckmrvLeechPlusNormalizedNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvLeechPlusNormalizedNumerator z z = 0 := by
  simp only [ckmrvLeechPlusNormalizedNumerator,
    ckmrvLeechPlusPolynomialNumerator_diagonal, ckmrvCoreContraction_smul,
    ckmrvPlusResidue_contract_self, mul_zero, zero_div]

theorem mdifferentiable_ckmrvEightPlusNormalizedNumerator :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusNormalizedNumerator p.1 p.2) := by
  have hN : MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvCoreContraction (ckmrvPhiBasis p.1) (ckmrvTildePhiBasis p.2)
        (ckmrvEightPlusPolynomialNumerator p.1 p.2)) := by
    have h (i j : Fin 3) : MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
        ckmrvPhiBasis p.1 i * ckmrvEightPlusPolynomialNumerator p.1 p.2 i j *
          ckmrvTildePhiBasis p.2 j) :=
      (((mdifferentiable_ckmrvPhiBasis i).comp mdifferentiable_fst).mul
        (mdifferentiable_ckmrvEightPlusPolynomialNumerator_entry i j)).mul
          ((mdifferentiable_ckmrvTildePhiBasis j).comp mdifferentiable_snd)
    have hs := (((((h 0 0).add (h 0 1)).add (h 0 2)).add
      (((h 1 0).add (h 1 1)).add (h 1 2))).add
        (((h 2 0).add (h 2 1)).add (h 2 2)))
    convert hs using 1
    funext p
    simp only [ckmrvCoreContraction, Fin.sum_univ_three, Pi.add_apply]
  exact (mdifferentiable_const.mul hN).div
    ((mdifferentiable_modularDiscriminant.comp mdifferentiable_fst).mul
      (mdifferentiable_modularDiscriminant.comp mdifferentiable_snd))
    (fun p => mul_ne_zero (ModularForm.discriminant_ne_zero p.1)
      (ModularForm.discriminant_ne_zero p.2))

theorem mdifferentiable_ckmrvLeechPlusNormalizedNumerator :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusNormalizedNumerator p.1 p.2) := by
  have hN : MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvCoreContraction (ckmrvPhiBasis p.1) (ckmrvTildePhiBasis p.2)
        (ckmrvLeechPlusPolynomialNumerator p.1 p.2)) := by
    have h (i j : Fin 3) : MDiff (fun p : UpperHalfPlane × UpperHalfPlane =>
        ckmrvPhiBasis p.1 i * ckmrvLeechPlusPolynomialNumerator p.1 p.2 i j *
          ckmrvTildePhiBasis p.2 j) :=
      (((mdifferentiable_ckmrvPhiBasis i).comp mdifferentiable_fst).mul
        (mdifferentiable_ckmrvLeechPlusPolynomialNumerator_entry i j)).mul
          ((mdifferentiable_ckmrvTildePhiBasis j).comp mdifferentiable_snd)
    have hs := (((((h 0 0).add (h 0 1)).add (h 0 2)).add
      (((h 1 0).add (h 1 1)).add (h 1 2))).add
        (((h 2 0).add (h 2 1)).add (h 2 2)))
    convert hs using 1
    funext p
    simp only [ckmrvCoreContraction, Fin.sum_univ_three, Pi.add_apply]
  exact (mdifferentiable_const.mul hN).div
    ((mdifferentiable_modularDiscriminant.comp mdifferentiable_fst).mul
      ((mdifferentiable_modularDiscriminant.comp mdifferentiable_snd).pow 2))
    (fun p => mul_ne_zero (ModularForm.discriminant_ne_zero p.1)
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero p.2)))

theorem ckmrvEightPlusKernel_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) :
    ckmrvEightPlusKernel τ z = ckmrvEightPlusNormalizedNumerator τ z /
      (kleinModularJ τ - kleinModularJ z) := by
  unfold ckmrvEightPlusKernel ckmrvEightPlusNormalizedNumerator ckmrvCoreContraction
  simp_rw [ckmrvEightPlusCoefficientMatrix_quotient τ z hg,
    ckmrvKleinCrossDifference_eq, div_div]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ckmrvLeechPlusKernel_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) :
    ckmrvLeechPlusKernel τ z = ckmrvLeechPlusNormalizedNumerator τ z /
      (kleinModularJ τ - kleinModularJ z) := by
  unfold ckmrvLeechPlusKernel ckmrvLeechPlusNormalizedNumerator ckmrvCoreContraction
  simp_rw [ckmrvLeechPlusCoefficientMatrix_quotient τ z hg,
    ckmrvLeechPolynomialDenominator_eq, div_div]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tendsto_ckmrvEightPlusKernel_diagonal_finite
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => ckmrvEightPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 (deriv (fun w : ℂ =>
        ckmrvEightPlusNormalizedNumerator (ofComplex w) z) (z : ℂ) /
          kleinModularJDerivative z)) := by
  have hn := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_ckmrvEightPlusNormalizedNumerator.comp
      (mdifferentiable_id.prodMk (mdifferentiable_const (c := z)))) z).differentiableAt.hasDerivAt
  have hj := (kleinModularJDerivative_ne_zero_iff z).mpr ⟨hA, hB⟩
  have h := tendsto_removable_quotient hn
    (by simpa only [ofComplex_apply, Function.comp_def, id_eq] using
      ckmrvEightPlusNormalizedNumerator_diagonal z)
    (hasDerivAt_kleinModularJ z) hj
  apply h.congr'
  filter_upwards [eventually_kleinModularJ_gap_ne_zero z hj] with w hw
  simpa only [ofComplex_apply, Function.comp_def, id_eq] using
    (ckmrvEightPlusKernel_quotient (ofComplex w) z hw).symm

theorem tendsto_ckmrvLeechPlusKernel_diagonal_finite
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => ckmrvLeechPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 (deriv (fun w : ℂ =>
        ckmrvLeechPlusNormalizedNumerator (ofComplex w) z) (z : ℂ) /
          kleinModularJDerivative z)) := by
  have hn := (analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_ckmrvLeechPlusNormalizedNumerator.comp
      (mdifferentiable_id.prodMk (mdifferentiable_const (c := z)))) z).differentiableAt.hasDerivAt
  have hj := (kleinModularJDerivative_ne_zero_iff z).mpr ⟨hA, hB⟩
  have h := tendsto_removable_quotient hn
    (by simpa only [ofComplex_apply, Function.comp_def, id_eq] using
      ckmrvLeechPlusNormalizedNumerator_diagonal z)
    (hasDerivAt_kleinModularJ z) hj
  apply h.congr'
  filter_upwards [eventually_kleinModularJ_gap_ne_zero z hj] with w hw
  simpa only [ofComplex_apply, Function.comp_def, id_eq] using
    (ckmrvLeechPlusKernel_quotient (ofComplex w) z hw).symm

theorem exists_ckmrvEightPlusKernel_continuous_diagonal_extension
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvEightPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 L) ∧
      ContinuousAt (Function.update (fun w : ℂ => ckmrvEightPlusKernel (ofComplex w) z)
        (z : ℂ) L) (z : ℂ) := by
  classical
  exact ⟨_, tendsto_ckmrvEightPlusKernel_diagonal_finite z hA hB,
    continuousAt_update_same.mpr (tendsto_ckmrvEightPlusKernel_diagonal_finite z hA hB)⟩

theorem exists_ckmrvLeechPlusKernel_continuous_diagonal_extension
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvLeechPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 L) ∧
      ContinuousAt (Function.update (fun w : ℂ => ckmrvLeechPlusKernel (ofComplex w) z)
        (z : ℂ) L) (z : ℂ) := by
  classical
  exact ⟨_, tendsto_ckmrvLeechPlusKernel_diagonal_finite z hA hB,
    continuousAt_update_same.mpr (tendsto_ckmrvLeechPlusKernel_diagonal_finite z hA hB)⟩

end E8Leech
