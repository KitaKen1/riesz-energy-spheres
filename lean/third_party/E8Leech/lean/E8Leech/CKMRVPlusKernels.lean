import E8Leech.CKMRVPlusBasis

/-!
# Explicit actual plus kernels and translated diagonal limits

Contract the published actual coefficient matrices with the actual phi and
tilde-phi bases. At E4/E6 nonzero points the integer-translation residue is
-n/(2*pi), including zero at the identity and -1/(2*pi) at T.
This proves the explicit plus formulas' local properties, not every global
functional equation, cusp bound, minus kernel, Fourier or energy certificate.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open UpperHalfPlane Filter Function
open scoped Manifold Topology Matrix BigOperators

theorem tendsto_ckmrvCoreContraction_scaled
    (a : ℂ → Fin 3 → ℂ) (b a₀ : Fin 3 → ℂ)
    (U : ℂ → Matrix (Fin 3) (Fin 3) ℂ) (R : Matrix (Fin 3) (Fin 3) ℂ)
    (x : ℂ) (ha : ∀ i, Tendsto (fun w => a w i) (𝓝[≠] x) (𝓝 (a₀ i)))
    (hU : ∀ i j, Tendsto (fun w => (w - x) * U w i j) (𝓝[≠] x) (𝓝 (R i j))) :
    Tendsto (fun w => (w - x) * ckmrvCoreContraction (a w) b (U w))
      (𝓝[≠] x) (𝓝 (ckmrvCoreContraction a₀ b R)) := by
  have h : Tendsto (fun w => ∑ i : Fin 3, ∑ j : Fin 3,
      a w i * ((w - x) * U w i j) * b j) (𝓝[≠] x)
      (𝓝 (ckmrvCoreContraction a₀ b R)) := by
    exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      ((ha i).mul (hU i j)).mul tendsto_const_nhds))
  apply h.congr
  intro w
  unfold ckmrvCoreContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def ckmrvEightPlusKernel (τ z : UpperHalfPlane) : ℂ :=
  ckmrvCoreContraction (ckmrvPhiBasis τ) (ckmrvTildePhiBasis z)
    (ckmrvEightPlusCoefficientMatrix τ z)

def ckmrvLeechPlusKernel (τ z : UpperHalfPlane) : ℂ :=
  ckmrvCoreContraction (ckmrvPhiBasis τ) (ckmrvTildePhiBasis z)
    (ckmrvLeechPlusCoefficientMatrix τ z)

theorem mdifferentiableOn_ckmrvEightPlusKernel :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusKernel p.1 p.2) := by
  have h (i j : Fin 3) : MDiff[ckmrvRegularLocus]
      (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvPhiBasis p.1 i *
        ckmrvEightPlusCoefficientMatrix p.1 p.2 i j * ckmrvTildePhiBasis p.2 j) :=
    (((mdifferentiable_ckmrvPhiBasis i).comp mdifferentiable_fst).mdifferentiableOn.mul
      (mdifferentiableOn_ckmrvEightPlusCoefficientMatrix_entry i j)).mul
        (((mdifferentiable_ckmrvTildePhiBasis j).comp mdifferentiable_snd).mdifferentiableOn)
  have hs := (((((h 0 0).add (h 0 1)).add (h 0 2)).add
    (((h 1 0).add (h 1 1)).add (h 1 2))).add
      (((h 2 0).add (h 2 1)).add (h 2 2)))
  convert hs using 1
  funext p
  simp only [ckmrvEightPlusKernel, ckmrvCoreContraction, Fin.sum_univ_three, Pi.add_apply]

theorem mdifferentiableOn_ckmrvLeechPlusKernel :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusKernel p.1 p.2) := by
  have h (i j : Fin 3) : MDiff[ckmrvRegularLocus]
      (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvPhiBasis p.1 i *
        ckmrvLeechPlusCoefficientMatrix p.1 p.2 i j * ckmrvTildePhiBasis p.2 j) :=
    (((mdifferentiable_ckmrvPhiBasis i).comp mdifferentiable_fst).mdifferentiableOn.mul
      (mdifferentiableOn_ckmrvLeechPlusCoefficientMatrix_entry i j)).mul
        (((mdifferentiable_ckmrvTildePhiBasis j).comp mdifferentiable_snd).mdifferentiableOn)
  have hs := (((((h 0 0).add (h 0 1)).add (h 0 2)).add
    (((h 1 0).add (h 1 1)).add (h 1 2))).add
      (((h 2 0).add (h 2 1)).add (h 2 2)))
  convert hs using 1
  funext p
  simp only [ckmrvLeechPlusKernel, ckmrvCoreContraction, Fin.sum_univ_three, Pi.add_apply]

theorem meromorphicAt_ckmrvEightPlusKernel_left (z ζ : UpperHalfPlane) :
    MeromorphicAt (fun w => ckmrvEightPlusKernel (ofComplex w) z) (ζ : ℂ) := by
  unfold ckmrvEightPlusKernel ckmrvCoreContraction
  apply MeromorphicAt.fun_sum
  intro i _
  apply MeromorphicAt.fun_sum
  intro j _
  exact (((analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_ckmrvPhiBasis i) ζ).meromorphicAt).mul
      (meromorphicAt_ckmrvEightPlusCoefficientMatrix_entry_comp id (fun _ => z)
        mdifferentiable_id mdifferentiable_const ζ i j)).mul (MeromorphicAt.const (ckmrvTildePhiBasis z j) (ζ : ℂ))

theorem meromorphicAt_ckmrvLeechPlusKernel_left (z ζ : UpperHalfPlane) :
    MeromorphicAt (fun w => ckmrvLeechPlusKernel (ofComplex w) z) (ζ : ℂ) := by
  unfold ckmrvLeechPlusKernel ckmrvCoreContraction
  apply MeromorphicAt.fun_sum
  intro i _
  apply MeromorphicAt.fun_sum
  intro j _
  exact (((analyticAt_of_upperHalfPlane_mdifferentiable
    (mdifferentiable_ckmrvPhiBasis i) ζ).meromorphicAt).mul
      (meromorphicAt_ckmrvLeechPlusCoefficientMatrix_entry_comp id (fun _ => z)
        mdifferentiable_id mdifferentiable_const ζ i j)).mul (MeromorphicAt.const (ckmrvTildePhiBasis z j) (ζ : ℂ))

private theorem mdifferentiable_phi_translate (n : ℤ) (i : Fin 3) :
    MDiff (fun z : UpperHalfPlane => ckmrvPhiBasis (ckmrvTranslate n z) i) := by
  simp_rw [ckmrvPhiBasis_translate]
  fin_cases i
  · exact mdifferentiable_coe.add mdifferentiable_const
  · exact ((mdifferentiable_coe.add mdifferentiable_const).mul E2_mdifferentiable).sub
      mdifferentiable_const
  · exact ((mdifferentiable_coe.add mdifferentiable_const).mul
      (E2_mdifferentiable.pow 2)).sub (mdifferentiable_const.mul E2_mdifferentiable)

private theorem phi_translate_tendsto (n : ℤ) (z : UpperHalfPlane) (i : Fin 3) :
    Tendsto (fun w : ℂ => ckmrvPhiBasis (ckmrvTranslate n (ofComplex w)) i)
      (𝓝[≠] (z : ℂ)) (𝓝 (ckmrvPhiBasis (ckmrvTranslate n z) i)) := by
  simpa only [ofComplex_apply] using
    (analyticAt_of_upperHalfPlane_mdifferentiable
      (mdifferentiable_phi_translate n i) z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem plus_residue_scalar (n : ℤ) (z : UpperHalfPlane) :
    ckmrvCoreContraction (ckmrvPhiBasis (ckmrvTranslate n z)) (ckmrvTildePhiBasis z)
      (((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) = -(n : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [ckmrvCoreContraction_smul, ckmrvPlusResidue_contract_translate]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp]
  ring

theorem tendsto_ckmrvEightPlusKernel_integer_translate
    (n : ℤ) (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightPlusKernel (ckmrvTranslate n (ofComplex w)) z)
      (𝓝[≠] (z : ℂ)) (𝓝 (-(n : ℂ) / (2 * (Real.pi : ℂ)))) := by
  have h := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPhiBasis (ckmrvTranslate n (ofComplex w))) (ckmrvTildePhiBasis z)
    (ckmrvPhiBasis (ckmrvTranslate n z)) (fun w => ckmrvEightPlusCoefficientMatrix (ofComplex w) z)
    (((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) (z : ℂ)
    (phi_translate_tendsto n z) (tendsto_ckmrvEightPlusCoefficientMatrix_published_residue z hA hB)
  rw [plus_residue_scalar] at h
  simpa only [ckmrvEightPlusKernel, ckmrvEightPlusCoefficientMatrix_translate_left] using h

theorem tendsto_ckmrvLeechPlusKernel_integer_translate
    (n : ℤ) (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechPlusKernel (ckmrvTranslate n (ofComplex w)) z)
      (𝓝[≠] (z : ℂ)) (𝓝 (-(n : ℂ) / (2 * (Real.pi : ℂ)))) := by
  have h := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPhiBasis (ckmrvTranslate n (ofComplex w))) (ckmrvTildePhiBasis z)
    (ckmrvPhiBasis (ckmrvTranslate n z)) (fun w => ckmrvLeechPlusCoefficientMatrix (ofComplex w) z)
    (((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) (z : ℂ)
    (phi_translate_tendsto n z) (tendsto_ckmrvLeechPlusCoefficientMatrix_published_residue z hA hB)
  rw [plus_residue_scalar] at h
  simpa only [ckmrvLeechPlusKernel, ckmrvLeechPlusCoefficientMatrix_translate_left] using h

theorem tendsto_ckmrvEightPlusKernel_diagonal_scaled_zero
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) * ckmrvEightPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  simpa [ckmrvTranslate, ofComplex_apply] using
    tendsto_ckmrvEightPlusKernel_integer_translate 0 z hA hB

theorem tendsto_ckmrvLeechPlusKernel_diagonal_scaled_zero
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) * ckmrvLeechPlusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  simpa [ckmrvTranslate, ofComplex_apply] using
    tendsto_ckmrvLeechPlusKernel_integer_translate 0 z hA hB

end E8Leech
