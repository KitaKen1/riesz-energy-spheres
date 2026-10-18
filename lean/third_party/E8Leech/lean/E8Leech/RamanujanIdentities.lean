import E8Leech.EisensteinCuspDerivative

/-!
# Actual E4 and E6 derivative identities

The Serre derivative is a genuine level-one form. The pinned rank-one spaces
of weights six and eight and the cusp constants determine it. No E2 derivative,
general finite-index dimension lemma or upstream SpherePacking import is used.
The rank/constant strategy is informed by the fixed Apache-2.0 source candidate
SpherePacking/ModularForms/RamanujanIdentities.lean (de0ce2b6d5a6).
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open UpperHalfPlane Filter
open scoped Manifold Topology MatrixGroups ModularForm

def levelOneSerreDerivative {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2) where
  toSlashInvariantForm := {
    toFun := Derivative.serreDerivative k f
    slash_action_eq' := fun γ hγ => by
      obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.mp hγ
      change Derivative.serreDerivative k f ∣[k + 2] γ' = Derivative.serreDerivative k f
      apply Derivative.serreDerivative_slash_invariant f.holo'
      change (f : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ) γ' = f
      exact f.slash_action_eq' _ ⟨γ', rfl⟩ }
  holo' := Derivative.serreDerivative_mdifferentiable k f.holo'
  bdd_at_cusps' := fun hc => (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A' _ => by
    have hslash : Derivative.serreDerivative k f ∣[k + 2]
        (Matrix.SpecialLinearGroup.mapGL ℝ) A' = Derivative.serreDerivative k f := by
      change Derivative.serreDerivative k f ∣[k + 2] A' = Derivative.serreDerivative k f
      apply Derivative.serreDerivative_slash_invariant f.holo'
      change (f : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ) A' = f
      exact f.slash_action_eq' _ ⟨A', rfl⟩
    exact hslash.symm ▸ serreDerivative_isBoundedAtImInfty_of_levelOne f

private theorem scalar_of_levelOne_rank_one {k : ℤ}
    (hr : Module.rank ℂ (ModularForm 𝒮ℒ k) = 1)
    (f g : ModularForm 𝒮ℒ k) (hg : (qExpansion 1 g).coeff 0 = 1) :
    ∃ c : ℂ, ∀ z : UpperHalfPlane, f z = c * g z := by
  have hne : g ≠ 0 := by
    intro hz
    rw [hz] at hg
    simp [qExpansion_zero] at hg
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' g hne).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hr) f
  refine ⟨c, fun z => ?_⟩
  have h := congrArg (fun F : ModularForm 𝒮ℒ k => F z) hc
  simpa using h.symm

private theorem scalar_of_limit {f g : UpperHalfPlane → ℂ} {c L : ℂ}
    (hfg : ∀ z, f z = c * g z) (hf : Tendsto f atImInfty (𝓝 L))
    (hg : Tendsto g atImInfty (𝓝 1)) : c = L := by
  have h : Tendsto f atImInfty (𝓝 (c * 1)) :=
    (tendsto_const_nhds.mul hg).congr (fun z => (hfg z).symm)
  simpa only [mul_one] using tendsto_nhds_unique h hf

theorem serreDerivative_eisensteinFour (z : UpperHalfPlane) :
    Derivative.serreDerivative 4 ModularForm.E₄ z = -(1 / 3 : ℂ) * ModularForm.E₆ z := by
  have h4 : (qExpansion 1 ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide)
  have h6 : (qExpansion 1 ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide)
  obtain ⟨c, hc⟩ := scalar_of_levelOne_rank_one ModularForm.levelOne_weight_six_rank_one
    (levelOneSerreDerivative ModularForm.E₄) ModularForm.E₆ h6
  have hfun : ∀ w, Derivative.serreDerivative 4 ModularForm.E₄ w = c * ModularForm.E₆ w := hc
  have hl : Tendsto (Derivative.serreDerivative 4 ModularForm.E₄) atImInfty (𝓝 (-(1 / 3 : ℂ))) := by
    have ht := serreDerivative_tendsto_of_levelOne ModularForm.E₄
    norm_num only [Int.cast_ofNat, h4, mul_one] at ht
    exact ht
  have hcval := scalar_of_limit hfun hl (by
    simpa only [h6] using levelOne_tendsto_qExpansion_constant ModularForm.E₆)
  rw [hfun, hcval]

theorem serreDerivative_eisensteinSix (z : UpperHalfPlane) :
    Derivative.serreDerivative 6 ModularForm.E₆ z = -(1 / 2 : ℂ) * ModularForm.E₄ z ^ 2 := by
  have h4 : (qExpansion 1 ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide)
  have h6 : (qExpansion 1 ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide)
  have hsq : (qExpansion 1 (ModularForm.E₄.pow 2)).coeff 0 = 1 := by
    rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    simp [pow_two, PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff, h4]
  have hr : Module.rank ℂ (ModularForm 𝒮ℒ 8) = 1 := by
    simpa [Nat.ModEq] using ModularForm.dimension_level_one 8 (by decide)
  obtain ⟨c, hc⟩ := scalar_of_levelOne_rank_one hr
    (levelOneSerreDerivative ModularForm.E₆) (ModularForm.E₄.pow 2) hsq
  have hfun : ∀ w, Derivative.serreDerivative 6 ModularForm.E₆ w = c * ModularForm.E₄ w ^ 2 := hc
  have hl : Tendsto (Derivative.serreDerivative 6 ModularForm.E₆) atImInfty (𝓝 (-(1 / 2 : ℂ))) := by
    have ht := serreDerivative_tendsto_of_levelOne ModularForm.E₆
    norm_num only [Int.cast_ofNat, h6, mul_one] at ht
    exact ht
  have hcval := scalar_of_limit hfun hl (by
    simpa only [h4, one_pow] using (levelOne_tendsto_qExpansion_constant ModularForm.E₄).pow 2)
  rw [hfun, hcval]

theorem normalizedDeriv_eisensteinFour (z : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex ModularForm.E₄ z =
      (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z) / 3 := by
  have h := serreDerivative_eisensteinFour z
  unfold Derivative.serreDerivative at h
  linear_combination h

theorem normalizedDeriv_eisensteinSix (z : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex ModularForm.E₆ z =
      (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) / 2 := by
  have h := serreDerivative_eisensteinSix z
  unfold Derivative.serreDerivative at h
  linear_combination h

theorem hasDerivAt_eisensteinFour (z : UpperHalfPlane) :
    HasDerivAt (fun w : ℂ => ModularForm.E₄ (ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z)) (z : ℂ) := by
  have h := (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₄.holo' z)).hasDerivAt
  change HasDerivAt (ModularForm.E₄ ∘ ofComplex)
    (deriv (ModularForm.E₄ ∘ ofComplex) (z : ℂ)) (z : ℂ) at h
  apply h.congr_deriv
  have hn := normalizedDeriv_eisensteinFour z
  unfold Derivative.normalizedDerivOfComplex at hn
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [hpi] at hn ⊢
  linear_combination hn

theorem hasDerivAt_eisensteinSix (z : UpperHalfPlane) :
    HasDerivAt (fun w : ℂ => ModularForm.E₆ (ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2)) (z : ℂ) := by
  have h := (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₆.holo' z)).hasDerivAt
  change HasDerivAt (ModularForm.E₆ ∘ ofComplex)
    (deriv (ModularForm.E₆ ∘ ofComplex) (z : ℂ)) (z : ℂ) at h
  apply h.congr_deriv
  have hn := normalizedDeriv_eisensteinSix z
  unfold Derivative.normalizedDerivOfComplex at hn
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [hpi] at hn ⊢
  linear_combination hn

end E8Leech
