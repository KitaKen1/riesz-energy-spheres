import E8Leech.ModularImaginaryIdentities

/-!
# Normalized products in the one-dimensional weights 8, 10 and 14

Use the known product as a candidate, then check the constant coefficient.
The pinned dimension formula makes each relevant space one-dimensional.
In particular weight 14 needs no new Bernoulli value or first coefficient.
These are identities with Mathlib's actual normalized Eisenstein series,
not definitions replacing the series by an unproved product.
-/

set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 3

noncomputable section
namespace E8Leech
open UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

/-- A normalized constant term determines a form in a rank-one space. -/
theorem normalized_levelOne_eq_of_rank_one {k : ℤ}
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k) = 1)
    (f g : ModularForm 𝒮ℒ k)
    (hf : (qExpansion 1 f).coeff 0 = 1)
    (hg : (qExpansion 1 g).coeff 0 = 1) : f = g := by
  have hne : g ≠ 0 := by
    intro hzero
    have h := hg
    rw [hzero] at h
    simp [qExpansion_zero] at h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' g hne).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f
  have hq := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c g
  have hcf : c • (g : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) := by
    ext z
    exact congrArg (fun F => F z) hc
  rw [hcf] at hq
  have hcoeff := congrArg (fun p : PowerSeries ℂ => p.coeff 0) hq
  rw [hf, PowerSeries.coeff_smul, hg] at hcoeff
  have hc1 : c = 1 := by simpa using hcoeff.symm
  rw [hc1, one_smul] at hc
  exact hc.symm

theorem eisensteinEight_eq_four_sq (z : UpperHalfPlane) :
    ModularForm.E (by norm_num : 3 ≤ 8) z = ModularForm.E₄ z ^ 2 := by
  have hrank : Module.rank ℂ (ModularForm 𝒮ℒ 8) = 1 := by
    simpa [Nat.ModEq] using ModularForm.dimension_level_one 8 (by decide)
  have h := normalized_levelOne_eq_of_rank_one hrank
    (ModularForm.E (by norm_num : 3 ≤ 8)) (ModularForm.E₄.pow 2)
    (E_qExpansion_coeff_zero _ (by decide)) (by
      rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
      simp [pow_two, PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide : Even 4)])
  exact congrArg (fun f => f z) h

theorem eisensteinTen_eq_four_mul_six (z : UpperHalfPlane) :
    ModularForm.E (by norm_num : 3 ≤ 10) z = ModularForm.E₄ z * ModularForm.E₆ z := by
  have hrank : Module.rank ℂ (ModularForm 𝒮ℒ 10) = 1 := by
    simpa [Nat.ModEq] using ModularForm.dimension_level_one 10 (by decide)
  have h := normalized_levelOne_eq_of_rank_one hrank
    (ModularForm.E (by norm_num : 3 ≤ 10)) (ModularForm.E₄.mul ModularForm.E₆)
    (E_qExpansion_coeff_zero _ (by decide)) (by
      rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
      simp [PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide : Even 4),
        E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide : Even 6)])
  exact congrArg (fun f => f z) h

theorem eisensteinFourteen_eq_four_sq_mul_six (z : UpperHalfPlane) :
    ModularForm.E (by norm_num : 3 ≤ 14) z = ModularForm.E₄ z ^ 2 * ModularForm.E₆ z := by
  have hrank : Module.rank ℂ (ModularForm 𝒮ℒ 14) = 1 := by
    simpa [Nat.ModEq] using ModularForm.dimension_level_one 14 (by decide)
  have h := normalized_levelOne_eq_of_rank_one hrank
    (ModularForm.E (by norm_num : 3 ≤ 14)) ((ModularForm.E₄.pow 2).mul ModularForm.E₆)
    (E_qExpansion_coeff_zero _ (by decide)) (by
      rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
      simp [pow_two, PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide : Even 4),
        E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide : Even 6)])
  exact congrArg (fun f => f z) h

end E8Leech
