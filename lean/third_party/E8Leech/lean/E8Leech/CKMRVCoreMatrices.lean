import E8Leech.CKMRVDenominatorBounds

/-!
# Finite algebra for the four explicit CKMRV coefficient cores

Section 4.4, printed page 60 of arXiv:1902.05438v3 gives diagonal factors
Pi_left, Pi_right around these three-by-three cores. We verify the core
algebra over any field, clearing the Leech-plus gap denominator, and prove
entry signs after substituting the actual Klein values on [3,4] x [1,2].

These are the middle matrices, not the full Upsilon matrices or kernels.
The modular diagonal factors, phi/psi contractions, analytic identities,
and kernel positivity still need proofs. Mixed core signs alone do not
imply the sign of a contracted kernel.
-/

noncomputable section
set_option maxSynthPendingDepth 3
namespace E8Leech
open Set
open scoped BigOperators Matrix

variable {𝕜 : Type*} [Field 𝕜]

def ckmrvEightPlusCore (g : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![g, 0, 1; -2 * g, -2, 0; 1, 0, 0]

def ckmrvEightMinusCore (J : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![-2 * 1728, 0, 0; 0, 1, -1; 0, 1728 - J, J]

def ckmrvLeechPlusCore (J g : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![6, 0, 1728 / g - 6;
     -12 * J + 5 * 1728, -2 * 1728 / g, 12 * J - 7 * 1728;
     1728 / g + 6, 0, -6]

def ckmrvLeechPlusClearedCore (J g : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![6 * g, 0, 1728 - 6 * g;
     (-12 * J + 5 * 1728) * g, -2 * 1728, (12 * J - 7 * 1728) * g;
     1728 + 6 * g, 0, -6 * g]

def ckmrvLeechMinusCore (J g : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![-2 * 1728, -2 * 1728 * g, 0;
     0, J + 2 * g, -1;
     0, 1728 - 2 * g - J, 1]

/-- The division is eliminated once, before any series or interval evaluation. -/
theorem ckmrvLeechPlusCore_clear (J g : 𝕜) (hg : g ≠ 0) :
    g • ckmrvLeechPlusCore J g = ckmrvLeechPlusClearedCore J g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ckmrvLeechPlusCore, ckmrvLeechPlusClearedCore] <;> field_simp

theorem ckmrvEightPlusCore_det (g : 𝕜) : (ckmrvEightPlusCore g).det = 2 := by
  rw [Matrix.det_fin_three]
  simp [ckmrvEightPlusCore]

theorem ckmrvEightMinusCore_det (J : 𝕜) :
    (ckmrvEightMinusCore J).det = -2 * 1728 ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [ckmrvEightMinusCore]
  ring

theorem ckmrvLeechPlusClearedCore_det (J g : 𝕜) :
    (ckmrvLeechPlusClearedCore J g).det = 2 * 1728 ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [ckmrvLeechPlusClearedCore]
  ring

theorem ckmrvLeechMinusCore_det (J g : 𝕜) :
    (ckmrvLeechMinusCore J g).det = -2 * 1728 ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [ckmrvLeechMinusCore]
  ring

/-- The two finite vectors include whatever diagonal factors are later certified. -/
def ckmrvCoreContraction (a b : Fin 3 → 𝕜) (M : Matrix (Fin 3) (Fin 3) 𝕜) : 𝕜 :=
  ∑ i, ∑ j, a i * M i j * b j

theorem ckmrvEightPlusCore_contract (a b : Fin 3 → 𝕜) (g : 𝕜) :
    ckmrvCoreContraction a b (ckmrvEightPlusCore g) =
      g * (a 0 - 2 * a 1) * b 0 + a 0 * b 2 - 2 * a 1 * b 1 + a 2 * b 0 := by
  simp [ckmrvCoreContraction, ckmrvEightPlusCore, Fin.sum_univ_three]
  ring

theorem ckmrvEightMinusCore_contract (a b : Fin 3 → 𝕜) (J : 𝕜) :
    ckmrvCoreContraction a b (ckmrvEightMinusCore J) =
      -2 * 1728 * a 0 * b 0 + a 1 * (b 1 - b 2) +
        a 2 * (1728 * b 1 + J * (b 2 - b 1)) := by
  simp [ckmrvCoreContraction, ckmrvEightMinusCore, Fin.sum_univ_three]
  ring

theorem ckmrvLeechPlusClearedCore_contract (a b : Fin 3 → 𝕜) (J g : 𝕜) :
    ckmrvCoreContraction a b (ckmrvLeechPlusClearedCore J g) =
      6 * g * (a 0 + a 2) * (b 0 - b 2) +
        1728 * (a 0 * b 2 + a 2 * b 0 - 2 * a 1 * b 1) +
        g * a 1 * ((-12 * J + 5 * 1728) * b 0 + (12 * J - 7 * 1728) * b 2) := by
  simp [ckmrvCoreContraction, ckmrvLeechPlusClearedCore, Fin.sum_univ_three]
  ring

theorem ckmrvLeechMinusCore_contract (a b : Fin 3 → 𝕜) (J g : 𝕜) :
    ckmrvCoreContraction a b (ckmrvLeechMinusCore J g) =
      -2 * 1728 * a 0 * (b 0 + g * b 1) +
        (a 1 - a 2) * ((J + 2 * g) * b 1 - b 2) + 1728 * a 2 * b 1 := by
  simp [ckmrvCoreContraction, ckmrvLeechMinusCore, Fin.sum_univ_three]
  ring

theorem ckmrvLeechPlusCore_contract_clear (a b : Fin 3 → 𝕜) (J g : 𝕜) (hg : g ≠ 0) :
    g * ckmrvCoreContraction a b (ckmrvLeechPlusCore J g) =
      ckmrvCoreContraction a b (ckmrvLeechPlusClearedCore J g) := by
  simp [ckmrvCoreContraction, ckmrvLeechPlusCore, ckmrvLeechPlusClearedCore,
    Fin.sum_univ_three]
  field_simp

-- Entry signs on the block for the actual Klein values, with no numerical oracle.
theorem ckmrv_gap_reciprocal_block_upper {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    0 < 1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) ∧
      1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) ≤ 27 / 31250 := by
  have hg := kleinJQ_imaginary_rectangle_gap hy hv
  have hp : 0 < kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v) := by
    linarith only [hg]
  refine ⟨div_pos (by norm_num) hp, (div_le_iff₀ hp).mpr ?_⟩
  linarith only [hg]

theorem ckmrvLeechPlusCore_block_signs {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    let M := ckmrvLeechPlusCore (kleinJQ (imaginaryNome y))
      (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v))
    0 < M 0 0 ∧ M 0 1 = 0 ∧ M 0 2 < 0 ∧
      M 1 0 < 0 ∧ M 1 1 < 0 ∧ 0 < M 1 2 ∧
      0 < M 2 0 ∧ M 2 1 = 0 ∧ M 2 2 < 0 := by
  have hj := kleinJQ_imaginary_dual_lower hy.1
  have hg := ckmrv_gap_reciprocal_block_upper hy hv
  change 0 < (6 : ℝ) ∧ (0 : ℝ) = 0 ∧
    1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) - 6 < 0 ∧
    -12 * kleinJQ (imaginaryNome y) + 5 * 1728 < 0 ∧
    -2 * 1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) < 0 ∧
    0 < 12 * kleinJQ (imaginaryNome y) - 7 * 1728 ∧
    0 < 1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) + 6 ∧
    (0 : ℝ) = 0 ∧ (-6 : ℝ) < 0
  have hn : -2 * 1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) =
      -2 * (1728 / (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v))) := by ring
  rw [hn]
  refine ⟨by norm_num, rfl, by linarith only [hg.2], by linarith only [hj],
    by linarith only [hg.1], by linarith only [hj], by linarith only [hg.1],
    rfl, by norm_num⟩

theorem ckmrvEightPlusCore_block_signs {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    let M := ckmrvEightPlusCore (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v))
    0 < M 0 0 ∧ M 1 0 < 0 ∧ M 1 1 < 0 ∧ M 0 2 = 1 ∧ M 2 0 = 1 := by
  have hg := kleinJQ_imaginary_rectangle_gap hy hv
  change 0 < kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v) ∧
    -2 * (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) < 0 ∧
    (-2 : ℝ) < 0 ∧ (1 : ℝ) = 1 ∧ (1 : ℝ) = 1
  exact ⟨by linarith only [hg], by linarith only [hg], by norm_num, rfl, rfl⟩

theorem ckmrvEightMinusCore_block_signs {y : ℝ} (hy : 3 ≤ y) :
    let M := ckmrvEightMinusCore (kleinJQ (imaginaryNome y))
    M 0 0 < 0 ∧ M 1 1 = 1 ∧ M 1 2 = -1 ∧ M 2 1 < 0 ∧ 0 < M 2 2 := by
  have hj := kleinJQ_imaginary_dual_lower hy
  change (-2 * 1728 : ℝ) < 0 ∧ (1 : ℝ) = 1 ∧ (-1 : ℝ) = -1 ∧
    1728 - kleinJQ (imaginaryNome y) < 0 ∧ 0 < kleinJQ (imaginaryNome y)
  exact ⟨by norm_num, rfl, rfl, by linarith only [hj], by linarith only [hj]⟩

theorem ckmrvLeechMinusCore_block_signs {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    let M := ckmrvLeechMinusCore (kleinJQ (imaginaryNome y))
      (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v))
    M 0 0 < 0 ∧ M 0 1 < 0 ∧ 0 < M 1 1 ∧ M 1 2 = -1 ∧ M 2 1 < 0 ∧ M 2 2 = 1 := by
  have hj := kleinJQ_imaginary_dual_lower hy.1
  have hg := kleinJQ_imaginary_rectangle_gap hy hv
  change (-2 * 1728 : ℝ) < 0 ∧
    -2 * 1728 * (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) < 0 ∧
    0 < kleinJQ (imaginaryNome y) + 2 * (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) ∧
    (-1 : ℝ) = -1 ∧
    1728 - 2 * (kleinJQ (imaginaryNome y) - kleinJQ (imaginaryNome v)) -
      kleinJQ (imaginaryNome y) < 0 ∧ (1 : ℝ) = 1
  exact ⟨by norm_num, by linarith only [hg], by linarith only [hj, hg],
    rfl, by linarith only [hj, hg], rfl⟩

theorem ckmrvLeechPlusCore_actual_block_clear {y v : ℝ}
    (hy : y ∈ Icc (3 : ℝ) 4) (hv : v ∈ Icc (1 : ℝ) 2) :
    let J := (kleinImaginaryJ y).re
    let g := (kleinImaginaryJ y - kleinImaginaryJ v).re
    g • ckmrvLeechPlusCore J g = ckmrvLeechPlusClearedCore J g := by
  apply ckmrvLeechPlusCore_clear
  have hg := kleinImaginaryJ_rectangle_real_gap hy hv
  linarith only [hg]

end E8Leech
