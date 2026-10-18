import E8Leech.CKMRVMinusBasis

/-!
# Right-variable functional equations of the explicit CKMRV kernels

CKMRV Theorem 4.3(2), right half: `K±|^z_{2-d/2} r = 0` for every
`r ∈ Ĩ± = (T − 2I + T⁻¹ ∓ 2S)R + (I ∓ STS)R`.

Known answer first. In every explicit coefficient the `z`-dependence is
`N(j(z)) f_k(z) / (s Δ(z) G(j(z)))`, which is level-one invariant of weight `w_k − 12`
(totalized division keeps this true on `j(τ) = j(z)` as well). Slash actions are
multiplicative, so each kernel relation reduces to the basis relations

* `φ̃` (Proposition 4.7): `T − 2I + T⁻¹ − 2S` and `I − STS`, from the `E₂` laws;
* `ψ̃` (Proposition 4.8): `T − 2I + T⁻¹ + 2S` and `I + STS`, from (2.11), (2.17) and Jacobi,

which are finite algebra. The weights add up to `2 − d/2` in every entry.
Residues, cusp asymptotics, membership in the growth class `P`, signs and the Fourier
side are not addressed here.
-/

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm Matrix BigOperators

/-! ## Slash evaluation -/

theorem ckmrv_slash_S_apply (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] ModularGroup.S) z = f (ModularGroup.S • z) * (z : ℂ) ^ (-k) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]

theorem ckmrv_slash_T_apply_smul (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] ModularGroup.T) z = f (ModularGroup.T • z) := by
  rw [ckmrv_slash_T_apply, ← T_smul_eq_ckmrvTranslate_one]

theorem slash_inv_eq_of_slash_eq {k : ℤ} {f g : ℍ → ℂ} {γ : SL(2, ℤ)} (h : g ∣[k] γ = f) :
    f ∣[k] γ⁻¹ = g := by
  rw [← h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem slash_STS (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] (ModularGroup.S * ModularGroup.T * ModularGroup.S) =
      ((f ∣[k] ModularGroup.S) ∣[k] ModularGroup.T) ∣[k] ModularGroup.S := by
  rw [SlashAction.slash_mul, SlashAction.slash_mul]

theorem eisensteinTwo_T (z : ℍ) :
    EisensteinSeries.E2 (ModularGroup.T • z) = EisensteinSeries.E2 z := by
  rw [T_smul_eq_ckmrvTranslate_one, eisensteinTwo_translate]

/-! ## The relations as predicates, and their closure properties -/

/-- `f|_k (T − 2I + T⁻¹ + 2εS) = 0`. -/
def CKMRVRightRelOne (k : ℤ) (ε : ℂ) (f : ℍ → ℂ) : Prop :=
  f ∣[k] ModularGroup.T - (2 : ℂ) • f + f ∣[k] ModularGroup.T⁻¹ +
    (2 * ε) • (f ∣[k] ModularGroup.S) = 0

/-- `f|_k (I + ε STS) = 0`. -/
def CKMRVRightRelTwo (k : ℤ) (ε : ℂ) (f : ℍ → ℂ) : Prop :=
  f + ε • (f ∣[k] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) = 0

theorem CKMRVRightRelOne.zero (k : ℤ) (ε : ℂ) : CKMRVRightRelOne k ε 0 := by
  simp [CKMRVRightRelOne]

theorem CKMRVRightRelTwo.zero (k : ℤ) (ε : ℂ) : CKMRVRightRelTwo k ε 0 := by
  simp [CKMRVRightRelTwo]

theorem CKMRVRightRelOne.add {k : ℤ} {ε : ℂ} {f g : ℍ → ℂ} (hf : CKMRVRightRelOne k ε f)
    (hg : CKMRVRightRelOne k ε g) : CKMRVRightRelOne k ε (f + g) := by
  unfold CKMRVRightRelOne at *
  simp only [SlashAction.add_slash]
  funext z
  have h1 := congrFun hf z
  have h2 := congrFun hg z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
  linear_combination h1 + h2

theorem CKMRVRightRelTwo.add {k : ℤ} {ε : ℂ} {f g : ℍ → ℂ} (hf : CKMRVRightRelTwo k ε f)
    (hg : CKMRVRightRelTwo k ε g) : CKMRVRightRelTwo k ε (f + g) := by
  unfold CKMRVRightRelTwo at *
  simp only [SlashAction.add_slash]
  funext z
  have h1 := congrFun hf z
  have h2 := congrFun hg z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
  linear_combination h1 + h2

theorem CKMRVRightRelOne.smul {k : ℤ} {ε : ℂ} (c : ℂ) {f : ℍ → ℂ}
    (hf : CKMRVRightRelOne k ε f) : CKMRVRightRelOne k ε (c • f) := by
  unfold CKMRVRightRelOne at *
  simp only [ModularForm.SL_smul_slash]
  funext z
  have h1 := congrFun hf z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

theorem CKMRVRightRelTwo.smul {k : ℤ} {ε : ℂ} (c : ℂ) {f : ℍ → ℂ}
    (hf : CKMRVRightRelTwo k ε f) : CKMRVRightRelTwo k ε (c • f) := by
  unfold CKMRVRightRelTwo at *
  simp only [ModularForm.SL_smul_slash]
  funext z
  have h1 := congrFun hf z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

theorem CKMRVRightRelOne.sum {k : ℤ} {ε : ℂ} {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, CKMRVRightRelOne k ε (f i)) : CKMRVRightRelOne k ε (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CKMRVRightRelOne k ε) (fun _ _ => CKMRVRightRelOne.add)
    (CKMRVRightRelOne.zero k ε) h

theorem CKMRVRightRelTwo.sum {k : ℤ} {ε : ℂ} {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, CKMRVRightRelTwo k ε (f i)) : CKMRVRightRelTwo k ε (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CKMRVRightRelTwo k ε) (fun _ _ => CKMRVRightRelTwo.add)
    (CKMRVRightRelTwo.zero k ε) h

/-- Multiplication by a level-one invariant function shifts the weight. -/
theorem CKMRVRightRelOne.mul_invariant {a b : ℤ} {ε : ℂ} {m f : ℍ → ℂ}
    (hm : ∀ γ : SL(2, ℤ), m ∣[a] γ = m) (hf : CKMRVRightRelOne b ε f) :
    CKMRVRightRelOne (a + b) ε (m * f) := by
  unfold CKMRVRightRelOne at *
  simp only [ModularForm.mul_slash_SL2, hm]
  funext z
  have h1 := congrFun hf z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Pi.zero_apply] at h1 ⊢
  linear_combination m z * h1

theorem CKMRVRightRelTwo.mul_invariant {a b : ℤ} {ε : ℂ} {m f : ℍ → ℂ}
    (hm : ∀ γ : SL(2, ℤ), m ∣[a] γ = m) (hf : CKMRVRightRelTwo b ε f) :
    CKMRVRightRelTwo (a + b) ε (m * f) := by
  unfold CKMRVRightRelTwo at *
  simp only [ModularForm.mul_slash_SL2, hm]
  funext z
  have h1 := congrFun hf z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
  linear_combination m z * h1

/-! ## Function-level laws (CKMRV (2.11), (2.17)) -/

private theorem sq_mul_zpow_neg_two (z : ℍ) : (z : ℂ) ^ 2 * (z : ℂ) ^ (-(2 : ℤ)) = 1 := by
  rw [zpow_neg, zpow_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero 2 z.ne_zero)

theorem thetaU_slash_T : thetaU ∣[(2 : ℤ)] ModularGroup.T = thetaW := by
  funext z
  rw [ckmrv_slash_T_apply_smul, thetaU_T]

theorem thetaV_slash_T : thetaV ∣[(2 : ℤ)] ModularGroup.T = -thetaV := by
  funext z
  rw [ckmrv_slash_T_apply_smul, thetaV_T, Pi.neg_apply]

theorem thetaW_slash_T : thetaW ∣[(2 : ℤ)] ModularGroup.T = thetaU := by
  funext z
  rw [ckmrv_slash_T_apply_smul, thetaW_T]

theorem thetaU_slash_S : thetaU ∣[(2 : ℤ)] ModularGroup.S = -thetaU := by
  funext z
  rw [ckmrv_slash_S_apply, thetaU_S, Pi.neg_apply]
  linear_combination (-thetaU z) * sq_mul_zpow_neg_two z

theorem thetaV_slash_S : thetaV ∣[(2 : ℤ)] ModularGroup.S = -thetaW := by
  funext z
  rw [ckmrv_slash_S_apply, thetaV_S, Pi.neg_apply]
  linear_combination (-thetaW z) * sq_mul_zpow_neg_two z

theorem thetaW_slash_S : thetaW ∣[(2 : ℤ)] ModularGroup.S = -thetaV := by
  funext z
  rw [ckmrv_slash_S_apply, thetaW_S, Pi.neg_apply]
  linear_combination (-thetaV z) * sq_mul_zpow_neg_two z

theorem thetaU_slash_T_inv : thetaU ∣[(2 : ℤ)] ModularGroup.T⁻¹ = thetaW :=
  slash_inv_eq_of_slash_eq thetaW_slash_T

theorem thetaW_slash_T_inv : thetaW ∣[(2 : ℤ)] ModularGroup.T⁻¹ = thetaU :=
  slash_inv_eq_of_slash_eq thetaU_slash_T

theorem thetaV_slash_T_inv : thetaV ∣[(2 : ℤ)] ModularGroup.T⁻¹ = -thetaV :=
  slash_inv_eq_of_slash_eq (by rw [SlashAction.neg_slash, thetaV_slash_T, neg_neg])

theorem ckmrvL_slash_S : ckmrvL ∣[(0 : ℤ)] ModularGroup.S = ckmrvLS := by
  funext z
  rw [ckmrv_slash_S_apply, ckmrvL_S, neg_zero, zpow_zero, mul_one]

theorem ckmrvLS_slash_S : ckmrvLS ∣[(0 : ℤ)] ModularGroup.S = ckmrvL := by
  funext z
  rw [ckmrv_slash_S_apply, ckmrvLS_S, neg_zero, zpow_zero, mul_one]

theorem ckmrvL_slash_T :
    ckmrvL ∣[(0 : ℤ)] ModularGroup.T = fun z => ckmrvL z - ckmrvLS z + π * I := by
  funext z
  rw [ckmrv_slash_T_apply_smul, ckmrvL_T]

theorem ckmrvLS_slash_T : ckmrvLS ∣[(0 : ℤ)] ModularGroup.T = -ckmrvLS := by
  funext z
  rw [ckmrv_slash_T_apply_smul, ckmrvLS_T, Pi.neg_apply]

theorem ckmrvL_slash_T_inv :
    ckmrvL ∣[(0 : ℤ)] ModularGroup.T⁻¹ = fun z => ckmrvL z - ckmrvLS z - π * I := by
  refine slash_inv_eq_of_slash_eq ?_
  funext z
  rw [ckmrv_slash_T_apply_smul]
  simp only [ckmrvL_T, ckmrvLS_T]
  ring

private theorem sq_slash {f g : ℍ → ℂ} {γ : SL(2, ℤ)} (h : f ∣[(2 : ℤ)] γ = g) :
    (f * f) ∣[(4 : ℤ)] γ = g * g := by
  have := ModularForm.mul_slash_SL2 2 2 γ f f
  rw [show (2 : ℤ) + 2 = 4 by norm_num, h] at this
  exact this

private theorem sub_slash' {k : ℤ} {γ : SL(2, ℤ)} (f g : ℍ → ℂ) :
    (f - g) ∣[k] γ = f ∣[k] γ - g ∣[k] γ := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

/-! ## The `ψ̃` relations (CKMRV Proposition 4.8, sign `+`) -/

def ckmrvTildePsiWeight : Fin 3 → ℤ := ![0, 2, 4]

theorem ckmrvTildePsiBasis_fun (j : Fin 3) :
    (fun z => ckmrvTildePsiBasis z j) =
      ![ckmrvL, thetaW, thetaU * thetaU - thetaV * thetaV] j := by
  fin_cases j <;> funext z <;> simp [ckmrvTildePsiBasis, sq]

theorem ckmrvTildePsiBasis_rel_one (j : Fin 3) :
    CKMRVRightRelOne (ckmrvTildePsiWeight j) 1 (fun z => ckmrvTildePsiBasis z j) := by
  rw [ckmrvTildePsiBasis_fun]
  fin_cases j
  · show CKMRVRightRelOne 0 1 ckmrvL
    unfold CKMRVRightRelOne
    rw [ckmrvL_slash_T, ckmrvL_slash_T_inv, ckmrvL_slash_S]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  · show CKMRVRightRelOne 2 1 thetaW
    unfold CKMRVRightRelOne
    rw [thetaW_slash_T, thetaW_slash_T_inv, thetaW_slash_S]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [thetaU_eq_add]
    ring
  · show CKMRVRightRelOne 4 1 (thetaU * thetaU - thetaV * thetaV)
    unfold CKMRVRightRelOne
    rw [sub_slash', sub_slash', sub_slash', sq_slash thetaU_slash_T, sq_slash thetaV_slash_T,
      sq_slash thetaU_slash_T_inv, sq_slash thetaV_slash_T_inv, sq_slash thetaU_slash_S,
      sq_slash thetaV_slash_S]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply,
      smul_eq_mul, Pi.zero_apply]
    ring

theorem ckmrvTildePsiBasis_rel_two (j : Fin 3) :
    CKMRVRightRelTwo (ckmrvTildePsiWeight j) 1 (fun z => ckmrvTildePsiBasis z j) := by
  rw [ckmrvTildePsiBasis_fun]
  fin_cases j
  · show CKMRVRightRelTwo 0 1 ckmrvL
    unfold CKMRVRightRelTwo
    rw [slash_STS, ckmrvL_slash_S, ckmrvLS_slash_T, SlashAction.neg_slash, ckmrvLS_slash_S]
    simp
  · show CKMRVRightRelTwo 2 1 thetaW
    unfold CKMRVRightRelTwo
    simp only [slash_STS, thetaW_slash_S, SlashAction.neg_slash, thetaV_slash_T, neg_neg,
      thetaV_slash_S]
    simp
  · show CKMRVRightRelTwo 4 1 (thetaU * thetaU - thetaV * thetaV)
    unfold CKMRVRightRelTwo
    have h1 : (thetaU * thetaU - thetaV * thetaV) ∣[(4 : ℤ)] ModularGroup.S =
        thetaU * thetaU - thetaW * thetaW := by
      rw [sub_slash', sq_slash thetaU_slash_S, sq_slash thetaV_slash_S, neg_mul_neg, neg_mul_neg]
    have h2 : (thetaU * thetaU - thetaW * thetaW) ∣[(4 : ℤ)] ModularGroup.T =
        thetaW * thetaW - thetaU * thetaU := by
      rw [sub_slash', sq_slash thetaU_slash_T, sq_slash thetaW_slash_T]
    have h3 : (thetaW * thetaW - thetaU * thetaU) ∣[(4 : ℤ)] ModularGroup.S =
        thetaV * thetaV - thetaU * thetaU := by
      rw [sub_slash', sq_slash thetaW_slash_S, sq_slash thetaU_slash_S, neg_mul_neg, neg_mul_neg]
    rw [slash_STS, h1, h2, h3]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      Pi.zero_apply]
    ring

/-! ## The `φ̃` relations (CKMRV Proposition 4.7, sign `−`) -/

theorem ckmrvTildePhiBasis_slash_S (j : Fin 3) :
    (fun z => ckmrvTildePhiBasis z j) ∣[ckmrvPhiWeight j] ModularGroup.S =
      fun z => ckmrvPhiTranslationSlope z j := by
  funext z
  rw [ckmrv_slash_S_apply, ckmrvTildePhiBasis_S_weighted]

theorem ckmrvPhiTranslationSlope_slash_T (j : Fin 3) :
    (fun z => ckmrvPhiTranslationSlope z j) ∣[ckmrvPhiWeight j] ModularGroup.T =
      fun z => ckmrvPhiTranslationSlope z j := by
  funext z
  rw [ckmrv_slash_T_apply_smul, T_smul_eq_ckmrvTranslate_one, ckmrvPhiTranslationSlope_translate]

theorem ckmrvPhiTranslationSlope_slash_S (j : Fin 3) :
    (fun z => ckmrvPhiTranslationSlope z j) ∣[ckmrvPhiWeight j] ModularGroup.S =
      fun z => ckmrvTildePhiBasis z j := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  funext z
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [ckmrv_slash_S_apply]
  fin_cases j
  · simp [ckmrvPhiTranslationSlope, ckmrvPhiWeight, ckmrvTildePhiBasis]
  · show EisensteinSeries.E2 (ModularGroup.S • z) * (z : ℂ) ^ (-(0 : ℤ)) =
      (z : ℂ) ^ 2 * EisensteinSeries.E2 z - 6 * I / (π : ℂ) * (z : ℂ)
    rw [eisensteinTwo_S_explicit]
    simp
  · simp only [ckmrvPhiTranslationSlope, ckmrvPhiWeight, ckmrvTildePhiBasis, Fin.reduceFinMk,
      Matrix.cons_val, eisensteinTwo_S_explicit]
    simp only [zpow_neg, zpow_ofNat]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem ckmrvTildePhiBasis_T (z : ℍ) :
    ckmrvTildePhiBasis (ModularGroup.T • z) =
      ![((z : ℂ) + 1) ^ 2,
        ((z : ℂ) + 1) ^ 2 * EisensteinSeries.E2 z - 6 * I / (π : ℂ) * ((z : ℂ) + 1),
        ((z : ℂ) + 1) ^ 2 * EisensteinSeries.E2 z ^ 2 -
          12 * I / (π : ℂ) * ((z : ℂ) + 1) * EisensteinSeries.E2 z - 36 / (π : ℂ) ^ 2] := by
  simp only [ckmrvTildePhiBasis, coe_T_smul, eisensteinTwo_T]

/-- `φ̃` at `z − 1`, the answer for the `T⁻¹` slash. -/
def ckmrvTildePhiShiftBack (z : ℍ) : Fin 3 → ℂ :=
  ![((z : ℂ) - 1) ^ 2,
    ((z : ℂ) - 1) ^ 2 * EisensteinSeries.E2 z - 6 * I / (π : ℂ) * ((z : ℂ) - 1),
    ((z : ℂ) - 1) ^ 2 * EisensteinSeries.E2 z ^ 2 -
      12 * I / (π : ℂ) * ((z : ℂ) - 1) * EisensteinSeries.E2 z - 36 / (π : ℂ) ^ 2]

theorem ckmrvTildePhiBasis_slash_T_inv (j : Fin 3) :
    (fun z => ckmrvTildePhiBasis z j) ∣[ckmrvPhiWeight j] ModularGroup.T⁻¹ =
      fun z => ckmrvTildePhiShiftBack z j := by
  refine slash_inv_eq_of_slash_eq ?_
  funext z
  rw [ckmrv_slash_T_apply_smul]
  simp only [ckmrvTildePhiShiftBack, coe_T_smul, eisensteinTwo_T]
  fin_cases j <;> simp [ckmrvTildePhiBasis]

theorem ckmrvTildePhiBasis_slash_T (j : Fin 3) :
    (fun z => ckmrvTildePhiBasis z j) ∣[ckmrvPhiWeight j] ModularGroup.T =
      fun z => ckmrvTildePhiBasis (ModularGroup.T • z) j := by
  funext z
  rw [ckmrv_slash_T_apply_smul]

theorem ckmrvTildePhiBasis_rel_one (j : Fin 3) :
    CKMRVRightRelOne (ckmrvPhiWeight j) (-1) (fun z => ckmrvTildePhiBasis z j) := by
  unfold CKMRVRightRelOne
  rw [ckmrvTildePhiBasis_slash_T, ckmrvTildePhiBasis_slash_T_inv, ckmrvTildePhiBasis_slash_S]
  funext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrvTildePhiBasis_T]
  fin_cases j <;>
    simp [ckmrvTildePhiShiftBack, ckmrvTildePhiBasis, ckmrvPhiTranslationSlope] <;> ring

theorem ckmrvTildePhiBasis_rel_two (j : Fin 3) :
    CKMRVRightRelTwo (ckmrvPhiWeight j) (-1) (fun z => ckmrvTildePhiBasis z j) := by
  unfold CKMRVRightRelTwo
  rw [slash_STS, ckmrvTildePhiBasis_slash_S, ckmrvPhiTranslationSlope_slash_T,
    ckmrvPhiTranslationSlope_slash_S]
  funext z
  simp

/-! ## Level-one invariant right multipliers -/

/-- Weights of the actual modular factors: −2, 0, 2, …, 14. -/
def ckmrvFactorWeight : Fin 9 → ℤ := ![-2, 0, 2, 4, 6, 8, 10, 12, 14]

theorem ckmrvModularFactor_S (z : ℍ) (k : Fin 9) :
    ckmrvModularFactor (ModularGroup.S • z) k =
      (z : ℂ) ^ ckmrvFactorWeight k * ckmrvModularFactor z k := by
  have hΔ := ModularForm.discriminant_ne_zero z
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  fin_cases k <;> simp [ckmrvFactorWeight, zpow_neg, zpow_ofNat] <;> field_simp

/-- `N(j(z)) f_k(z) / (s Δ(z) G(j(z)))`. -/
def ckmrvRightMultiplier (s : ℂ) (G N : ℂ → ℂ) (k : Fin 9) (z : ℍ) : ℂ :=
  (s * ModularForm.discriminant z * G (kleinModularJ z))⁻¹ * N (kleinModularJ z) *
    ckmrvModularFactor z k

theorem ckmrvRightMultiplier_slash (s : ℂ) (G N : ℂ → ℂ) (k : Fin 9) (γ : SL(2, ℤ)) :
    ckmrvRightMultiplier s G N k ∣[ckmrvFactorWeight k - 12] γ =
      ckmrvRightMultiplier s G N k := by
  refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_ γ
  · funext z
    have hz : (z : ℂ) ≠ 0 := z.ne_zero
    rw [ckmrv_slash_S_apply]
    simp only [ckmrvRightMultiplier, discriminant_S, kleinModularJ_S, ckmrvModularFactor_S]
    have hinv : (s * ((z : ℂ) ^ 12 * ModularForm.discriminant z) * G (kleinModularJ z))⁻¹ =
        ((z : ℂ) ^ 12)⁻¹ * (s * ModularForm.discriminant z * G (kleinModularJ z))⁻¹ := by
      rw [show s * ((z : ℂ) ^ 12 * ModularForm.discriminant z) * G (kleinModularJ z) =
        (z : ℂ) ^ 12 * (s * ModularForm.discriminant z * G (kleinModularJ z)) by ring, mul_inv]
    have key : ((z : ℂ) ^ 12)⁻¹ * (z : ℂ) ^ ckmrvFactorWeight k *
        (z : ℂ) ^ (-(ckmrvFactorWeight k - 12)) = 1 := by
      rw [mul_assoc, ← zpow_add₀ hz, show ckmrvFactorWeight k + -(ckmrvFactorWeight k - 12) = 12
        by ring, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 12 hz)]
    rw [hinv]
    linear_combination ((s * ModularForm.discriminant z * G (kleinModularJ z))⁻¹ *
      N (kleinModularJ z) * ckmrvModularFactor z k) * key
  · funext z
    rw [ckmrv_slash_T_apply_smul, T_smul_eq_ckmrvTranslate_one]
    simp only [ckmrvRightMultiplier, discriminant_translate, kleinModularJ_translate,
      ckmrvModularFactor_translate]

/-! ## Decomposition of the kernels in the right variable -/

private theorem contraction_right_sum (A B : Fin 3 → ℂ) (lf : Fin 3 → ℂ) (c : ℂ)
    (M : Matrix (Fin 3) (Fin 3) ℂ) (rf : Fin 3 → ℂ) :
    ckmrvCoreContraction A B (c⁻¹ • ckmrvDiagonalCore lf rf M) =
      ∑ i, ∑ j, (A i * lf i) * (c⁻¹ * M i j * rf j * B j) := by
  simp only [ckmrvCoreContraction, Matrix.smul_apply, ckmrvDiagonalCore_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ckmrvEightPlusKernel_right_sum (τ : ℍ) :
    (fun z => ckmrvEightPlusKernel τ z) = ∑ i : Fin 3, ∑ j : Fin 3,
      (ckmrvPhiBasis τ i * ckmrvModularFactor τ (![4, 3, 2] i)) •
        (ckmrvRightMultiplier ckmrvPlusScale (fun x => kleinModularJ τ - x)
          (fun x => ckmrvEightPlusCore (kleinModularJ τ - x) i j) (![7, 6, 5] j) *
            fun z => ckmrvTildePhiBasis z j) := by
  funext z
  simp only [ckmrvEightPlusKernel, ckmrvEightPlusCoefficientMatrix, ckmrvModularCoreMatrix,
    contraction_right_sum, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    ckmrvRightMultiplier]

theorem ckmrvLeechPlusKernel_right_sum (τ : ℍ) :
    (fun z => ckmrvLeechPlusKernel τ z) = ∑ i : Fin 3, ∑ j : Fin 3,
      (ckmrvPhiBasis τ i * ckmrvModularFactor τ (![8, 7, 6] i)) •
        (ckmrvRightMultiplier (1728 * ckmrvPlusScale) (fun _ => 1)
          (fun x => ckmrvLeechPlusCore (kleinModularJ τ) (kleinModularJ τ - x) i j)
            (![3, 2, 1] j) * fun z => ckmrvTildePhiBasis z j) := by
  funext z
  simp only [ckmrvLeechPlusKernel, ckmrvLeechPlusCoefficientMatrix, ckmrvModularCoreMatrix,
    contraction_right_sum, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    ckmrvRightMultiplier, mul_one]

theorem ckmrvEightMinusKernel_right_sum (τ : ℍ) :
    (fun z => ckmrvEightMinusKernel τ z) = ∑ i : Fin 3, ∑ j : Fin 3,
      (ckmrvPsiBasis τ i * ckmrvModularFactor τ (![3, 2, 1] i)) •
        (ckmrvRightMultiplier ckmrvMinusScale (fun x => kleinModularJ τ - x)
          (fun _ => ckmrvEightMinusCore (kleinModularJ τ) i j) (![6, 5, 4] j) *
            fun z => ckmrvTildePsiBasis z j) := by
  funext z
  simp only [ckmrvEightMinusKernel, ckmrvEightMinusCoefficientMatrix, ckmrvModularCoreMatrix,
    contraction_right_sum, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    ckmrvRightMultiplier]

theorem ckmrvLeechMinusKernel_right_sum (τ : ℍ) :
    (fun z => ckmrvLeechMinusKernel τ z) = ∑ i : Fin 3, ∑ j : Fin 3,
      (ckmrvPsiBasis τ i * ckmrvModularFactor τ (![7, 6, 5] i)) •
        (ckmrvRightMultiplier ckmrvMinusScale (fun x => kleinModularJ τ - x)
          (fun x => ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - x) i j)
            (![2, 1, 0] j) * fun z => ckmrvTildePsiBasis z j) := by
  funext z
  simp only [ckmrvLeechMinusKernel, ckmrvLeechMinusCoefficientMatrix, ckmrvModularCoreMatrix,
    contraction_right_sum, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    ckmrvRightMultiplier]

/-! ## CKMRV Theorem 4.3(2), right half -/

theorem ckmrvEightPlusKernel_right_rel_one (τ : ℍ) :
    CKMRVRightRelOne (-2) (-1) (fun z => ckmrvEightPlusKernel τ z) := by
  rw [ckmrvEightPlusKernel_right_sum]
  refine CKMRVRightRelOne.sum _ fun i _ => CKMRVRightRelOne.sum _ fun j _ =>
    CKMRVRightRelOne.smul _ ?_
  have h := (ckmrvTildePhiBasis_rel_one j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvPlusScale (fun x => kleinModularJ τ - x)
      (fun x => ckmrvEightPlusCore (kleinModularJ τ - x) i j) (![7, 6, 5] j))
  have hw : ckmrvFactorWeight (![7, 6, 5] j) - 12 + ckmrvPhiWeight j = -2 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvPhiWeight]
  rwa [hw] at h

theorem ckmrvEightPlusKernel_right_rel_two (τ : ℍ) :
    CKMRVRightRelTwo (-2) (-1) (fun z => ckmrvEightPlusKernel τ z) := by
  rw [ckmrvEightPlusKernel_right_sum]
  refine CKMRVRightRelTwo.sum _ fun i _ => CKMRVRightRelTwo.sum _ fun j _ =>
    CKMRVRightRelTwo.smul _ ?_
  have h := (ckmrvTildePhiBasis_rel_two j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvPlusScale (fun x => kleinModularJ τ - x)
      (fun x => ckmrvEightPlusCore (kleinModularJ τ - x) i j) (![7, 6, 5] j))
  have hw : ckmrvFactorWeight (![7, 6, 5] j) - 12 + ckmrvPhiWeight j = -2 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvPhiWeight]
  rwa [hw] at h

theorem ckmrvLeechPlusKernel_right_rel_one (τ : ℍ) :
    CKMRVRightRelOne (-10) (-1) (fun z => ckmrvLeechPlusKernel τ z) := by
  rw [ckmrvLeechPlusKernel_right_sum]
  refine CKMRVRightRelOne.sum _ fun i _ => CKMRVRightRelOne.sum _ fun j _ =>
    CKMRVRightRelOne.smul _ ?_
  have h := (ckmrvTildePhiBasis_rel_one j).mul_invariant
    (ckmrvRightMultiplier_slash (1728 * ckmrvPlusScale) (fun _ => 1)
      (fun x => ckmrvLeechPlusCore (kleinModularJ τ) (kleinModularJ τ - x) i j) (![3, 2, 1] j))
  have hw : ckmrvFactorWeight (![3, 2, 1] j) - 12 + ckmrvPhiWeight j = -10 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvPhiWeight]
  rwa [hw] at h

theorem ckmrvLeechPlusKernel_right_rel_two (τ : ℍ) :
    CKMRVRightRelTwo (-10) (-1) (fun z => ckmrvLeechPlusKernel τ z) := by
  rw [ckmrvLeechPlusKernel_right_sum]
  refine CKMRVRightRelTwo.sum _ fun i _ => CKMRVRightRelTwo.sum _ fun j _ =>
    CKMRVRightRelTwo.smul _ ?_
  have h := (ckmrvTildePhiBasis_rel_two j).mul_invariant
    (ckmrvRightMultiplier_slash (1728 * ckmrvPlusScale) (fun _ => 1)
      (fun x => ckmrvLeechPlusCore (kleinModularJ τ) (kleinModularJ τ - x) i j) (![3, 2, 1] j))
  have hw : ckmrvFactorWeight (![3, 2, 1] j) - 12 + ckmrvPhiWeight j = -10 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvPhiWeight]
  rwa [hw] at h

theorem ckmrvEightMinusKernel_right_rel_one (τ : ℍ) :
    CKMRVRightRelOne (-2) 1 (fun z => ckmrvEightMinusKernel τ z) := by
  rw [ckmrvEightMinusKernel_right_sum]
  refine CKMRVRightRelOne.sum _ fun i _ => CKMRVRightRelOne.sum _ fun j _ =>
    CKMRVRightRelOne.smul _ ?_
  have h := (ckmrvTildePsiBasis_rel_one j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvMinusScale (fun x => kleinModularJ τ - x)
      (fun _ => ckmrvEightMinusCore (kleinModularJ τ) i j) (![6, 5, 4] j))
  have hw : ckmrvFactorWeight (![6, 5, 4] j) - 12 + ckmrvTildePsiWeight j = -2 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvTildePsiWeight]
  rwa [hw] at h

theorem ckmrvEightMinusKernel_right_rel_two (τ : ℍ) :
    CKMRVRightRelTwo (-2) 1 (fun z => ckmrvEightMinusKernel τ z) := by
  rw [ckmrvEightMinusKernel_right_sum]
  refine CKMRVRightRelTwo.sum _ fun i _ => CKMRVRightRelTwo.sum _ fun j _ =>
    CKMRVRightRelTwo.smul _ ?_
  have h := (ckmrvTildePsiBasis_rel_two j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvMinusScale (fun x => kleinModularJ τ - x)
      (fun _ => ckmrvEightMinusCore (kleinModularJ τ) i j) (![6, 5, 4] j))
  have hw : ckmrvFactorWeight (![6, 5, 4] j) - 12 + ckmrvTildePsiWeight j = -2 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvTildePsiWeight]
  rwa [hw] at h

theorem ckmrvLeechMinusKernel_right_rel_one (τ : ℍ) :
    CKMRVRightRelOne (-10) 1 (fun z => ckmrvLeechMinusKernel τ z) := by
  rw [ckmrvLeechMinusKernel_right_sum]
  refine CKMRVRightRelOne.sum _ fun i _ => CKMRVRightRelOne.sum _ fun j _ =>
    CKMRVRightRelOne.smul _ ?_
  have h := (ckmrvTildePsiBasis_rel_one j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvMinusScale (fun x => kleinModularJ τ - x)
      (fun x => ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - x) i j) (![2, 1, 0] j))
  have hw : ckmrvFactorWeight (![2, 1, 0] j) - 12 + ckmrvTildePsiWeight j = -10 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvTildePsiWeight]
  rwa [hw] at h

theorem ckmrvLeechMinusKernel_right_rel_two (τ : ℍ) :
    CKMRVRightRelTwo (-10) 1 (fun z => ckmrvLeechMinusKernel τ z) := by
  rw [ckmrvLeechMinusKernel_right_sum]
  refine CKMRVRightRelTwo.sum _ fun i _ => CKMRVRightRelTwo.sum _ fun j _ =>
    CKMRVRightRelTwo.smul _ ?_
  have h := (ckmrvTildePsiBasis_rel_two j).mul_invariant
    (ckmrvRightMultiplier_slash ckmrvMinusScale (fun x => kleinModularJ τ - x)
      (fun x => ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - x) i j) (![2, 1, 0] j))
  have hw : ckmrvFactorWeight (![2, 1, 0] j) - 12 + ckmrvTildePsiWeight j = -10 := by
    fin_cases j <;> simp [ckmrvFactorWeight, ckmrvTildePsiWeight]
  rwa [hw] at h

end E8Leech
