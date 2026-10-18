-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.E2.Basic
import SpherePacking.ModularForms.SlashActionAuxil
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal


/-!
# Transformation formulas for `E₂`

This file proves modular transformation and Fourier expansion formulas for the weight-2 Eisenstein
series `E₂`, including the correction term in its `S`-transform.

## Main statements
* `G2_q_exp`, `E₂_eq`
* `G₂_transform`, `E₂_transform`, `E₂_S_transform`
-/


open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Matrix.SpecialLinearGroup

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups Matrix.SpecialLinearGroup

open ArithmeticFunction


noncomputable section Definitions

lemma PS1 (z : ℍ) (m : ℤ) : limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = 0 := by
  refine Filter.Tendsto.limUnder_eq ?_
  -- Telescoping sum and known `tendsto` facts.
  have htel :
      (fun N : ℕ => ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
          (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
        fun N : ℕ => 1 / ((m : ℂ) * z - N) - 1 / (m * z + N) := by
    ext N
    simpa using telescope_aux z m N
  rw [htel]
  simpa using (tendstozero_inv_linear_neg z m).sub (tendstozero_inv_linear z m)


lemma PS2 (z : ℍ) : ∑' m : ℤ, (limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))) = 0 := by
  simpa using (tsum_congr fun m => (PS1 z m))

lemma auxr (z : ℍ) (b : ℤ) :
    ((limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n)) +
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1))) =
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2) := by
  have := limUnder_add (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1))+ δ b n))
    (g := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)))
      (extracted_2_δ z b) (by apply extracted_3 z b)
  rw [this]
  refine limUnder_congr_eventually _ _ ?_ (by
    apply CauchySeq.add (extracted_2_δ z b) (extracted_3 z b))
  simp only [one_div, mul_inv_rev, Pi.add_apply, eventually_atTop,
    ge_iff_le]
  use 1
  intro c hc
  rw [← Finset.sum_add_distrib ]
  congr
  ext n
  apply poly_id z b n


--this sum is now abs convergent. Idea is to subtract PS1 from the G₂ defn.
lemma G2_alt_eq (z : ℍ) : G₂ z = ∑' m : ℤ, ∑' n : ℤ,
    (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n) := by
  rw [G₂]
  have := PS2 z
  set t := ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n)
  rw [show t = t + 0 by ring, ← this]
  simp only [t]
  have hG2AltProd :=
    (by
        have H := G_2_alt_summable_δ z
        rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
        exact H.prod)
  rw [← Summable.tsum_add]
  · rw [tsum_limUnder_atTop]
    · congr
      ext n
      congr
      ext m
      rw [tsum_limUnder_atTop, tsum_limUnder_atTop, auxr z m]
      · have H := G2_prod_summable1_δ z m
        simpa using H
      · have H := linear_right_summable z m Int.le_rfl
        simpa using H
    · refine hG2AltProd.congr ?_
      intro b
      simpa using PS1 z b
  · refine hG2AltProd.congr ?_
    intro b
    simp only [Fin.isValue, one_div, mul_inv_rev, finTwoArrowEquiv_symm_apply, comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · refine (summable_zero : Summable fun _ : ℤ => (0 : ℂ)).congr ?_
    intro b
    simpa using (PS1 z b).symm


lemma G2_transf_aux (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  G₂ z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

@[simp] lemma ModularGroup.coe_mul (A B : SL(2, ℤ)) :
    (ModularGroup.coe A) * B = ModularGroup.coe (A * B) := by
  simp [ModularGroup.coe]

lemma denom_diff (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
  (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  have h1 := Matrix.det_fin_two B.1
  simp_rw [← map_mul, ModularGroup.denom_apply]
  simp [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, h1,
    Int.cast_sub, h0.2.2.2]
  ring


@[simp]
lemma denom_sim (A : SL(2, ℤ)) (z : ℍ) :
    denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) z = denom (coe2 A) z :=
  rfl

@[simp]
lemma coe2_smul (A : SL(2, ℤ)) (z : ℍ) :
  (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) • z = (coe2 A) • z :=
  rfl

lemma D2_mul (A B : SL(2, ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B):= by
  ext z
  have hco := denom_cocycle A B z.im_ne_zero
  simp_rw [SL_slash_def]
  simp_rw [denom_sim]
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Int.reduceNeg, zpow_neg,
    Pi.add_apply]
  simp_rw [coe2_mul]
  simp_rw [← mul_div, mul_assoc, ← mul_add]
  congr
  simp only [Fin.isValue, ModularGroup.sl_moeb, coe2_smul]
  have hde : denom B z ≠ 0 := by exact denom_ne_zero (↑B) z
  field_simp [hde]
  have hd := denom_diff A B z
  rw [ ← sub_eq_iff_eq_add] at hd
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.det_coe,
    Int.cast_one, mul_one] at hd
  simp only [Fin.isValue, ← hd, hco, pow_two]
  have : denom (↑A) (num ↑B ↑z / denom ↑B ↑z) = denom ↑A ↑(↑B • z) := by
    congr 1
    simp [UpperHalfPlane.specialLinearGroup_apply]
    congr
  rw [this]
  try simp only [Fin.isValue, ModularGroup.sl_moeb, coe2_smul]
  ring


lemma D2_one : D₂ 1 = 0 := by
  ext z; simp [D₂]

lemma D2_inv (A : SL(2, ℤ)) : (D₂ A)∣[(2 : ℤ)] A⁻¹ = - D₂ (A⁻¹) := by
  have h : (D₂ A)∣[(2 : ℤ)] A⁻¹ + D₂ (A⁻¹) = 0 := by
    simpa [mul_inv_cancel, SL_slash, D2_one] using (D2_mul A A⁻¹).symm
  exact eq_neg_of_add_eq_zero_left h


lemma D2_T : D₂ ModularGroup.T = 0 := by
  ext z; simp [D₂, ModularGroup.T]

set_option backward.isDefEq.respectTransparency false in
lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z := by
  simp [D₂, ModularGroup.denom_S]

lemma SL2_gens : Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤ := by
  exact SpecialLinearGroup.SL2Z_generators

lemma G₂_eq_G₂_a (z : ℍ) : G₂ z = G₂_a z := by
  rw [G₂, G₂_a]
  rw [Filter.Tendsto.limUnder_eq]
  have := CauchySeq.tendsto_limUnder (G2_cauchy z)
  apply tendsto_of_tendsto_sub _ _ _ this
  have h0 := cc _ (G2_cauchy z) ?_
  conv =>
    enter [1]
    ext N
    simp
    rw [sum_Icc_eq_sum_Ico_succ _ (by omega)]
    simp
  · have := Filter.Tendsto.neg h0
    simp only [one_div, neg_zero] at this
    have := int_tendsto_nat this
    apply this
  · intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring

/-- Fourier expansion of `G₂` as a constant term plus an exponential series. -/
public lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
    ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
  rw [G₂_eq_G₂_a, G₂_a]
  refine Filter.Tendsto.limUnder_eq ?_
  rw [t8 z, sub_eq_add_neg]
  refine tendsto_const_nhds.add ?_
  simpa [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one] using G2_c_tendsto z

lemma G2_periodic : (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  ext z
  rw [modular_slash_T_apply, G2_q_exp, G2_q_exp]
  congr 2
  refine tsum_congr ?_
  intro n
  congr 1
  -- `exp_periodo` is stated with `(1 + z)`; rewrite `((1 : ℝ) +ᵥ z)` accordingly.
  simpa [coe_vadd, add_comm, add_left_comm, add_assoc] using exp_periodo z (n : ℕ)

/-- The Eisenstein series `E₂` is 1-periodic: `E₂ ((1 : ℝ) +ᵥ z) = E₂ z`. -/
public lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  have h := congrFun G2_periodic z
  rw [modular_slash_T_apply] at h
  simp only [E₂, Pi.smul_apply, smul_eq_mul, h]

/-- The modular transformation law for `G₂`, with the correction term `D₂`. -/
public lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ) := by
  refine
    Subgroup.closure_induction (G := SL(2, ℤ))
      (p := fun γ _ ↦ G₂ ∣[(2 : ℤ)] γ = G₂ - D₂ γ)
      (k := ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ))))
      (fun a ha => ?_) ?_ (fun a b ha hb HA HB => ?_) (fun g hg hg2 => ?_) ?_
  · try dsimp
    rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ha) with rfl | rfl
    · ext z
      simp only [Pi.sub_apply]
      rw [D2_S z]
      have := modular_slash_S_apply G₂ 2 z
      simp only [Int.reduceNeg, zpow_neg] at this
      rw [this, mul_comm]
      rw [← G2_transf_aux z]
      ring_nf
      rw [modular_S_smul]
      congr
      · simp [inv_pow, inv_inj]
        try norm_cast
      · simp
    · simpa [D2_T, sub_zero] using G2_periodic
  · simp only [SlashAction.slash_one, D2_one, sub_zero]
  · try dsimp at HA HB ⊢
    rw [D2_mul, SlashAction.slash_mul, HA, sub_eq_add_neg, SlashAction.add_slash, HB]
    ext z
    simp only [SlashAction.neg_slash, SL_slash, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  · try dsimp at hg2 ⊢
    have H1 : (G₂ ∣[(2 : ℤ)] g) ∣[(2 : ℤ)] g⁻¹ = (G₂ - D₂ g) ∣[(2 : ℤ)] g⁻¹ := by
      simpa using congrArg (fun F => F ∣[(2 : ℤ)] g⁻¹) hg2
    rw [← SlashAction.slash_mul, sub_eq_add_neg, SlashAction.add_slash] at H1
    simp only [mul_inv_cancel, SlashAction.slash_one, SL_slash, SlashAction.neg_slash] at H1
    nth_rw 2 [H1]
    rw [← sub_eq_add_neg]
    have := D2_inv g
    simp only [SL_slash] at this
    rw [this]
    simp only [SL_slash, sub_neg_eq_add, add_sub_cancel_right]
  · simp [SL2_gens]


/-- The `S`-transform of `E₂` in slash-action form. -/
public lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
    E₂ z + 6 / (π * Complex.I * z) := by
  rw [E₂, ModularForm.SL_smul_slash (2 : ℤ) ModularGroup.S G₂ (1 / (2 * riemannZeta 2))]
  have hG := G₂_transform (ModularGroup.S)
  simp only [SL_slash, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul] at *
  rw [hG]
  simp only [Pi.sub_apply]
  rw [D2_S]
  ring_nf
  rw [sub_eq_add_neg]
  congr
  rw [riemannZeta_two]
  have hpi : (π : ℂ) ≠ 0 := by simp
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)).
    This is derived from E₂_transform by relating the slash action to the direct value. -/
public lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_two] at h
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero hz hz
  have h' := congrArg (· * ((z : ℂ) * (z : ℂ))) h
  try simp only at h'
  -- Cancel the `z^(-2)` factor coming from the slash action.
  rw [mul_assoc, inv_mul_cancel₀ hz2, mul_one] at h'
  simpa [sq, mul_comm, mul_left_comm, mul_assoc] using h'

/-- Convert a geometric-series expression to a divisor-sum expression via `sigma`. -/
public lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ, (n + 1) *
    cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π * Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  -- Use the general sigma identity for geometric series from Mathlib, then shift `ℕ+` → `ℕ`.
  set r : ℂ := cexp (2 * ↑π * Complex.I * (z : ℂ))
  have hr : ‖r‖ < 1 := by simpa [r] using exp_upperHalfPlane_lt_one z
  have hσ :
      (∑' n : ℕ+, (n : ℂ) * r ^ (n : ℕ) / (1 - r ^ (n : ℕ))) =
        ∑' n : ℕ+, (sigma 1 n : ℂ) * r ^ (n : ℕ) := by
    simpa [pow_one] using (tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℂ) (r := r) hr 1)
  -- Convert both sides of the goal to `ℕ+`-indexed sums and apply `hσ`.
  have hL :
      (∑' n : ℕ, (n + 1) * r ^ (n + 1) / (1 - r ^ (n + 1))) =
        ∑' n : ℕ+, (n : ℂ) * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (tsum_pnat_eq_tsum_succ3 (fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n))).symm
  have hR :
      (∑' n : ℕ, sigma 1 (n + 1) * r ^ (n + 1)) =
        ∑' n : ℕ+, (sigma 1 n : ℂ) * r ^ (n : ℕ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (tsum_pnat_eq_tsum_succ3 (fun n : ℕ => (sigma 1 n : ℂ) * r ^ n)).symm
  -- Rewrite the original sums as `r`-powers via `exp_aux`.
  have hL' :
      (∑' n : ℕ, (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) /
          (1 - cexp (2 * π * Complex.I * (n + 1) * z))) =
        ∑' n : ℕ, (n + 1) * r ^ (n + 1) / (1 - r ^ (n + 1)) := by
    refine tsum_congr fun n => ?_
    have : cexp (2 * π * Complex.I * (n + 1) * z) = r ^ (n + 1) := by
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using (exp_aux z (n + 1))
    simp [this]
  have hR' :
      (∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z)) =
        ∑' n : ℕ, sigma 1 (n + 1) * r ^ (n + 1) := by
    refine tsum_congr fun n => ?_
    have : cexp (2 * π * Complex.I * (n + 1) * z) = r ^ (n + 1) := by
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using (exp_aux z (n + 1))
    simp [this]
  -- Combine.
  grind only

/-- A standard Fourier expansion formula for `E₂`. -/
public lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂]
  simp only [one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_q_exp]
  rw [mul_sub]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.pi_pos.ne')
  congr 1
  · rw [riemannZeta_two]
    field_simp [hpi]
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      field_simp [hpi]
      ring
    · have hl := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 n * cexp (2 * π * Complex.I * n * z))
      have hr := tsum_pnat_eq_tsum_succ3 (fun n => n * cexp (2 * π * Complex.I * n * z) / (1 - cexp
        (2 * π * Complex.I * n * z)))
      rw [hl, hr]
      simpa [Nat.cast_add, Nat.cast_one] using (tsum_eq_tsum_sigma z).symm

end Definitions
