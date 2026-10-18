-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import SpherePacking.ModularForms.Cauchylems
public import SpherePacking.ModularForms.LimUnderLemmas
public import SpherePacking.ModularForms.TendsToLemmas
import SpherePacking.ModularForms.SummableLemmas.Basic
import SpherePacking.ModularForms.SummableLemmas.Cotangent
import SpherePacking.ModularForms.SummableLemmas.G2
import SpherePacking.ModularForms.SummableLemmas.QExpansion
import SpherePacking.ModularForms.SummableLemmas.IntPNat


/-!
# The Eisenstein series `E₂`

This file defines the weight-2 Eisenstein series `E₂` on the upper half-plane, together with the
auxiliary series `G₂` used to define it and a correction term `D₂` which appears in its modular
transformation behavior.

## Main definitions
* `G₂`, `G₂_a`
* `E₂`
* `D₂`
-/

open scoped Interval Real Topology BigOperators Nat Matrix.SpecialLinearGroup

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory
  Metric Filter Function Complex MatrixGroups Matrix.SpecialLinearGroup

open ArithmeticFunction

noncomputable section Definitions


/-- The series `G₂`, defined using symmetric partial sums over `Ico (-N) N` and `limUnder`. -/
@[expose] public def G₂ : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

/-- A variant of `G₂` using symmetric partial sums over `Icc (-N) N`. -/
@[expose] public def G₂_a : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

/-- The Eisenstein series `E₂`, normalized as a scalar multiple of `G₂`. -/
@[expose] public def E₂ : ℍ → ℂ := (1 / (2 * riemannZeta 2)) • G₂

/-- Coercion of `SL(2,ℤ)` matrices to `GL(2,ℝ)` via the standard map. -/
@[coe, reducible, expose] public def coe2 (g : SL(2, ℤ)) : (GL (Fin 2) ℝ) :=
  Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)

/-- The canonical coercion `SL(2,ℤ) → GL(2,ℝ)`. -/
public instance : Coe SL(2, ℤ) (GL (Fin 2) ℝ) := ⟨coe2⟩

/-- Compatibility of `coe2` with multiplication. -/
@[simp]
public lemma coe2_mul (A B : SL(2, ℤ)) :
     coe2 (A * B) = (coe2 A) * (coe2 B) := by simp [coe2]

/-- The correction term appearing in the weight-2 transformation law. -/
@[expose] public def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma extracted_77 (z : ℍ) (n : ℤ) : Summable fun b : ℤ ↦ (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  have := (linear_right_summable (-1 /z) (-n) Int.le_rfl).mul_left ((z : ℂ)^2)⁻¹
  refine this.congr ?_
  intro b
  have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
  simp only [Int.cast_neg, neg_mul]
  field_simp [hz]
  ring_nf

theorem extracted_66 (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp only [inv_neg, mul_neg, Pi.mul_apply]
  rw [@Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
    grind only
  · intro i hi
    exact extracted_77 z i

lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) = limUnder (atTop)
    fun N : ℕ => ((∑' (n : ℤ), ∑ m ∈ Finset.Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) := by
  rw [ modular_S_smul]
  simp only [G₂, inv_neg, one_div]
  rw [ limUnder_mul_const]
  · congr
    simpa [Function.comp_def, Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Pi.smul_def, Pi.div_def] using extracted_66 z
  · apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro d
      rw [int_sum_neg]
      congr
      ext n
      simp only [Int.cast_neg, neg_mul, inv_inj]
      ring
    have := G2_cauchy ⟨-(1 : ℂ) / z, by simpa using pnat_div_upper 1 z⟩
    grind only


theorem series_eql' (z : ℍ) :
    ↑π * Complex.I - 2 * ↑π * Complex.I * ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  rw [EisensteinSeries_Identity z]
  congr
  ext n
  rw [← Complex.exp_nat_mul]
  ring_nf

theorem extracted_summable (z : ℍ) (n : ℕ+) : Summable fun m : ℕ ↦
    cexp (2 * ↑π * Complex.I * (-↑↑n / ↑z) * ↑m) := by
  simpa using a1 1 1 ⟨-n / z, pnat_div_upper n z⟩

theorem tsum_exp_tendsto_zero (z : ℍ) :
    Tendsto (fun x : ℕ+ ↦ 2 / ↑z * 2 * ↑π * Complex.I *
    ∑' (n : ℕ), cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop (𝓝 (4 * ↑π * Complex.I / ↑z))
    := by
  -- Reduce to the geometric series formula.
  set r : ℂ := cexp (2 * ↑π * Complex.I * (-1 / (z : ℂ)))
  have hr : ‖r‖ < 1 := by
    simpa [r] using exp_upperHalfPlane_lt_one ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
  have hr0 : Tendsto (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) atTop (𝓝 (0 : ℂ)) := by
    have hxr :
        (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) = fun x : ℕ+ ↦ r ^ (x : ℕ) := by
      funext x
      have hx :
          2 * ↑π * Complex.I * (-↑↑x / ↑z) =
            (x : ℕ) * (2 * ↑π * Complex.I * (-1 / ↑z)) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simpa [r, hx] using (Complex.exp_nat_mul (2 * ↑π * Complex.I * (-1 / ↑z)) (x : ℕ))
    have hp : Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 (0 : ℂ)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
    have hp' : Tendsto (fun x : ℕ+ ↦ r ^ (x : ℕ)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_comp_val_Ioi_atTop.mpr hp
    simpa [hxr] using hp'
  have htsum :
      Tendsto (fun x : ℕ+ ↦ ∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop
        (𝓝 (1 : ℂ)) := by
    have hgeom :
        (fun x : ℕ+ ↦ ∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) =
          fun x : ℕ+ ↦ (1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z)))⁻¹ := by
      funext x
      set ξ : ℂ := cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))
      have hξ : ‖ξ‖ < 1 := by
        simpa [ξ] using exp_upperHalfPlane_lt_one ⟨-x / z, by simpa using pnat_div_upper x z⟩
      have hterm :
          (fun n : ℕ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) = fun n : ℕ ↦ ξ ^ n := by
        funext n
        simpa [ξ, mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_nat_mul (2 * ↑π * Complex.I * (-↑↑x / ↑z)) n)
      simpa [hterm] using (tsum_geometric_of_norm_lt_one (ξ := ξ) hξ)
    have h1 :
        Tendsto (fun x : ℕ+ ↦ 1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) atTop (𝓝 (1 : ℂ)) := by
      simpa using (tendsto_const_nhds.sub hr0)
    have h1inv :
        Tendsto (fun x : ℕ+ ↦ (1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z)))⁻¹) atTop
          (𝓝 (1 : ℂ)) := by
      simpa using (h1.inv₀ (by simp))
    simpa [hgeom] using h1inv
  -- Reinsert the constant prefactor.
  have :=
    (tendsto_const_nhds.mul htsum : Tendsto
      (fun x : ℕ+ ↦ (2 / ↑z * 2 * ↑π * Complex.I) *
        (∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n))) atTop
        (𝓝 ((2 / ↑z * 2 * ↑π * Complex.I) * (1 : ℂ))))
  have h22 : (2 : ℂ) * 2 = 4 := by norm_num
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, h22] using this


theorem extracted_12 (z : ℍ) :
    Tendsto (fun n : ℕ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
  have : Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
    have : (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
     (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) = (fun N : ℕ+ =>
      (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
      ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n) - z / (-(N : ℂ))))) := by
      funext N
      set Z : ℍ := ⟨-(N : ℂ) / z, by simpa using pnat_div_upper N z⟩
      have hS := series_eql' Z
      grind only
    rw [this]
    have h3 : (fun N : ℕ+ =>
        (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n) - z / (-(N : ℂ))))) =
        (fun N : ℕ+ => ((2 / (z : ℂ)) * ↑π * Complex.I - ((2 / z) * 2 * ↑π * Complex.I *
          ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n)) - 2 / (-(N : ℂ)))) := by
        funext N
        have hz : 2 / (-(N : ℂ)) = (2 / z) * (z / (-(N : ℂ))) := by
          have : (z : ℂ) ≠ 0 := ne_zero z
          field_simp
        rw [hz]
        ring
    rw [h3]
    rw [show -2 * ↑π * Complex.I / ↑z = 2 * ↑π * Complex.I / ↑z - 4 * ↑π * Complex.I / ↑z - 0 by
      ring]
    apply Tendsto.sub
    · apply Tendsto.sub
      · simp only [tendsto_const_nhds_iff]
        ring
      apply tsum_exp_tendsto_zero
    have := tendsto_const_div_pow 2 1 (Nat.one_ne_zero)
    rw [Metric.tendsto_atTop] at *
    simp only [one_div, gt_iff_lt, ge_iff_le, pow_one, dist_zero_right, norm_div, Real.norm_ofNat,
      Real.norm_natCast, norm_ofNat, norm_neg] at *
    intro ε hε
    have ht := this ε hε
    obtain ⟨N,HN ⟩ := ht
    use ⟨(N + 1), Nat.zero_lt_succ N⟩
    intro n hn
    have hn1 : N + 1 ≤ (n : ℕ) := by
      have : ((⟨N + 1, Nat.zero_lt_succ N⟩ : ℕ+) : ℕ) ≤ n := (PNat.coe_le_coe _ _).2 hn
      simpa using this
    have hn' : N ≤ (n : ℕ) := Nat.le_trans (Nat.le_succ N) hn1
    simpa [RCLike.norm_natCast] using HN (n : ℕ) hn'
  rw [Metric.tendsto_atTop] at *
  simp only [gt_iff_lt, ge_iff_le, one_div, neg_mul] at *
  intro ε hε
  have th := this ε hε
  obtain ⟨N, hN⟩ := th
  use N
  intro n hn
  have hn0 : 0 < n := by
   have l := N.2
   simp only [gt_iff_lt] at *
   apply Nat.lt_of_lt_of_le l hn
  have HNN := hN ⟨n, hn0⟩ ?_
  · simp only [PNat.mk_coe, gt_iff_lt] at *
    exact HNN
  norm_cast

theorem PS3tn22 (z : ℍ) :
  Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N,
    ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1))) atTop
    (𝓝 (-2 * ↑π * Complex.I / ↑z)) := by
  have : (fun N : ℕ+ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
    (fun N : ℕ+ =>
    ∑' m : ℤ , ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))
      := by
    ext n
    rw [Summable.tsum_finsetSum]
    intro i hi
    apply summable_pain
  conv at this =>
    enter [2]
    ext
    conv =>
      enter [1]
      ext m
      rw [telescope_aux z]
  have hp := sum_int_pnat2_pnat z
  conv at this =>
    enter [2]
    ext m
    rw [show (m : ℂ) = (m : ℕ+) by simp]
    rw [hp]
  rw [this]
  rw [show -2 * ↑π * Complex.I / ↑z = 0 + -2 * ↑π * Complex.I / ↑z by ring]
  apply Tendsto.add
  · exact nat_tendsto_pnat _ _ (tendsto_const_div_atTop_nhds_zero_nat (-2 : ℂ))
  · conv =>
      enter [1]
      ext n
      rw [show (n : ℂ) = (n : ℤ) by simp]
      rw [sum_int_pnat3]
    have := nat_tendsto_pnat _ _ (extracted_12 z)
    exact this

lemma PS3 (z : ℍ) : limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = -2 * π * Complex.I / z := by
  refine Filter.Tendsto.limUnder_eq ?_
  exact pnat_tendsto_nat _ _ (PS3tn22 z)


/-- An algebraic identity used to rewrite terms in the transformed `G₂` series. -/
public theorem poly_id (z : ℍ) (b n : ℤ) :
  ((b : ℂ) * ↑z + ↑n + 1)⁻¹ * (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ + (δ b n) +
    (((b : ℂ) * ↑z + ↑n)⁻¹ - ((b : ℂ) * ↑z + ↑n + 1)⁻¹) =
    (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · simp [δ, h.1, h.2]
  have hn0_of_b0 : b = 0 → n ≠ 0 := fun hb hn => h ⟨hb, hn⟩
  by_cases hb : b = 0
  · subst hb
    by_cases hn : n = -1
    · simp [δ, hn]
      ring
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hn0_of_b0 rfl)
    have hn1 : (n : ℂ) + 1 ≠ 0 := by
      have : (n : ℂ) ≠ (-1 : ℂ) := by exact_mod_cast hn
      simpa [add_eq_zero_iff_eq_neg] using this
    have hδ : δ 0 n = 0 := by simp [δ, hn0_of_b0 rfl, hn]
    simp [hδ]
    field_simp [hn0, hn1]
    ring
  have hδ : δ b n = 0 := by simp [δ, hb]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcd1 : (![(b : ℝ), n + 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    exact hbR (by simpa using congrArg (fun v : Fin 2 → ℝ => v 0) h0)
  have hcd0 : (![(b : ℝ), n] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    exact hbR (by simpa using congrArg (fun v : Fin 2 → ℝ => v 0) h0)
  have h0 : (b : ℂ) * (z : ℂ) + n + 1 ≠ 0 := by
    simpa [add_assoc] using (linear_ne_zero (cd := ![(b : ℝ), n + 1]) z hcd1)
  have h1 : (b : ℂ) * (z : ℂ) + n ≠ 0 := by
    simpa using (linear_ne_zero (cd := ![(b : ℝ), n]) z hcd0)
  simp [hδ]
  field_simp [h0, h1]
  ring

theorem extracted_66c (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp only [inv_neg, mul_neg, Pi.mul_apply]
  rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
    grind only
  · intro i hi
    exact extracted_77 z i

theorem extracted_6 (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-(N : ℤ)) ↑N,
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) := by
  refine Filter.Tendsto.cauchySeq (x := (-2 * π * Complex.I / z)) ?_
  exact pnat_tendsto_nat _ _ (PS3tn22 z)

/-- An `ℤ × ℤ` reindexing of the transformed `G₂` expression on the left-hand side. -/
public lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  rw [G2_S_act, ← PS3 z, tsum_limUnder_atTop, limUnder_sub]
  · congr
    ext N
    simp only [one_div, Pi.sub_apply, mul_inv_rev]
    rw [Summable.tsum_finsetSum, ← Finset.sum_sub_distrib ]
    · congr
      ext n
      rw [← Summable.tsum_sub]
      · congr
        ext m
        have := poly_id z m n
        nth_rw 1 [← this]
        simp only [add_sub_cancel_right]
      · exact extracted_77 z n
      · simpa only [one_div] using (summable_pain z n)
    · intro i hi
      exact extracted_77 z i
  · conv =>
      enter [1]
      ext N
      rw [Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro n
      nth_rw 2 [int_sum_neg]
      congr
      ext m
      simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
      ring
    conv =>
      enter [1]
      ext N
      rw [← Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    have := G2_cauchy ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
    have hC := cauchy_seq_mul_const _ ((z : ℂ) ^ 2)⁻¹ this
    apply hC.congr
    have H := extracted_66c z
    simp only [one_div] at *
    rw [← H]
    ext N
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ (by simpa using inv_ne_zero (pow_ne_zero 2 (ne_zero z)))
    congr
    ext n
    congr
    ext m
    congr
    ring
  · apply extracted_6
  · have := G_2_alt_summable_δ z
    simp only [Fin.isValue, one_div, mul_inv_rev] at this
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    have ht := Summable.prod this
    simp only [Fin.isValue, swap_equiv, Equiv.coe_fn_mk, finTwoArrowEquiv_symm_apply, comp_apply,
      swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
      Matrix.cons_val_zero, one_div, mul_inv_rev] at *
    exact ht

end Definitions
