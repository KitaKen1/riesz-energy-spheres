import E8Leech.CKMRVSeriesTM

/-!
# Sparse series with geometrically growing weights

The same Taylor models as in `CKMRVSeriesTM`, for weights `|wₖ| ≤ W ρᵏ` (`ρ ≥ 1`), with the
remainders `W ρᴺ X^{E N}/(1 − ρX)` (value) and `W ρᴺ E(N) M^{E N − 1}/(1 − ρM)²` (divided
difference). This covers `E₂(x) = 1 − 24 Σ σ₁(n) x^{2n}` with `σ₁(n + 1) ≤ 4ⁿ`.
-/

namespace E8Leech.Taylor

open scoped Real

theorem abs_tail_le_geom {E : ℕ → ℕ} (hE : StrictMono E) {w : ℕ → ℝ} {W ρ : ℝ}
    (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ) {x : ℝ} (hx0 : 0 ≤ x) (hρx : ρ * x < 1)
    (N : ℕ) : |∑' k, w (k + N) * x ^ E (k + N)| ≤ W * ρ ^ N * x ^ E N / (1 - ρ * x) := by
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
  have hW : 0 ≤ W := by
    have := le_trans (abs_nonneg _) (hw 0)
    simpa using this
  have hρx0 : 0 ≤ ρ * x := mul_nonneg hρ0 hx0
  have hx1 : x ≤ 1 := by nlinarith
  have hgeom : Summable fun k : ℕ => W * ρ ^ N * x ^ E N * (ρ * x) ^ k :=
    (summable_geometric_of_lt_one hρx0 hρx).mul_left _
  have hbound : ∀ k, |w (k + N) * x ^ E (k + N)| ≤ W * ρ ^ N * x ^ E N * (ρ * x) ^ k := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
    have h1 := hw (k + N)
    have h2 : x ^ E (k + N) ≤ x ^ (E N + k) := pow_le_pow_of_le_one hx0 hx1 (strictMono_add_le hE N k)
    calc |w (k + N)| * x ^ E (k + N) ≤ W * ρ ^ (k + N) * x ^ (E N + k) :=
          mul_le_mul h1 h2 (pow_nonneg hx0 _) (by positivity)
      _ = W * ρ ^ N * x ^ E N * (ρ * x) ^ k := by rw [pow_add, pow_add, mul_pow]; ring
  have hs : Summable fun k => w (k + N) * x ^ E (k + N) :=
    Summable.of_norm_bounded hgeom (fun k => by simpa [Real.norm_eq_abs] using hbound k)
  calc |∑' k, w (k + N) * x ^ E (k + N)|
      ≤ ∑' k, |w (k + N) * x ^ E (k + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun k => w (k + N) * x ^ E (k + N))
          (by simpa only [Real.norm_eq_abs] using hs.abs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k, W * ρ ^ N * x ^ E N * (ρ * x) ^ k := Summable.tsum_le_tsum hbound hs.abs hgeom
    _ = W * ρ ^ N * x ^ E N / (1 - ρ * x) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρx0 hρx]
        ring

theorem summable_series_geom {E : ℕ → ℕ} (hE : StrictMono E) {w : ℕ → ℝ} {W ρ : ℝ}
    (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ) {x : ℝ} (hx0 : 0 ≤ x) (hρx : ρ * x < 1) :
    Summable fun k => w k * x ^ E k := by
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
  have hW : 0 ≤ W := by
    have := le_trans (abs_nonneg _) (hw 0)
    simpa using this
  have hρx0 : 0 ≤ ρ * x := mul_nonneg hρ0 hx0
  have hx1 : x ≤ 1 := by nlinarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρx0 hρx).mul_left W) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
  calc |w k| * x ^ E k ≤ W * ρ ^ k * x ^ k :=
        mul_le_mul (hw k) (pow_le_pow_of_le_one hx0 hx1 (strictMono_le_self hE k))
          (pow_nonneg hx0 _) (by positivity)
    _ = W * (ρ * x) ^ k := by rw [mul_pow]; ring

/-- **Value Taylor model, geometric weights.** -/
theorem seriesTM_approx_geom {B : Box} {S : Env → Prop} (side : Bool) {E : ℕ → ℕ}
    (hE : StrictMono E) {w : ℕ → ℚ} {W ρ : ℚ} (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ)
    (c0 : ℚ) (N : ℕ) {X : ℚ} (hρX : ρ * X < 1)
    (hside : ∀ e, B.Mem e → 0 ≤ e.nome side ∧ e.nome side ≤ X) :
    (⟨seriesPoly side c0 w E N, W * ρ ^ N * X ^ E N / (1 - ρ * X)⟩ : TM).Approx B S
      (fun e => c0 + ∑' k, (w k : ℝ) * e.nome side ^ E k) := by
  intro e he _
  obtain ⟨hx0, hxX⟩ := hside e he
  have hρ' : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ'
  have hρX' : (ρ : ℝ) * X < 1 := by exact_mod_cast hρX
  have hρx : (ρ : ℝ) * e.nome side < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxX hρ0) hρX'
  have hw' : ∀ k, |(w k : ℝ)| ≤ W * (ρ : ℝ) ^ k := fun k => by exact_mod_cast hw k
  have hs := summable_series_geom hE hw' hρ' hx0 hρx
  simp only
  rw [seriesPoly_eval, ← hs.sum_add_tsum_nat_add N]
  have htail := abs_tail_le_geom hE hw' hρ' hx0 hρx N
  have hW : (0 : ℝ) ≤ W := by
    have := le_trans (abs_nonneg _) (hw' 0)
    simpa using this
  have hX0 : (0 : ℝ) ≤ X := le_trans hx0 hxX
  calc |(c0 : ℝ) + (∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k +
          ∑' k, (w (k + N) : ℝ) * e.nome side ^ E (k + N)) -
        (c0 + ∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k)|
      = |∑' k, (w (k + N) : ℝ) * e.nome side ^ E (k + N)| := by congr 1; ring
    _ ≤ W * ρ ^ N * e.nome side ^ E N / (1 - ρ * e.nome side) := htail
    _ ≤ W * ρ ^ N * (X : ℝ) ^ E N / (1 - ρ * X) := by
        have h1 : 0 < 1 - (ρ : ℝ) * X := by linarith
        have h2 : 0 < 1 - (ρ : ℝ) * e.nome side := by linarith
        rw [div_le_div_iff₀ h2 h1]
        have hp : e.nome side ^ E N ≤ (X : ℝ) ^ E N := pow_le_pow_left₀ hx0 hxX _
        have hc : (0 : ℝ) ≤ W * ρ ^ N := by positivity
        have k1 : W * ρ ^ N * e.nome side ^ E N * (1 - ρ * X) ≤
            W * ρ ^ N * (X : ℝ) ^ E N * (1 - ρ * X) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) h1.le
        have k2 : W * ρ ^ N * (X : ℝ) ^ E N * (1 - ρ * X) ≤
            W * ρ ^ N * (X : ℝ) ^ E N * (1 - ρ * e.nome side) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hc (pow_nonneg hX0 _))
        linarith
    _ = _ := by push_cast; ring

/-- **Divided-difference Taylor model, geometric weights**, off the diagonal `a = b`. -/
theorem seriesDD_approx_geom {B : Box} {S : Env → Prop} {E : ℕ → ℕ} (hE : StrictMono E)
    (hE0 : 1 ≤ E 0) {w : ℕ → ℚ} {W ρ : ℚ} (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ)
    (c0 : ℚ) (N : ℕ) {M : ℚ} (hM : M ≤ 1 / 2) (hρM : ρ * M < 1)
    (hab : ∀ e, B.Mem e → 0 ≤ e.a ∧ e.a ≤ M ∧ 0 ≤ e.b ∧ e.b ≤ M) :
    (⟨seriesDDPoly w E N, W * ρ ^ N * E N * M ^ (E N - 1) / (1 - ρ * M) ^ 2⟩ : TM).Approx B
      (fun e => S e ∧ e.a ≠ e.b)
      (fun e => ((c0 + ∑' k, (w k : ℝ) * e.b ^ E k) - (c0 + ∑' k, (w k : ℝ) * e.a ^ E k)) /
        (e.b - e.a)) := by
  intro e he hs
  obtain ⟨ha0, haM, hb0, hbM⟩ := hab e he
  have hM' : (M : ℝ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hM
  have hρ' : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ'
  have hρM' : (ρ : ℝ) * M < 1 := by exact_mod_cast hρM
  have hM0 : (0 : ℝ) ≤ M := le_trans ha0 haM
  have hρM0 : (0 : ℝ) ≤ ρ * M := mul_nonneg hρ0 hM0
  have hρa : (ρ : ℝ) * e.a < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left haM hρ0) hρM'
  have hρb : (ρ : ℝ) * e.b < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbM hρ0) hρM'
  have hw' : ∀ k, |(w k : ℝ)| ≤ W * (ρ : ℝ) ^ k := fun k => by exact_mod_cast hw k
  have hW : (0 : ℝ) ≤ W := by
    have := le_trans (abs_nonneg _) (hw' 0)
    simpa using this
  have hba : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  set h : ℕ → ℝ := fun k => (w k : ℝ) * ∑ i ∈ Finset.range (E k), e.a ^ i * e.b ^ (E k - 1 - i)
    with hh
  have hterm : ∀ k, |h k| ≤ W * (ρ : ℝ) ^ k * ((E k : ℝ) * M ^ (E k - 1)) := fun k => by
    rw [hh, abs_mul]
    exact mul_le_mul (hw' k) (abs_hsum_le _ ha0 hb0 haM hbM) (abs_nonneg _) (by positivity)
  have hEk : ∀ k, 1 ≤ E k := fun k => le_trans hE0 (hE.monotone (Nat.zero_le k))
  have hmaj : ∀ k, W * (ρ : ℝ) ^ (k + N) * ((E (k + N) : ℝ) * M ^ (E (k + N) - 1)) ≤
      W * (ρ : ℝ) ^ N * ((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * (ρ * M) ^ k) := fun k => by
    have h1 : (E (k + N) : ℝ) * M ^ (E (k + N) - 1) ≤ ((E N + k : ℕ) : ℝ) * M ^ (E N + k - 1) :=
      mul_pow_antitone hM0 hM' (by have := hEk N; omega) (strictMono_add_le hE N k)
    have h2 : ((E N + k : ℕ) : ℝ) * M ^ (E N + k - 1) ≤
        ((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * M ^ k) := by
      have hEN := hEk N
      have hexp : E N + k - 1 = (E N - 1) + k := by omega
      rw [hexp, pow_add]
      have hk : (0 : ℝ) ≤ M ^ (E N - 1) * M ^ k := by positivity
      push_cast
      have hENr : (1 : ℝ) ≤ E N := by exact_mod_cast hEN
      nlinarith [mul_nonneg hk (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    calc W * (ρ : ℝ) ^ (k + N) * ((E (k + N) : ℝ) * M ^ (E (k + N) - 1))
        ≤ W * (ρ : ℝ) ^ (k + N) * (((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * M ^ k)) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
      _ = _ := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable fun k : ℕ =>
      W * (ρ : ℝ) ^ N * ((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * (ρ * M) ^ k) := by
    refine Summable.mul_left _ ?_
    have hs1 : Summable fun k : ℕ => (k : ℝ) * (ρ * M) ^ k :=
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hρM0]; exact hρM')).congr fun k => by simp
    exact (hs1.add (summable_geometric_of_lt_one hρM0 hρM')).congr fun k => by ring
  have hsum_h : Summable h := by
    have hshift : Summable fun k => h (k + N) :=
      Summable.of_norm_bounded hgeo fun k => by
        rw [Real.norm_eq_abs]; exact le_trans (hterm _) (hmaj k)
    exact (summable_nat_add_iff N).mp hshift
  have hfa := summable_series_geom hE hw' hρ' ha0 hρa
  have hfb := summable_series_geom hE hw' hρ' hb0 hρb
  have hdd : ((c0 + ∑' k, (w k : ℝ) * e.b ^ E k) - (c0 + ∑' k, (w k : ℝ) * e.a ^ E k)) /
      (e.b - e.a) = ∑' k, h k := by
    rw [div_eq_iff hba, add_sub_add_left_eq_sub, ← hfb.tsum_sub hfa, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [hh]
    simp only
    rw [mul_assoc, hsum_mul_sub]
    ring
  dsimp only
  rw [hdd, seriesDDPoly_eval, ← hsum_h.sum_add_tsum_nat_add N]
  have htail : |∑' k, h (k + N)| ≤
      W * (ρ : ℝ) ^ N * ((E N : ℝ) * M ^ (E N - 1)) * (1 / (1 - ρ * M) ^ 2) := by
    rw [← tsum_succ_mul_geometric hρM0 hρM', ← tsum_mul_left]
    calc |∑' k, h (k + N)| ≤ ∑' k, |h (k + N)| := by
          have := norm_tsum_le_tsum_norm (f := fun k => h (k + N)) (by
            simpa only [Real.norm_eq_abs] using ((summable_nat_add_iff N).mpr hsum_h).abs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ _ := Summable.tsum_le_tsum (fun k => le_trans (hterm _) (hmaj k))
          ((summable_nat_add_iff N).mpr hsum_h).abs hgeo
  calc |∑ k ∈ Finset.range N, h k + ∑' k, h (k + N) - ∑ k ∈ Finset.range N, h k|
      = |∑' k, h (k + N)| := by congr 1; ring
    _ ≤ W * (ρ : ℝ) ^ N * ((E N : ℝ) * M ^ (E N - 1)) * (1 / (1 - ρ * M) ^ 2) := htail
    _ = _ := by push_cast; ring

end E8Leech.Taylor
