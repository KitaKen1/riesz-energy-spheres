import E8Leech.KronDD
import E8Leech.CKMRVGeneratorModels

/-!
# The nome generators as divided-difference models with majorants

The four sparse series `θ₃, θ₄, η₁, E₂` of the nome and the nome itself are modelled as `MDD`
triples. The remainders are monomials in the nomes:

* value in the nome `x`: `|tail| ≤ W ρᴺ x^{E N}/(1 − ρ x)`, a multiple of `x^{E N}`;
* divided difference: `|tail| ≤ W ρᴺ (a + b)^{E N − 1}/(1 − ρ (a + b))`, because
  `Σ_{i<n} aⁱ b^{n−1−i} ≤ (a + b)^{n−1}`.

Hence the remainders vanish with the nomes, which an absolute radius cannot express. The real
series identities are those of `CKMRVGenDD`; the weights are integers here.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

/-! ## Pointwise tails of sparse series -/

theorem series_tail_le {E : ℕ → ℕ} (hE : StrictMono E) {w : ℕ → ℝ} {W ρ : ℝ}
    (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ) {x : ℝ} (hx0 : 0 ≤ x) (hρx : ρ * x < 1) (c0 : ℝ)
    (N : ℕ) :
    |(c0 + ∑' k, w k * x ^ E k) - (c0 + ∑ k ∈ Finset.range N, w k * x ^ E k)| ≤
      W * ρ ^ N * x ^ E N / (1 - ρ * x) := by
  have hs := summable_series_geom hE hw hρ hx0 hρx
  have htail := abs_tail_le_geom hE hw hρ hx0 hρx N
  have h2 : ∀ A T : ℝ, c0 + (A + T) - (c0 + A) = T := fun A T => by ring
  rw [← hs.sum_add_tsum_nat_add N, h2]
  exact htail

/-- `Σ_{i ≤ m} aⁱ b^{m−i} ≤ (a + b)ᵐ`. -/
theorem hsum_le_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m - i) ≤ (a + b) ^ m := by
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  have hc : (1 : ℝ) ≤ (m.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hnn : 0 ≤ a ^ i * b ^ (m - i) := mul_nonneg (pow_nonneg ha i) (pow_nonneg hb _)
  nlinarith [mul_nonneg hnn (sub_nonneg.mpr hc)]

/-- The tail of the divided difference of a sparse series, as a power of `a + b`. -/
theorem seriesDD_tail_le {E : ℕ → ℕ} (hE : StrictMono E) (hE0 : 1 ≤ E 0) {w : ℕ → ℝ}
    {W ρ : ℝ} (hw : ∀ k, |w k| ≤ W * ρ ^ k) (hρ : 1 ≤ ρ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) (hρs : ρ * (a + b) < 1) (c0 : ℝ) (N : ℕ) :
    |((c0 + ∑' k, w k * b ^ E k) - (c0 + ∑' k, w k * a ^ E k)) / (b - a) -
        ∑ k ∈ Finset.range N, w k * ∑ i ∈ Finset.range (E k), a ^ i * b ^ (E k - 1 - i)| ≤
      W * ρ ^ N * (a + b) ^ (E N - 1) / (1 - ρ * (a + b)) := by
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ
  have hs0 : 0 ≤ a + b := add_nonneg ha hb
  have hρs0 : 0 ≤ ρ * (a + b) := mul_nonneg hρ0 hs0
  have hs1 : a + b ≤ 1 := by nlinarith
  have hρa : ρ * a < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) hρ0) hρs
  have hρb : ρ * b < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) hρ0) hρs
  have hW : (0 : ℝ) ≤ W := by
    have := le_trans (abs_nonneg _) (hw 0)
    simpa using this
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hEk : ∀ k, 1 ≤ E k := fun k => le_trans hE0 (hE.monotone (Nat.zero_le k))
  set h : ℕ → ℝ := fun k => w k * ∑ i ∈ Finset.range (E k), a ^ i * b ^ (E k - 1 - i) with hh
  have hterm : ∀ k, |h k| ≤ W * ρ ^ k * (a + b) ^ (E k - 1) := fun k => by
    have hsum := hsum_le_add_pow ha hb (E k - 1)
    rw [Nat.sub_add_cancel (hEk k)] at hsum
    have hnn : 0 ≤ ∑ i ∈ Finset.range (E k), a ^ i * b ^ (E k - 1 - i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg ha i) (pow_nonneg hb _)
    rw [hh, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul (hw k) hsum hnn (by positivity)
  have hmaj : ∀ k, W * ρ ^ (k + N) * (a + b) ^ (E (k + N) - 1) ≤
      W * ρ ^ N * (a + b) ^ (E N - 1) * (ρ * (a + b)) ^ k := fun k => by
    have hexp : E N - 1 + k ≤ E (k + N) - 1 := by
      have h1 := strictMono_add_le hE N k
      have h2 := hEk N
      omega
    have hp : (a + b) ^ (E (k + N) - 1) ≤ (a + b) ^ (E N - 1 + k) :=
      pow_le_pow_of_le_one hs0 hs1 hexp
    calc W * ρ ^ (k + N) * (a + b) ^ (E (k + N) - 1)
        ≤ W * ρ ^ (k + N) * (a + b) ^ (E N - 1 + k) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [pow_add, pow_add, mul_pow]; ring
  have hgeo : Summable fun k : ℕ => W * ρ ^ N * (a + b) ^ (E N - 1) * (ρ * (a + b)) ^ k :=
    (summable_geometric_of_lt_one hρs0 hρs).mul_left _
  have hsum_h : Summable h := by
    have hshift : Summable fun k => h (k + N) :=
      Summable.of_norm_bounded hgeo fun k => by
        rw [Real.norm_eq_abs]
        exact le_trans (hterm _) (hmaj k)
    exact (summable_nat_add_iff N).mp hshift
  have hfa := summable_series_geom hE hw hρ ha hρa
  have hfb := summable_series_geom hE hw hρ hb hρb
  have hdd : ((c0 + ∑' k, w k * b ^ E k) - (c0 + ∑' k, w k * a ^ E k)) / (b - a) =
      ∑' k, h k := by
    rw [div_eq_iff hba, add_sub_add_left_eq_sub, ← hfb.tsum_sub hfa, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [hh]
    simp only
    rw [mul_assoc, hsum_mul_sub]
    ring
  have htail : |∑' k, h (k + N)| ≤ W * ρ ^ N * (a + b) ^ (E N - 1) / (1 - ρ * (a + b)) := by
    calc |∑' k, h (k + N)| ≤ ∑' k, |h (k + N)| := by
          have := norm_tsum_le_tsum_norm (f := fun k => h (k + N)) (by
            simpa only [Real.norm_eq_abs] using ((summable_nat_add_iff N).mpr hsum_h).abs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' k, W * ρ ^ N * (a + b) ^ (E N - 1) * (ρ * (a + b)) ^ k :=
          Summable.tsum_le_tsum (fun k => le_trans (hterm _) (hmaj k))
            ((summable_nat_add_iff N).mpr hsum_h).abs hgeo
      _ = W * ρ ^ N * (a + b) ^ (E N - 1) / (1 - ρ * (a + b)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hρs0 hρs]
          ring
  have h2 : ∀ A T : ℝ, A + T - A = T := fun A T => by ring
  rw [hdd, ← hsum_h.sum_add_tsum_nat_add N, h2]
  exact htail

/-! ## Majorant constants -/

/-- `⌈W ρᴺ / (1 − ρ num/den)⌉`. -/
def tailConst (W ρ N num den : ℕ) : ℕ := ceilDiv (W * ρ ^ N * den) (den - ρ * num)

theorem tailConst_spec {W ρ N num den : ℕ} (h : ρ * num < den) {x : ℝ}
    (hx : x * den ≤ num) :
    (W : ℝ) * (ρ : ℝ) ^ N ≤ (tailConst W ρ N num den : ℝ) * (1 - ρ * x) := by
  have hd : 0 < den - ρ * num := Nat.sub_pos_of_lt h
  have hden : (0 : ℝ) < den := by exact_mod_cast Nat.zero_lt_of_lt h
  have h1 : ((W * ρ ^ N * den : ℕ) : ℝ) ≤
      ((tailConst W ρ N num den * (den - ρ * num) : ℕ) : ℝ) := by
    exact_mod_cast le_ceilDiv_mul (W * ρ ^ N * den) hd
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h.le, Nat.cast_mul]
    at h1
  have hK : (0 : ℝ) ≤ (tailConst W ρ N num den : ℝ) := Nat.cast_nonneg _
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have h2 : (den : ℝ) - ρ * num ≤ (1 - ρ * x) * den := by
    nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hx)]
  have h3 : (W : ℝ) * (ρ : ℝ) ^ N * den ≤ (tailConst W ρ N num den : ℝ) * (1 - ρ * x) * den := by
    calc (W : ℝ) * (ρ : ℝ) ^ N * den ≤ (tailConst W ρ N num den : ℝ) * ((den : ℝ) - ρ * num) := h1
      _ ≤ (tailConst W ρ N num den : ℝ) * ((1 - ρ * x) * den) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hden

theorem tail_le_const_mul {W ρ N num den : ℕ} (h : ρ * num < den) {x y : ℝ}
    (hx : x * den ≤ num) (hy : 0 ≤ y) :
    (W : ℝ) * (ρ : ℝ) ^ N * y / (1 - ρ * x) ≤ (tailConst W ρ N num den : ℝ) * y := by
  have hden : (0 : ℝ) < den := by exact_mod_cast Nat.zero_lt_of_lt h
  have hlt : (ρ : ℝ) * x < 1 := by
    have h1 : ((ρ * num : ℕ) : ℝ) < den := by exact_mod_cast h
    push_cast at h1
    have h2 : (ρ : ℝ) * x * den ≤ ρ * num := by
      have := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg ρ : (0 : ℝ) ≤ ρ)
      linarith
    by_contra hcon
    have h3 : (1 : ℝ) * den ≤ ρ * x * den :=
      mul_le_mul_of_nonneg_right (not_lt.mp hcon) hden.le
    linarith
  rw [div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_right (tailConst_spec (W := W) (N := N) h hx) hy
  linarith

/-! ## Series polynomials with integer weights -/

namespace IPoly

theorem eval_map_range (f : ℕ → NMono × ℤ) (N : ℕ) (e : NEnv) :
    eval ((List.range N).map f) e =
      ∑ k ∈ Finset.range N, ((f k).2 : ℝ) * (f k).1.eval e := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, eval_append, ih, Finset.sum_range_succ]
    simp

/-- The monomial `xⁿ` in the nome `a` (`side = true`) or `b`. -/
def nomeMono (side : Bool) (n : ℕ) : NMono := bif side then ⟨n, 0, 0, 0, 0⟩ else ⟨0, n, 0, 0, 0⟩

end IPoly

/-- The nome `a` (`side = true`) or `b`. -/
def NEnv.nome (side : Bool) (e : NEnv) : ℝ := bif side then e.a else e.b

namespace IPoly

theorem nomeMono_eval (side : Bool) (n : ℕ) (e : NEnv) :
    (nomeMono side n).eval e = e.nome side ^ n := by
  cases side <;> simp [nomeMono, NEnv.nome, NMono.eval]

/-- `c₀ + Σ_{k<N} wₖ x^{E k}`. -/
def seriesIPoly (side : Bool) (c0 : ℤ) (w : ℕ → ℤ) (E : ℕ → ℕ) (N : ℕ) : IPoly :=
  (NMono.one, c0) :: (List.range N).map fun k => (nomeMono side (E k), w k)

theorem seriesIPoly_eval (side : Bool) (c0 : ℤ) (w : ℕ → ℤ) (E : ℕ → ℕ) (N : ℕ) (e : NEnv) :
    eval (seriesIPoly side c0 w E N) e =
      c0 + ∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k := by
  rw [seriesIPoly, eval_cons, eval_map_range]
  simp [NMono.eval_one, IPoly.nomeMono_eval]

/-- `Σ_{i<n} aⁱ b^{n−1−i}`. -/
def hIPoly (n : ℕ) : IPoly := (List.range n).map fun i => (⟨i, n - 1 - i, 0, 0, 0⟩, 1)

theorem hIPoly_eval (n : ℕ) (e : NEnv) :
    eval (hIPoly n) e = ∑ i ∈ Finset.range n, e.a ^ i * e.b ^ (n - 1 - i) := by
  rw [hIPoly, eval_map_range]
  simp [NMono.eval]

/-- `Σ_{k<N} wₖ h_{E k}(a, b)`. -/
def seriesDDIPoly (w : ℕ → ℤ) (E : ℕ → ℕ) (N : ℕ) : IPoly :=
  ((List.range N).map fun k => scale (w k) (hIPoly (E k))).flatten

theorem seriesDDIPoly_eval (w : ℕ → ℤ) (E : ℕ → ℕ) (N : ℕ) (e : NEnv) :
    eval (seriesDDIPoly w E N) e =
      ∑ k ∈ Finset.range N, (w k : ℝ) *
        ∑ i ∈ Finset.range (E k), e.a ^ i * e.b ^ (E k - 1 - i) := by
  unfold seriesDDIPoly
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, eval_append, ih,
      Finset.sum_range_succ]
    simp [eval_scale, hIPoly_eval]

/-- `(a + b)ᵐ`. -/
def addPowIPoly (m : ℕ) : IPoly :=
  (List.range (m + 1)).map fun i => (⟨i, m - i, 0, 0, 0⟩, (m.choose i : ℤ))

theorem addPowIPoly_eval (m : ℕ) (e : NEnv) : eval (addPowIPoly m) e = (e.a + e.b) ^ m := by
  rw [addPowIPoly, eval_map_range, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [NMono.eval, pow_zero, mul_one]
  push_cast
  ring

end IPoly

/-! ## The series triple -/

open IPoly

/-- The triple of a sparse series with integer weights and monomial remainders. -/
def seriesMDD (Bx : Bounds) (c0 : ℤ) (w : ℕ → ℤ) (E : ℕ → ℕ) (W ρ N : ℕ) : MDD :=
  ⟨⟨seriesIPoly true c0 w E N, [(nomeMono true (E N), (tailConst W ρ N Bx.an Bx.ad : ℕ))]⟩,
    ⟨seriesIPoly false c0 w E N, [(nomeMono false (E N), (tailConst W ρ N Bx.bn Bx.bd : ℕ))]⟩,
    ⟨seriesDDIPoly w E N,
      IPoly.scale (tailConst W ρ N (Bx.an * Bx.bd + Bx.bn * Bx.ad) (Bx.ad * Bx.bd) : ℕ)
        (addPowIPoly (E N - 1))⟩⟩

/-- The nome bounds leave room for the geometric tails with ratio `ρ`. -/
def SeriesOK (Bx : Bounds) (ρ : ℕ) : Prop :=
  Bx.Valid ∧ ρ * Bx.an < Bx.ad ∧ ρ * Bx.bn < Bx.bd ∧
    ρ * (Bx.an * Bx.bd + Bx.bn * Bx.ad) < Bx.ad * Bx.bd

instance (Bx : Bounds) (ρ : ℕ) : Decidable (SeriesOK Bx ρ) := by
  unfold SeriesOK Bounds.Valid
  infer_instance

theorem approx_seriesMDD {Bx : Bounds} {S : NEnv → Prop} {E : ℕ → ℕ} (hE : StrictMono E)
    (hE0 : 1 ≤ E 0) {w : ℕ → ℚ} {W ρ : ℕ} (hw : ∀ k, |w k| ≤ (W : ℚ) * (ρ : ℚ) ^ k)
    (hρ : 1 ≤ ρ) (hOK : SeriesOK Bx ρ) (c0 : ℤ) (N : ℕ) (wZ : ℕ → ℤ)
    (hwZ : ∀ k, k < N → ((wZ k : ℤ) : ℚ) = w k) :
    (seriesMDD Bx c0 wZ E W ρ N).Approx Bx S
      (fun e => (c0 : ℝ) + ∑' k, (w k : ℝ) * e.a ^ E k)
      (fun e => (c0 : ℝ) + ∑' k, (w k : ℝ) * e.b ^ E k) := by
  obtain ⟨hB, hsa, hsb, hss⟩ := hOK
  have hw' : ∀ k, |(w k : ℝ)| ≤ (W : ℝ) * (ρ : ℝ) ^ k := fun k => by exact_mod_cast hw k
  have hρ' : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have hcast : ∀ k, k < N → ((wZ k : ℤ) : ℝ) = (w k : ℝ) := fun k hk => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hwZ k hk)
    simpa using this
  have hlt : ∀ {num den : ℕ} {x : ℝ}, ρ * num < den → x * den ≤ num → (ρ : ℝ) * x < 1 := by
    intro num den x h hx
    have hden : (0 : ℝ) < den := by exact_mod_cast Nat.zero_lt_of_lt h
    have h1 : ((ρ * num : ℕ) : ℝ) < den := by exact_mod_cast h
    push_cast at h1
    have h2 : (ρ : ℝ) * x * den ≤ ρ * num := by
      have := mul_le_mul_of_nonneg_left hx hρ0
      linarith
    by_contra hcon
    have h3 : (1 : ℝ) * den ≤ ρ * x * den :=
      mul_le_mul_of_nonneg_right (not_lt.mp hcon) hden.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro e he _
    obtain ⟨ha, ha', -⟩ := he
    have ht := series_tail_le hE hw' hρ' ha (hlt hsa ha') (c0 : ℝ) N
    have hb := tail_le_const_mul (W := W) (N := N) hsa ha' (pow_nonneg ha (E N))
    have hP : eval (seriesIPoly true c0 wZ E N) e =
        (c0 : ℝ) + ∑ k ∈ Finset.range N, (w k : ℝ) * e.a ^ E k := by
      rw [seriesIPoly_eval]
      congr 1
      exact Finset.sum_congr rfl fun k hk => by
        rw [hcast k (Finset.mem_range.mp hk)]
        rfl
    have hR : eval [(nomeMono true (E N), ((tailConst W ρ N Bx.an Bx.ad : ℕ) : ℤ))] e =
        (tailConst W ρ N Bx.an Bx.ad : ℝ) * e.a ^ E N := by
      rw [eval_cons, eval_nil, IPoly.nomeMono_eval, add_zero]
      simp [NEnv.nome]
    show |(c0 : ℝ) + ∑' k, (w k : ℝ) * e.a ^ E k - eval (seriesIPoly true c0 wZ E N) e| ≤
      eval [(nomeMono true (E N), ((tailConst W ρ N Bx.an Bx.ad : ℕ) : ℤ))] e
    rw [hP, hR]
    exact ht.trans hb
  · intro e he _
    obtain ⟨-, -, hb0, hb', -⟩ := he
    have ht := series_tail_le hE hw' hρ' hb0 (hlt hsb hb') (c0 : ℝ) N
    have hb := tail_le_const_mul (W := W) (N := N) hsb hb' (pow_nonneg hb0 (E N))
    have hP : eval (seriesIPoly false c0 wZ E N) e =
        (c0 : ℝ) + ∑ k ∈ Finset.range N, (w k : ℝ) * e.b ^ E k := by
      rw [seriesIPoly_eval]
      congr 1
      exact Finset.sum_congr rfl fun k hk => by
        rw [hcast k (Finset.mem_range.mp hk)]
        rfl
    have hR : eval [(nomeMono false (E N), ((tailConst W ρ N Bx.bn Bx.bd : ℕ) : ℤ))] e =
        (tailConst W ρ N Bx.bn Bx.bd : ℝ) * e.b ^ E N := by
      rw [eval_cons, eval_nil, IPoly.nomeMono_eval, add_zero]
      simp [NEnv.nome]
    show |(c0 : ℝ) + ∑' k, (w k : ℝ) * e.b ^ E k - eval (seriesIPoly false c0 wZ E N) e| ≤
      eval [(nomeMono false (E N), ((tailConst W ρ N Bx.bn Bx.bd : ℕ) : ℤ))] e
    rw [hP, hR]
    exact ht.trans hb
  · intro e he hs
    obtain ⟨ha, ha', hb0, hb', -⟩ := he
    have hs0 : 0 ≤ e.a + e.b := add_nonneg ha hb0
    have hsx : (e.a + e.b) * ((Bx.ad * Bx.bd : ℕ) : ℝ) ≤ ((Bx.an * Bx.bd + Bx.bn * Bx.ad : ℕ) : ℝ) := by
      push_cast
      have h1 := mul_le_mul_of_nonneg_right ha' (Nat.cast_nonneg Bx.bd : (0 : ℝ) ≤ Bx.bd)
      have h2 := mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg Bx.ad : (0 : ℝ) ≤ Bx.ad)
      nlinarith
    have ht := seriesDD_tail_le hE hE0 hw' hρ' ha hb0 hs.2 (hlt hss hsx) (c0 : ℝ) N
    have hb := tail_le_const_mul (W := W) (N := N) hss hsx (pow_nonneg hs0 (E N - 1))
    have hP : eval (seriesDDIPoly wZ E N) e = ∑ k ∈ Finset.range N, (w k : ℝ) *
        ∑ i ∈ Finset.range (E k), e.a ^ i * e.b ^ (E k - 1 - i) := by
      rw [seriesDDIPoly_eval]
      exact Finset.sum_congr rfl fun k hk => by rw [hcast k (Finset.mem_range.mp hk)]
    have hR : eval (IPoly.scale
        ((tailConst W ρ N (Bx.an * Bx.bd + Bx.bn * Bx.ad) (Bx.ad * Bx.bd) : ℕ) : ℤ)
        (addPowIPoly (E N - 1))) e =
        (tailConst W ρ N (Bx.an * Bx.bd + Bx.bn * Bx.ad) (Bx.ad * Bx.bd) : ℝ) *
          (e.a + e.b) ^ (E N - 1) := by
      rw [eval_scale, addPowIPoly_eval]
      push_cast
      ring
    show |((c0 : ℝ) + ∑' k, (w k : ℝ) * e.b ^ E k - ((c0 : ℝ) + ∑' k, (w k : ℝ) * e.a ^ E k)) /
        (e.b - e.a) - eval (seriesDDIPoly wZ E N) e| ≤ _
    rw [hP]
    refine ht.trans (hb.trans (le_of_eq ?_))
    exact hR.symm

end E8Leech.Kron
