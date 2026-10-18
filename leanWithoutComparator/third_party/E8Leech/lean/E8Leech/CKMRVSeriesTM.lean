import E8Leech.TaylorModelOps
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Ring.GeomSum

/-!
# Taylor models of the sparse nome series

For a series `f(x) = c₀ + Σₖ wₖ x^{E k}` with strictly increasing exponents `E k ≥ 1` and
`|wₖ| ≤ W`, on `0 ≤ x ≤ X < 1`:

* the value `f(x)` is the truncated polynomial `c₀ + Σ_{k<N} wₖ x^{E k}` up to `W X^{E N}/(1 − X)`;
* the divided difference `(f(b) − f(a))/(b − a)` is `Σ_{k<N} wₖ h_{E k − 1}(a, b)`
  (`hₙ(a, b) = Σ_{i ≤ n} aⁱ bⁿ⁻ⁱ`) up to `W E(N) m^{E N − 1}/(1 − m)²`, `m = max(a, b) ≤ 1/2`.

This covers `θ₃`, `θ₄` and `η₁`.
-/

namespace E8Leech.Taylor

open scoped Real

/-- The monomial `xⁿ` on the side `a` (`true`) or `b` (`false`). -/
def nomeMono (side : Bool) (n : ℕ) : Mono :=
  if side then ⟨n, 0, 0, 0, 0, 0⟩ else ⟨0, n, 0, 0, 0, 0⟩

/-- The nome on the given side. -/
def Env.nome (side : Bool) (e : Env) : ℝ := if side then e.a else e.b

theorem nomeMono_eval (side : Bool) (n : ℕ) (e : Env) :
    (nomeMono side n).eval e = e.nome side ^ n := by
  cases side <;> simp [nomeMono, Mono.eval, Env.nome]

/-- `c₀ + Σ_{k<N} wₖ x^{E k}` on one side. -/
def seriesPoly (side : Bool) (c0 : ℚ) (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) : Poly :=
  (Mono.one, c0) :: (List.range N).map fun k => (nomeMono side (E k), w k)

theorem eval_map_range (side : Bool) (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) (e : Env) :
    Poly.eval ((List.range N).map fun k => (nomeMono side (E k), w k)) e =
      ∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, Poly.eval_append, ih, Finset.sum_range_succ]
    simp [nomeMono_eval]

theorem seriesPoly_eval (side : Bool) (c0 : ℚ) (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) (e : Env) :
    (seriesPoly side c0 w E N).eval e = c0 + ∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k := by
  rw [seriesPoly, Poly.eval_cons, eval_map_range, Mono.eval_one, mul_one]

theorem strictMono_add_le {E : ℕ → ℕ} (hE : StrictMono E) (N k : ℕ) : E N + k ≤ E (k + N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := hE (show k + N < k + 1 + N by omega)
    omega

/-- The tail of a sparse series with bounded weights. -/
theorem abs_tail_le {E : ℕ → ℕ} (hE : StrictMono E) {w : ℕ → ℝ} {W : ℝ} (hw : ∀ k, |w k| ≤ W)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    |∑' k, w (k + N) * x ^ E (k + N)| ≤ W * x ^ E N / (1 - x) := by
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (hw 0)
  have hgeom : Summable fun k : ℕ => W * x ^ E N * x ^ k :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have hbound : ∀ k, |w (k + N) * x ^ E (k + N)| ≤ W * x ^ E N * x ^ k := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _), mul_assoc, ← pow_add]
    exact mul_le_mul (hw _) (pow_le_pow_of_le_one hx0 hx1.le (strictMono_add_le hE N k))
      (pow_nonneg hx0 _) hW
  have hs : Summable fun k => w (k + N) * x ^ E (k + N) :=
    Summable.of_norm_bounded hgeom (fun k => by simpa [Real.norm_eq_abs] using hbound k)
  calc |∑' k, w (k + N) * x ^ E (k + N)|
      ≤ ∑' k, |w (k + N) * x ^ E (k + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun k => w (k + N) * x ^ E (k + N))
          (by simpa only [Real.norm_eq_abs] using hs.abs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k, W * x ^ E N * x ^ k := Summable.tsum_le_tsum hbound hs.abs hgeom
    _ = W * x ^ E N / (1 - x) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
        ring


theorem strictMono_le_self {E : ℕ → ℕ} (hE : StrictMono E) (k : ℕ) : k ≤ E k :=
  hE.id_le k

theorem summable_series {E : ℕ → ℕ} (hE : StrictMono E) {w : ℕ → ℝ} {W : ℝ}
    (hw : ∀ k, |w k| ≤ W) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun k => w k * x ^ E k := by
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (hw 0)
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hx0 hx1).mul_left W) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
  exact mul_le_mul (hw k) (pow_le_pow_of_le_one hx0 hx1.le (strictMono_le_self hE k))
    (pow_nonneg hx0 _) hW

/-- **Value Taylor model of a sparse series.** -/
theorem seriesTM_approx {B : Box} {S : Env → Prop} (side : Bool) {E : ℕ → ℕ} (hE : StrictMono E)
    {w : ℕ → ℚ} {W : ℚ} (hw : ∀ k, |w k| ≤ W) (c0 : ℚ) (N : ℕ) {X : ℚ} (hX1 : X < 1)
    (hside : ∀ e, B.Mem e → 0 ≤ e.nome side ∧ e.nome side ≤ X) :
    (⟨seriesPoly side c0 w E N, W * X ^ E N / (1 - X)⟩ : TM).Approx B S
      (fun e => c0 + ∑' k, (w k : ℝ) * e.nome side ^ E k) := by
  intro e he _
  obtain ⟨hx0, hxX⟩ := hside e he
  have hX1' : (X : ℝ) < 1 := by exact_mod_cast hX1
  have hx1 : e.nome side < 1 := lt_of_le_of_lt hxX hX1'
  have hw' : ∀ k, |(w k : ℝ)| ≤ W := fun k => by exact_mod_cast hw k
  have hs := summable_series hE hw' hx0 hx1
  simp only
  rw [seriesPoly_eval, ← hs.sum_add_tsum_nat_add N]
  have htail := abs_tail_le hE hw' hx0 hx1 N
  have hW : (0 : ℝ) ≤ W := le_trans (abs_nonneg _) (hw' 0)
  calc |(c0 : ℝ) + (∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k +
          ∑' k, (w (k + N) : ℝ) * e.nome side ^ E (k + N)) -
        (c0 + ∑ k ∈ Finset.range N, (w k : ℝ) * e.nome side ^ E k)|
      = |∑' k, (w (k + N) : ℝ) * e.nome side ^ E (k + N)| := by congr 1; ring
    _ ≤ W * e.nome side ^ E N / (1 - e.nome side) := htail
    _ ≤ W * (X : ℝ) ^ E N / (1 - X) := by
        have h1 : 0 < 1 - (X : ℝ) := by linarith
        have h2 : 0 < 1 - e.nome side := by linarith
        rw [div_le_div_iff₀ h2 h1]
        have hp : e.nome side ^ E N ≤ (X : ℝ) ^ E N := pow_le_pow_left₀ hx0 hxX _
        have hX0 : (0 : ℝ) ≤ X := le_trans hx0 hxX
        have k1 : W * e.nome side ^ E N * (1 - X) ≤ W * (X : ℝ) ^ E N * (1 - X) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hW) h1.le
        have k2 : W * (X : ℝ) ^ E N * (1 - X) ≤ W * (X : ℝ) ^ E N * (1 - e.nome side) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW (pow_nonneg hX0 _))
        linarith
    _ = _ := by push_cast; ring


/-! ## Divided differences of sparse series -/

/-- `Σ_{i<n} aⁱ b^{n−1−i}` as a polynomial. -/
def hPoly (n : ℕ) : Poly := (List.range n).map fun i => (⟨i, n - 1 - i, 0, 0, 0, 0⟩, (1 : ℚ))

theorem hPoly_eval (n : ℕ) (e : Env) :
    Poly.eval (hPoly n) e = ∑ i ∈ Finset.range n, e.a ^ i * e.b ^ (n - 1 - i) := by
  unfold hPoly
  generalize hm : n - 1 = m
  clear hm
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Poly.eval_append, ih, Finset.sum_range_succ]
    simp [Mono.eval]

theorem hsum_mul_sub (n : ℕ) (a b : ℝ) :
    (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (b - a) = b ^ n - a ^ n := by
  have h := geom_sum₂_mul a b n
  linear_combination -h

theorem abs_hsum_le (n : ℕ) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)| ≤ n * M ^ (n - 1) := by
  have hM : 0 ≤ M := le_trans ha haM
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  calc ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
      ≤ ∑ i ∈ Finset.range n, M ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
        calc a ^ i * b ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) :=
              mul_le_mul (pow_le_pow_left₀ ha haM i) (pow_le_pow_left₀ hb hbM _)
                (pow_nonneg hb _) (pow_nonneg hM _)
          _ = M ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    _ = n * M ^ (n - 1) := by simp

theorem succ_mul_pow_le {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) * M ^ n ≤ n * M ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  have hk : (0 : ℝ) ≤ M ^ k := pow_nonneg hM0 k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : ((k : ℝ) + 1 + 1) * M ≤ (k : ℝ) + 1 := by nlinarith
  push_cast
  calc ((k : ℝ) + 1 + 1) * (M ^ k * M) = M ^ k * (((k : ℝ) + 1 + 1) * M) := by ring
    _ ≤ M ^ k * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 hk
    _ = ((k : ℝ) + 1) * M ^ k := by ring

theorem mul_pow_antitone {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 1 / 2) {n n' : ℕ} (hn : 1 ≤ n)
    (hnn : n ≤ n') : (n' : ℝ) * M ^ (n' - 1) ≤ n * M ^ (n - 1) := by
  induction n' with
  | zero => omega
  | succ n' ih =>
    rcases Nat.eq_or_lt_of_le hnn with h | h
    · rw [h]
    · have h' : n ≤ n' := by omega
      have := succ_mul_pow_le hM0 hM (le_trans hn h')
      simp only [Nat.add_sub_cancel] at this ⊢
      exact le_trans this (ih h')

theorem tsum_succ_mul_geometric {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    ∑' k : ℕ, ((k : ℝ) + 1) * M ^ k = 1 / (1 - M) ^ 2 := by
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one (r := M) (by rw [Real.norm_eq_abs, abs_of_nonneg hM0]; exact hM1)
  have h2 := tsum_geometric_of_lt_one hM0 hM1
  have hs1 : Summable fun k : ℕ => (k : ℝ) * M ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hM0]; exact hM1) |>.congr fun k => by simp
  have hs2 := summable_geometric_of_lt_one hM0 hM1
  have hsplit : ∑' k : ℕ, ((k : ℝ) + 1) * M ^ k = ∑' k : ℕ, (k : ℝ) * M ^ k + ∑' k : ℕ, M ^ k := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun k => by ring
  rw [hsplit, h1, h2]
  have : (1 - M) ≠ 0 := by linarith
  field_simp
  ring


/-- `Σ_{k<N} wₖ h_{E k}(a, b)`. -/
def seriesDDPoly (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) : Poly :=
  ((List.range N).map fun k => Poly.scale (w k) (hPoly (E k))).flatten

theorem seriesDDPoly_eval (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) (e : Env) :
    Poly.eval (seriesDDPoly w E N) e =
      ∑ k ∈ Finset.range N, (w k : ℝ) *
        ∑ i ∈ Finset.range (E k), e.a ^ i * e.b ^ (E k - 1 - i) := by
  unfold seriesDDPoly
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, Poly.eval_append, ih,
      Finset.sum_range_succ]
    simp [Poly.eval_scale, hPoly_eval]

/-- **Divided-difference Taylor model of a sparse series**, off the diagonal `a = b`. -/
theorem seriesDD_approx {B : Box} {S : Env → Prop} {E : ℕ → ℕ} (hE : StrictMono E)
    (hE0 : 1 ≤ E 0) {w : ℕ → ℚ} {W : ℚ} (hw : ∀ k, |w k| ≤ W) (c0 : ℚ) (N : ℕ) {M : ℚ}
    (hM : M ≤ 1 / 2) (hab : ∀ e, B.Mem e → 0 ≤ e.a ∧ e.a ≤ M ∧ 0 ≤ e.b ∧ e.b ≤ M) :
    (⟨seriesDDPoly w E N, W * E N * M ^ (E N - 1) / (1 - M) ^ 2⟩ : TM).Approx B
      (fun e => S e ∧ e.a ≠ e.b)
      (fun e => ((c0 + ∑' k, (w k : ℝ) * e.b ^ E k) - (c0 + ∑' k, (w k : ℝ) * e.a ^ E k)) /
        (e.b - e.a)) := by
  intro e he hs
  obtain ⟨ha0, haM, hb0, hbM⟩ := hab e he
  have hM' : (M : ℝ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := le_trans ha0 haM
  have hM1 : (M : ℝ) < 1 := by linarith
  have ha1 : e.a < 1 := by linarith
  have hb1 : e.b < 1 := by linarith
  have hw' : ∀ k, |(w k : ℝ)| ≤ W := fun k => by exact_mod_cast hw k
  have hW : (0 : ℝ) ≤ W := le_trans (abs_nonneg _) (hw' 0)
  have hba : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  set h : ℕ → ℝ := fun k => (w k : ℝ) * ∑ i ∈ Finset.range (E k), e.a ^ i * e.b ^ (E k - 1 - i)
    with hh
  -- termwise bound
  have hterm : ∀ k, |h k| ≤ W * ((E k : ℝ) * M ^ (E k - 1)) := fun k => by
    rw [hh, abs_mul]
    exact mul_le_mul (hw' k) (abs_hsum_le _ ha0 hb0 haM hbM) (abs_nonneg _) hW
  have hEk : ∀ k, 1 ≤ E k := fun k => le_trans hE0 (hE.monotone (Nat.zero_le k))
  -- summability of the majorant `(E N + k) M^{E N + k − 1}` dominated by `(k+1) M^k`
  have hmaj : ∀ k, W * ((E (k + N) : ℝ) * M ^ (E (k + N) - 1)) ≤
      W * ((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * M ^ k) := fun k => by
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
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (le_trans h1 h2) hW) (by ring)
  have hgeo : Summable fun k : ℕ => W * ((E N : ℝ) * M ^ (E N - 1)) * (((k : ℝ) + 1) * M ^ k) := by
    refine Summable.mul_left _ ?_
    have hs1 : Summable fun k : ℕ => (k : ℝ) * M ^ k :=
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hM0]; exact hM1)).congr fun k => by simp
    exact (hs1.add (summable_geometric_of_lt_one hM0 hM1)).congr fun k => by ring
  -- summability of `h`
  have hsum_h : Summable h := by
    have hshift : Summable fun k => h (k + N) :=
      Summable.of_norm_bounded hgeo fun k => by
        rw [Real.norm_eq_abs]; exact le_trans (hterm _) (hmaj k)
    exact (summable_nat_add_iff N).mp hshift
  -- the divided difference is `Σ h`
  have hfa := summable_series hE hw' ha0 ha1
  have hfb := summable_series hE hw' hb0 hb1
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
  have htail : |∑' k, h (k + N)| ≤ W * ((E N : ℝ) * M ^ (E N - 1)) * (1 / (1 - M) ^ 2) := by
    rw [← tsum_succ_mul_geometric hM0 hM1, ← tsum_mul_left]
    calc |∑' k, h (k + N)| ≤ ∑' k, |h (k + N)| := by
          have := norm_tsum_le_tsum_norm (f := fun k => h (k + N)) (by
            simpa only [Real.norm_eq_abs] using ((summable_nat_add_iff N).mpr hsum_h).abs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ _ := Summable.tsum_le_tsum (fun k => le_trans (hterm _) (hmaj k))
          ((summable_nat_add_iff N).mpr hsum_h).abs hgeo
  calc |∑ k ∈ Finset.range N, h k + ∑' k, h (k + N) - ∑ k ∈ Finset.range N, h k|
      = |∑' k, h (k + N)| := by congr 1; ring
    _ ≤ W * ((E N : ℝ) * M ^ (E N - 1)) * (1 / (1 - M) ^ 2) := htail
    _ = _ := by push_cast; ring

end E8Leech.Taylor
