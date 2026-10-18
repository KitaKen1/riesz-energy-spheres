import E8Leech.TaylorModelOps
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Taylor models of `1/(1 + g)` and `log (1 + g)`

For a Taylor model `T` of a function `g` with `|g| ≤ G < 1` on the box:

* `TM.inv1p`: `1/(1 + g) = Σ_{k<K} (−g)ᵏ` up to `G^K/(1 − G)`;
* `TM.log1p`: `log (1 + g) = Σ_{1 ≤ k ≤ K} (−1)^{k+1} gᵏ/k` up to `G^{K+1}/(1 − G)`;
* `TM.logRatio`: `log (1 + z)/z = Σ_{k<K} (−z)ᵏ/(k + 1)` up to `G^K/(1 − G)` (value `1` at `z = 0`).

The polynomial parts are evaluated by Horner's rule with `TM.mul`.
-/

namespace E8Leech.Taylor

/-- `c₀ + y (c₁ + y (c₂ + …))`. -/
noncomputable def hornerVal : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, y => c + y * hornerVal cs y

theorem hornerVal_range (f : ℕ → ℚ) (K : ℕ) (y : ℝ) :
    hornerVal ((List.range K).map f) y = ∑ k ∈ Finset.range K, (f k : ℝ) * y ^ k := by
  induction K generalizing f with
  | zero => simp [hornerVal]
  | succ K ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerVal, Finset.sum_range_succ']
    have := ih (f ∘ Nat.succ)
    simp only [Function.comp] at this ⊢
    rw [this, Finset.mul_sum]
    simp only [pow_succ, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

namespace TM

/-- An upper bound of `|g|` on the box from a Taylor model of `g`. -/
def absBound (B : Box) (T : TM) : ℚ := Poly.bound B T.P + T.r

theorem abs_le_absBound {B : Box} (hB : B.Valid) {S : Env → Prop} {T : TM} {g : Env → ℝ}
    (h : T.Approx B S g) {e : Env} (he : B.Mem e) (hs : S e) : |g e| ≤ absBound B T := by
  have h1 := h e he hs
  have h2 := Poly.abs_eval_le hB he T.P
  unfold absBound
  push_cast
  calc |g e| = |(g e - Poly.eval T.P e) + Poly.eval T.P e| := by ring_nf
    _ ≤ |g e - Poly.eval T.P e| + |Poly.eval T.P e| := abs_add_le _ _
    _ ≤ T.r + Poly.bound B T.P := add_le_add h1 h2
    _ = _ := by ring

/-- Horner evaluation of a polynomial with rational coefficients at a Taylor model. -/
def horner (B : Box) (D : ℕ) (T : TM) : List ℚ → TM
  | [] => zero
  | c :: cs => add (const c) (mul B D T (horner B D T cs))

theorem approx_horner {B : Box} (hB : B.Valid) (D : ℕ) {S : Env → Prop} {T : TM}
    {g : Env → ℝ} (h : T.Approx B S g) (cs : List ℚ) :
    (horner B D T cs).Approx B S (fun e => hornerVal cs (g e)) := by
  induction cs with
  | nil => exact approx_congr approx_zero fun e _ _ => by simp [hornerVal]
  | cons c cs ih =>
    exact approx_congr (approx_add (approx_const c) (approx_mul hB D h ih))
      fun e _ _ => by simp [hornerVal]

/-- Widen the radius by `ε`. -/
def widen (T : TM) (ε : ℚ) : TM := ⟨T.P, T.r + ε⟩

theorem approx_widen {B : Box} {S : Env → Prop} {T : TM} {g f : Env → ℝ} (h : T.Approx B S g)
    {ε : ℚ} (hε : ∀ e, B.Mem e → S e → |f e - g e| ≤ ε) : (widen T ε).Approx B S f := by
  intro e he hs
  have h1 := h e he hs
  have h2 := hε e he hs
  simp only [widen]
  push_cast
  calc |f e - Poly.eval T.P e| = |(f e - g e) + (g e - Poly.eval T.P e)| := by ring_nf
    _ ≤ |f e - g e| + |g e - Poly.eval T.P e| := abs_add_le _ _
    _ ≤ ε + T.r := add_le_add h2 h1
    _ = _ := by ring

/-- `1/(1 + g)`. -/
def inv1p (B : Box) (D K : ℕ) (T : TM) : TM :=
  let G := absBound B T
  widen (horner B D T ((List.range K).map fun k => (-1 : ℚ) ^ k)) (G ^ K / (1 - G))

theorem abs_inv_one_add_sub_le {y G : ℝ} (hy : |y| ≤ G) (hG : G < 1) (K : ℕ) :
    |1 / (1 + y) - ∑ k ∈ Finset.range K, ((-1 : ℚ) ^ k : ℚ) * y ^ k| ≤ G ^ K / (1 - G) := by
  have hy1 : |y| < 1 := lt_of_le_of_lt hy hG
  have h1y : 0 < 1 + y := by have := neg_abs_le y; linarith
  have hgeom : ∑ k ∈ Finset.range K, ((-1 : ℚ) ^ k : ℚ) * y ^ k =
      ∑ k ∈ Finset.range K, (-y) ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [neg_pow y k]
  rw [hgeom, geom_sum_eq (by intro h; have := congrArg abs h; simp at this; linarith) K]
  have hden : (-y) - 1 = -(1 + y) := by ring
  rw [hden]
  have : 1 / (1 + y) - ((-y) ^ K - 1) / -(1 + y) = (-y) ^ K / (1 + y) := by
    field_simp
    ring
  rw [this, abs_div, abs_of_pos h1y, abs_pow, abs_neg]
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) hy
  have h1 : 1 - G ≤ 1 + y := by have := neg_abs_le y; linarith
  have h2 : 0 < 1 - G := by linarith
  calc |y| ^ K / (1 + y) ≤ G ^ K / (1 + y) := by
        gcongr
    _ ≤ G ^ K / (1 - G) := div_le_div_of_nonneg_left (pow_nonneg hG0 K) h2 h1

theorem approx_inv1p {B : Box} (hB : B.Valid) (D K : ℕ) {S : Env → Prop} {T : TM}
    {g : Env → ℝ} (h : T.Approx B S g) (hG : absBound B T < 1) :
    (inv1p B D K T).Approx B S (fun e => 1 / (1 + g e)) := by
  refine approx_widen (approx_horner hB D h _) fun e he hs => ?_
  have hy := abs_le_absBound hB h he hs
  have hG' : ((absBound B T : ℚ) : ℝ) < 1 := by exact_mod_cast hG
  rw [hornerVal_range]
  have := abs_inv_one_add_sub_le hy hG' K
  push_cast at this ⊢
  exact this

/-- `log (1 + y) − Σ_{i<n} (−1)ⁱ y^{i+1}/(i+1)` is at most `|y|^{n+1}/(1 − |y|)`. -/
theorem abs_log_one_add_sub_le {y : ℝ} (hy : |y| < 1) (n : ℕ) :
    |Real.log (1 + y) - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1)| ≤
      |y| ^ (n + 1) / (1 - |y|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) (by rwa [abs_neg]) n
  rw [abs_neg, sub_neg_eq_add] at h
  have hsum : ∑ i ∈ Finset.range n, (-y) ^ (i + 1) / ((i : ℝ) + 1) =
      -∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow, pow_succ (-1 : ℝ)]
    ring
  rw [hsum] at h
  calc |Real.log (1 + y) - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1)|
      = |-∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1) + Real.log (1 + y)| := by
        congr 1; ring
    _ ≤ _ := h

/-- Coefficients `0, 1, −1/2, 1/3, …` of `log (1 + y)`. -/
def logCoeff (k : ℕ) : ℚ := if k = 0 then 0 else (-1 : ℚ) ^ (k - 1) / k

theorem sum_logCoeff (n : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (logCoeff k : ℝ) * y ^ k =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1) := by
  rw [Finset.sum_range_succ']
  have h0 : (logCoeff 0 : ℝ) * y ^ 0 = 0 := by simp [logCoeff]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : logCoeff (i + 1) = (-1 : ℚ) ^ i / ((i : ℚ) + 1) := by
    simp [logCoeff]
  rw [hc]
  push_cast
  ring

/-- `log (1 + g)`. -/
def log1p (B : Box) (D n : ℕ) (T : TM) : TM :=
  let G := absBound B T
  widen (horner B D T ((List.range (n + 1)).map logCoeff)) (G ^ (n + 1) / (1 - G))

theorem approx_log1p {B : Box} (hB : B.Valid) (D n : ℕ) {S : Env → Prop} {T : TM}
    {g : Env → ℝ} (h : T.Approx B S g) (hG : absBound B T < 1) :
    (log1p B D n T).Approx B S (fun e => Real.log (1 + g e)) := by
  refine approx_widen (approx_horner hB D h _) fun e he hs => ?_
  have hy := abs_le_absBound hB h he hs
  have hG' : ((absBound B T : ℚ) : ℝ) < 1 := by exact_mod_cast hG
  have hy1 : |g e| < 1 := lt_of_le_of_lt hy hG'
  rw [hornerVal_range, sum_logCoeff]
  have h1 := abs_log_one_add_sub_le hy1 n
  have hG0 : (0 : ℝ) ≤ absBound B T := le_trans (abs_nonneg _) hy
  have h2 : |g e| ^ (n + 1) / (1 - |g e|) ≤
      ((absBound B T : ℚ) : ℝ) ^ (n + 1) / (1 - (absBound B T : ℝ)) := by
    have hd : 0 < 1 - (absBound B T : ℝ) := by linarith
    have hd' : 1 - (absBound B T : ℝ) ≤ 1 - |g e| := by linarith
    calc |g e| ^ (n + 1) / (1 - |g e|) ≤ (absBound B T : ℝ) ^ (n + 1) / (1 - |g e|) := by
          gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hG0 _) hd hd'
  push_cast
  exact le_trans h1 h2

/-- `log (1 + z)/z`, continuously extended by `1` at `z = 0`. -/
noncomputable def logRatio (z : ℝ) : ℝ := if z = 0 then 1 else Real.log (1 + z) / z

/-- Coefficients `1, −1/2, 1/3, …` of `log (1 + z)/z`. -/
def logRatioCoeff (k : ℕ) : ℚ := (-1 : ℚ) ^ k / (k + 1)

theorem abs_logRatio_sub_le {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    |logRatio z - ∑ k ∈ Finset.range n, (logRatioCoeff k : ℝ) * z ^ k| ≤ |z| ^ n / (1 - |z|) := by
  by_cases h0 : z = 0
  · subst h0
    rcases n with _ | n
    · simp [logRatio]
    · rw [Finset.sum_range_succ']
      simp [logRatio, logRatioCoeff]
  · have h1 := abs_log_one_add_sub_le hz n
    have hz0 : 0 < |z| := abs_pos.mpr h0
    have hsum : ∑ k ∈ Finset.range n, (logRatioCoeff k : ℝ) * z ^ k =
        (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1)) / z := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [logRatioCoeff]
      push_cast
      field_simp
      ring
    rw [logRatio, if_neg h0, hsum, ← sub_div, abs_div]
    rw [div_le_div_iff₀ hz0 (by linarith)]
    have hne : 1 - |z| ≠ 0 := by linarith
    calc |Real.log (1 + z) - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1)| *
          (1 - |z|) ≤ |z| ^ (n + 1) / (1 - |z|) * (1 - |z|) := by
          gcongr
      _ = |z| ^ n * |z| := by
          rw [div_mul_cancel₀ _ hne, pow_succ]

/-- `log (1 + z)/z`. -/
def logRatioTM (B : Box) (D n : ℕ) (T : TM) : TM :=
  let G := absBound B T
  widen (horner B D T ((List.range n).map logRatioCoeff)) (G ^ n / (1 - G))

theorem approx_logRatio {B : Box} (hB : B.Valid) (D n : ℕ) {S : Env → Prop} {T : TM}
    {g : Env → ℝ} (h : T.Approx B S g) (hG : absBound B T < 1) :
    (logRatioTM B D n T).Approx B S (fun e => logRatio (g e)) := by
  refine approx_widen (approx_horner hB D h _) fun e he hs => ?_
  have hy := abs_le_absBound hB h he hs
  have hG' : ((absBound B T : ℚ) : ℝ) < 1 := by exact_mod_cast hG
  have hy1 : |g e| < 1 := lt_of_le_of_lt hy hG'
  rw [hornerVal_range]
  have h1 := abs_logRatio_sub_le hy1 n
  have hG0 : (0 : ℝ) ≤ absBound B T := le_trans (abs_nonneg _) hy
  have h2 : |g e| ^ n / (1 - |g e|) ≤ ((absBound B T : ℚ) : ℝ) ^ n / (1 - (absBound B T : ℝ)) := by
    have hd : 0 < 1 - (absBound B T : ℝ) := by linarith
    have hd' : 1 - (absBound B T : ℝ) ≤ 1 - |g e| := by linarith
    calc |g e| ^ n / (1 - |g e|) ≤ (absBound B T : ℝ) ^ n / (1 - |g e|) := by
          gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hG0 _) hd hd'
  push_cast
  exact le_trans h1 h2

end TM

end E8Leech.Taylor
