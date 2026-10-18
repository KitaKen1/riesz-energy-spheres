import E8Leech.KronMajorant
import E8Leech.TaylorModelFun

/-!
# Inverse and logarithm for Taylor models with majorants

For a model `T` of `g` whose majorant of `|g|` is at most `1/2` on the bounds:

* `MTM.inv1p`: `1/(1 + g) = Σ_{k<K} (−g)ᵏ` up to `2 Gᴷ`;
* `MTM.log1p`: `Λ log (1 + g) = Σ_{1 ≤ k ≤ n} (−1)^{k+1} (Λ/k) gᵏ` up to `2 Λ G^{n+1}`;
* `MTM.logRatio`: `Λ log (1 + z)/z = Σ_{k<n} (−1)ᵏ (Λ/(k+1)) zᵏ` up to `2 Λ Gⁿ`.

Here `G` is a polynomial majorant of `|g|` in the nomes, so the remainders are again polynomials
in the nomes. The factor `Λ` (divisible by `1, …, n`) keeps all coefficients integers.
The real-analysis estimates are those of `TaylorModelFun`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

/-! ## Horner evaluation with integer coefficients -/

/-- `c₀ + y (c₁ + y (c₂ + …))`. -/
noncomputable def hornerZ : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, y => c + y * hornerZ cs y

theorem hornerZ_range (f : ℕ → ℤ) (K : ℕ) (y : ℝ) :
    hornerZ ((List.range K).map f) y = ∑ k ∈ Finset.range K, (f k : ℝ) * y ^ k := by
  induction K generalizing f with
  | zero => simp [hornerZ]
  | succ K ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerZ, Finset.sum_range_succ']
    have := ih (f ∘ Nat.succ)
    simp only [Function.comp] at this ⊢
    rw [this, Finset.mul_sum]
    simp only [pow_succ, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- `Gᵐ/(1 − G) ≤ 2 Gᵐ` for `0 ≤ G ≤ 1/2`. -/
theorem pow_div_one_sub_le {G : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ 1 / 2) (m : ℕ) :
    G ^ m / (1 - G) ≤ 2 * G ^ m := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (pow_nonneg hG0 m) (by linarith : (0 : ℝ) ≤ 1 / 2 - G)]

/-- `|y|ᵐ/(1 − |y|) ≤ 2 Gᵐ` for `|y| ≤ G ≤ 1/2`. -/
theorem abs_pow_div_one_sub_le {y G : ℝ} (hy : |y| ≤ G) (hG : G ≤ 1 / 2) (m : ℕ) :
    |y| ^ m / (1 - |y|) ≤ 2 * G ^ m := by
  have h1 := pow_div_one_sub_le (abs_nonneg y) (hy.trans hG) m
  have h2 : |y| ^ m ≤ G ^ m := pow_le_pow_left₀ (abs_nonneg y) hy m
  linarith

/-! ## Upper bounds of a polynomial on the bounds -/

namespace IPoly

/-- An upper bound of one term on the bounds. -/
def termUB (B : Bounds) (x : NMono × ℤ) : ℚ :=
  (x.2.natAbs : ℚ) * (((B.an : ℚ) / B.ad) ^ x.1.ea * ((B.bn : ℚ) / B.bd) ^ x.1.eb *
    ((B.un : ℚ) / B.ud) ^ x.1.eu * ((B.tn : ℚ) / B.td) ^ x.1.et * ((B.ln : ℚ) / B.ld) ^ x.1.el)

/-- An upper bound of a polynomial on the bounds. -/
def evalUB (B : Bounds) (G : IPoly) : ℚ := (G.map (termUB B)).sum

theorem pow_le_div_pow {v : ℝ} {n d : ℕ} (hv : 0 ≤ v) (hd : 0 < d) (h : v * d ≤ n) (k : ℕ) :
    v ^ k ≤ ((n : ℝ) / d) ^ k :=
  pow_le_pow_left₀ hv ((le_div_iff₀ (by exact_mod_cast hd)).mpr h) k

theorem term_le_termUB {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (x : NMono × ℤ) :
    (x.2 : ℝ) * x.1.eval e ≤ (termUB B x : ℝ) := by
  obtain ⟨ha, ha', hb, hb', hu, hu', ht, ht', hl, hl'⟩ := he
  obtain ⟨da, db, du, dt, dl⟩ := hB
  have h1 := pow_le_div_pow ha da ha' x.1.ea
  have h2 := pow_le_div_pow hb db hb' x.1.eb
  have h3 := pow_le_div_pow hu du hu' x.1.eu
  have h4 := pow_le_div_pow ht dt ht' x.1.et
  have h5 := pow_le_div_pow hl dl hl' x.1.el
  have p1 := pow_nonneg ha x.1.ea
  have p2 := pow_nonneg hb x.1.eb
  have p3 := pow_nonneg hu x.1.eu
  have p4 := pow_nonneg ht x.1.et
  have p5 := pow_nonneg hl x.1.el
  have q1 := p1.trans h1
  have q2 := p2.trans h2
  have q3 := p3.trans h3
  have q4 := p4.trans h4
  have hM : x.1.eval e ≤ ((B.an : ℝ) / B.ad) ^ x.1.ea * ((B.bn : ℝ) / B.bd) ^ x.1.eb *
      ((B.un : ℝ) / B.ud) ^ x.1.eu * ((B.tn : ℝ) / B.td) ^ x.1.et *
        ((B.ln : ℝ) / B.ld) ^ x.1.el := by
    simp only [NMono.eval]
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2))
      h4 p4 (mul_nonneg (mul_nonneg q1 q2) q3)) h5 p5
      (mul_nonneg (mul_nonneg (mul_nonneg q1 q2) q3) q4)
  have hM0 : 0 ≤ x.1.eval e := by
    simp only [NMono.eval]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p1 p2) p3) p4) p5
  simp only [termUB]
  push_cast
  rw [natAbs_cast_abs]
  calc (x.2 : ℝ) * x.1.eval e ≤ |(x.2 : ℝ)| * x.1.eval e :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hM0
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (abs_nonneg _)

theorem eval_le_evalUB {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (G : IPoly) :
    eval G e ≤ (evalUB B G : ℝ) := by
  induction G with
  | nil => simp [evalUB]
  | cons x G ih =>
    simp only [evalUB, List.map_cons, List.sum_cons, eval_cons] at ih ⊢
    rw [Rat.cast_add]
    exact add_le_add (term_le_termUB hB he x) ih

/-- A capped power of a majorant. -/
def powMaj (B : Bounds) (Dcap : ℕ) (G : IPoly) : ℕ → IPoly
  | 0 => unit
  | k + 1 => cap B Dcap (mulK G (powMaj B Dcap G k))

theorem pow_le_powMaj {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (Dcap : ℕ)
    (G : IPoly) (hG : 0 ≤ eval G e) : ∀ k, eval G e ^ k ≤ eval (powMaj B Dcap G k) e
  | 0 => by simp [powMaj, eval_unit]
  | k + 1 => by
    have ih := pow_le_powMaj hB he Dcap G hG k
    have hc := eval_le_cap hB he Dcap (mulK G (powMaj B Dcap G k))
    rw [eval_mulK] at hc
    calc eval G e ^ (k + 1) = eval G e * eval G e ^ k := by ring
      _ ≤ eval G e * eval (powMaj B Dcap G k) e := mul_le_mul_of_nonneg_left ih hG
      _ ≤ eval (powMaj B Dcap G (k + 1)) e := hc

end IPoly

/-! ## Functions of a model -/

namespace MTM

open IPoly

variable {B : Bounds} {S : NEnv → Prop}

/-- Horner evaluation of a polynomial with integer coefficients at a model. -/
def horner (B : Bounds) (D Dcap : ℕ) (T : MTM) : List ℤ → MTM
  | [] => zero
  | c :: cs => (const c).add (mul B D Dcap T (horner B D Dcap T cs))

theorem approx_horner (hB : B.Valid) (D Dcap : ℕ) {T : MTM} {g : NEnv → ℝ}
    (h : T.Approx B S g) :
    ∀ cs : List ℤ, (horner B D Dcap T cs).Approx B S (fun e => hornerZ cs (g e))
  | [] => approx_zero
  | c :: cs => approx_add (approx_const c) (approx_mul hB D Dcap h (approx_horner hB D Dcap h cs))

/-- A polynomial majorant of `|g|` in the nomes. -/
def absMaj (B : Bounds) (T : MTM) : IPoly := maj B T.P ++ T.R

theorem abs_le_absMaj (hB : B.Valid) {T : MTM} {g : NEnv → ℝ} (h : T.Approx B S g) {e : NEnv}
    (he : B.Mem e) (hs : S e) : |g e| ≤ (absMaj B T).eval e := by
  have h1 := h e he hs
  have h2 := abs_eval_le_maj hB he T.P
  have h3 := abs_sub_le (g e) (T.P.eval e) 0
  rw [sub_zero, sub_zero] at h3
  rw [absMaj, eval_append]
  linarith

/-- The majorant of `|g|` is at most `1/2` on the bounds. -/
def HalfOK (B : Bounds) (T : MTM) : Prop := evalUB B (absMaj B T) ≤ 1 / 2

instance (B : Bounds) (T : MTM) : Decidable (HalfOK B T) := by
  unfold HalfOK
  infer_instance

theorem absMaj_le_half (hB : B.Valid) {T : MTM} (hG : HalfOK B T) {e : NEnv} (he : B.Mem e) :
    (absMaj B T).eval e ≤ 1 / 2 := by
  have h1 := eval_le_evalUB hB he (absMaj B T)
  have hG' : evalUB B (absMaj B T) ≤ 1 / 2 := hG
  have h2 : ((evalUB B (absMaj B T) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hG'
  have h3 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  linarith

/-- Coefficients `1, −1, 1, …` of `1/(1 + y)`. -/
def invCoeffs (K : ℕ) : List ℤ := (List.range K).map fun k => (-1 : ℤ) ^ k

/-- `1/(1 + g)`. -/
def inv1p (B : Bounds) (D Dcap K : ℕ) (T : MTM) : MTM :=
  ⟨(horner B D Dcap T (invCoeffs K)).P,
    IPoly.add (horner B D Dcap T (invCoeffs K)).R
      (IPoly.scale 2 (powMaj B Dcap (absMaj B T) K))⟩

theorem approx_inv1p (hB : B.Valid) (D Dcap K : ℕ) {T : MTM} {g : NEnv → ℝ}
    (h : T.Approx B S g) (hG : HalfOK B T) :
    (inv1p B D Dcap K T).Approx B S (fun e => 1 / (1 + g e)) := by
  intro e he hs
  have hH := approx_horner hB D Dcap h (invCoeffs K) e he hs
  have hy := abs_le_absMaj hB h he hs
  have hG0 : 0 ≤ (absMaj B T).eval e := (abs_nonneg _).trans hy
  have hGh := absMaj_le_half hB hG he
  have hser := TM.abs_inv_one_add_sub_le hy (by linarith) K
  have hsum : hornerZ (invCoeffs K) (g e) =
      ∑ k ∈ Finset.range K, (((-1 : ℚ) ^ k : ℚ) : ℝ) * g e ^ k := by
    rw [invCoeffs, hornerZ_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [← hsum] at hser
  have htri := abs_sub_le (1 / (1 + g e)) (hornerZ (invCoeffs K) (g e))
    ((horner B D Dcap T (invCoeffs K)).P.eval e)
  have hrem := pow_div_one_sub_le hG0 hGh K
  have hpow := pow_le_powMaj hB he Dcap (absMaj B T) hG0 K
  simp only [inv1p, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

/-- Integer coefficients `0, Λ, −Λ/2, Λ/3, …` of `Λ log (1 + y)`. -/
def logCoeffZ (Λ k : ℕ) : ℤ := if k = 0 then 0 else (-1) ^ (k - 1) * ((Λ : ℤ) / (k : ℤ))

theorem cast_logCoeffZ_succ {Λ i : ℕ} (hd : (i + 1) ∣ Λ) :
    (logCoeffZ Λ (i + 1) : ℝ) = (-1 : ℝ) ^ i * ((Λ : ℝ) / ((i : ℝ) + 1)) := by
  have hd' : ((i + 1 : ℕ) : ℤ) ∣ (Λ : ℤ) := by exact_mod_cast hd
  unfold logCoeffZ
  rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, Int.cast_mul,
    Int.cast_div hd' (by exact_mod_cast Nat.succ_ne_zero i)]
  push_cast
  ring

theorem sum_logCoeffZ {Λ n : ℕ} (hΛ : ∀ i, i < n → (i + 1) ∣ Λ) (y : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (logCoeffZ Λ k : ℝ) * y ^ k =
      (Λ : ℝ) * ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (logCoeffZ Λ 0 : ℝ) * y ^ 0 = 0 := by simp [logCoeffZ]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cast_logCoeffZ_succ (hΛ i (Finset.mem_range.mp hi))]
  ring

/-- Coefficients of `Λ log (1 + y)` up to order `n`. -/
def logCoeffs (Λ n : ℕ) : List ℤ := (List.range (n + 1)).map (logCoeffZ Λ)

/-- `Λ log (1 + g)`. -/
def log1p (B : Bounds) (D Dcap Λ n : ℕ) (T : MTM) : MTM :=
  ⟨(horner B D Dcap T (logCoeffs Λ n)).P,
    IPoly.add (horner B D Dcap T (logCoeffs Λ n)).R
      (IPoly.scale ((2 * Λ : ℕ) : ℤ) (powMaj B Dcap (absMaj B T) (n + 1)))⟩

theorem approx_log1p (hB : B.Valid) (D Dcap : ℕ) {Λ n : ℕ} (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    {T : MTM} {g : NEnv → ℝ} (h : T.Approx B S g) (hG : HalfOK B T) :
    (log1p B D Dcap Λ n T).Approx B S (fun e => (Λ : ℝ) * Real.log (1 + g e)) := by
  intro e he hs
  have hH := approx_horner hB D Dcap h (logCoeffs Λ n) e he hs
  have hy := abs_le_absMaj hB h he hs
  have hG0 : 0 ≤ (absMaj B T).eval e := (abs_nonneg _).trans hy
  have hGh := absMaj_le_half hB hG he
  have hy1 : |g e| < 1 := by linarith
  have hser := TM.abs_log_one_add_sub_le hy1 n
  have hrem := abs_pow_div_one_sub_le hy hGh (n + 1)
  have hsum : hornerZ (logCoeffs Λ n) (g e) =
      (Λ : ℝ) * ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * g e ^ (i + 1) / (i + 1) := by
    rw [logCoeffs, hornerZ_range, sum_logCoeffZ hΛ]
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg Λ
  have hscaled : |(Λ : ℝ) * Real.log (1 + g e) - hornerZ (logCoeffs Λ n) (g e)| ≤
      (Λ : ℝ) * (2 * (absMaj B T).eval e ^ (n + 1)) := by
    rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    exact mul_le_mul_of_nonneg_left (hser.trans hrem) hΛ0
  have htri := abs_sub_le ((Λ : ℝ) * Real.log (1 + g e)) (hornerZ (logCoeffs Λ n) (g e))
    ((horner B D Dcap T (logCoeffs Λ n)).P.eval e)
  have hpow := pow_le_powMaj hB he Dcap (absMaj B T) hG0 (n + 1)
  have hpow' : (Λ : ℝ) * (2 * (absMaj B T).eval e ^ (n + 1)) ≤
      (Λ : ℝ) * (2 * (powMaj B Dcap (absMaj B T) (n + 1)).eval e) :=
    mul_le_mul_of_nonneg_left (by linarith) hΛ0
  simp only [log1p, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

/-- Integer coefficients `Λ, −Λ/2, Λ/3, …` of `Λ log (1 + z)/z`. -/
def logRatioCoeffZ (Λ k : ℕ) : ℤ := (-1) ^ k * ((Λ : ℤ) / ((k + 1 : ℕ) : ℤ))

theorem cast_logRatioCoeffZ {Λ k : ℕ} (hd : (k + 1) ∣ Λ) :
    (logRatioCoeffZ Λ k : ℝ) = (Λ : ℝ) * (TM.logRatioCoeff k : ℝ) := by
  have hd' : ((k + 1 : ℕ) : ℤ) ∣ (Λ : ℤ) := by exact_mod_cast hd
  unfold logRatioCoeffZ TM.logRatioCoeff
  rw [Int.cast_mul, Int.cast_div hd' (by exact_mod_cast Nat.succ_ne_zero k)]
  push_cast
  ring

/-- Coefficients of `Λ log (1 + z)/z` up to order `n − 1`. -/
def logRatioCoeffs (Λ n : ℕ) : List ℤ := (List.range n).map (logRatioCoeffZ Λ)

/-- `Λ log (1 + z)/z`. -/
def logRatio (B : Bounds) (D Dcap Λ n : ℕ) (T : MTM) : MTM :=
  ⟨(horner B D Dcap T (logRatioCoeffs Λ n)).P,
    IPoly.add (horner B D Dcap T (logRatioCoeffs Λ n)).R
      (IPoly.scale ((2 * Λ : ℕ) : ℤ) (powMaj B Dcap (absMaj B T) n))⟩

theorem approx_logRatio (hB : B.Valid) (D Dcap : ℕ) {Λ n : ℕ} (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    {T : MTM} {g : NEnv → ℝ} (h : T.Approx B S g) (hG : HalfOK B T) :
    (logRatio B D Dcap Λ n T).Approx B S (fun e => (Λ : ℝ) * TM.logRatio (g e)) := by
  intro e he hs
  have hH := approx_horner hB D Dcap h (logRatioCoeffs Λ n) e he hs
  have hy := abs_le_absMaj hB h he hs
  have hG0 : 0 ≤ (absMaj B T).eval e := (abs_nonneg _).trans hy
  have hGh := absMaj_le_half hB hG he
  have hy1 : |g e| < 1 := by linarith
  have hser := TM.abs_logRatio_sub_le hy1 n
  have hrem := abs_pow_div_one_sub_le hy hGh n
  have hsum : hornerZ (logRatioCoeffs Λ n) (g e) =
      (Λ : ℝ) * ∑ k ∈ Finset.range n, (TM.logRatioCoeff k : ℝ) * g e ^ k := by
    rw [logRatioCoeffs, hornerZ_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [cast_logRatioCoeffZ (hΛ k (Finset.mem_range.mp hk))]
    ring
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg Λ
  have hscaled : |(Λ : ℝ) * TM.logRatio (g e) - hornerZ (logRatioCoeffs Λ n) (g e)| ≤
      (Λ : ℝ) * (2 * (absMaj B T).eval e ^ n) := by
    rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    exact mul_le_mul_of_nonneg_left (hser.trans hrem) hΛ0
  have htri := abs_sub_le ((Λ : ℝ) * TM.logRatio (g e)) (hornerZ (logRatioCoeffs Λ n) (g e))
    ((horner B D Dcap T (logRatioCoeffs Λ n)).P.eval e)
  have hpow := pow_le_powMaj hB he Dcap (absMaj B T) hG0 n
  have hpow' : (Λ : ℝ) * (2 * (absMaj B T).eval e ^ n) ≤
      (Λ : ℝ) * (2 * (powMaj B Dcap (absMaj B T) n).eval e) :=
    mul_le_mul_of_nonneg_left (by linarith) hΛ0
  simp only [logRatio, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

end MTM

end E8Leech.Kron
