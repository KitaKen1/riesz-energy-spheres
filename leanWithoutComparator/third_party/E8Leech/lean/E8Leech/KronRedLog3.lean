import E8Leech.KronRedLog

/-!
# Higher reductions of the logarithm

`log (1 + z) = z − z²/2 + … ± zʲ/j + zʲ⁺¹ ℓ_j(z)`, where `ℓ_j(z) = Σ_k c_{k+j} zᵏ` is the series of
`ℓ = log (1 + z)/z` with its first `j` coefficients removed (`c_k = (−1)ᵏ/(k + 1)`). For
`f = 1 + x d(x)` this gives

`log f = x d − x² d²/2 + x³ d³ ℓ₂(x d)`,

so a numerator that vanishes to the third order at the cusp of the second variable can be written
as the cube of the nome times an expression in the functions `Λ ℓ₂(x d)`. Their models and the
models of their divided differences are those of `KronRedLog` with shifted coefficient lists.

* `logRatioSh`, `logRatio_eq_sum_add`, `log_one_add_cube`, `abs_logRatioSh_sub_le`: the series.
* `logRatioShDD`, `logRatioSh_sub`, `abs_logRatioShDD_sub_le`: its divided difference.
* `MTM.logRatioSh`, `MTM.logRatioShDD` and their soundness.
* `MDD.rlogSh`, `MDD.approx_rlogSh`: the model of `Λ ℓ_j(x d)` from a model of `d`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-! ## The series with shifted coefficients -/

/-- `ℓ_j(z) = Σ_k c_{k+j} zᵏ`. -/
noncomputable def logRatioSh (j : ℕ) (z : ℝ) : ℝ :=
  ∑' k : ℕ, (TM.logRatioCoeff (k + j) : ℝ) * z ^ k

theorem abs_logRatioSh_term_le (j : ℕ) (z : ℝ) (k : ℕ) :
    |(TM.logRatioCoeff (k + j) : ℝ) * z ^ k| ≤ |z| ^ k := by
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg z) k) (abs_logRatioCoeff_le _)

theorem hasSum_logRatioSh (j : ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun k : ℕ => (TM.logRatioCoeff (k + j) : ℝ) * z ^ k) (logRatioSh j z) := by
  have hsum : Summable fun k : ℕ => (TM.logRatioCoeff (k + j) : ℝ) * z ^ k :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg z) hz) fun k => by
      rw [Real.norm_eq_abs]
      exact abs_logRatioSh_term_le j z k
  exact hsum.hasSum

/-- `ℓ(z) = Σ_{k<j} c_k zᵏ + zʲ ℓ_j(z)`. -/
theorem logRatio_eq_sum_add (j : ℕ) {z : ℝ} (hz : |z| < 1) :
    TM.logRatio z =
      (∑ k ∈ Finset.range j, (TM.logRatioCoeff k : ℝ) * z ^ k) + z ^ j * logRatioSh j z := by
  have h1 := (hasSum_nat_add_iff' j).mpr (hasSum_logRatio hz)
  have h2 := (hasSum_logRatioSh j hz).mul_left (z ^ j)
  have e : (fun k : ℕ => z ^ j * ((TM.logRatioCoeff (k + j) : ℝ) * z ^ k)) =
      fun k => (TM.logRatioCoeff (k + j) : ℝ) * z ^ (k + j) := by
    funext k
    rw [pow_add]
    ring
  rw [e] at h2
  have h3 := h1.unique h2
  linarith

/-- **The logarithm to the third order**: `log (1 + z) = z − z²/2 + z³ ℓ₂(z)`. -/
theorem log_one_add_cube {z : ℝ} (hz : |z| < 1) :
    Real.log (1 + z) = z - z ^ 2 / 2 + z ^ 3 * logRatioSh 2 z := by
  have h := logRatio_eq_sum_add 2 hz
  have hc : ∑ k ∈ Finset.range 2, (TM.logRatioCoeff k : ℝ) * z ^ k = 1 - z / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [TM.logRatioCoeff]
    ring
  rw [hc] at h
  by_cases h0 : z = 0
  · subst h0
    simp
  · have hl : TM.logRatio z = Real.log (1 + z) / z := by rw [TM.logRatio, if_neg h0]
    rw [hl, div_eq_iff h0] at h
    rw [h]
    ring

theorem abs_logRatioSh_sub_le (j : ℕ) {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    |logRatioSh j z - ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + j) : ℝ) * z ^ k| ≤
      |z| ^ n / (1 - |z|) := by
  refine abs_hasSum_sub_le (hasSum_logRatioSh j hz) (abs_nonneg z) hz n fun k => ?_
  have h := abs_logRatioSh_term_le j z (k + n)
  have e : |z| ^ (k + n) = |z| ^ n * |z| ^ k := by rw [pow_add, mul_comm]
  rw [e] at h
  exact h

/-! ## The divided difference -/

/-- The divided difference of `ℓ_j`, as a series. -/
noncomputable def logRatioShDD (j : ℕ) (p q : ℝ) : ℝ :=
  ∑' k : ℕ, (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q

theorem abs_logRatioShDD_term_le (j : ℕ) (p q : ℝ) (k : ℕ) :
    |(TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q| ≤ (|p| + |q|) ^ k := by
  rw [abs_mul]
  calc |(TM.logRatioCoeff (k + 1 + j) : ℝ)| * |hsum (k + 1) p q| ≤ 1 * (|p| + |q|) ^ k :=
        mul_le_mul (abs_logRatioCoeff_le _) (abs_hsum_succ_le k p q) (abs_nonneg _) zero_le_one
    _ = (|p| + |q|) ^ k := one_mul _

theorem hasSum_logRatioShDD (j : ℕ) {p q : ℝ} (hs : |p| + |q| < 1) :
    HasSum (fun k : ℕ => (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q)
      (logRatioShDD j p q) := by
  have hs0 : 0 ≤ |p| + |q| := add_nonneg (abs_nonneg p) (abs_nonneg q)
  have hsum : Summable fun k : ℕ => (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hs0 hs) fun k => by
      rw [Real.norm_eq_abs]
      exact abs_logRatioShDD_term_le j p q k
  exact hsum.hasSum

/-- **The difference of `ℓ_j` at two arguments.** -/
theorem logRatioSh_sub (j : ℕ) {p q : ℝ} (hs : |p| + |q| < 1) :
    logRatioSh j q - logRatioSh j p = (q - p) * logRatioShDD j p q := by
  have hp : |p| < 1 := by linarith [abs_nonneg q]
  have hq : |q| < 1 := by linarith [abs_nonneg p]
  have hd := (hasSum_logRatioSh j hq).sub (hasSum_logRatioSh j hp)
  have h1 := (hasSum_nat_add_iff' 1).mpr hd
  have hfun : (fun k : ℕ => (q - p) *
      ((TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q)) =
      fun k => (TM.logRatioCoeff (k + 1 + j) : ℝ) * q ^ (k + 1) -
        (TM.logRatioCoeff (k + 1 + j) : ℝ) * p ^ (k + 1) := by
    funext k
    have h := hsum_mul (k + 1) p q
    linear_combination (TM.logRatioCoeff (k + 1 + j) : ℝ) * h
  have h2 : HasSum (fun k : ℕ => (q - p) *
      ((TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q))
      (logRatioSh j q - logRatioSh j p) := by
    rw [hfun]
    simpa using h1
  exact h2.unique ((hasSum_logRatioShDD j hs).mul_left (q - p))

theorem abs_logRatioShDD_sub_le (j : ℕ) {p q : ℝ} (hs : |p| + |q| < 1) (n : ℕ) :
    |logRatioShDD j p q -
        ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) p q| ≤
      (|p| + |q|) ^ n / (1 - (|p| + |q|)) := by
  have hs0 : 0 ≤ |p| + |q| := add_nonneg (abs_nonneg p) (abs_nonneg q)
  refine abs_hasSum_sub_le (hasSum_logRatioShDD j hs) hs0 hs n fun k => ?_
  have h := abs_logRatioShDD_term_le j p q (k + n)
  have e : (|p| + |q|) ^ (k + n) = (|p| + |q|) ^ n * (|p| + |q|) ^ k := by rw [pow_add, mul_comm]
  rw [e] at h
  exact h

/-! ## The models -/

namespace MTM

variable {B : Bounds} {S : NEnv → Prop}

/-- Coefficients of `Λ ℓ_j` up to order `n − 1`. -/
def logRatioShCoeffs (Λ n j : ℕ) : List ℤ := (List.range n).map fun k => logRatioCoeffZ Λ (k + j)

/-- `Λ ℓ_j`. -/
def logRatioSh (B : Bounds) (D Dcap Λ n j : ℕ) (T : MTM) : MTM :=
  ⟨(horner B D Dcap T (logRatioShCoeffs Λ n j)).P,
    IPoly.add (horner B D Dcap T (logRatioShCoeffs Λ n j)).R
      (IPoly.scale ((2 * Λ : ℕ) : ℤ) (powMaj B Dcap (absMaj B T) n))⟩

theorem approx_logRatioSh (hB : B.Valid) (D Dcap : ℕ) {Λ n j : ℕ}
    (hΛ : ∀ i, i < n → (i + j + 1) ∣ Λ) {T : MTM} {g : NEnv → ℝ} (h : T.Approx B S g)
    (hG : HalfOK B T) :
    (logRatioSh B D Dcap Λ n j T).Approx B S (fun e => (Λ : ℝ) * Kron.logRatioSh j (g e)) := by
  intro e he hs
  have hH := approx_horner hB D Dcap h (logRatioShCoeffs Λ n j) e he hs
  have hy := abs_le_absMaj hB h he hs
  have hG0 : 0 ≤ (absMaj B T).eval e := (abs_nonneg _).trans hy
  have hGh := absMaj_le_half hB hG he
  have hy1 : |g e| < 1 := by linarith
  have hser := abs_logRatioSh_sub_le j hy1 n
  have hrem := abs_pow_div_one_sub_le hy hGh n
  have hsum : hornerZ (logRatioShCoeffs Λ n j) (g e) =
      (Λ : ℝ) * ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + j) : ℝ) * g e ^ k := by
    rw [logRatioShCoeffs, hornerZ_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [cast_logRatioCoeffZ (hΛ k (Finset.mem_range.mp hk))]
    ring
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg Λ
  have hscaled : |(Λ : ℝ) * Kron.logRatioSh j (g e) - hornerZ (logRatioShCoeffs Λ n j) (g e)| ≤
      (Λ : ℝ) * (2 * (absMaj B T).eval e ^ n) := by
    rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    exact mul_le_mul_of_nonneg_left (hser.trans hrem) hΛ0
  have htri := abs_sub_le ((Λ : ℝ) * Kron.logRatioSh j (g e))
    (hornerZ (logRatioShCoeffs Λ n j) (g e))
    ((horner B D Dcap T (logRatioShCoeffs Λ n j)).P.eval e)
  have hpow := pow_le_powMaj hB he Dcap (absMaj B T) hG0 n
  have hpow' : (Λ : ℝ) * (2 * (absMaj B T).eval e ^ n) ≤
      (Λ : ℝ) * (2 * (powMaj B Dcap (absMaj B T) n).eval e) :=
    mul_le_mul_of_nonneg_left (by linarith) hΛ0
  simp only [logRatioSh, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

/-- Coefficients of `Λ` times the divided difference of `ℓ_j`. -/
def logRatioShDDCoeffs (Λ n j : ℕ) : List ℤ :=
  (List.range n).map fun k => logRatioCoeffZ Λ (k + 1 + j)

/-- `Λ` times the divided difference of `ℓ_j` between the values of two models. -/
def logRatioShDD (B : Bounds) (D Dcap Λ n j : ℕ) (P Q : MTM) : MTM :=
  ⟨(hsumAux B D Dcap P Q (logRatioShDDCoeffs Λ n j) (const 1) (const 1) zero).P,
    IPoly.add (hsumAux B D Dcap P Q (logRatioShDDCoeffs Λ n j) (const 1) (const 1) zero).R
      (IPoly.scale ((2 * Λ : ℕ) : ℤ)
        (powMaj B Dcap (IPoly.add (absMaj B P) (absMaj B Q)) n))⟩

theorem approx_logRatioShDD (hB : B.Valid) (D Dcap : ℕ) {Λ n j : ℕ}
    (hΛ : ∀ i, i < n → (i + 1 + j + 1) ∣ Λ) {P Q : MTM} {p q : NEnv → ℝ} (hP : P.Approx B S p)
    (hQ : Q.Approx B S q) (hG : HalfOK2 B P Q) :
    (logRatioShDD B D Dcap Λ n j P Q).Approx B S
      (fun e => (Λ : ℝ) * Kron.logRatioShDD j (p e) (q e)) := by
  intro e he hs
  have h1 : (const 1).Approx B S (fun e => hsum (0 + 1) (p e) (q e)) :=
    approx_congr (approx_const (B := B) (S := S) 1) fun e _ _ => by
      rw [hsum_one]
      norm_num
  have h2 : (const 1).Approx B S (fun e => q e ^ 0) :=
    approx_congr (approx_const (B := B) (S := S) 1) fun e _ _ => by norm_num
  have hH := approx_hsumAux hB D Dcap hP hQ (logRatioShDDCoeffs Λ n j)
    0 _ _ _ _ h1 h2 (approx_zero (B := B) (S := S)) e he hs
  have hpa := abs_le_absMaj hB hP he hs
  have hqa := abs_le_absMaj hB hQ he hs
  have hG0 : 0 ≤ (IPoly.add (absMaj B P) (absMaj B Q)).eval e := by
    rw [IPoly.eval_add]
    exact add_nonneg ((abs_nonneg _).trans hpa) ((abs_nonneg _).trans hqa)
  have hGh : (IPoly.add (absMaj B P) (absMaj B Q)).eval e ≤ 1 / 2 := by
    have h := eval_le_evalUB hB he (IPoly.add (absMaj B P) (absMaj B Q))
    have hG' : ((evalUB B (IPoly.add (absMaj B P) (absMaj B Q)) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hG
    have h12 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    linarith
  have hsle : |p e| + |q e| ≤ (IPoly.add (absMaj B P) (absMaj B Q)).eval e := by
    rw [IPoly.eval_add]
    linarith
  have hs1 : |p e| + |q e| < 1 := by linarith
  have hs0 : 0 ≤ |p e| + |q e| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hser := abs_logRatioShDD_sub_le j hs1 n
  have hrem : (|p e| + |q e|) ^ n / (1 - (|p e| + |q e|)) ≤
      2 * (IPoly.add (absMaj B P) (absMaj B Q)).eval e ^ n := by
    have h := abs_pow_div_one_sub_le (y := |p e| + |q e|)
      (G := (IPoly.add (absMaj B P) (absMaj B Q)).eval e) (by rwa [abs_of_nonneg hs0]) hGh n
    rwa [abs_of_nonneg hs0] at h
  simp only [zero_add] at hH
  have hsumEq : ∑ i ∈ Finset.range (logRatioShDDCoeffs Λ n j).length,
      ((((logRatioShDDCoeffs Λ n j).getD i 0 : ℤ) : ℝ) * hsum (1 + i) (p e) (q e)) =
      (Λ : ℝ) * ∑ k ∈ Finset.range n,
        (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) (p e) (q e) := by
    rw [logRatioShDDCoeffs, List.length_map, List.length_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    have hget : ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1 + j)).getD k 0 =
        logRatioCoeffZ Λ (k + 1 + j) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
      rfl
    rw [hget, cast_logRatioCoeffZ (hΛ k hk'), Nat.add_comm 1 k]
    ring
  rw [hsumEq] at hH
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg Λ
  have hpow := pow_le_powMaj hB he Dcap (IPoly.add (absMaj B P) (absMaj B Q)) hG0 n
  have hscaled : |(Λ : ℝ) * Kron.logRatioShDD j (p e) (q e) - (Λ : ℝ) *
      ∑ k ∈ Finset.range n,
        (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) (p e) (q e)| ≤
      (Λ : ℝ) * (2 * (powMaj B Dcap (IPoly.add (absMaj B P) (absMaj B Q)) n).eval e) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    exact mul_le_mul_of_nonneg_left (by linarith) hΛ0
  have htri := abs_sub_le ((Λ : ℝ) * Kron.logRatioShDD j (p e) (q e))
    ((Λ : ℝ) * ∑ k ∈ Finset.range n,
      (TM.logRatioCoeff (k + 1 + j) : ℝ) * hsum (k + 1) (p e) (q e))
    ((hsumAux B D Dcap P Q (logRatioShDDCoeffs Λ n j) (const 1) (const 1) zero).P.eval e)
  simp only [MTM.logRatioShDD, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

end MTM

/-! ## The reduced logarithm of higher order -/

namespace MDD

variable {Bx : Bounds} {S : NEnv → Prop}

/-- The triple of `Λ ℓ_j(x d)` from the triple of `d`. -/
def rlogSh (Bx : Bounds) (D Dcap Λ n j : ℕ) (d : MDD) : MDD :=
  ⟨MTM.logRatioSh Bx D Dcap Λ n j (MTM.mul Bx D Dcap nomeA d.A),
    MTM.logRatioSh Bx D Dcap Λ n j (MTM.mul Bx D Dcap nomeB d.B),
    MTM.mul Bx D Dcap (d.B.add (MTM.mul Bx D Dcap nomeA d.D))
      (MTM.logRatioShDD Bx D Dcap Λ n j (MTM.mul Bx D Dcap nomeA d.A)
        (MTM.mul Bx D Dcap nomeB d.B))⟩

theorem approx_rlogSh (hB : Bx.Valid) (D Dcap : ℕ) {Λ n j : ℕ}
    (hΛ : ∀ i, i < n + 1 → (i + j + 1) ∣ Λ) {d : MDD} {da db : NEnv → ℝ}
    (hd : d.Approx Bx S da db) (hOK : RLogOK Bx D Dcap d) :
    (rlogSh Bx D Dcap Λ n j d).Approx Bx S
      (fun e => (Λ : ℝ) * logRatioSh j (e.a * da e))
      (fun e => (Λ : ℝ) * logRatioSh j (e.b * db e)) := by
  obtain ⟨hGa, hGb, hG2⟩ := hOK
  have hΛ1 : ∀ i, i < n → (i + j + 1) ∣ Λ := fun i hi => hΛ i (by omega)
  have hΛ2 : ∀ i, i < n → (i + 1 + j + 1) ∣ Λ := fun i hi => hΛ (i + 1) (by omega)
  have hza := MTM.approx_mul hB D Dcap (approx_nomeA (Bx := Bx) (S := S)) hd.1
  have hzb := MTM.approx_mul hB D Dcap (approx_nomeB (Bx := Bx) (S := S)) hd.2.1
  refine ⟨MTM.approx_logRatioSh hB D Dcap hΛ1 hza hGa, MTM.approx_logRatioSh hB D Dcap hΛ1 hzb hGb,
    ?_⟩
  have hS : ∀ e, (S e ∧ e.a ≠ e.b) → S e := fun e h => h.1
  have hdb' := MTM.approx_mono_S hd.2.1 hS
  have hza' := MTM.approx_mono_S hza hS
  have hzb' := MTM.approx_mono_S hzb hS
  have hzD := MTM.approx_add hdb'
    (MTM.approx_mul hB D Dcap (approx_nomeA (Bx := Bx) (S := fun e => S e ∧ e.a ≠ e.b)) hd.2.2)
  have hDD := MTM.approx_logRatioShDD hB D Dcap hΛ2 hza' hzb' hG2
  refine MTM.approx_congr (MTM.approx_mul hB D Dcap hzD hDD) fun e he hs => ?_
  have hne : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  have hsmall : |e.a * da e| + |e.b * db e| < 1 := by
    have hpa := MTM.abs_le_absMaj hB hza' he hs
    have hqa := MTM.abs_le_absMaj hB hzb' he hs
    have h := IPoly.eval_le_evalUB hB he
      (IPoly.add (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeA d.A))
        (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeB d.B)))
    have hG' : ((evalUB Bx (IPoly.add (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeA d.A))
        (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeB d.B))) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hG2
    have h12 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [IPoly.eval_add] at h
    linarith
  have hkey := logRatioSh_sub j hsmall
  have hδ : (db e - da e) / (e.b - e.a) * (e.b - e.a) = db e - da e := div_mul_cancel₀ _ hne
  show ((Λ : ℝ) * logRatioSh j (e.b * db e) - (Λ : ℝ) * logRatioSh j (e.a * da e)) /
      (e.b - e.a) =
    (db e + e.a * ((db e - da e) / (e.b - e.a))) *
      ((Λ : ℝ) * Kron.logRatioShDD j (e.a * da e) (e.b * db e))
  rw [div_eq_iff hne]
  generalize (db e - da e) / (e.b - e.a) = δ at hδ ⊢
  linear_combination (-(Λ : ℝ) * e.a * Kron.logRatioShDD j (e.a * da e) (e.b * db e)) * hδ +
    (Λ : ℝ) * hkey

end MDD

end E8Leech.Kron
