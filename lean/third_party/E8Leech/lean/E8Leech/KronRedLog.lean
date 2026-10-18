import E8Leech.KronDevAtoms

/-!
# Logarithms divided by the nome

For `f = 1 + x d(x)` the quotient `log f(x) / x = d · ℓ(x d)`, `ℓ(z) = log (1 + z)/z`, is again a
nice function at the cusp `x = 0`. Its divided difference needs the divided difference of `ℓ`
between two arguments,

`ℓ(q) − ℓ(p) = (q − p) Σ_{k ≥ 1} c_k h_{k−1}(p, q)`,  `c_k = (−1)ᵏ/(k + 1)`,

with the complete homogeneous sums `h_{k−1}`. The tail after `n` terms is at most
`(|p| + |q|)ⁿ / (1 − |p| − |q|)`.

* `hsum`, `logRatioDD`, `logRatio_sub`, `abs_logRatioDD_sub_le`: the real analysis.
* `MTM.logRatioDD`, `MTM.approx_logRatioDD`: the model of `Λ` times the divided difference.
* `MDD.rlog`, `MDD.approx_rlog`: the model of `Λ log (1 + x d)/x` from a model of `d`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-! ## The divided difference of `log (1 + z)/z` -/

/-- `Σ_{i < k} pⁱ q^{k−1−i}`, the divided difference of the `k`-th power. -/
noncomputable def hsum (k : ℕ) (p q : ℝ) : ℝ := ∑ i ∈ Finset.range k, p ^ i * q ^ (k - 1 - i)

theorem hsum_mul (k : ℕ) (p q : ℝ) : hsum k p q * (q - p) = q ^ k - p ^ k := hsum_mul_sub k p q

theorem hsum_one (p q : ℝ) : hsum 1 p q = 1 := by simp [hsum]

theorem hsum_succ_succ (k : ℕ) (p q : ℝ) :
    hsum (k + 1 + 1) p q = p * hsum (k + 1) p q + q ^ (k + 1) := by
  have e1 : ∀ i, p ^ (i + 1) * q ^ (k + 1 + 1 - 1 - (i + 1)) =
      p * (p ^ i * q ^ (k + 1 - 1 - i)) := by
    intro i
    have h : k + 1 + 1 - 1 - (i + 1) = k + 1 - 1 - i := by omega
    rw [h, pow_succ]
    ring
  have h0 : k + 1 + 1 - 1 - 0 = k + 1 := by omega
  unfold hsum
  rw [Finset.sum_range_succ', Finset.mul_sum, Finset.sum_congr rfl fun i _ => e1 i, h0,
    pow_zero, one_mul]

theorem abs_hsum_succ_le (k : ℕ) (p q : ℝ) : |hsum (k + 1) p q| ≤ (|p| + |q|) ^ k := by
  unfold hsum
  calc |∑ i ∈ Finset.range (k + 1), p ^ i * q ^ (k + 1 - 1 - i)|
      ≤ ∑ i ∈ Finset.range (k + 1), |p ^ i * q ^ (k + 1 - 1 - i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (k + 1), |p| ^ i * |q| ^ (k - i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_pow, abs_pow, Nat.add_sub_cancel]
    _ ≤ (|p| + |q|) ^ k := hsum_le_add_pow (abs_nonneg p) (abs_nonneg q) k

theorem abs_logRatioCoeff_le (k : ℕ) : |(TM.logRatioCoeff k : ℝ)| ≤ 1 := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h : (TM.logRatioCoeff k : ℝ) = (-1) ^ k / ((k : ℝ) + 1) := by
    simp [TM.logRatioCoeff]
  rw [h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hpos, div_le_one hpos]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The series of `log (1 + z)/z`. -/
theorem hasSum_logRatio {z : ℝ} (hz : |z| < 1) :
    HasSum (fun k : ℕ => (TM.logRatioCoeff k : ℝ) * z ^ k) (TM.logRatio z) := by
  by_cases h0 : z = 0
  · subst h0
    have hf : (fun k : ℕ => (TM.logRatioCoeff k : ℝ) * (0 : ℝ) ^ k) =
        fun k => if k = 0 then (1 : ℝ) else 0 := by
      funext k
      rcases k with _ | k
      · simp [TM.logRatioCoeff]
      · simp
    rw [hf, TM.logRatio, if_pos rfl]
    exact hasSum_ite_eq 0 1
  · have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -z) (by rwa [abs_neg])
    have h2 := h.mul_left (-z⁻¹)
    have e1 : (fun n : ℕ => -z⁻¹ * ((-z) ^ (n + 1) / ((n : ℝ) + 1))) =
        fun k => (TM.logRatioCoeff k : ℝ) * z ^ k := by
      funext n
      have hc : (TM.logRatioCoeff n : ℝ) = (-1) ^ n / ((n : ℝ) + 1) := by
        simp [TM.logRatioCoeff]
      have hp : (-z) ^ (n + 1) = -((-1) ^ n * z ^ n * z) := by
        rw [pow_succ, neg_pow]
        ring
      rw [hc, hp]
      calc -z⁻¹ * (-((-1) ^ n * z ^ n * z) / ((n : ℝ) + 1))
          = z⁻¹ * z * ((-1) ^ n * z ^ n / ((n : ℝ) + 1)) := by ring
        _ = (-1) ^ n / ((n : ℝ) + 1) * z ^ n := by
            rw [inv_mul_cancel₀ h0]
            ring
    have e2 : -z⁻¹ * -Real.log (1 - -z) = TM.logRatio z := by
      rw [TM.logRatio, if_neg h0, sub_neg_eq_add]
      ring
    rw [e1, e2] at h2
    exact h2

/-- A series whose terms from the index `n` on are dominated by `C sᵏ` is within `C/(1 − s)` of
its `n`-th partial sum. -/
theorem abs_hasSum_sub_le {f : ℕ → ℝ} {A C s : ℝ} (hf : HasSum f A) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (n : ℕ) (hb : ∀ k, |f (k + n)| ≤ C * s ^ k) :
    |A - ∑ k ∈ Finset.range n, f k| ≤ C / (1 - s) := by
  have hsum := hf.summable
  have htail : A - ∑ k ∈ Finset.range n, f k = ∑' k, f (k + n) := by
    rw [← hf.tsum_eq, ← hsum.sum_add_tsum_nat_add n]
    ring
  have hgeom : Summable fun k : ℕ => C * s ^ k :=
    (summable_geometric_of_lt_one hs0 hs1).mul_left C
  have hs' : Summable fun k => f (k + n) := (summable_nat_add_iff n).mpr hsum
  rw [htail]
  calc |∑' k, f (k + n)| ≤ ∑' k, |f (k + n)| := by
        have h := norm_tsum_le_tsum_norm (f := fun k => f (k + n))
          (by simpa only [Real.norm_eq_abs] using hs'.abs)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' k, C * s ^ k := Summable.tsum_le_tsum hb hs'.abs hgeom
    _ = C / (1 - s) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hs0 hs1]
        ring

/-- The divided difference of `log (1 + z)/z`, as a series. -/
noncomputable def logRatioDD (p q : ℝ) : ℝ :=
  ∑' k : ℕ, (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q

theorem abs_logRatioDD_term_le (p q : ℝ) (k : ℕ) :
    |(TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q| ≤ (|p| + |q|) ^ k := by
  rw [abs_mul]
  calc |(TM.logRatioCoeff (k + 1) : ℝ)| * |hsum (k + 1) p q| ≤ 1 * (|p| + |q|) ^ k :=
        mul_le_mul (abs_logRatioCoeff_le _) (abs_hsum_succ_le k p q) (abs_nonneg _) zero_le_one
    _ = (|p| + |q|) ^ k := one_mul _

theorem hasSum_logRatioDD {p q : ℝ} (hs : |p| + |q| < 1) :
    HasSum (fun k : ℕ => (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q) (logRatioDD p q) := by
  have hs0 : 0 ≤ |p| + |q| := add_nonneg (abs_nonneg p) (abs_nonneg q)
  have hsum : Summable fun k : ℕ => (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hs0 hs) fun k => by
      rw [Real.norm_eq_abs]
      exact abs_logRatioDD_term_le p q k
  exact hsum.hasSum

/-- **The difference of `log (1 + z)/z` at two arguments.** -/
theorem logRatio_sub {p q : ℝ} (hs : |p| + |q| < 1) :
    TM.logRatio q - TM.logRatio p = (q - p) * logRatioDD p q := by
  have hp : |p| < 1 := by linarith [abs_nonneg q]
  have hq : |q| < 1 := by linarith [abs_nonneg p]
  have hd := (hasSum_logRatio hq).sub (hasSum_logRatio hp)
  have h1 := (hasSum_nat_add_iff' 1).mpr hd
  have hfun : (fun k : ℕ => (q - p) * ((TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q)) =
      fun k => (TM.logRatioCoeff (k + 1) : ℝ) * q ^ (k + 1) -
        (TM.logRatioCoeff (k + 1) : ℝ) * p ^ (k + 1) := by
    funext k
    have h := hsum_mul (k + 1) p q
    linear_combination (TM.logRatioCoeff (k + 1) : ℝ) * h
  have h2 : HasSum (fun k : ℕ => (q - p) * ((TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q))
      (TM.logRatio q - TM.logRatio p) := by
    rw [hfun]
    simpa using h1
  exact h2.unique ((hasSum_logRatioDD hs).mul_left (q - p))

theorem abs_logRatioDD_sub_le {p q : ℝ} (hs : |p| + |q| < 1) (n : ℕ) :
    |logRatioDD p q - ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) p q| ≤
      (|p| + |q|) ^ n / (1 - (|p| + |q|)) := by
  have hs0 : 0 ≤ |p| + |q| := add_nonneg (abs_nonneg p) (abs_nonneg q)
  refine abs_hasSum_sub_le (hasSum_logRatioDD hs) hs0 hs n fun k => ?_
  have h := abs_logRatioDD_term_le p q (k + n)
  rw [pow_add, mul_comm ((|p| + |q|) ^ k)] at h
  exact h

/-! ## The model of the divided difference -/

namespace MTM

variable {B : Bounds} {S : NEnv → Prop}

/-- `acc + Σ c_i h_{k+i}(P, Q)` by the recurrence `h_{k+1} = P h_k + Q^{k+1}`; `h` is the model
of `h_k` and `qp` the model of `Q^k`. -/
def hsumAux (B : Bounds) (D Dcap : ℕ) (P Q : MTM) : List ℤ → MTM → MTM → MTM → MTM
  | [], _, _, acc => acc
  | c :: cs, h, qp, acc =>
    hsumAux B D Dcap P Q cs ((mul B D Dcap P h).add (mul B D Dcap qp Q)) (mul B D Dcap qp Q)
      (acc.add (h.scale c))

theorem approx_hsumAux (hB : B.Valid) (D Dcap : ℕ) {P Q : MTM} {p q : NEnv → ℝ}
    (hP : P.Approx B S p) (hQ : Q.Approx B S q) :
    ∀ (cs : List ℤ) (k : ℕ) (h qp acc : MTM) (A : NEnv → ℝ),
      h.Approx B S (fun e => hsum (k + 1) (p e) (q e)) → qp.Approx B S (fun e => q e ^ k) →
      acc.Approx B S A →
      (hsumAux B D Dcap P Q cs h qp acc).Approx B S (fun e => A e +
        ∑ i ∈ Finset.range cs.length, ((cs.getD i 0 : ℤ) : ℝ) * hsum (k + 1 + i) (p e) (q e))
  | [], k, h, qp, acc, A, _, _, ha => by
    simpa [hsumAux] using ha
  | c :: cs, k, h, qp, acc, A, hh, hq, ha => by
    have hq' := approx_mul hB D Dcap hq hQ
    have hh' := approx_add (approx_mul hB D Dcap hP hh) hq'
    have ha' := approx_add ha (approx_scale c hh)
    have ih := approx_hsumAux hB D Dcap hP hQ cs (k + 1) _ _ _ _
      (approx_congr hh' fun e _ _ => by rw [hsum_succ_succ, pow_succ])
      (approx_congr hq' fun e _ _ => by rw [pow_succ]) ha'
    refine approx_congr ih fun e _ _ => ?_
    have hidx : ∀ i, k + 1 + (i + 1) = k + 1 + 1 + i := fun i => by omega
    have hre : ∑ i ∈ Finset.range cs.length,
        (((c :: cs).getD (i + 1) 0 : ℤ) : ℝ) * hsum (k + 1 + (i + 1)) (p e) (q e) =
        ∑ i ∈ Finset.range cs.length,
          ((cs.getD i 0 : ℤ) : ℝ) * hsum (k + 1 + 1 + i) (p e) (q e) :=
      Finset.sum_congr rfl fun i _ => by rw [List.getD_cons_succ, hidx]
    rw [List.length_cons, Finset.sum_range_succ', hre, List.getD_cons_zero, Nat.add_zero]
    ring

/-- Both arguments together are at most `1/2` in absolute value. -/
def HalfOK2 (B : Bounds) (P Q : MTM) : Prop :=
  evalUB B (IPoly.add (absMaj B P) (absMaj B Q)) ≤ 1 / 2

instance (B : Bounds) (P Q : MTM) : Decidable (HalfOK2 B P Q) := by
  unfold HalfOK2
  infer_instance

/-- `Λ` times the divided difference of `log (1 + z)/z` between the values of two models. -/
def logRatioDD (B : Bounds) (D Dcap Λ n : ℕ) (P Q : MTM) : MTM :=
  ⟨(hsumAux B D Dcap P Q ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)) (const 1)
      (const 1) zero).P,
    IPoly.add (hsumAux B D Dcap P Q ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1))
        (const 1) (const 1) zero).R
      (IPoly.scale ((2 * Λ : ℕ) : ℤ)
        (powMaj B Dcap (IPoly.add (absMaj B P) (absMaj B Q)) n))⟩

theorem approx_logRatioDD (hB : B.Valid) (D Dcap : ℕ) {Λ n : ℕ}
    (hΛ : ∀ i, i < n + 1 → (i + 1) ∣ Λ) {P Q : MTM} {p q : NEnv → ℝ} (hP : P.Approx B S p)
    (hQ : Q.Approx B S q) (hG : HalfOK2 B P Q) :
    (logRatioDD B D Dcap Λ n P Q).Approx B S
      (fun e => (Λ : ℝ) * Kron.logRatioDD (p e) (q e)) := by
  intro e he hs
  have h1 : (const 1).Approx B S (fun e => hsum (0 + 1) (p e) (q e)) :=
    approx_congr (approx_const (B := B) (S := S) 1) fun e _ _ => by
      rw [hsum_one]
      norm_num
  have h2 : (const 1).Approx B S (fun e => q e ^ 0) :=
    approx_congr (approx_const (B := B) (S := S) 1) fun e _ _ => by norm_num
  have hH := approx_hsumAux hB D Dcap hP hQ ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1))
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
  have hser := abs_logRatioDD_sub_le hs1 n
  have hrem : (|p e| + |q e|) ^ n / (1 - (|p e| + |q e|)) ≤
      2 * (IPoly.add (absMaj B P) (absMaj B Q)).eval e ^ n := by
    have h := abs_pow_div_one_sub_le (y := |p e| + |q e|)
      (G := (IPoly.add (absMaj B P) (absMaj B Q)).eval e) (by rwa [abs_of_nonneg hs0]) hGh n
    rwa [abs_of_nonneg hs0] at h
  simp only [zero_add] at hH
  have hsumEq : ∑ i ∈ Finset.range ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)).length,
      (((((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)).getD i 0 : ℤ) : ℝ) *
        hsum (1 + i) (p e) (q e)) =
      (Λ : ℝ) * ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) (p e) (q e) := by
    rw [List.length_map, List.length_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    have hget : ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)).getD k 0 =
        logRatioCoeffZ Λ (k + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
      rfl
    rw [hget, cast_logRatioCoeffZ (hΛ (k + 1) (by omega)), Nat.add_comm 1 k]
    ring
  rw [hsumEq] at hH
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg Λ
  have hpow := pow_le_powMaj hB he Dcap (IPoly.add (absMaj B P) (absMaj B Q)) hG0 n
  have hscaled : |(Λ : ℝ) * Kron.logRatioDD (p e) (q e) - (Λ : ℝ) *
      ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) (p e) (q e)| ≤
      (Λ : ℝ) * (2 * (powMaj B Dcap (IPoly.add (absMaj B P) (absMaj B Q)) n).eval e) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    exact mul_le_mul_of_nonneg_left (by linarith) hΛ0
  have htri := abs_sub_le ((Λ : ℝ) * Kron.logRatioDD (p e) (q e))
    ((Λ : ℝ) * ∑ k ∈ Finset.range n, (TM.logRatioCoeff (k + 1) : ℝ) * hsum (k + 1) (p e) (q e))
    ((hsumAux B D Dcap P Q ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)) (const 1)
      (const 1) zero).P.eval e)
  simp only [MTM.logRatioDD, IPoly.eval_add, IPoly.eval_scale]
  push_cast
  linarith

end MTM

/-! ## The reduced logarithm -/

namespace MDD

variable {Bx : Bounds} {S : NEnv → Prop}

/-- The models of the nome on the two sides. -/
def nomeA : MTM := MTM.mono ⟨1, 0, 0, 0, 0⟩ 1

def nomeB : MTM := MTM.mono ⟨0, 1, 0, 0, 0⟩ 1

theorem approx_nomeA : nomeA.Approx Bx S (fun e => e.a) :=
  MTM.approx_congr (MTM.approx_mono _ 1) fun e _ _ => by simp [NMono.eval]

theorem approx_nomeB : nomeB.Approx Bx S (fun e => e.b) :=
  MTM.approx_congr (MTM.approx_mono _ 1) fun e _ _ => by simp [NMono.eval]

/-- The triple of `Λ log (1 + x d)/x = Λ d ℓ(x d)` from the triple of `d`. -/
def rlog (Bx : Bounds) (D Dcap Λ n : ℕ) (d : MDD) : MDD :=
  ⟨MTM.mul Bx D Dcap d.A (MTM.logRatio Bx D Dcap Λ n (MTM.mul Bx D Dcap nomeA d.A)),
    MTM.mul Bx D Dcap d.B (MTM.logRatio Bx D Dcap Λ n (MTM.mul Bx D Dcap nomeB d.B)),
    (MTM.mul Bx D Dcap d.D (MTM.logRatio Bx D Dcap Λ n (MTM.mul Bx D Dcap nomeB d.B))).add
      (MTM.mul Bx D Dcap d.A (MTM.mul Bx D Dcap (d.B.add (MTM.mul Bx D Dcap nomeA d.D))
        (MTM.logRatioDD Bx D Dcap Λ n (MTM.mul Bx D Dcap nomeA d.A)
          (MTM.mul Bx D Dcap nomeB d.B))))⟩

/-- The smallness checks of `MDD.rlog`. -/
def RLogOK (Bx : Bounds) (D Dcap : ℕ) (d : MDD) : Prop :=
  MTM.HalfOK Bx (MTM.mul Bx D Dcap nomeA d.A) ∧ MTM.HalfOK Bx (MTM.mul Bx D Dcap nomeB d.B) ∧
    MTM.HalfOK2 Bx (MTM.mul Bx D Dcap nomeA d.A) (MTM.mul Bx D Dcap nomeB d.B)

instance (Bx : Bounds) (D Dcap : ℕ) (d : MDD) : Decidable (RLogOK Bx D Dcap d) := by
  unfold RLogOK
  infer_instance

theorem approx_rlog (hB : Bx.Valid) (D Dcap : ℕ) {Λ n : ℕ} (hΛ : ∀ i, i < n + 1 → (i + 1) ∣ Λ)
    {d : MDD} {da db : NEnv → ℝ} (hd : d.Approx Bx S da db) (hOK : RLogOK Bx D Dcap d) :
    (rlog Bx D Dcap Λ n d).Approx Bx S
      (fun e => (Λ : ℝ) * (da e * TM.logRatio (e.a * da e)))
      (fun e => (Λ : ℝ) * (db e * TM.logRatio (e.b * db e))) := by
  obtain ⟨hGa, hGb, hG2⟩ := hOK
  have hΛ' : ∀ i, i < n → (i + 1) ∣ Λ := fun i hi => hΛ i (by omega)
  have hza := MTM.approx_mul hB D Dcap (approx_nomeA (Bx := Bx) (S := S)) hd.1
  have hzb := MTM.approx_mul hB D Dcap (approx_nomeB (Bx := Bx) (S := S)) hd.2.1
  have hla := MTM.approx_logRatio hB D Dcap hΛ' hza hGa
  have hlb := MTM.approx_logRatio hB D Dcap hΛ' hzb hGb
  refine ⟨?_, ?_, ?_⟩
  · refine MTM.approx_congr (MTM.approx_mul hB D Dcap hd.1 hla) fun e _ _ => ?_
    show (Λ : ℝ) * (da e * TM.logRatio (e.a * da e)) = da e * ((Λ : ℝ) * TM.logRatio (e.a * da e))
    ring
  · refine MTM.approx_congr (MTM.approx_mul hB D Dcap hd.2.1 hlb) fun e _ _ => ?_
    show (Λ : ℝ) * (db e * TM.logRatio (e.b * db e)) = db e * ((Λ : ℝ) * TM.logRatio (e.b * db e))
    ring
  · have hS : ∀ e, (S e ∧ e.a ≠ e.b) → S e := fun e h => h.1
    have hda' := MTM.approx_mono_S hd.1 hS
    have hdb' := MTM.approx_mono_S hd.2.1 hS
    have hza' := MTM.approx_mono_S hza hS
    have hzb' := MTM.approx_mono_S hzb hS
    have hlb' := MTM.approx_mono_S hlb hS
    have hzD := MTM.approx_add hdb'
      (MTM.approx_mul hB D Dcap (approx_nomeA (Bx := Bx) (S := fun e => S e ∧ e.a ≠ e.b)) hd.2.2)
    have hDD := MTM.approx_logRatioDD hB D Dcap hΛ hza' hzb' hG2
    have hterm1 := MTM.approx_mul hB D Dcap hd.2.2 hlb'
    have hterm2 := MTM.approx_mul hB D Dcap hda' (MTM.approx_mul hB D Dcap hzD hDD)
    refine MTM.approx_congr (MTM.approx_add hterm1 hterm2) fun e he hs => ?_
    have hne : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
    have hpa := MTM.abs_le_absMaj hB hza' he hs
    have hqa := MTM.abs_le_absMaj hB hzb' he hs
    have hsmall : |e.a * da e| + |e.b * db e| < 1 := by
      have h := IPoly.eval_le_evalUB hB he
        (IPoly.add (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeA d.A))
          (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeB d.B)))
      have hG' : ((evalUB Bx (IPoly.add (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeA d.A))
          (MTM.absMaj Bx (MTM.mul Bx D Dcap nomeB d.B))) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hG2
      have h12 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
      rw [IPoly.eval_add] at h
      linarith
    have hkey := logRatio_sub hsmall
    have hδ : (db e - da e) / (e.b - e.a) * (e.b - e.a) = db e - da e := div_mul_cancel₀ _ hne
    show ((Λ : ℝ) * (db e * TM.logRatio (e.b * db e)) -
        (Λ : ℝ) * (da e * TM.logRatio (e.a * da e))) / (e.b - e.a) =
      (db e - da e) / (e.b - e.a) * ((Λ : ℝ) * TM.logRatio (e.b * db e)) +
        da e * ((db e + e.a * ((db e - da e) / (e.b - e.a))) *
          ((Λ : ℝ) * Kron.logRatioDD (e.a * da e) (e.b * db e)))
    rw [div_eq_iff hne]
    generalize (db e - da e) / (e.b - e.a) = δ at hδ ⊢
    linear_combination (-((Λ : ℝ) * TM.logRatio (e.b * db e)) -
      (Λ : ℝ) * da e * e.a * Kron.logRatioDD (e.a * da e) (e.b * db e)) * hδ +
        (Λ : ℝ) * da e * hkey

end MDD

end E8Leech.Kron
