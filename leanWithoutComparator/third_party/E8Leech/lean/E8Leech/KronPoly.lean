import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Integer polynomials with kernel-fast certified multiplication

The Taylor-model certificates for the CKMRV kernel inequality multiply polynomials with several
hundred terms. A list-based product costs the kernel a few milliseconds per pair of terms, which
makes high truncation orders infeasible. Here a product is obtained from *one* multiplication of
big natural numbers (Kronecker substitution), which the kernel performs with GMP, and the result
is accepted only after a cheap certificate check:

* `NMono`: a monomial `a^ea b^eb u^eu t^et l^el` with natural exponents; `IPoly`: a list of
  monomials with integer coefficients.
* `NMono.key`: the mixed-radix position of a monomial. It is additive, and injective on
  monomials whose exponents `eu, et, el, ea` are below the radices.
* `keyed_sum_eq_zero`: if a keyed integer combination vanishes at a base `β` that exceeds the
  sum of the absolute coefficients, every linear functional of the keys vanishes on it.
  (A polynomial with coefficients of absolute value `< β` and the root `β` is zero.)
* `IPoly.eval_of_certOK`: the certificate. The decoded candidate `R` is never trusted; only the
  integer identity `val P * val Q = val R`, the exponent ranges and the coefficient bound are
  checked.
* `IPoly.mulK`: the product used by later modules. `eval_mulK` holds unconditionally, because
  `mulK` falls back to the schoolbook product when the certificate check fails.
-/

namespace E8Leech.Kron

/-! ## A polynomial with small coefficients that vanishes at the base is zero -/

theorem poly_eq_zero_of_eval_base {β : ℤ} (hβ : 0 < β) :
    ∀ (n : ℕ) (G : Polynomial ℤ), G.natDegree ≤ n → (∀ k, |G.coeff k| < β) →
      G.eval β = 0 → G = 0 := by
  intro n
  induction n with
  | zero =>
    intro G hdeg _ hev
    have hG := Polynomial.eq_C_of_natDegree_le_zero hdeg
    rw [hG, Polynomial.eval_C] at hev
    rw [hG, hev, map_zero]
  | succ n ih =>
    intro G hdeg hc hev
    have hsplit := Polynomial.divX_mul_X_add G
    have hev' : (Polynomial.divX G).eval β * β + G.coeff 0 = 0 := by
      have h := congrArg (Polynomial.eval β) hsplit
      rwa [Polynomial.eval_add, Polynomial.eval_mul_X, Polynomial.eval_C, hev] at h
    have hdvd : β ∣ G.coeff 0 := ⟨-(Polynomial.divX G).eval β, by linear_combination hev'⟩
    have h0 : G.coeff 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hc 0)
    have hev'' : (Polynomial.divX G).eval β = 0 := by
      rw [h0, add_zero] at hev'
      exact (mul_eq_zero.mp hev').resolve_right hβ.ne'
    have hdiv : Polynomial.divX G = 0 :=
      ih _ (by rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; omega)
        (fun k => by rw [Polynomial.coeff_divX]; exact hc (k + 1)) hev''
    rw [← hsplit, hdiv, h0]
    simp

/-! ## Keyed coefficient lists -/

/-- The value at the base `β` of a list of coefficients with digit positions. -/
def kval (β : ℤ) (T : List (ℕ × ℤ)) : ℤ := (T.map fun x => x.2 * β ^ x.1).sum

/-- The sum of the absolute coefficients. -/
def knorm (T : List (ℕ × ℤ)) : ℤ := (T.map fun x => |x.2|).sum

/-- The univariate polynomial with the listed coefficients; only used in proofs. -/
noncomputable def kpoly (T : List (ℕ × ℤ)) : Polynomial ℤ :=
  (T.map fun x => Polynomial.monomial x.1 x.2).sum

theorem kpoly_eval (β : ℤ) (T : List (ℕ × ℤ)) : (kpoly T).eval β = kval β T := by
  induction T with
  | nil => simp [kpoly, kval]
  | cons x T ih =>
    simp only [kpoly, kval, List.map_cons, List.sum_cons, Polynomial.eval_add,
      Polynomial.eval_monomial] at ih ⊢
    rw [ih]

theorem abs_kpoly_coeff_le (T : List (ℕ × ℤ)) (k : ℕ) : |(kpoly T).coeff k| ≤ knorm T := by
  induction T with
  | nil => simp [kpoly, knorm]
  | cons x T ih =>
    simp only [kpoly, knorm, List.map_cons, List.sum_cons, Polynomial.coeff_add,
      Polynomial.coeff_monomial] at ih ⊢
    split_ifs
    · exact (abs_add_le _ _).trans (add_le_add le_rfl ih)
    · rw [zero_add]
      exact ih.trans (le_add_of_nonneg_left (abs_nonneg _))

theorem kpoly_sum (T : List (ℕ × ℤ)) (f : ℕ → ℝ) :
    (kpoly T).sum (fun k c => (c : ℝ) * f k) = (T.map fun x => (x.2 : ℝ) * f x.1).sum := by
  induction T with
  | nil => simp [kpoly]
  | cons x T ih =>
    simp only [kpoly, List.map_cons, List.sum_cons] at ih ⊢
    rw [Polynomial.sum_add_index _ _ _ (fun i => by simp)
      (fun a b₁ b₂ => by push_cast; ring), Polynomial.sum_monomial_index _ _ (by simp), ih]

/-- **Digit uniqueness.** If the base exceeds the sum of the absolute coefficients and the keyed
combination vanishes at the base, then all coefficient sums over equal keys vanish; hence every
functional `Σ c · f key` vanishes. -/
theorem keyed_sum_eq_zero {β : ℤ} (hβ : 0 < β) (T : List (ℕ × ℤ)) (hn : knorm T < β)
    (hv : kval β T = 0) (f : ℕ → ℝ) : (T.map fun x => (x.2 : ℝ) * f x.1).sum = 0 := by
  have h0 : kpoly T = 0 := poly_eq_zero_of_eval_base hβ _ (kpoly T) le_rfl
    (fun k => (abs_kpoly_coeff_le T k).trans_lt hn) (by rw [kpoly_eval, hv])
  rw [← kpoly_sum, h0, Polynomial.sum_zero_index]

/-! ## Monomials -/

/-- A monomial `a^ea b^eb u^eu t^et l^el`. -/
structure NMono where
  ea : ℕ
  eb : ℕ
  eu : ℕ
  et : ℕ
  el : ℕ
  deriving DecidableEq, Repr

/-- Values of the five variables. -/
structure NEnv where
  a : ℝ
  b : ℝ
  u : ℝ
  t : ℝ
  l : ℝ

/-- Radices of the exponents `eu, et, el, ea`. The exponent `eb` is the top digit. -/
structure Radix where
  ru : ℕ
  rt : ℕ
  rl : ℕ
  ra : ℕ

namespace NMono

def one : NMono := ⟨0, 0, 0, 0, 0⟩

def mul (m n : NMono) : NMono :=
  ⟨m.ea + n.ea, m.eb + n.eb, m.eu + n.eu, m.et + n.et, m.el + n.el⟩

noncomputable def eval (m : NMono) (e : NEnv) : ℝ :=
  e.a ^ m.ea * e.b ^ m.eb * e.u ^ m.eu * e.t ^ m.et * e.l ^ m.el

theorem eval_one (e : NEnv) : one.eval e = 1 := by simp [one, eval]

theorem eval_mul (m n : NMono) (e : NEnv) : (m.mul n).eval e = m.eval e * n.eval e := by
  simp only [mul, eval, pow_add]
  ring

/-- The mixed-radix digit position. -/
def key (r : Radix) (m : NMono) : ℕ :=
  m.eu + r.ru * (m.et + r.rt * (m.el + r.rl * (m.ea + r.ra * m.eb)))

theorem key_mul (r : Radix) (m n : NMono) : (m.mul n).key r = m.key r + n.key r := by
  simp only [key, mul]
  ring

/-- The exponents other than `eb` are below their radices. -/
def InRange (r : Radix) (m : NMono) : Prop :=
  m.eu < r.ru ∧ m.et < r.rt ∧ m.el < r.rl ∧ m.ea < r.ra

end NMono

/-- The monomial at a digit position. -/
def unkey (r : Radix) (k : ℕ) : NMono :=
  ⟨k / r.ru / r.rt / r.rl % r.ra, k / r.ru / r.rt / r.rl / r.ra, k % r.ru, k / r.ru % r.rt,
    k / r.ru / r.rt % r.rl⟩

theorem digit_mod {x n : ℕ} (y : ℕ) (h : x < n) : (x + n * y) % n = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem digit_div {x n : ℕ} (y : ℕ) (h : x < n) : (x + n * y) / n = y := by
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt h), Nat.div_eq_of_lt h, Nat.zero_add]

theorem unkey_key {r : Radix} {m : NMono} (h : m.InRange r) : unkey r (m.key r) = m := by
  obtain ⟨hu, ht, hl, ha⟩ := h
  obtain ⟨ea, eb, eu, et, el⟩ := m
  simp only [unkey, NMono.key] at *
  simp only [digit_div _ hu, digit_div _ ht, digit_div _ hl, digit_div _ ha, digit_mod _ hu,
    digit_mod _ ht, digit_mod _ hl, digit_mod _ ha]

/-! ## Integer polynomials -/

/-- A polynomial: a list of monomials with integer coefficients. -/
abbrev IPoly := List (NMono × ℤ)

namespace IPoly

noncomputable def eval (P : IPoly) (e : NEnv) : ℝ := (P.map fun x => (x.2 : ℝ) * x.1.eval e).sum

@[simp] theorem eval_nil (e : NEnv) : eval [] e = 0 := rfl

@[simp] theorem eval_cons (x : NMono × ℤ) (P : IPoly) (e : NEnv) :
    eval (x :: P) e = (x.2 : ℝ) * x.1.eval e + eval P e := by
  simp [eval]

theorem eval_append (P Q : IPoly) (e : NEnv) : eval (P ++ Q) e = eval P e + eval Q e := by
  simp [eval]

/-- The digit positions of the terms. -/
def keyed (r : Radix) (P : IPoly) : List (ℕ × ℤ) := P.map fun x => (x.1.key r, x.2)

def InRange (r : Radix) (P : IPoly) : Prop := ∀ x ∈ P, x.1.InRange r

/-- The sum of the absolute coefficients. -/
def norm (P : IPoly) : ℤ := (P.map fun x => |x.2|).sum

def neg (P : IPoly) : IPoly := P.map fun x => (x.1, -x.2)

/-- The schoolbook product. It is used in proofs and as a fallback, not in certificates. -/
def mulSlow (P Q : IPoly) : IPoly := P.flatMap fun x => Q.map fun y => (x.1.mul y.1, x.2 * y.2)

theorem kval_keyed (β : ℤ) (r : Radix) (P : IPoly) :
    kval β (keyed r P) = (P.map fun x => x.2 * β ^ x.1.key r).sum := by
  simp [kval, keyed, List.map_map, Function.comp_def]

theorem knorm_keyed (r : Radix) (P : IPoly) : knorm (keyed r P) = norm P := by
  simp [knorm, keyed, norm, List.map_map, Function.comp_def]

theorem eval_neg (P : IPoly) (e : NEnv) : eval (neg P) e = -eval P e := by
  induction P with
  | nil => simp [neg]
  | cons x P ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem norm_neg (P : IPoly) : norm (neg P) = norm P := by
  simp [norm, neg, List.map_map, Function.comp_def]

theorem norm_append (P Q : IPoly) : norm (P ++ Q) = norm P + norm Q := by
  simp [norm]

theorem kval_keyed_neg (β : ℤ) (r : Radix) (P : IPoly) :
    kval β (keyed r (neg P)) = -kval β (keyed r P) := by
  rw [kval_keyed, kval_keyed]
  induction P with
  | nil => simp [neg]
  | cons x P ih =>
    simp only [neg, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem kval_keyed_append (β : ℤ) (r : Radix) (P Q : IPoly) :
    kval β (keyed r (P ++ Q)) = kval β (keyed r P) + kval β (keyed r Q) := by
  simp [kval, keyed]

/-- A multiplicative weight of the terms is multiplicative on the schoolbook product. -/
theorem sum_mulSlow {S : Type*} [CommSemiring S] (g : ℤ → S) (φ : NMono → S)
    (hg : ∀ x y, g (x * y) = g x * g y) (hφ : ∀ m n, φ (m.mul n) = φ m * φ n) (P Q : IPoly) :
    ((mulSlow P Q).map fun x => g x.2 * φ x.1).sum =
      (P.map fun x => g x.2 * φ x.1).sum * (Q.map fun x => g x.2 * φ x.1).sum := by
  induction P with
  | nil => simp [mulSlow]
  | cons x P ih =>
    have hrow : ((Q.map fun y => (x.1.mul y.1, x.2 * y.2)).map fun z => g z.2 * φ z.1).sum =
        g x.2 * φ x.1 * (Q.map fun y => g y.2 * φ y.1).sum := by
      rw [← List.sum_map_mul_left, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
      simp only [Function.comp_apply, hg, hφ]
      ring
    simp only [mulSlow, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, add_mul] at ih ⊢
    rw [hrow, ih]

theorem eval_mulSlow (P Q : IPoly) (e : NEnv) : eval (mulSlow P Q) e = eval P e * eval Q e :=
  sum_mulSlow (fun c => (c : ℝ)) (fun m => m.eval e) (fun x y => by push_cast; ring)
    (fun m n => NMono.eval_mul m n e) P Q

theorem kval_mulSlow (β : ℤ) (r : Radix) (P Q : IPoly) :
    kval β (keyed r (mulSlow P Q)) = kval β (keyed r P) * kval β (keyed r Q) := by
  rw [kval_keyed, kval_keyed, kval_keyed]
  exact sum_mulSlow (fun c => c) (fun m => β ^ m.key r) (fun _ _ => rfl)
    (fun m n => by rw [NMono.key_mul, pow_add]) P Q

theorem norm_mulSlow (P Q : IPoly) : norm (mulSlow P Q) = norm P * norm Q := by
  have h := sum_mulSlow (fun c : ℤ => |c|) (fun _ => (1 : ℤ)) abs_mul (fun _ _ => by simp) P Q
  simpa [norm] using h

/-- In-range terms: the evaluation is a functional of the digit positions. -/
theorem eval_eq_keyed_sum {r : Radix} {P : IPoly} (hP : P.InRange r) (e : NEnv) :
    eval P e = ((keyed r P).map fun x => (x.2 : ℝ) * (unkey r x.1).eval e).sum := by
  rw [eval, keyed, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  simp only [Function.comp_apply, unkey_key (hP x hx)]

/-- An in-range polynomial with small coefficients whose base value vanishes evaluates to zero. -/
theorem eval_eq_zero_of_kval {r : Radix} {β : ℤ} (hβ : 0 < β) {T : IPoly} (hr : T.InRange r)
    (hn : norm T < β) (hv : kval β (keyed r T) = 0) (e : NEnv) : eval T e = 0 := by
  rw [eval_eq_keyed_sum hr e]
  exact keyed_sum_eq_zero hβ _ (by rwa [knorm_keyed]) hv (fun k => (unkey r k).eval e)

/-- **The product certificate** in mathematical form. -/
theorem eval_mul_of_kval {r : Radix} {β : ℤ} (hβ : 0 < β) {P Q R : IPoly}
    (hPQ : (mulSlow P Q).InRange r) (hR : R.InRange r)
    (hn : norm P * norm Q + norm R < β)
    (hv : kval β (keyed r P) * kval β (keyed r Q) = kval β (keyed r R)) (e : NEnv) :
    eval R e = eval P e * eval Q e := by
  have hT : (mulSlow P Q ++ neg R).InRange r := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hPQ x h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact hR y hy
  have h0 := eval_eq_zero_of_kval hβ hT
    (by rw [norm_append, norm_mulSlow, norm_neg]; exact hn)
    (by rw [kval_keyed_append, kval_mulSlow, kval_keyed_neg, hv]; ring) e
  rw [eval_append, eval_mulSlow, eval_neg] at h0
  linarith

/-! ## The computable certificate check -/

/-- Componentwise `≤` on the exponents other than `eb`. -/
def leB (m b : NMono) : Bool :=
  Nat.ble m.eu b.eu && Nat.ble m.et b.et && Nat.ble m.el b.el && Nat.ble m.ea b.ea

/-- The exponents other than `eb` are below the radices. -/
def ltB (m : NMono) (r : Radix) : Bool :=
  Nat.blt m.eu r.ru && Nat.blt m.et r.rt && Nat.blt m.el r.rl && Nat.blt m.ea r.ra

theorem leB_iff {m b : NMono} :
    leB m b = true ↔ m.eu ≤ b.eu ∧ m.et ≤ b.et ∧ m.el ≤ b.el ∧ m.ea ≤ b.ea := by
  simp only [leB, Bool.and_eq_true, Nat.ble_eq, and_assoc]

theorem ltB_iff {m : NMono} {r : Radix} : ltB m r = true ↔ m.InRange r := by
  simp only [ltB, Bool.and_eq_true, Nat.blt_eq, NMono.InRange, and_assoc]

/-- The sum of the absolute coefficients as a natural number. -/
def normN (P : IPoly) : ℕ := (P.map fun x => x.2.natAbs).sum

theorem normN_cast (P : IPoly) : (normN P : ℤ) = norm P := by
  induction P with
  | nil => simp [normN, norm]
  | cons x P ih =>
    simp only [normN, norm, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, ih, Int.natCast_natAbs]

/-! ### The encoding by binary splitting

The kernel keeps every intermediate number of a reduction, so adding the terms one by one costs
(number of terms) × (size of the value). Binary splitting encodes the two halves of a list
relative to their own least keys; for sorted keys every intermediate number is then as short as
the block of digits it represents. Nothing is assumed about the order: the least key is a
checked hint. -/

/-- The value of a keyed list relative to the key `b`. -/
def krel (w b : ℕ) (T : List (ℕ × ℤ)) : ℤ := (T.map fun x => x.2 * 2 ^ (w * (x.1 - b))).sum

theorem krel_append (w b : ℕ) (T₁ T₂ : List (ℕ × ℤ)) :
    krel w b (T₁ ++ T₂) = krel w b T₁ + krel w b T₂ := by
  simp [krel]

theorem krel_shift (w b k : ℕ) (hbk : b ≤ k) (T : List (ℕ × ℤ)) (hT : ∀ y ∈ T, k ≤ y.1) :
    krel w b T = 2 ^ (w * (k - b)) * krel w k T := by
  induction T with
  | nil => simp [krel]
  | cons y T ih =>
    have hy := hT y List.mem_cons_self
    have ih' := ih fun z hz => hT z (List.mem_cons_of_mem _ hz)
    simp only [krel, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    have he : w * (y.1 - b) = w * (k - b) + w * (y.1 - k) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [he, pow_add]
    ring

theorem krel_zero (w : ℕ) (T : List (ℕ × ℤ)) : krel w 0 T = kval (2 ^ w) T := by
  simp [krel, kval, pow_mul]

/-- The positive and the negative part of the relative value, term by term. -/
def kencAux (w b : ℕ) : List (ℕ × ℤ) → ℕ → ℕ → ℕ × ℕ
  | [], p, n => (p, n)
  | (k, c) :: T, p, n =>
    match c with
    | Int.ofNat c => kencAux w b T (p + c <<< (w * (k - b))) n
    | Int.negSucc c => kencAux w b T p (n + (c + 1) <<< (w * (k - b)))

theorem kencAux_spec (w b : ℕ) : ∀ (T : List (ℕ × ℤ)) (p n : ℕ),
    ((kencAux w b T p n).1 : ℤ) - (kencAux w b T p n).2 = (p : ℤ) - n + krel w b T
  | [], p, n => by simp [kencAux, krel]
  | (k, c) :: T, p, n => by
    have hk : krel w b ((k, c) :: T) = c * 2 ^ (w * (k - b)) + krel w b T := by
      simp [krel]
    cases c with
    | ofNat c =>
      rw [hk]
      simp only [kencAux]
      rw [kencAux_spec w b T, Int.ofNat_eq_natCast]
      push_cast [Nat.shiftLeft_eq]
      ring
    | negSucc c =>
      rw [hk]
      simp only [kencAux]
      rw [kencAux_spec w b T, Int.negSucc_eq]
      push_cast [Nat.shiftLeft_eq]
      ring

/-- The least key of a list (a hint; `kencSplit` checks it). -/
def kmin : List (ℕ × ℤ) → ℕ → ℕ
  | [], m => m
  | x :: T, m => kmin T (Nat.min m x.1)

/-- Join the value pairs of two halves; the second one is relative to the key `k ≥ b`. -/
def kencNode (w b k : ℕ) (X Y : ℕ × ℕ) : ℕ × ℕ :=
  (X.1 + Y.1 <<< (w * (k - b)), X.2 + Y.2 <<< (w * (k - b)))

theorem kencNode_spec (w b k : ℕ) (X Y : ℕ × ℕ) :
    ((kencNode w b k X Y).1 : ℤ) - (kencNode w b k X Y).2 =
      ((X.1 : ℤ) - X.2) + 2 ^ (w * (k - b)) * ((Y.1 : ℤ) - Y.2) := by
  simp only [kencNode]
  push_cast [Nat.shiftLeft_eq]
  ring

/-- One splitting step: the halves `T₁, T₂` of `T` and the claimed least key `k` of `T₂`. -/
def kencSplit (w : ℕ) (rec : ℕ → List (ℕ × ℤ) → ℕ × ℕ) (b : ℕ) (T T₁ T₂ : List (ℕ × ℤ))
    (k : ℕ) : ℕ × ℕ :=
  bif Nat.ble b k && T₂.all (fun y => Nat.ble k y.1) then kencNode w b k (rec b T₁) (rec k T₂)
  else kencAux w b T 0 0

theorem kencSplit_spec (w : ℕ) (rec : ℕ → List (ℕ × ℤ) → ℕ × ℕ)
    (hrec : ∀ (b : ℕ) (T : List (ℕ × ℤ)), (∀ y ∈ T, b ≤ y.1) →
      ((rec b T).1 : ℤ) - (rec b T).2 = krel w b T)
    (b : ℕ) (T T₁ T₂ : List (ℕ × ℤ)) (k : ℕ) (hT : ∀ y ∈ T, b ≤ y.1) (hsplit : T₁ ++ T₂ = T) :
    ((kencSplit w rec b T T₁ T₂ k).1 : ℤ) - (kencSplit w rec b T T₁ T₂ k).2 = krel w b T := by
  unfold kencSplit
  cases hc : (Nat.ble b k && T₂.all fun y => Nat.ble k y.1)
  · simp only [cond_false]
    rw [kencAux_spec]
    simp
  · simp only [cond_true]
    simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hc
    obtain ⟨hbk, hall⟩ := hc
    rw [kencNode_spec, hrec b T₁ (fun y hy => hT y (hsplit ▸ List.mem_append_left _ hy)),
      hrec k T₂ hall, ← hsplit, krel_append, krel_shift w b k hbk T₂ hall]

/-- The value pair of a keyed list relative to `b`, by binary splitting. -/
def kencDC (w : ℕ) : ℕ → ℕ → List (ℕ × ℤ) → ℕ × ℕ
  | 0, b, T => kencAux w b T 0 0
  | fuel + 1, b, T =>
    bif Nat.ble T.length 8 then kencAux w b T 0 0
    else kencSplit w (kencDC w fuel) b T (T.take (T.length / 2)) (T.drop (T.length / 2))
      (kmin (T.drop (T.length / 2)) ((T.drop (T.length / 2)).headD (0, 0)).1)

theorem kencDC_spec (w : ℕ) : ∀ (fuel b : ℕ) (T : List (ℕ × ℤ)), (∀ y ∈ T, b ≤ y.1) →
    ((kencDC w fuel b T).1 : ℤ) - (kencDC w fuel b T).2 = krel w b T
  | 0, b, T, _ => by
    simp only [kencDC]
    rw [kencAux_spec]
    simp
  | fuel + 1, b, T, hT => by
    simp only [kencDC]
    cases h8 : Nat.ble T.length 8
    · simp only [cond_false]
      exact kencSplit_spec w _ (kencDC_spec w fuel) b T _ _ _ hT (List.take_append_drop _ _)
    · simp only [cond_true]
      rw [kencAux_spec]
      simp

/-- The value pair of a polynomial. -/
def enc (w : ℕ) (r : Radix) (P : IPoly) : ℕ × ℕ := kencDC w P.length 0 (keyed r P)

theorem enc_spec (w : ℕ) (r : Radix) (P : IPoly) :
    ((enc w r P).1 : ℤ) - (enc w r P).2 = kval (2 ^ w) (keyed r P) := by
  rw [enc, kencDC_spec w _ 0 _ (fun _ _ => Nat.zero_le _), krel_zero]

/-- All checks of a product certificate. `bP, bQ` bound the exponents of `P, Q`. -/
def certOK (w : ℕ) (r : Radix) (bP bQ : NMono) (P Q R : IPoly) : Bool :=
  P.all (fun x => leB x.1 bP) && Q.all (fun x => leB x.1 bQ) && ltB (bP.mul bQ) r &&
    R.all (fun x => ltB x.1 r) && Nat.blt (normN P * normN Q + normN R) (2 ^ w) &&
      Nat.beq ((enc w r P).1 * (enc w r Q).1 + (enc w r P).2 * (enc w r Q).2 + (enc w r R).2)
        ((enc w r P).1 * (enc w r Q).2 + (enc w r P).2 * (enc w r Q).1 + (enc w r R).1)

theorem inRange_mulSlow {r : Radix} {bP bQ : NMono} {P Q : IPoly}
    (hP : ∀ x ∈ P, leB x.1 bP = true) (hQ : ∀ x ∈ Q, leB x.1 bQ = true)
    (hr : ltB (bP.mul bQ) r = true) : (mulSlow P Q).InRange r := by
  intro z hz
  obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  obtain ⟨h1, h2, h3, h4⟩ := leB_iff.mp (hP x hx)
  obtain ⟨k1, k2, k3, k4⟩ := leB_iff.mp (hQ y hy)
  obtain ⟨r1, r2, r3, r4⟩ := ltB_iff.mp hr
  simp only [NMono.mul] at r1 r2 r3 r4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [NMono.mul] <;> omega

/-- **The product certificate.** -/
theorem eval_of_certOK {w : ℕ} {r : Radix} {bP bQ : NMono} {P Q R : IPoly}
    (h : certOK w r bP bQ P Q R = true) (e : NEnv) : eval R e = eval P e * eval Q e := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hP, hQ⟩, hr⟩, hR⟩, hn⟩, hv⟩ := h
  have hv := Nat.eq_of_beq_eq_true hv
  have hβ : (0 : ℤ) < 2 ^ w := by positivity
  refine eval_mul_of_kval hβ (inRange_mulSlow hP hQ hr) (fun x hx => ltB_iff.mp (hR x hx)) ?_ ?_ e
  · rw [← normN_cast, ← normN_cast, ← normN_cast]
    exact_mod_cast hn
  · rw [← enc_spec, ← enc_spec, ← enc_spec]
    have hz : (((enc w r P).1 * (enc w r Q).1 + (enc w r P).2 * (enc w r Q).2 + (enc w r R).2 : ℕ) : ℤ) =
        (((enc w r P).1 * (enc w r Q).2 + (enc w r P).2 * (enc w r Q).1 + (enc w r R).1 : ℕ) : ℤ) :=
      congrArg _ hv
    push_cast at hz
    linear_combination hz

end IPoly

end E8Leech.Kron
