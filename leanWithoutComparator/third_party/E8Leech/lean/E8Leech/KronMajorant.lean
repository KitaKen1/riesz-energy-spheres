import E8Leech.KronMul
import Mathlib.Tactic.Positivity

/-!
# Taylor models with polynomial majorants on kernel-fast integer polynomials

A model `MTM` is a pair of integer polynomials `(P, R)`. It approximates `f` on a set of bounds
if `|f e - P e| ≤ R e` for all admissible `e`. The remainder `R` is a polynomial in the two nomes
with natural coefficients, so the error bound shrinks with the nomes. This is what lets one
certificate cover a region in which the nomes tend to `0`: an absolute error radius cannot prove
the positivity of a function of size `a²(a + b)` there.

* `IPoly.normalize`: the canonical form of a polynomial, obtained from the certified product
  with `1`; sums and differences are normalized concatenations.
* `Bounds`: upper bounds of the five nonnegative variables as fractions of natural numbers.
* `IPoly.maj`: a majorant of `|P|` in the nomes only; `IPoly.cap`: the reduction of high nome
  powers of a majorant by the bounds of the nomes.
* `MTM.mul`: the product truncated at total nome degree `D`, with the certified product
  `IPoly.mulK` and all discarded terms in the majorant.
-/

namespace E8Leech.Kron

/-! ## Rounding up -/

/-- `⌈x / d⌉` for natural numbers. -/
def ceilDiv (x d : ℕ) : ℕ := (x + (d - 1)) / d

theorem le_ceilDiv_mul (x : ℕ) {d : ℕ} (hd : 0 < d) : x ≤ ceilDiv x d * d := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (x + (d - 1)) d
  have h2 := Nat.mod_lt (x + (d - 1)) hd
  rw [Nat.mul_comm]
  generalize d * ((x + (d - 1)) / d) = A at h1 ⊢
  omega

theorem natAbs_cast_abs (c : ℤ) : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

/-- If `σ ≤ N / Dn`, then `|c| σ ≤ ⌈|c| N / Dn⌉`. -/
theorem abs_mul_le_ceilDiv (c : ℤ) {σ : ℝ} {N Dn : ℕ} (hD : 0 < Dn) (hσ : σ * Dn ≤ N) :
    |(c : ℝ)| * σ ≤ (ceilDiv (c.natAbs * N) Dn : ℕ) := by
  have hD' : (0 : ℝ) < Dn := by exact_mod_cast hD
  have h1 : ((c.natAbs * N : ℕ) : ℝ) ≤ ((ceilDiv (c.natAbs * N) Dn * Dn : ℕ) : ℝ) := by
    exact_mod_cast le_ceilDiv_mul (c.natAbs * N) hD
  push_cast at h1
  rw [natAbs_cast_abs] at h1
  have h2 : |(c : ℝ)| * σ * Dn ≤ (ceilDiv (c.natAbs * N) Dn : ℕ) * Dn := by
    calc |(c : ℝ)| * σ * Dn = |(c : ℝ)| * (σ * Dn) := by ring
      _ ≤ |(c : ℝ)| * N := mul_le_mul_of_nonneg_left hσ (abs_nonneg _)
      _ ≤ _ := h1
  exact le_of_mul_le_mul_right h2 hD'

theorem pow_mul_le {y : ℝ} {n d : ℕ} (hy : 0 ≤ y) (h : y * d ≤ n) (k : ℕ) :
    y ^ k * (d : ℝ) ^ k ≤ (n : ℝ) ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg hy (Nat.cast_nonneg d)) h k

/-! ## Sums, differences, truncation -/

namespace IPoly

/-- The constant polynomial `1`. -/
def unit : IPoly := [(NMono.one, 1)]

theorem eval_unit (e : NEnv) : eval unit e = 1 := by simp [unit, NMono.eval_one]

/-- Canonical form: equal monomials are combined and the terms are sorted by digit position. -/
def normalize (P : IPoly) : IPoly := mulK P unit

theorem eval_normalize (P : IPoly) (e : NEnv) : eval (normalize P) e = eval P e := by
  rw [normalize, eval_mulK, eval_unit, mul_one]

def add (P Q : IPoly) : IPoly := normalize (P ++ Q)

theorem eval_add (P Q : IPoly) (e : NEnv) : eval (add P Q) e = eval P e + eval Q e := by
  rw [add, eval_normalize, eval_append]

def scale (c : ℤ) (P : IPoly) : IPoly := P.map fun x => (x.1, c * x.2)

theorem eval_scale (c : ℤ) (P : IPoly) (e : NEnv) : eval (scale c P) e = c * eval P e := by
  induction P with
  | nil => simp [scale]
  | cons x P ih =>
    simp only [scale, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

def sub (P Q : IPoly) : IPoly := normalize (P ++ neg Q)

theorem eval_sub (P Q : IPoly) (e : NEnv) : eval (sub P Q) e = eval P e - eval Q e := by
  rw [sub, eval_normalize, eval_append, eval_neg]
  ring

/-- The terms of total nome degree `≤ D`. -/
def low (D : ℕ) (P : IPoly) : IPoly := P.filter fun x => Nat.ble (x.1.ea + x.1.eb) D

/-- The terms of total nome degree `> D`. -/
def high (D : ℕ) (P : IPoly) : IPoly := P.filter fun x => !Nat.ble (x.1.ea + x.1.eb) D

theorem eval_low_add_high (D : ℕ) (P : IPoly) (e : NEnv) :
    eval (low D P) e + eval (high D P) e = eval P e := by
  induction P with
  | nil => simp [low, high]
  | cons x P ih =>
    simp only [low, high] at ih ⊢
    cases h : Nat.ble (x.1.ea + x.1.eb) D
    · rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h]),
        eval_cons, eval_cons]
      linarith
    · rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp [h]),
        eval_cons, eval_cons]
      linarith

end IPoly

/-! ## Bounds and majorants -/

/-- Upper bounds `an/ad, bn/bd, un/ud, tn/td, ln/ld` of the five nonnegative variables. -/
structure Bounds where
  an : ℕ
  ad : ℕ
  bn : ℕ
  bd : ℕ
  un : ℕ
  ud : ℕ
  tn : ℕ
  td : ℕ
  ln : ℕ
  ld : ℕ

namespace Bounds

def Valid (B : Bounds) : Prop := 0 < B.ad ∧ 0 < B.bd ∧ 0 < B.ud ∧ 0 < B.td ∧ 0 < B.ld

def Mem (B : Bounds) (e : NEnv) : Prop :=
  0 ≤ e.a ∧ e.a * B.ad ≤ B.an ∧ 0 ≤ e.b ∧ e.b * B.bd ≤ B.bn ∧ 0 ≤ e.u ∧ e.u * B.ud ≤ B.un ∧
    0 ≤ e.t ∧ e.t * B.td ≤ B.tn ∧ 0 ≤ e.l ∧ e.l * B.ld ≤ B.ln

end Bounds

namespace IPoly

/-- Numerator of the bound of `u^eu t^et l^el`. -/
def restNum (B : Bounds) (m : NMono) : ℕ := B.un ^ m.eu * B.tn ^ m.et * B.ln ^ m.el

/-- Denominator of the bound of `u^eu t^et l^el`. -/
def restDen (B : Bounds) (m : NMono) : ℕ := B.ud ^ m.eu * B.td ^ m.et * B.ld ^ m.el

theorem restDen_pos {B : Bounds} (hB : B.Valid) (m : NMono) : 0 < restDen B m := by
  obtain ⟨_, _, hu, ht, hl⟩ := hB
  exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hu) (Nat.pow_pos ht)) (Nat.pow_pos hl)

theorem rest_le {B : Bounds} {e : NEnv} (he : B.Mem e) (m : NMono) :
    e.u ^ m.eu * e.t ^ m.et * e.l ^ m.el * (restDen B m : ℝ) ≤ restNum B m := by
  obtain ⟨_, _, _, _, hu0, hu, ht0, ht, hl0, hl⟩ := he
  have h1 := pow_mul_le hu0 hu m.eu
  have h2 := pow_mul_le ht0 ht m.et
  have h3 := pow_mul_le hl0 hl m.el
  have n1 : (0 : ℝ) ≤ e.u ^ m.eu * (B.ud : ℝ) ^ m.eu :=
    mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  have n2 : (0 : ℝ) ≤ e.t ^ m.et * (B.td : ℝ) ^ m.et :=
    mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  have n3 : (0 : ℝ) ≤ e.l ^ m.el * (B.ld : ℝ) ^ m.el :=
    mul_nonneg (pow_nonneg hl0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  have k1 : (0 : ℝ) ≤ (B.un : ℝ) ^ m.eu := pow_nonneg (Nat.cast_nonneg _) _
  have k2 : (0 : ℝ) ≤ (B.tn : ℝ) ^ m.et := pow_nonneg (Nat.cast_nonneg _) _
  simp only [restDen, restNum]
  push_cast
  calc e.u ^ m.eu * e.t ^ m.et * e.l ^ m.el *
        ((B.ud : ℝ) ^ m.eu * (B.td : ℝ) ^ m.et * (B.ld : ℝ) ^ m.el)
      = e.u ^ m.eu * (B.ud : ℝ) ^ m.eu * (e.t ^ m.et * (B.td : ℝ) ^ m.et) *
          (e.l ^ m.el * (B.ld : ℝ) ^ m.el) := by ring
    _ ≤ (B.un : ℝ) ^ m.eu * (B.tn : ℝ) ^ m.et * (B.ln : ℝ) ^ m.el :=
        mul_le_mul (mul_le_mul h1 h2 n2 k1) h3 n3 (mul_nonneg k1 k2)

/-- One term of the majorant: `|c| u^eu t^et l^el` is replaced by a natural upper bound. -/
def majTerm (B : Bounds) (x : NMono × ℤ) : NMono × ℤ :=
  (⟨x.1.ea, x.1.eb, 0, 0, 0⟩, (ceilDiv (x.2.natAbs * restNum B x.1) (restDen B x.1) : ℕ))

/-- The majorant before normalization. -/
def majRaw (B : Bounds) (P : IPoly) : IPoly := P.map (majTerm B)

theorem abs_term_le_majTerm {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e)
    (x : NMono × ℤ) :
    |(x.2 : ℝ) * x.1.eval e| ≤ ((majTerm B x).2 : ℝ) * (majTerm B x).1.eval e := by
  have ha : 0 ≤ e.a := he.1
  have hb : 0 ≤ e.b := he.2.2.1
  have hu : 0 ≤ e.u := he.2.2.2.2.1
  have ht : 0 ≤ e.t := he.2.2.2.2.2.2.1
  have hl : 0 ≤ e.l := he.2.2.2.2.2.2.2.2.1
  have hab : 0 ≤ e.a ^ x.1.ea * e.b ^ x.1.eb := mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have hρ : 0 ≤ e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el :=
    mul_nonneg (mul_nonneg (pow_nonneg hu _) (pow_nonneg ht _)) (pow_nonneg hl _)
  have hc := abs_mul_le_ceilDiv x.2 (restDen_pos hB x.1) (rest_le he x.1)
  have hm : x.1.eval e = e.a ^ x.1.ea * e.b ^ x.1.eb *
      (e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el) := by
    simp only [NMono.eval]
    ring
  have hm' : (majTerm B x).1.eval e = e.a ^ x.1.ea * e.b ^ x.1.eb := by
    simp [majTerm, NMono.eval]
  rw [hm', hm, abs_mul, abs_of_nonneg (mul_nonneg hab hρ)]
  simp only [majTerm]
  push_cast
  calc |(x.2 : ℝ)| * (e.a ^ x.1.ea * e.b ^ x.1.eb * (e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el))
      = |(x.2 : ℝ)| * (e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el) *
          (e.a ^ x.1.ea * e.b ^ x.1.eb) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hab

theorem abs_eval_le_majRaw {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (P : IPoly) :
    |eval P e| ≤ eval (majRaw B P) e := by
  induction P with
  | nil => simp [majRaw]
  | cons x P ih =>
    simp only [majRaw, List.map_cons, eval_cons] at ih ⊢
    exact (abs_add_le _ _).trans (add_le_add (abs_term_le_majTerm hB he x) ih)

/-- A majorant of `|P|` in the nomes, in canonical form. -/
def maj (B : Bounds) (P : IPoly) : IPoly := normalize (majRaw B P)

theorem abs_eval_le_maj {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (P : IPoly) :
    |eval P e| ≤ eval (maj B P) e := by
  rw [maj, eval_normalize]
  exact abs_eval_le_majRaw hB he P

/-! ## Reduction of high nome powers -/

/-- The reduced exponent of `b`: at least `min j 1`. -/
def capJ (Dcap i j : ℕ) : ℕ := Nat.min j (Nat.max 1 (Dcap - i))

/-- The reduced exponent of `a`: at least `min i 3`. -/
def capI (Dcap i j : ℕ) : ℕ := Nat.min i (Nat.max 3 (Dcap - capJ Dcap i j))

theorem capJ_le (Dcap i j : ℕ) : capJ Dcap i j ≤ j := Nat.min_le_left _ _

theorem capI_le (Dcap i j : ℕ) : capI Dcap i j ≤ i := Nat.min_le_left _ _

/-- One term of the reduced majorant. -/
def capTerm (B : Bounds) (Dcap : ℕ) (x : NMono × ℤ) : NMono × ℤ :=
  (⟨capI Dcap x.1.ea x.1.eb, capJ Dcap x.1.ea x.1.eb, x.1.eu, x.1.et, x.1.el⟩,
    (ceilDiv
      (x.2.natAbs * (B.an ^ (x.1.ea - capI Dcap x.1.ea x.1.eb) *
        B.bn ^ (x.1.eb - capJ Dcap x.1.ea x.1.eb)))
      (B.ad ^ (x.1.ea - capI Dcap x.1.ea x.1.eb) *
        B.bd ^ (x.1.eb - capJ Dcap x.1.ea x.1.eb)) : ℕ))

def capRaw (B : Bounds) (Dcap : ℕ) (R : IPoly) : IPoly := R.map (capTerm B Dcap)

theorem term_le_capTerm {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (Dcap : ℕ)
    (x : NMono × ℤ) :
    (x.2 : ℝ) * x.1.eval e ≤ ((capTerm B Dcap x).2 : ℝ) * (capTerm B Dcap x).1.eval e := by
  obtain ⟨ha, ha', hb, hb', hu, _, ht, _, hl, _⟩ := he
  have hi := capI_le Dcap x.1.ea x.1.eb
  have hj := capJ_le Dcap x.1.ea x.1.eb
  simp only [capTerm, NMono.eval]
  generalize capI Dcap x.1.ea x.1.eb = i' at hi ⊢
  generalize capJ Dcap x.1.ea x.1.eb = j' at hj ⊢
  have hi2 : i' + (x.1.ea - i') = x.1.ea := Nat.add_sub_cancel' hi
  have hj2 : j' + (x.1.eb - j') = x.1.eb := Nat.add_sub_cancel' hj
  have hA : e.a ^ x.1.ea = e.a ^ i' * e.a ^ (x.1.ea - i') := by rw [← pow_add, hi2]
  have hBb : e.b ^ x.1.eb = e.b ^ j' * e.b ^ (x.1.eb - j') := by rw [← pow_add, hj2]
  have hσ0 : 0 ≤ e.a ^ (x.1.ea - i') * e.b ^ (x.1.eb - j') :=
    mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have hW : 0 ≤ e.a ^ i' * e.b ^ j' * e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))
      (pow_nonneg hu _)) (pow_nonneg ht _)) (pow_nonneg hl _)
  have hσ : e.a ^ (x.1.ea - i') * e.b ^ (x.1.eb - j') *
      ((B.ad ^ (x.1.ea - i') * B.bd ^ (x.1.eb - j') : ℕ) : ℝ) ≤
        ((B.an ^ (x.1.ea - i') * B.bn ^ (x.1.eb - j') : ℕ) : ℝ) := by
    have h1 := pow_mul_le ha ha' (x.1.ea - i')
    have h2 := pow_mul_le hb hb' (x.1.eb - j')
    push_cast
    calc e.a ^ (x.1.ea - i') * e.b ^ (x.1.eb - j') *
          ((B.ad : ℝ) ^ (x.1.ea - i') * (B.bd : ℝ) ^ (x.1.eb - j'))
        = e.a ^ (x.1.ea - i') * (B.ad : ℝ) ^ (x.1.ea - i') *
            (e.b ^ (x.1.eb - j') * (B.bd : ℝ) ^ (x.1.eb - j')) := by ring
      _ ≤ (B.an : ℝ) ^ (x.1.ea - i') * (B.bn : ℝ) ^ (x.1.eb - j') :=
          mul_le_mul h1 h2
            (mul_nonneg (pow_nonneg hb _) (pow_nonneg (Nat.cast_nonneg _) _))
            (pow_nonneg (Nat.cast_nonneg _) _)
  have hD : 0 < B.ad ^ (x.1.ea - i') * B.bd ^ (x.1.eb - j') :=
    Nat.mul_pos (Nat.pow_pos hB.1) (Nat.pow_pos hB.2.1)
  have hc := abs_mul_le_ceilDiv x.2 hD hσ
  rw [hA, hBb, Int.cast_natCast]
  calc (x.2 : ℝ) * (e.a ^ i' * e.a ^ (x.1.ea - i') * (e.b ^ j' * e.b ^ (x.1.eb - j')) *
        e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el)
      = (x.2 : ℝ) * (e.a ^ (x.1.ea - i') * e.b ^ (x.1.eb - j')) *
          (e.a ^ i' * e.b ^ j' * e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el) := by ring
    _ ≤ |(x.2 : ℝ)| * (e.a ^ (x.1.ea - i') * e.b ^ (x.1.eb - j')) *
          (e.a ^ i' * e.b ^ j' * e.u ^ x.1.eu * e.t ^ x.1.et * e.l ^ x.1.el) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hσ0) hW
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hW

theorem eval_le_capRaw {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (Dcap : ℕ)
    (R : IPoly) : eval R e ≤ eval (capRaw B Dcap R) e := by
  induction R with
  | nil => simp [capRaw]
  | cons x R ih =>
    simp only [capRaw, List.map_cons, eval_cons] at ih ⊢
    exact add_le_add (term_le_capTerm hB he Dcap x) ih

/-- The majorant with nome degrees reduced to about `Dcap`, in canonical form. -/
def cap (B : Bounds) (Dcap : ℕ) (R : IPoly) : IPoly := normalize (capRaw B Dcap R)

theorem eval_le_cap {B : Bounds} (hB : B.Valid) {e : NEnv} (he : B.Mem e) (Dcap : ℕ)
    (R : IPoly) : eval R e ≤ eval (cap B Dcap R) e := by
  rw [cap, eval_normalize]
  exact eval_le_capRaw hB he Dcap R

end IPoly

/-! ## Taylor models with majorants -/

/-- A polynomial with a polynomial remainder bound. -/
structure MTM where
  P : IPoly
  R : IPoly
  deriving DecidableEq

namespace MTM

open IPoly

/-- `T` approximates `f` on the bounds, where the side condition `S` holds. -/
def Approx (B : Bounds) (S : NEnv → Prop) (T : MTM) (f : NEnv → ℝ) : Prop :=
  ∀ e, B.Mem e → S e → |f e - T.P.eval e| ≤ T.R.eval e

def zero : MTM := ⟨[], []⟩

def const (c : ℤ) : MTM := ⟨[(NMono.one, c)], []⟩

def mono (m : NMono) (c : ℤ) : MTM := ⟨[(m, c)], []⟩

def add (X Y : MTM) : MTM := ⟨IPoly.add X.P Y.P, IPoly.add X.R Y.R⟩

def sub (X Y : MTM) : MTM := ⟨IPoly.sub X.P Y.P, IPoly.add X.R Y.R⟩

def scale (c : ℤ) (X : MTM) : MTM := ⟨IPoly.scale c X.P, IPoly.scale (c.natAbs : ℕ) X.R⟩

/-- The product, truncated at total nome degree `D`; majorant degrees are reduced to `Dcap`. -/
def mul (B : Bounds) (D Dcap : ℕ) (X Y : MTM) : MTM :=
  ⟨low D (mulK X.P Y.P),
    cap B Dcap (maj B (high D (mulK X.P Y.P)) ++
      (mulK X.R (maj B Y.P ++ Y.R) ++ mulK (maj B X.P) Y.R))⟩

variable {B : Bounds} {S : NEnv → Prop}

theorem approx_zero : zero.Approx B S (fun _ => 0) := by
  intro e _ _
  simp [zero]

theorem approx_const (c : ℤ) : (const c).Approx B S (fun _ => c) := by
  intro e _ _
  simp [const, NMono.eval_one]

theorem approx_mono (m : NMono) (c : ℤ) : (mono m c).Approx B S (fun e => c * m.eval e) := by
  intro e _ _
  simp [mono]

theorem approx_congr {T : MTM} {f g : NEnv → ℝ} (h : T.Approx B S f)
    (hfg : ∀ e, B.Mem e → S e → g e = f e) : T.Approx B S g := by
  intro e he hs
  rw [hfg e he hs]
  exact h e he hs

theorem approx_mono_S {T : MTM} {S' : NEnv → Prop} {f : NEnv → ℝ} (h : T.Approx B S f)
    (hS : ∀ e, S' e → S e) : T.Approx B S' f := fun e he hs => h e he (hS e hs)

theorem approx_add {X Y : MTM} {f g : NEnv → ℝ} (hX : X.Approx B S f) (hY : Y.Approx B S g) :
    (X.add Y).Approx B S (fun e => f e + g e) := by
  intro e he hs
  have h1 := hX e he hs
  have h2 := hY e he hs
  simp only [add, IPoly.eval_add]
  calc |f e + g e - (X.P.eval e + Y.P.eval e)|
      = |(f e - X.P.eval e) + (g e - Y.P.eval e)| := by congr 1; ring
    _ ≤ |f e - X.P.eval e| + |g e - Y.P.eval e| := abs_add_le _ _
    _ ≤ X.R.eval e + Y.R.eval e := add_le_add h1 h2

theorem approx_sub {X Y : MTM} {f g : NEnv → ℝ} (hX : X.Approx B S f) (hY : Y.Approx B S g) :
    (X.sub Y).Approx B S (fun e => f e - g e) := by
  intro e he hs
  have h1 := hX e he hs
  have h2 := hY e he hs
  simp only [sub, IPoly.eval_sub, IPoly.eval_add]
  calc |f e - g e - (X.P.eval e - Y.P.eval e)|
      = |(f e - X.P.eval e) - (g e - Y.P.eval e)| := by congr 1; ring
    _ ≤ |f e - X.P.eval e| + |g e - Y.P.eval e| := abs_sub _ _
    _ ≤ X.R.eval e + Y.R.eval e := add_le_add h1 h2

theorem approx_scale (c : ℤ) {X : MTM} {f : NEnv → ℝ} (hX : X.Approx B S f) :
    (X.scale c).Approx B S (fun e => c * f e) := by
  intro e he hs
  have h1 := hX e he hs
  simp only [scale, IPoly.eval_scale]
  have hc : (((c.natAbs : ℕ) : ℤ) : ℝ) = |(c : ℝ)| := by
    rw [Int.cast_natCast, natAbs_cast_abs]
  rw [hc]
  calc |(c : ℝ) * f e - c * X.P.eval e| = |(c : ℝ)| * |f e - X.P.eval e| := by
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ |(c : ℝ)| * X.R.eval e := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem approx_mul (hB : B.Valid) (D Dcap : ℕ) {X Y : MTM} {f g : NEnv → ℝ}
    (hX : X.Approx B S f) (hY : Y.Approx B S g) :
    (mul B D Dcap X Y).Approx B S (fun e => f e * g e) := by
  intro e he hs
  have h1 := hX e he hs
  have h2 := hY e he hs
  have hrx : 0 ≤ X.R.eval e := (abs_nonneg _).trans h1
  have hry : 0 ≤ Y.R.eval e := (abs_nonneg _).trans h2
  have hp := abs_eval_le_maj hB he X.P
  have hq := abs_eval_le_maj hB he Y.P
  have hhi := abs_eval_le_maj hB he (high D (mulK X.P Y.P))
  have hsplit := eval_low_add_high D (mulK X.P Y.P) e
  rw [eval_mulK] at hsplit
  have hcap := eval_le_cap hB he Dcap (maj B (high D (mulK X.P Y.P)) ++
    (mulK X.R (maj B Y.P ++ Y.R) ++ mulK (maj B X.P) Y.R))
  rw [eval_append, eval_append, eval_mulK, eval_mulK, eval_append] at hcap
  simp only [mul]
  refine le_trans ?_ hcap
  have hg : |g e| ≤ (maj B Y.P).eval e + Y.R.eval e := by
    calc |g e| = |(g e - Y.P.eval e) + Y.P.eval e| := by congr 1; ring
      _ ≤ |g e - Y.P.eval e| + |Y.P.eval e| := abs_add_le _ _
      _ ≤ Y.R.eval e + (maj B Y.P).eval e := add_le_add h2 hq
      _ = _ := add_comm _ _
  have hmp : 0 ≤ (maj B X.P).eval e := (abs_nonneg _).trans hp
  calc |f e * g e - (low D (mulK X.P Y.P)).eval e|
      = |(f e - X.P.eval e) * g e + X.P.eval e * (g e - Y.P.eval e) +
          (high D (mulK X.P Y.P)).eval e| := by
        congr 1
        linear_combination (-1 : ℝ) * hsplit
    _ ≤ |(f e - X.P.eval e) * g e| + |X.P.eval e * (g e - Y.P.eval e)| +
          |(high D (mulK X.P Y.P)).eval e| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ X.R.eval e * ((maj B Y.P).eval e + Y.R.eval e) + (maj B X.P).eval e * Y.R.eval e +
          (maj B (high D (mulK X.P Y.P))).eval e := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add (mul_le_mul h1 hg (abs_nonneg _) hrx)
          (mul_le_mul hp h2 (abs_nonneg _) hmp)) hhi
    _ = _ := by ring

end MTM

end E8Leech.Kron
