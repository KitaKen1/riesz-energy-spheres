import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Kernel-checkable Taylor models in the nome variables

A small verified polynomial arithmetic for the certificate of the CKMRV inequality (6.4)(1).

* `Mono`: a monomial `a^ea b^eb u^eu t^et p^ep l^el` (`t, p` may carry negative exponents).
  The variables stand for the two nomes `a, b`, the polynomial parts `u, t`, `p = π` and
  `l = log 2`.
* `Poly`: a list of monomials with rational coefficients. Its value is the sum of the terms.
  `Poly.merge` adds two polynomials and combines equal monomials at the heads. The ordering only
  affects efficiency: `eval (merge P Q) = eval P + eval Q` holds for all inputs.
* `Box`: rational bounds for all variables; `Poly.bound` bounds `|P|` on a box.
* `TM`: a polynomial with an absolute remainder radius on a box; `TM.mul` truncates the product
  to total degree `≤ D` in `(a, b)` and moves the rest into the radius.

Everything is computable with structural recursion only, so `decide` can run it in the kernel.
-/

namespace E8Leech.Taylor

/-- A monomial `a^ea b^eb u^eu t^et p^ep l^el`. -/
structure Mono where
  ea : ℕ
  eb : ℕ
  eu : ℕ
  et : ℤ
  ep : ℤ
  el : ℕ
  deriving DecidableEq, Repr

/-- Values of the six variables. -/
structure Env where
  a : ℝ
  b : ℝ
  u : ℝ
  t : ℝ
  p : ℝ
  l : ℝ

namespace Mono

def one : Mono := ⟨0, 0, 0, 0, 0, 0⟩

def mul (m n : Mono) : Mono :=
  ⟨m.ea + n.ea, m.eb + n.eb, m.eu + n.eu, m.et + n.et, m.ep + n.ep, m.el + n.el⟩

/-- Total degree in the nomes. -/
def deg (m : Mono) : ℕ := m.ea + m.eb

/-- An ordering key; only used to keep lists sorted for efficiency. -/
def key (m : Mono) : ℤ :=
  ((((m.ea * 64 + m.eb : ℕ) * 64 + m.eu : ℕ) * 64 + (m.et + 32)) * 64 + (m.ep + 32)) * 64 + m.el

noncomputable def eval (m : Mono) (e : Env) : ℝ :=
  e.a ^ m.ea * e.b ^ m.eb * e.u ^ m.eu * e.t ^ m.et * e.p ^ m.ep * e.l ^ m.el

theorem eval_one (e : Env) : one.eval e = 1 := by simp [one, eval]

theorem eval_mul (m n : Mono) (e : Env) (ht : e.t ≠ 0) (hp : e.p ≠ 0) :
    (m.mul n).eval e = m.eval e * n.eval e := by
  simp only [mul, eval, pow_add, zpow_add₀ ht, zpow_add₀ hp]
  ring

end Mono

/-- A polynomial: a list of terms. -/
abbrev Poly := List (Mono × ℚ)

namespace Poly

noncomputable def eval (P : Poly) (e : Env) : ℝ :=
  (P.map fun mc => (mc.2 : ℝ) * mc.1.eval e).sum

@[simp] theorem eval_nil (e : Env) : eval [] e = 0 := rfl

@[simp] theorem eval_cons (mc : Mono × ℚ) (P : Poly) (e : Env) :
    eval (mc :: P) e = (mc.2 : ℝ) * mc.1.eval e + eval P e := by
  simp [eval]

theorem eval_append (P Q : Poly) (e : Env) : eval (P ++ Q) e = eval P e + eval Q e := by
  simp [eval]

/-- Merge two polynomials, combining equal head monomials. `fuel` bounds the recursion. -/
def mergeAux : ℕ → Poly → Poly → Poly
  | 0, P, Q => P ++ Q
  | _ + 1, [], Q => Q
  | _ + 1, P, [] => P
  | n + 1, (m, c) :: P, (m', c') :: Q =>
    if m = m' then
      let s := c + c'
      if s = 0 then mergeAux n P Q else (m, s) :: mergeAux n P Q
    else if m.key ≤ m'.key then (m, c) :: mergeAux n P ((m', c') :: Q)
    else (m', c') :: mergeAux n ((m, c) :: P) Q

def merge (P Q : Poly) : Poly := mergeAux (P.length + Q.length) P Q

theorem eval_mergeAux (n : ℕ) (P Q : Poly) (e : Env) :
    eval (mergeAux n P Q) e = eval P e + eval Q e := by
  induction n generalizing P Q with
  | zero => simp [mergeAux, eval_append]
  | succ n ih =>
    match P, Q with
    | [], Q => simp [mergeAux]
    | (m, c) :: P, [] => simp [mergeAux]
    | (m, c) :: P, (m', c') :: Q =>
      simp only [mergeAux]
      by_cases hm : m = m'
      · subst hm
        simp only [if_true]
        by_cases hs : c + c' = 0
        · simp only [hs, if_true, ih, eval_cons]
          have : (c : ℝ) + c' = 0 := by exact_mod_cast hs
          linear_combination (-(Mono.eval m e)) * this
        · simp only [hs, if_false, eval_cons, ih]
          push_cast
          ring
      · simp only [hm, if_false]
        split_ifs
        · simp only [eval_cons, ih]
          ring
        · simp only [eval_cons, ih]
          ring

theorem eval_merge (P Q : Poly) (e : Env) : eval (merge P Q) e = eval P e + eval Q e :=
  eval_mergeAux _ P Q e

/-- Multiply every term by `(m, c)`. -/
def scaleMono (m : Mono) (c : ℚ) (Q : Poly) : Poly := Q.map fun mc => (m.mul mc.1, c * mc.2)

theorem eval_scaleMono (m : Mono) (c : ℚ) (Q : Poly) (e : Env) (ht : e.t ≠ 0) (hp : e.p ≠ 0) :
    eval (scaleMono m c Q) e = (c : ℝ) * m.eval e * eval Q e := by
  induction Q with
  | nil => simp [scaleMono]
  | cons mc Q ih =>
    simp only [scaleMono, List.map_cons, eval_cons] at ih ⊢
    rw [ih, Mono.eval_mul _ _ _ ht hp]
    push_cast
    ring

/-- Sum a list of polynomials by repeated merging. -/
def sumList : List Poly → Poly
  | [] => []
  | P :: Ps => merge P (sumList Ps)

theorem eval_sumList (Ps : List Poly) (e : Env) :
    eval (sumList Ps) e = (Ps.map fun P => eval P e).sum := by
  induction Ps with
  | nil => simp [sumList]
  | cons P Ps ih => simp [sumList, eval_merge, ih]

def mul (P Q : Poly) : Poly := sumList (P.map fun mc => scaleMono mc.1 mc.2 Q)

theorem eval_mul (P Q : Poly) (e : Env) (ht : e.t ≠ 0) (hp : e.p ≠ 0) :
    eval (mul P Q) e = eval P e * eval Q e := by
  rw [mul, eval_sumList]
  induction P with
  | nil => simp
  | cons mc P ih =>
    simp only [List.map_cons, List.sum_cons, eval_cons] at ih ⊢
    rw [ih, eval_scaleMono _ _ _ _ ht hp]
    ring

def scale (c : ℚ) (P : Poly) : Poly := P.map fun mc => (mc.1, c * mc.2)

theorem eval_scale (c : ℚ) (P : Poly) (e : Env) : eval (scale c P) e = c * eval P e := by
  induction P with
  | nil => simp [scale]
  | cons mc P ih =>
    simp only [scale, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- Split off the terms of total nome degree `> D`. -/
def low (D : ℕ) (P : Poly) : Poly := P.filter fun mc => mc.1.deg ≤ D

def high (D : ℕ) (P : Poly) : Poly := P.filter fun mc => ¬ mc.1.deg ≤ D

theorem eval_low_add_high (D : ℕ) (P : Poly) (e : Env) :
    eval (low D P) e + eval (high D P) e = eval P e := by
  induction P with
  | nil => simp [low, high]
  | cons mc P ih =>
    by_cases h : mc.1.deg ≤ D
    · simp only [low, high, List.filter_cons, h, decide_true, decide_not, Bool.not_true,
        if_true, eval_cons] at ih ⊢
      simp only [Bool.false_eq_true, if_false]
      linarith
    · simp only [low, high, List.filter_cons, h, decide_false, decide_not, Bool.not_false,
        if_true, eval_cons] at ih ⊢
      simp only [Bool.false_eq_true, if_false]
      linarith

end Poly

/-- Rational bounds on the six variables; all lower bounds positive except possibly `a, b ≥ 0`. -/
structure Box where
  alo : ℚ
  ahi : ℚ
  blo : ℚ
  bhi : ℚ
  ulo : ℚ
  uhi : ℚ
  tlo : ℚ
  thi : ℚ
  plo : ℚ
  phi : ℚ
  llo : ℚ
  lhi : ℚ
  deriving Repr

namespace Box

def Valid (B : Box) : Prop :=
  0 ≤ B.alo ∧ 0 ≤ B.blo ∧ 0 < B.ulo ∧ 0 < B.tlo ∧ 0 < B.plo ∧ 0 < B.llo

def Mem (B : Box) (e : Env) : Prop :=
  (B.alo : ℝ) ≤ e.a ∧ e.a ≤ B.ahi ∧ (B.blo : ℝ) ≤ e.b ∧ e.b ≤ B.bhi ∧
    (B.ulo : ℝ) ≤ e.u ∧ e.u ≤ B.uhi ∧ (B.tlo : ℝ) ≤ e.t ∧ e.t ≤ B.thi ∧
      (B.plo : ℝ) ≤ e.p ∧ e.p ≤ B.phi ∧ (B.llo : ℝ) ≤ e.l ∧ e.l ≤ B.lhi

end Box

/-- `x^n` bound for `x ∈ [lo, hi]`, `0 < lo`, any integer `n`. -/
def zpowHi (lo hi : ℚ) (n : ℤ) : ℚ := if 0 ≤ n then hi ^ n.toNat else lo ^ n

/-- An upper bound of `|m|` on the box. -/
def Mono.bound (B : Box) (m : Mono) : ℚ :=
  B.ahi ^ m.ea * B.bhi ^ m.eb * B.uhi ^ m.eu * zpowHi B.tlo B.thi m.et *
    zpowHi B.plo B.phi m.ep * B.lhi ^ m.el

/-- An upper bound of `|P|` on the box. -/
def Poly.bound (B : Box) (P : Poly) : ℚ := (P.map fun mc => |mc.2| * Mono.bound B mc.1).sum

/-- A Taylor model: polynomial part and absolute remainder radius. -/
structure TM where
  P : Poly
  r : ℚ

/-- `T` approximates `f` on the part of the box where the side condition `S` holds. -/
def TM.Approx (B : Box) (S : Env → Prop) (T : TM) (f : Env → ℝ) : Prop :=
  ∀ e, B.Mem e → S e → |f e - T.P.eval e| ≤ T.r

end E8Leech.Taylor
