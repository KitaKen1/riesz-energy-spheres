import E8Leech.KronCornerGrid

/-!
# Interval jets of arbitrary order

`KronJet` carries enclosures of a value and of its first two derivations through a program. The
corner certificate for `d = 24` needs Taylor enclosures of higher order of functions that already
contain two derivations. Here a jet is a list of intervals, entry `k` enclosing the `k`-fold
derivation `dzn k x` of the expression.

Sums and products follow the Leibniz rule. The jets of the leaves are not obtained from the
expression trees of their derivations (those grow too fast): the jet of order `n + 1` of an atom
is the jet of order `n` extended by the entry `n` of the jet of its derivation, and the derivations
of the eight atoms are computed by one small program with shared subexpressions.

* `IExpr.dzn`, `IExpr.evalB_dzn_add`, `IExpr.evalB_dzn_mul`: the iterated derivation and the
  Leibniz rule for the values.
* `QI.scale`, `JMem`, `jadd`, `jsub`, `jmul`, `jconst`: jets and their arithmetic.
* `jetE`, `jMem_jetE`: the jet of an expression tree from the jets of its leaves.
* `ISLP.runJN`, `ISLP.mem_runJN`: the jet run of a program.
* `monoJet`, `jMem_monoJet`: the jets of the monomials, by recursion on the order.
* `atomDProg`, `atomDProg_spec`: the program of the derivations of the atoms.
* `atomJets`, `jMem_atomJets`: the jets of the atoms, by recursion on the order, rounded outward.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

namespace IExpr

/-- The `k`-fold derivation. -/
def dzn (Λ : ℕ) (k : ℕ) (x : IExpr) : IExpr := (dz Λ)^[k] x

theorem dzn_zero (Λ : ℕ) (x : IExpr) : dzn Λ 0 x = x := rfl

theorem dzn_succ (Λ k : ℕ) (x : IExpr) : dzn Λ (k + 1) x = dzn Λ k (dz Λ x) := rfl

theorem dzn_add_apply (Λ j k : ℕ) (x : IExpr) : dzn Λ (j + k) x = dzn Λ j (dzn Λ k x) :=
  Function.iterate_add_apply _ _ _ _

variable (fs : List (ℝ → ℝ)) (Λ : ℕ) (e : NEnv)

theorem evalB_dzn_add (k : ℕ) (x y : IExpr) :
    evalB fs (dzn Λ k (.add x y)) e = evalB fs (dzn Λ k x) e + evalB fs (dzn Λ k y) e := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => exact ih (dz Λ x) (dz Λ y)

theorem evalB_dzn_sub (k : ℕ) (x y : IExpr) :
    evalB fs (dzn Λ k (.sub x y)) e = evalB fs (dzn Λ k x) e - evalB fs (dzn Λ k y) e := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => exact ih (dz Λ x) (dz Λ y)

theorem evalB_dzn_cst (k : ℕ) (c : ℤ) :
    evalB fs (dzn Λ (k + 1) (.cst c)) e = 0 := by
  induction k with
  | zero =>
    show ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  | succ k ih => exact ih

theorem evalB_dzn_tat (k i : ℕ) : evalB fs (dzn Λ (k + 1) (.tat i)) e = 0 :=
  evalB_dzn_cst fs Λ e k 0

/-- **The Leibniz rule** for the values of the iterated derivation. -/
theorem evalB_dzn_mul (k : ℕ) (x y : IExpr) :
    evalB fs (dzn Λ k (.mul x y)) e =
      ((List.range (k + 1)).map fun i =>
        (k.choose i : ℝ) * (evalB fs (dzn Λ i x) e * evalB fs (dzn Λ (k - i) y) e)).sum := by
  induction k generalizing x y with
  | zero =>
    show evalB fs x e * evalB fs y e = _
    simp [dzn_zero]
  | succ k ih =>
    have h1 : evalB fs (dzn Λ (k + 1) (.mul x y)) e =
        evalB fs (dzn Λ k (.mul (dz Λ x) y)) e + evalB fs (dzn Λ k (.mul x (dz Λ y))) e :=
      evalB_dzn_add fs Λ e k (.mul (dz Λ x) y) (.mul x (dz Λ y))
    rw [h1, ih (dz Λ x) y, ih x (dz Λ y)]
    -- abbreviations for the two sequences of values
    set a : ℕ → ℝ := fun i => evalB fs (dzn Λ i x) e with ha
    set b : ℕ → ℝ := fun i => evalB fs (dzn Λ i y) e with hb
    have e1 : ((List.range (k + 1)).map fun i =>
        (k.choose i : ℝ) * (evalB fs (dzn Λ i (dz Λ x)) e * evalB fs (dzn Λ (k - i) y) e)) =
        (List.range (k + 1)).map fun i => (k.choose i : ℝ) * (a (i + 1) * b (k - i)) := rfl
    have e2 : ((List.range (k + 1)).map fun i =>
        (k.choose i : ℝ) * (evalB fs (dzn Λ i x) e * evalB fs (dzn Λ (k - i) (dz Λ y)) e)) =
        (List.range (k + 1)).map fun i => (k.choose i : ℝ) * (a i * b (k - i + 1)) := rfl
    have e3 : ((List.range (k + 1 + 1)).map fun i => ((k + 1).choose i : ℝ) *
        (evalB fs (dzn Λ i x) e * evalB fs (dzn Λ (k + 1 - i) y) e)) =
        (List.range (k + 1 + 1)).map fun i => ((k + 1).choose i : ℝ) * (a i * b (k + 1 - i)) :=
      rfl
    rw [e1, e2, e3]
    -- pass to sums over `Finset.range`
    have toF : ∀ (n : ℕ) (f : ℕ → ℝ), ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
      intro n f
      induction n with
      | zero => simp
      | succ n ihn => rw [List.sum_range_succ, Finset.sum_range_succ, ihn]
    rw [toF, toF, toF]
    -- the Pascal rearrangement
    have hS2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (a i * b (k - i + 1)) =
        a 0 * b (k + 1) +
          ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * (a (i + 1) * b (k - i)) := by
      rw [Finset.sum_range_succ']
      have hterm : ∀ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * (a (i + 1) * b (k - (i + 1) + 1)) =
          (k.choose (i + 1) : ℝ) * (a (i + 1) * b (k - i)) := by
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have : k - (i + 1) + 1 = k - i := by omega
        rw [this]
      rw [Finset.sum_congr rfl hterm]
      simp
      ring
    have hT : ∑ i ∈ Finset.range (k + 1 + 1), ((k + 1).choose i : ℝ) * (a i * b (k + 1 - i)) =
        a 0 * b (k + 1) +
          ∑ i ∈ Finset.range (k + 1),
            ((k.choose i : ℝ) + (k.choose (i + 1) : ℝ)) * (a (i + 1) * b (k - i)) := by
      rw [Finset.sum_range_succ']
      have hterm : ∀ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℝ) * (a (i + 1) * b (k + 1 - (i + 1))) =
          ((k.choose i : ℝ) + (k.choose (i + 1) : ℝ)) * (a (i + 1) * b (k - i)) := by
        intro i _
        have h1 : k + 1 - (i + 1) = k - i := by omega
        rw [h1, Nat.choose_succ_succ]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm]
      simp
      ring
    have hlast : ∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * (a (i + 1) * b (k - i)) =
        ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * (a (i + 1) * b (k - i)) := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self]
      simp
    rw [hS2, hT]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hlast]
    ring

/-- A constant factor passes through the iterated derivation. -/
theorem evalB_dzn_cst_mul (k : ℕ) (c : ℤ) (x : IExpr) :
    evalB fs (dzn Λ k (.mul (.cst c) x)) e = (c : ℝ) * evalB fs (dzn Λ k x) e := by
  induction k generalizing c x with
  | zero => rfl
  | succ k ih =>
    have h1 : evalB fs (dzn Λ (k + 1) (.mul (.cst c) x)) e =
        evalB fs (dzn Λ k (.mul (.cst 0) x)) e + evalB fs (dzn Λ k (.mul (.cst c) (dz Λ x))) e :=
      evalB_dzn_add fs Λ e k (.mul (.cst 0) x) (.mul (.cst c) (dz Λ x))
    rw [h1, ih 0 x, ih c (dz Λ x)]
    show ((0 : ℤ) : ℝ) * _ + _ = (c : ℝ) * evalB fs (dzn Λ k (dz Λ x)) e
    rw [Int.cast_zero, zero_mul, zero_add]

end IExpr

/-! ## Jets -/

namespace QI

/-- The interval scaled by a nonnegative rational. -/
def scale (c : ℚ) (I : QI) : QI := ⟨c * I.lo, c * I.hi⟩

theorem mem_scale {c : ℚ} (hc : 0 ≤ c) {I : QI} {v : ℝ} (h : I.Mem v) :
    (I.scale c).Mem ((c : ℝ) * v) := by
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  refine ⟨?_, ?_⟩
  · show ((c * I.lo : ℚ) : ℝ) ≤ (c : ℝ) * v
    rw [Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left h.1 hc'
  · show (c : ℝ) * v ≤ ((c * I.hi : ℚ) : ℝ)
    rw [Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left h.2 hc'

end QI

/-- The jet `J` encloses the expression `x` and its first `n` derivations. -/
def JMem (Λ : ℕ) (fs : List (ℝ → ℝ)) (e : NEnv) (n : ℕ) (J : List QI) (x : IExpr) : Prop :=
  ∀ k, k ≤ n → (J.getD k QI.zero).Mem (IExpr.evalB fs (IExpr.dzn Λ k x) e)

/-- The constant jet. -/
def jconst (n : ℕ) (I : QI) : List QI := I :: List.replicate n QI.zero

def jadd (n : ℕ) (a b : List QI) : List QI :=
  (List.range (n + 1)).map fun k => (a.getD k QI.zero).add (b.getD k QI.zero)

def jsub (n : ℕ) (a b : List QI) : List QI :=
  (List.range (n + 1)).map fun k => (a.getD k QI.zero).sub (b.getD k QI.zero)

/-- The interval sum of a list. -/
def qsum : List QI → QI
  | [] => QI.zero
  | I :: Is => I.add (qsum Is)

/-- The entry `k` of the Leibniz product. -/
def leib (a b : List QI) (k : ℕ) : QI :=
  qsum ((List.range (k + 1)).map fun i =>
    ((a.getD i QI.zero).mul (b.getD (k - i) QI.zero)).scale (k.choose i))

def jmul (n : ℕ) (a b : List QI) : List QI := (List.range (n + 1)).map fun k => leib a b k

theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n k : ℕ} (h : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem mem_qsum : ∀ (Is : List QI) (vs : List ℝ), List.Forall₂ QI.Mem Is vs →
    (qsum Is).Mem vs.sum
  | [], _, h => by
    cases h
    simpa [qsum] using QI.mem_zero
  | I :: Is, _, h => by
    cases h with
    | cons h1 h2 =>
      simp only [qsum, List.sum_cons]
      exact QI.mem_add h1 (mem_qsum Is _ h2)

section JetArith

variable {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv} {n : ℕ}

theorem jMem_mono {m : ℕ} (hmn : m ≤ n) {J : List QI} {x : IExpr} (h : JMem Λ fs e n J x) :
    JMem Λ fs e m J x := fun k hk => h k (hk.trans hmn)

theorem getD_jconst_succ (n : ℕ) (I : QI) (k : ℕ) :
    (jconst n I).getD (k + 1) QI.zero = QI.zero := by
  rw [jconst, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem jMem_jconst_cst (c : ℤ) : JMem Λ fs e n (jconst n (QI.const c)) (.cst c) := by
  intro k _
  rcases k with _ | k
  · exact QI.mem_const c
  · rw [getD_jconst_succ, IExpr.evalB_dzn_cst]
    exact QI.mem_zero

theorem jMem_jconst_tat {I : QI} {i : ℕ} (h : I.Mem (fs.getD i (fun _ => 0) e.a)) :
    JMem Λ fs e n (jconst n I) (.tat i) := by
  intro k _
  rcases k with _ | k
  · exact h
  · rw [getD_jconst_succ, IExpr.evalB_dzn_tat]
    exact QI.mem_zero

theorem jMem_jadd {a b : List QI} {x y : IExpr} (ha : JMem Λ fs e n a x)
    (hb : JMem Λ fs e n b y) : JMem Λ fs e n (jadd n a b) (.add x y) := by
  intro k hk
  rw [jadd, getD_map_range _ _ (Nat.lt_succ_of_le hk), IExpr.evalB_dzn_add]
  exact QI.mem_add (ha k hk) (hb k hk)

theorem jMem_jsub {a b : List QI} {x y : IExpr} (ha : JMem Λ fs e n a x)
    (hb : JMem Λ fs e n b y) : JMem Λ fs e n (jsub n a b) (.sub x y) := by
  intro k hk
  rw [jsub, getD_map_range _ _ (Nat.lt_succ_of_le hk), IExpr.evalB_dzn_sub]
  exact QI.mem_sub (ha k hk) (hb k hk)

theorem mem_leib {a b : List QI} {x y : IExpr} (ha : JMem Λ fs e n a x)
    (hb : JMem Λ fs e n b y) {k : ℕ} (hk : k ≤ n) :
    (leib a b k).Mem (IExpr.evalB fs (IExpr.dzn Λ k (.mul x y)) e) := by
  rw [IExpr.evalB_dzn_mul, leib]
  refine mem_qsum _ _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun i hi => ?_
  have hik : i < k + 1 := List.mem_range.mp hi
  have h1 : i ≤ n := (Nat.lt_succ_iff.mp hik).trans hk
  have h2 : k - i ≤ n := (Nat.sub_le k i).trans hk
  have h := QI.mem_scale (c := (k.choose i : ℚ)) (Nat.cast_nonneg _)
    (QI.mem_mul (ha i h1) (hb (k - i) h2))
  rwa [Rat.cast_natCast] at h

theorem jMem_jmul {a b : List QI} {x y : IExpr} (ha : JMem Λ fs e n a x)
    (hb : JMem Λ fs e n b y) : JMem Λ fs e n (jmul n a b) (.mul x y) := by
  intro k hk
  rw [jmul, getD_map_range _ _ (Nat.lt_succ_of_le hk)]
  exact mem_leib ha hb hk

/-- The jet of the derivation is the shifted jet. -/
theorem jMem_drop {J : List QI} {x : IExpr} (j : ℕ) (h : JMem Λ fs e (n + j) J x) :
    JMem Λ fs e n (J.drop j) (IExpr.dzn Λ j x) := by
  intro k hk
  have h1 := h (k + j) (Nat.add_le_add_right hk j)
  rw [IExpr.dzn_add_apply] at h1
  have h2 : (J.drop j).getD k QI.zero = J.getD (k + j) QI.zero := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [Nat.add_comm]
  rw [h2]
  exact h1

/-- A jet extended by one entry. -/
theorem jMem_snoc {J : List QI} {x : IExpr} {I : QI} (hlen : J.length = n + 1)
    (h : JMem Λ fs e n J x)
    (hI : I.Mem (IExpr.evalB fs (IExpr.dzn Λ (n + 1) x) e)) :
    JMem Λ fs e (n + 1) (J ++ [I]) x := by
  intro k hk
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · have h2 : (J ++ [I]).getD k QI.zero = J.getD k QI.zero := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rw [h2]
    exact h k (Nat.lt_succ_iff.mp hlt)
  · have hk' : k = n + 1 := le_antisymm hk hge
    subst hk'
    have h2 : (J ++ [I]).getD (n + 1) QI.zero = I := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hlen]
      simp
    rw [h2]
    exact hI

end JetArith

/-! ## The jet of an expression from the jets of its leaves -/

/-- The jet of order `n` of an expression; `za` and `mo` are the jets of the atoms of the second
variable and of the monomials. -/
def jetE (n : ℕ) (E : IEnv) (za : ℕ → List QI) (mo : NMono → List QI) : IExpr → List QI
  | .zat i => za i
  | .tat i => jconst n (E.ta i)
  | .cst c => jconst n (QI.const c)
  | .mono m => mo m
  | .add x y => jadd n (jetE n E za mo x) (jetE n E za mo y)
  | .sub x y => jsub n (jetE n E za mo x) (jetE n E za mo y)
  | .mul x y => jmul n (jetE n E za mo x) (jetE n E za mo y)

theorem jMem_jetE {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv} {n : ℕ} {E : IEnv}
    (hE : E.Sound fs e) {za : ℕ → List QI} {mo : NMono → List QI}
    (hza : ∀ i, JMem Λ fs e n (za i) (.zat i)) (hmo : ∀ m, JMem Λ fs e n (mo m) (.mono m)) :
    ∀ x : IExpr, JMem Λ fs e n (jetE n E za mo x) x
  | .zat i => hza i
  | .tat i => jMem_jconst_tat (hE.2.1 i)
  | .cst c => jMem_jconst_cst c
  | .mono m => hmo m
  | .add x y => jMem_jadd (jMem_jetE hE hza hmo x) (jMem_jetE hE hza hmo y)
  | .sub x y => jMem_jsub (jMem_jetE hE hza hmo x) (jMem_jetE hE hza hmo y)
  | .mul x y => jMem_jmul (jMem_jetE hE hza hmo x) (jMem_jetE hE hza hmo y)

/-! ## The jet run of a program -/

namespace ISLP

/-- One instruction on jets of order `n`. -/
def stepJN (n : ℕ) (E : IEnv) (za : ℕ → List QI) (mo : NMono → List QI)
    (regs : List (List QI)) : IInstr → List QI
  | .zat i => za i
  | .tat i => jconst n (E.ta i)
  | .cst c => jconst n (QI.const c)
  | .mono m => mo m
  | .add i j => jadd n (regs.getD i []) (regs.getD j [])
  | .sub i j => jsub n (regs.getD i []) (regs.getD j [])
  | .mul i j => jmul n (regs.getD i []) (regs.getD j [])

def runJN (n : ℕ) (E : IEnv) (za : ℕ → List QI) (mo : NMono → List QI) :
    List IInstr → List (List QI) → List (List QI)
  | [], regs => regs
  | ins :: rest, regs => runJN n E za mo rest (regs ++ [stepJN n E za mo regs ins])

variable {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv} {n : ℕ} {E : IEnv} {za : ℕ → List QI}
  {mo : NMono → List QI}

theorem jMem_nil : JMem Λ fs e n [] (.cst 0) := by
  intro k _
  have hv : IExpr.evalB fs (IExpr.dzn Λ k (.cst 0)) e = 0 := by
    rcases k with _ | k
    · show ((0 : ℤ) : ℝ) = 0
      exact Int.cast_zero
    · exact IExpr.evalB_dzn_cst fs Λ e k 0
  rw [hv]
  simpa using QI.mem_zero

theorem mem_stepJN (hE : E.Sound fs e) (hza : ∀ i, JMem Λ fs e n (za i) (.zat i))
    (hmo : ∀ m, JMem Λ fs e n (mo m) (.mono m)) {regs : List (List QI)} {xs : List IExpr}
    (hk : ∀ k, JMem Λ fs e n (regs.getD k []) (xs.getD k (.cst 0))) (ins : IInstr) :
    JMem Λ fs e n (stepJN n E za mo regs ins) (stepExpr xs ins) := by
  cases ins with
  | zat i => exact hza i
  | tat i => exact jMem_jconst_tat (hE.2.1 i)
  | cst c => exact jMem_jconst_cst c
  | mono m => exact hmo m
  | add i j => exact jMem_jadd (hk i) (hk j)
  | sub i j => exact jMem_jsub (hk i) (hk j)
  | mul i j => exact jMem_jmul (hk i) (hk j)

theorem mem_runJN_aux (hE : E.Sound fs e) (hza : ∀ i, JMem Λ fs e n (za i) (.zat i))
    (hmo : ∀ m, JMem Λ fs e n (mo m) (.mono m)) :
    ∀ (prog : List IInstr) (regs : List (List QI)) (xs : List IExpr), xs.length = regs.length →
      (∀ k, JMem Λ fs e n (regs.getD k []) (xs.getD k (.cst 0))) →
      ∀ k, JMem Λ fs e n ((runJN n E za mo prog regs).getD k [])
        ((runExpr prog xs).getD k (.cst 0))
  | [], _, _, _, hk => hk
  | ins :: rest, regs, xs, hlen, hk => by
    simp only [runJN, runExpr]
    refine mem_runJN_aux hE hza hmo rest _ _ (by simp [hlen]) (fun k => ?_)
    rw [SLP.getD_append_single, SLP.getD_append_single, hlen]
    split_ifs with h1 h2
    · exact hk k
    · exact mem_stepJN hE hza hmo hk ins
    · exact jMem_nil

/-- **The jet run encloses the expressions that the program computes, with `n` derivations.** -/
theorem mem_runJN (hE : E.Sound fs e) (hza : ∀ i, JMem Λ fs e n (za i) (.zat i))
    (hmo : ∀ m, JMem Λ fs e n (mo m) (.mono m)) (prog : List IInstr) (k : ℕ) :
    JMem Λ fs e n ((runJN n E za mo prog []).getD k []) ((runExpr prog []).getD k (.cst 0)) :=
  mem_runJN_aux hE hza hmo prog [] [] rfl
    (fun k => by
      rw [List.getD_nil, List.getD_nil]
      exact jMem_nil) k

end ISLP

/-! ## The jets of the monomials -/

/-- The monomial `t̂`. -/
def thMono : NMono := ⟨0, 0, 0, 1, 0⟩

/-- The jet of a monomial: `∂ m = 12 e_b m + 12 e_t m t̂`. -/
def monoJet (E : IEnv) : ℕ → NMono → List QI
  | 0, m => [E.mono m]
  | n + 1, m =>
    monoJet E n m ++ [(((monoJet E n m).getD n QI.zero).scale (12 * m.eb)).add
      ((leib (monoJet E n m) (monoJet E n thMono) n).scale (12 * m.et))]

theorem monoJet_length (E : IEnv) : ∀ (n : ℕ) (m : NMono), (monoJet E n m).length = n + 1
  | 0, _ => rfl
  | n + 1, m => by
    rw [monoJet, List.length_append, monoJet_length E n m]
    rfl

theorem jMem_monoJet {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv} {E : IEnv} (hE : E.Sound fs e) :
    ∀ (n : ℕ) (m : NMono), JMem Λ fs e n (monoJet E n m) (.mono m)
  | 0, m => by
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact IEnv.mem_mono hE m
  | n + 1, m => by
    have ih := jMem_monoJet (Λ := Λ) hE n m
    have iht := jMem_monoJet (Λ := Λ) hE n thMono
    refine jMem_snoc (monoJet_length E n m) ih ?_
    -- `dzn (n+1) (mono m) = dzn n (12 e_b · mono m + 12 e_t · (mono m · t̂))`
    have hd : IExpr.dzn Λ (n + 1) (.mono m) =
        IExpr.dzn Λ n (.add (.mul (.cst (12 * m.eb)) (.mono m))
          (.mul (.cst (12 * m.et)) (.mul (.mono m) (.mono thMono)))) := rfl
    rw [hd, IExpr.evalB_dzn_add, IExpr.evalB_dzn_cst_mul, IExpr.evalB_dzn_cst_mul]
    have c1 : ((12 * (m.eb : ℚ) : ℚ) : ℝ) = ((12 * (m.eb : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have c2 : ((12 * (m.et : ℚ) : ℚ) : ℝ) = ((12 * (m.et : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have h1 := QI.mem_scale (c := 12 * (m.eb : ℚ)) (by positivity) (ih n le_rfl)
    have h2 := QI.mem_scale (c := 12 * (m.et : ℚ)) (by positivity) (mem_leib ih iht le_rfl)
    rw [c1] at h1
    rw [c2] at h2
    exact QI.mem_add h1 h2

/-! ## The jets of the atoms -/

/-- A program for the derivations `dz Λ (.zat i)` of the eight atoms, with shared
subexpressions: `V` is register `11`, `W` register `15`. -/
def atomDProg (Λ : ℕ) : List IInstr :=
  [.zat 0, .zat 2, .zat 3, .zat 4, .cst 1, .cst 16, .mul 5 0, .mul 4 2, .mul 7 2, .mul 8 2,
    .mul 9 2, .mul 6 10, .mul 4 1, .mul 12 1, .mul 13 1, .mul 14 1, .add 3 11, .sub 16 15, .cst 2,
    .mul 18 11, .sub 3 19, .sub 20 15, .mul 18 15, .add 16 22, .cst 3, .sub 23 24, .zat 1,
    .mul 26 17, .mul 1 21, .mul 2 25, .mul 4 3, .mul 30 3, .mul 4 11, .mul 32 11, .mul 11 15,
    .add 33 34, .mul 4 15, .mul 36 15, .add 35 37, .sub 31 38, .mul 18 39, .cst Λ, .mul 41 17,
    .mul 41 21, .mul 41 25, .cst 12, .mul 45 0]

/-- The registers of `atomDProg` that hold the derivations of the atoms `0, …, 7`. -/
def atomDOut : List ℕ := [46, 27, 28, 29, 40, 42, 43, 44]

theorem atomDProg_spec (Λ : ℕ) : ∀ i, i < 8 →
    (ISLP.runExpr (atomDProg Λ) []).getD (atomDOut.getD i 0) (.cst 0) = IExpr.dz Λ (.zat i) := by
  intro i hi
  interval_cases i <;> rfl

/-- The jets of the eight atoms of the second variable: the jet of order `n + 1` of an atom is
the jet of order `n` extended by the entry `n` of the jet of its derivation, rounded outward to
multiples of `2⁻ᵖ`. -/
def atomJets (Λ p : ℕ) (E : IEnv) : ℕ → List (List QI)
  | 0 => (List.range 8).map fun i => [E.za i]
  | n + 1 =>
    (List.range 8).map fun i =>
      (atomJets Λ p E n).getD i [] ++
        [(((ISLP.runJN n E (fun j => (atomJets Λ p E n).getD j []) (monoJet E n) (atomDProg Λ)
          []).getD (atomDOut.getD i 0) []).getD n QI.zero).round p]

theorem atomJets_length (Λ p : ℕ) (E : IEnv) :
    ∀ (n i : ℕ), i < 8 → ((atomJets Λ p E n).getD i []).length = n + 1
  | 0, i, hi => by
    rw [atomJets, getD_map_range _ _ hi]
    rfl
  | n + 1, i, hi => by
    rw [atomJets, getD_map_range _ _ hi, List.length_append, atomJets_length Λ p E n i hi]
    rfl

/-- The jets of the atoms are sound: beyond the eighth atom the atoms and their derivations
vanish. -/
theorem jMem_atomJets {Λ p : ℕ} {e : NEnv} {E : IEnv} (hE : E.Sound (kernelAtoms Λ ++ []) e) :
    ∀ (n i : ℕ), JMem Λ (kernelAtoms Λ ++ []) e n ((atomJets Λ p E n).getD i []) (.zat i) := by
  -- the atoms beyond the eighth
  have hfar : ∀ (n i : ℕ), 8 ≤ i →
      JMem Λ (kernelAtoms Λ ++ []) e n ((atomJets Λ p E n).getD i []) (.zat i) := by
    intro n i hi k _
    have hnil : (atomJets Λ p E n).getD i [] = [] := by
      have hlen : (atomJets Λ p E n).length = 8 := by
        cases n <;> simp [atomJets]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hnil]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 := ⟨i - 8, by omega⟩
    have hval : IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ k (.zat (j + 8))) e = 0 := by
      rcases k with _ | k
      · rfl
      · exact IExpr.evalB_dzn_cst _ Λ e k 0
    rw [hval]
    simpa using QI.mem_zero
  intro n
  induction n with
  | zero =>
    intro i
    rcases Nat.lt_or_ge i 8 with hi | hi
    · intro k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [atomJets, getD_map_range _ _ hi]
      exact hE.1 i
    · exact hfar 0 i hi
  | succ n ih =>
    intro i
    rcases Nat.lt_or_ge i 8 with hi | hi
    · rw [atomJets, getD_map_range _ _ hi]
      refine jMem_snoc (atomJets_length Λ p E n i hi) (ih i) ?_
      have hj := ISLP.mem_runJN (Λ := Λ) hE ih (jMem_monoJet hE n) (atomDProg Λ)
        (atomDOut.getD i 0) n le_rfl
      rw [atomDProg_spec Λ i hi] at hj
      exact QI.mem_round p hj
    · exact hfar (n + 1) i hi

end E8Leech.Kron
