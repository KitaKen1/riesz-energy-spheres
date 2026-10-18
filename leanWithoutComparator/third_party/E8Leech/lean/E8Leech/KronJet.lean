import E8Leech.KronCorner
import E8Leech.KronInterval

/-!
# Interval jets of straight-line programs

The second-derivative expressions `hOf x = ∂²x − 48 t̂ ∂x + 288 t̂² x` of the corner certificate are
far too large as expression trees (the product rule doubles a tree at every factor). Instead of
expanding them, a program is run on jets: every register carries enclosures of its value, of its
derivation `dz` and of its second derivation. Sums and products follow the Leibniz rule, and only
the leaves need the derivation of an expression.

* `IExpr.zOnly_dz`, `IExpr.zOnly_hOf`: the derivation keeps expressions on the `z`-side.
* `IExpr.evalI`, `IExpr.mem_evalI`: interval evaluation of an expression tree.
* `QJ`, `QJ.Mem`, `QJ.mem_add`, `QJ.mem_sub`, `QJ.mem_mul`, `QJ.mem_ofExpr`: jets.
* `QJ.hOf`, `QJ.mem_hOf`: the enclosure of `hOf x` from the jet of `x`.
* `ISLP.runJ`, `ISLP.mem_runJ`: the jet run of a program encloses the expressions that the program
  computes together with their first two derivations.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

namespace IExpr

/-! ## The derivation keeps expressions on the `z`-side -/

theorem zOnly_dz (Λ : ℕ) : ∀ x : IExpr, x.zOnly = true → (dz Λ x).zOnly = true
  | .zat i, _ => by
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> rfl
  | .tat _, h => by simp [zOnly] at h
  | .cst _, _ => rfl
  | .mono m, h => by
    have h' : (m.ea == 0 && m.eu == 0) = true := h
    have e : (dz Λ (.mono m)).zOnly =
        ((true && (m.ea == 0 && m.eu == 0)) && (true && ((m.ea == 0 && m.eu == 0) && true))) :=
      rfl
    exact e.trans (by simp only [h', Bool.and_self])
  | .add x y, h => by
    have h' : (x.zOnly && y.zOnly) = true := h
    rw [Bool.and_eq_true] at h'
    have hx := zOnly_dz Λ x h'.1
    have hy := zOnly_dz Λ y h'.2
    have e : (dz Λ (.add x y)).zOnly = ((dz Λ x).zOnly && (dz Λ y).zOnly) := rfl
    exact e.trans (by simp only [hx, hy, Bool.and_self])
  | .sub x y, h => by
    have h' : (x.zOnly && y.zOnly) = true := h
    rw [Bool.and_eq_true] at h'
    have hx := zOnly_dz Λ x h'.1
    have hy := zOnly_dz Λ y h'.2
    have e : (dz Λ (.sub x y)).zOnly = ((dz Λ x).zOnly && (dz Λ y).zOnly) := rfl
    exact e.trans (by simp only [hx, hy, Bool.and_self])
  | .mul x y, h => by
    have h' : (x.zOnly && y.zOnly) = true := h
    rw [Bool.and_eq_true] at h'
    have hx := zOnly_dz Λ x h'.1
    have hy := zOnly_dz Λ y h'.2
    have e : (dz Λ (.mul x y)).zOnly =
        (((dz Λ x).zOnly && y.zOnly) && (x.zOnly && (dz Λ y).zOnly)) := rfl
    exact e.trans (by simp only [hx, hy, h'.1, h'.2, Bool.and_self])

theorem zOnly_hOf (Λ : ℕ) {x : IExpr} (h : x.zOnly = true) : (hOf Λ x).zOnly = true := by
  have h1 := zOnly_dz Λ x h
  have h2 := zOnly_dz Λ _ h1
  have e : (hOf Λ x).zOnly =
      (((dz Λ (dz Λ x)).zOnly && (true && (dz Λ x).zOnly)) && (true && x.zOnly)) := rfl
  exact e.trans (by simp only [h, h1, h2, Bool.and_self])

/-! ## Interval evaluation of a tree -/

/-- The enclosure of an expression tree, by interval arithmetic along the tree. -/
def evalI (E : IEnv) : IExpr → QI
  | .zat i => E.za i
  | .tat i => E.ta i
  | .cst c => QI.const c
  | .mono m => E.mono m
  | .add x y => (evalI E x).add (evalI E y)
  | .sub x y => (evalI E x).sub (evalI E y)
  | .mul x y => (evalI E x).mul (evalI E y)

theorem mem_evalI {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e) :
    ∀ x : IExpr, (evalI E x).Mem (evalB fs x e)
  | .zat i => hE.1 i
  | .tat i => hE.2.1 i
  | .cst c => QI.mem_const c
  | .mono m => IEnv.mem_mono hE m
  | .add x y => QI.mem_add (mem_evalI hE x) (mem_evalI hE y)
  | .sub x y => QI.mem_sub (mem_evalI hE x) (mem_evalI hE y)
  | .mul x y => QI.mem_mul (mem_evalI hE x) (mem_evalI hE y)

end IExpr

/-! ## Jets -/

/-- An interval jet: enclosures of a value, of its derivation and of its second derivation. -/
structure QJ where
  v : QI
  d : QI
  h : QI

namespace QJ

def zero : QJ := ⟨QI.zero, QI.zero, QI.zero⟩

def add (a b : QJ) : QJ := ⟨a.v.add b.v, a.d.add b.d, a.h.add b.h⟩

def sub (a b : QJ) : QJ := ⟨a.v.sub b.v, a.d.sub b.d, a.h.sub b.h⟩

/-- The Leibniz rule, in the order of the terms of `dz (dz (x * y))`. -/
def mul (a b : QJ) : QJ :=
  ⟨a.v.mul b.v, (a.d.mul b.v).add (a.v.mul b.d),
    ((a.h.mul b.v).add (a.d.mul b.d)).add ((a.d.mul b.d).add (a.v.mul b.h))⟩

/-- The jet of an expression, by interval evaluation of the expression and of its derivations.
Meant for the leaves of a program. -/
def ofExpr (Λ : ℕ) (E : IEnv) (x : IExpr) : QJ :=
  ⟨IExpr.evalI E x, IExpr.evalI E (IExpr.dz Λ x), IExpr.evalI E (IExpr.dz Λ (IExpr.dz Λ x))⟩

/-- The enclosure of `hOf x = ∂²x − 48 t̂ ∂x + 288 t̂² x` from the jet of `x`. -/
def hOf (E : IEnv) (J : QJ) : QI :=
  (J.h.sub ((IExpr.evalI E (48 * thE)).mul J.d)).add ((IExpr.evalI E (288 * thE ^ 2)).mul J.v)

/-- The jet encloses the expression and its first two derivations. -/
def Mem (Λ : ℕ) (fs : List (ℝ → ℝ)) (e : NEnv) (J : QJ) (x : IExpr) : Prop :=
  J.v.Mem (IExpr.evalB fs x e) ∧ J.d.Mem (IExpr.evalB fs (IExpr.dz Λ x) e) ∧
    J.h.Mem (IExpr.evalB fs (IExpr.dz Λ (IExpr.dz Λ x)) e)

variable {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv}

theorem mem_zero (Λ : ℕ) (fs : List (ℝ → ℝ)) (e : NEnv) : zero.Mem Λ fs e (.cst 0) := by
  have h : IExpr.evalB fs (.cst 0) e = 0 := by
    show ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  have m : QI.zero.Mem (IExpr.evalB fs (.cst 0) e) := by
    rw [h]
    exact QI.mem_zero
  exact ⟨m, m, m⟩

theorem mem_add {a b : QJ} {x y : IExpr} (ha : a.Mem Λ fs e x) (hb : b.Mem Λ fs e y) :
    (a.add b).Mem Λ fs e (.add x y) :=
  ⟨QI.mem_add ha.1 hb.1, QI.mem_add ha.2.1 hb.2.1, QI.mem_add ha.2.2 hb.2.2⟩

theorem mem_sub {a b : QJ} {x y : IExpr} (ha : a.Mem Λ fs e x) (hb : b.Mem Λ fs e y) :
    (a.sub b).Mem Λ fs e (.sub x y) :=
  ⟨QI.mem_sub ha.1 hb.1, QI.mem_sub ha.2.1 hb.2.1, QI.mem_sub ha.2.2 hb.2.2⟩

theorem mem_mul {a b : QJ} {x y : IExpr} (ha : a.Mem Λ fs e x) (hb : b.Mem Λ fs e y) :
    (a.mul b).Mem Λ fs e (.mul x y) :=
  ⟨QI.mem_mul ha.1 hb.1, QI.mem_add (QI.mem_mul ha.2.1 hb.1) (QI.mem_mul ha.1 hb.2.1),
    QI.mem_add (QI.mem_add (QI.mem_mul ha.2.2 hb.1) (QI.mem_mul ha.2.1 hb.2.1))
      (QI.mem_add (QI.mem_mul ha.2.1 hb.2.1) (QI.mem_mul ha.1 hb.2.2))⟩

theorem mem_ofExpr {E : IEnv} (hE : E.Sound fs e) (Λ : ℕ) (x : IExpr) :
    (ofExpr Λ E x).Mem Λ fs e x :=
  ⟨IExpr.mem_evalI hE _, IExpr.mem_evalI hE _, IExpr.mem_evalI hE _⟩

theorem mem_hOf {E : IEnv} (hE : E.Sound fs e) {J : QJ} {x : IExpr} (hJ : J.Mem Λ fs e x) :
    (J.hOf E).Mem (IExpr.evalB fs (IExpr.hOf Λ x) e) := by
  show ((J.h.sub ((IExpr.evalI E (48 * thE)).mul J.d)).add
      ((IExpr.evalI E (288 * thE ^ 2)).mul J.v)).Mem
    (IExpr.evalB fs (IExpr.dz Λ (IExpr.dz Λ x)) e -
      IExpr.evalB fs (48 * thE) e * IExpr.evalB fs (IExpr.dz Λ x) e +
      IExpr.evalB fs (288 * thE ^ 2) e * IExpr.evalB fs x e)
  exact QI.mem_add (QI.mem_sub hJ.2.2 (QI.mem_mul (IExpr.mem_evalI hE _) hJ.2.1))
    (QI.mem_mul (IExpr.mem_evalI hE _) hJ.1)

end QJ

/-! ## The jet run of a program -/

namespace ISLP

/-- One instruction on jets. -/
def stepJ (Λ : ℕ) (E : IEnv) (regs : List QJ) : IInstr → QJ
  | .zat i => QJ.ofExpr Λ E (.zat i)
  | .tat i => QJ.ofExpr Λ E (.tat i)
  | .cst c => QJ.ofExpr Λ E (.cst c)
  | .mono m => QJ.ofExpr Λ E (.mono m)
  | .add i j => (regs.getD i QJ.zero).add (regs.getD j QJ.zero)
  | .sub i j => (regs.getD i QJ.zero).sub (regs.getD j QJ.zero)
  | .mul i j => (regs.getD i QJ.zero).mul (regs.getD j QJ.zero)

def runJ (Λ : ℕ) (E : IEnv) : List IInstr → List QJ → List QJ
  | [], regs => regs
  | ins :: rest, regs => runJ Λ E rest (regs ++ [stepJ Λ E regs ins])

variable {Λ : ℕ} {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv}

theorem mem_stepJ (hE : E.Sound fs e) {regs : List QJ} {xs : List IExpr}
    (hk : ∀ k, (regs.getD k QJ.zero).Mem Λ fs e (xs.getD k (.cst 0))) (ins : IInstr) :
    (stepJ Λ E regs ins).Mem Λ fs e (stepExpr xs ins) := by
  cases ins with
  | zat i => exact QJ.mem_ofExpr hE Λ _
  | tat i => exact QJ.mem_ofExpr hE Λ _
  | cst c => exact QJ.mem_ofExpr hE Λ _
  | mono m => exact QJ.mem_ofExpr hE Λ _
  | add i j => exact QJ.mem_add (hk i) (hk j)
  | sub i j => exact QJ.mem_sub (hk i) (hk j)
  | mul i j => exact QJ.mem_mul (hk i) (hk j)

theorem mem_runJ_aux (hE : E.Sound fs e) :
    ∀ (prog : List IInstr) (regs : List QJ) (xs : List IExpr), xs.length = regs.length →
      (∀ k, (regs.getD k QJ.zero).Mem Λ fs e (xs.getD k (.cst 0))) →
      ∀ k, ((runJ Λ E prog regs).getD k QJ.zero).Mem Λ fs e ((runExpr prog xs).getD k (.cst 0))
  | [], _, _, _, hk => hk
  | ins :: rest, regs, xs, hlen, hk => by
    simp only [runJ, runExpr]
    refine mem_runJ_aux hE rest _ _ (by simp [hlen]) (fun k => ?_)
    rw [SLP.getD_append_single, SLP.getD_append_single, hlen]
    split_ifs with h1 h2
    · exact hk k
    · exact mem_stepJ hE hk ins
    · exact QJ.mem_zero Λ fs e

/-- **The jet run encloses the expressions that the program computes, with two derivations.** -/
theorem mem_runJ (hE : E.Sound fs e) (prog : List IInstr) (k : ℕ) :
    ((runJ Λ E prog []).getD k QJ.zero).Mem Λ fs e ((runExpr prog []).getD k (.cst 0)) :=
  mem_runJ_aux hE prog [] [] rfl
    (fun k => by
      rw [List.getD_nil, List.getD_nil]
      exact QJ.mem_zero Λ fs e) k

end ISLP

end E8Leech.Kron
