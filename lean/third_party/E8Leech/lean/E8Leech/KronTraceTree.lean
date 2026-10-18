import E8Leech.KronTrace

/-!
# Checking a model run with the registers in a binary tree

`ISLP.StepOK` reads the instruction, the operands and the result of a step from lists, and the
kernel walks a list cell by cell: a step at the register `i` costs about `i` reductions per access
(none of which is released before the end of the declaration). For a program of several thousand
instructions these walks cost more than the arithmetic. Here the program and the register file are
binary trees, read in logarithmically many reductions; the lists of `KronTrace` are *defined* as
the lists of entries of the trees.

* `BTree`, `BTree.get`, `BTree.toList`: the tree, its entries, the list of the first entries.
* `ISLP.stepsOKTb`: the decidable check of a range of registers on the trees.
* `ISLP.RangeOK.of_checkT`: a checked range is correct in the sense of `KronTrace`.
-/

namespace E8Leech.Kron

/-- A binary tree of values. -/
inductive BTree (α : Type) where
  | nil : BTree α
  | node (l : BTree α) (v : α) (r : BTree α) : BTree α

namespace BTree

variable {α : Type}

/-- The entry `i`: the root is the entry `0`; the left subtree holds the entries `2k + 1` and the
right subtree the entries `2k + 2`, at their positions `k`. Missing entries are `d`. -/
def get (d : α) : BTree α → ℕ → α
  | nil, _ => d
  | node l v r, i =>
    bif Nat.beq i 0 then v
    else bif Nat.beq (i % 2) 1 then l.get d (i / 2) else r.get d (i / 2 - 1)

/-- The list of the first `n` entries. -/
def toList (d : α) (T : BTree α) (n : ℕ) : List α := (List.range n).map (T.get d)

theorem length_toList (d : α) (T : BTree α) (n : ℕ) : (T.toList d n).length = n := by
  rw [toList, List.length_map, List.length_range]

theorem getD_toList (d : α) (T : BTree α) {n i : ℕ} (h : i < n) :
    (T.toList d n).getD i d = T.get d i := by
  rw [toList, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- An entry of an initial segment of the list. -/
theorem getD_take_toList (d : α) (T : BTree α) {n i a : ℕ} (hi : i ≤ n) (ha : a < i) :
    ((T.toList d n).take i).getD a d = T.get d a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ha, ← List.getD_eq_getElem?_getD,
    getD_toList d T (lt_of_lt_of_le ha hi)]

end BTree

namespace ISLP

variable (Bx : Bounds) (D Dcap : ℕ) (At : List MDD)

/-- The operands of an instruction are registers below `i`. -/
def opsLt (i : ℕ) : IInstr → Bool
  | .add a b => Nat.blt a i && Nat.blt b i
  | .sub a b => Nat.blt a i && Nat.blt b i
  | .mul a b => Nat.blt a i && Nat.blt b i
  | _ => true

/-- One instruction on the models of a register tree. -/
def stepMDDT (T : BTree MDD) : IInstr → MDD
  | .zat i => At.getD i MDD.zero
  | .tat i => MDD.tau (At.getD i MDD.zero).A
  | .cst c => MDD.tau (MTM.const c)
  | .mono m => MDD.tau (MTM.mono m 1)
  | .add i j => (T.get MDD.zero i).add (T.get MDD.zero j)
  | .sub i j => (T.get MDD.zero i).sub (T.get MDD.zero j)
  | .mul i j => MDD.mul Bx D Dcap (T.get MDD.zero i) (T.get MDD.zero j)

/-- The registers `lo, …, lo + n − 1` of the tree are correct, and their instructions read
earlier registers only. -/
def stepsOKTb (PT : BTree IInstr) (T : BTree MDD) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 =>
    (opsLt lo (PT.get (.cst 0) lo) &&
      decide (stepMDDT Bx D Dcap At T (PT.get (.cst 0) lo) = T.get MDD.zero lo)) &&
      stepsOKTb PT T (lo + 1) n

variable {Bx D Dcap At}

/-- On an initial segment that contains the operands, the step on the list is the step on the
tree. -/
theorem stepMDD_take_toList (T : BTree MDD) {N i : ℕ} (hi : i ≤ N) :
    ∀ ins : IInstr, opsLt i ins = true →
      stepMDD Bx D Dcap At ((T.toList MDD.zero N).take i) ins = stepMDDT Bx D Dcap At T ins
  | .zat _, _ => rfl
  | .tat _, _ => rfl
  | .cst _, _ => rfl
  | .mono _, _ => rfl
  | .add a b, h => by
    simp only [opsLt, Bool.and_eq_true, Nat.blt_eq] at h
    simp only [stepMDD, stepMDDT, BTree.getD_take_toList MDD.zero T hi h.1,
      BTree.getD_take_toList MDD.zero T hi h.2]
  | .sub a b, h => by
    simp only [opsLt, Bool.and_eq_true, Nat.blt_eq] at h
    simp only [stepMDD, stepMDDT, BTree.getD_take_toList MDD.zero T hi h.1,
      BTree.getD_take_toList MDD.zero T hi h.2]
  | .mul a b, h => by
    simp only [opsLt, Bool.and_eq_true, Nat.blt_eq] at h
    simp only [stepMDD, stepMDDT, BTree.getD_take_toList MDD.zero T hi h.1,
      BTree.getD_take_toList MDD.zero T hi h.2]

/-- A step that is correct on the trees is correct on the lists of their entries. -/
theorem StepOK.of_tree {PT : BTree IInstr} {T : BTree MDD} {N i : ℕ} (hi : i < N)
    (hops : opsLt i (PT.get (.cst 0) i) = true)
    (h : stepMDDT Bx D Dcap At T (PT.get (.cst 0) i) = T.get MDD.zero i) :
    StepOK Bx D Dcap At (PT.toList (.cst 0) N) (T.toList MDD.zero N) i := by
  unfold StepOK
  rw [BTree.getD_toList _ _ hi, BTree.getD_toList _ _ hi, stepMDD_take_toList T hi.le _ hops, h]

/-- **A checked range of the trees is a correct range of the lists.** -/
theorem RangeOK.of_checkT {PT : BTree IInstr} {T : BTree MDD} {N : ℕ} :
    ∀ (n lo hi : ℕ), stepsOKTb Bx D Dcap At PT T lo n = true → lo + n = hi → hi ≤ N →
      RangeOK Bx D Dcap At (PT.toList (.cst 0) N) (T.toList MDD.zero N) lo hi
  | 0, lo, hi, _, hhi, _ => fun i h1 h2 => by omega
  | n + 1, lo, hi, h, hhi, hN => fun i h1 h2 => by
    simp only [stepsOKTb, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · rw [← heq]
      exact StepOK.of_tree (by omega) h.1.1 h.1.2
    · exact RangeOK.of_checkT n (lo + 1) hi h.2 (by omega) hN i hlt h2

end ISLP

end E8Leech.Kron
