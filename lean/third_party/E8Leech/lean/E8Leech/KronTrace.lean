import E8Leech.KronExpr

/-!
# Checking a model run register by register

The kernel keeps every intermediate value of one reduction until the declaration is finished.
A long straight-line program is therefore not run in one piece. Instead the list of all register
values is written down (`regs`), and the kernel checks in separate declarations that each
register is the result of its instruction applied to the earlier registers.

* `ISLP.StepOK`: register `i` is correct, given the earlier ones.
* `ISLP.stepsOKb`: a decidable check of a range of registers.
* `ISLP.RangeOK.of_check`, `ISLP.RangeOK.trans`: ranges are glued.
* `ISLP.runMDD_eq_of_rangeOK`: a fully checked register file is the result of the run.
-/

namespace E8Leech.Kron.ISLP

variable (Bx : Bounds) (D Dcap : ℕ) (At : List MDD)

/-- Register `i` of the claimed file is the result of instruction `i` on the earlier ones. -/
def StepOK (prog : List IInstr) (regs : List MDD) (i : ℕ) : Prop :=
  stepMDD Bx D Dcap At (regs.take i) (prog.getD i (.cst 0)) = regs.getD i MDD.zero

instance (prog : List IInstr) (regs : List MDD) (i : ℕ) :
    Decidable (StepOK Bx D Dcap At prog regs i) := by
  unfold StepOK
  infer_instance

/-- The registers `lo, …, lo + n − 1` are correct. -/
def stepsOKb (prog : List IInstr) (regs : List MDD) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => decide (StepOK Bx D Dcap At prog regs lo) &&
      stepsOKb prog regs (lo + 1) n

/-- The registers `lo ≤ i < hi` are correct. -/
def RangeOK (prog : List IInstr) (regs : List MDD) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → StepOK Bx D Dcap At prog regs i

variable {Bx D Dcap At}

theorem RangeOK.of_check {prog : List IInstr} {regs : List MDD} :
    ∀ (n lo hi : ℕ), stepsOKb Bx D Dcap At prog regs lo n = true → lo + n = hi →
      RangeOK Bx D Dcap At prog regs lo hi
  | 0, lo, hi, _, hhi => fun i h1 h2 => by omega
  | n + 1, lo, hi, h, hhi => fun i h1 h2 => by
    simp only [stepsOKb, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · rw [← heq]
      exact h.1
    · exact RangeOK.of_check n (lo + 1) hi h.2 (by omega) i hlt h2

theorem RangeOK.trans {prog : List IInstr} {regs : List MDD} {lo mid hi : ℕ}
    (h1 : RangeOK Bx D Dcap At prog regs lo mid) (h2 : RangeOK Bx D Dcap At prog regs mid hi) :
    RangeOK Bx D Dcap At prog regs lo hi := fun i hlo hhi => by
  rcases Nat.lt_or_ge i mid with h | h
  · exact h1 i hlo h
  · exact h2 i h hhi

/-- **A checked register file is the result of the run.** -/
theorem runMDD_eq_of_rangeOK {prog : List IInstr} {regs : List MDD}
    (hlen : regs.length = prog.length)
    (h : RangeOK Bx D Dcap At prog regs 0 prog.length) :
    runMDD Bx D Dcap At prog [] = regs := by
  have key : ∀ (p2 p1 : List IInstr), p1 ++ p2 = prog →
      runMDD Bx D Dcap At p2 (regs.take p1.length) = regs := by
    intro p2
    induction p2 with
    | nil =>
      intro p1 hp
      rw [List.append_nil] at hp
      simp only [runMDD]
      rw [hp, ← hlen, List.take_length]
    | cons ins rest ih =>
      intro p1 hp
      have hi : p1.length < prog.length := by
        rw [← hp, List.length_append, List.length_cons]
        omega
      have hs := h p1.length (Nat.zero_le _) hi
      unfold StepOK at hs
      have hins : prog.getD p1.length (.cst 0) = ins := by
        rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      rw [hins] at hs
      have hlt : p1.length < regs.length := by
        rw [hlen]
        exact hi
      have hreg : regs.take p1.length ++ [regs.getD p1.length MDD.zero] =
          regs.take (p1 ++ [ins]).length := by
        rw [List.length_append, List.length_singleton, List.take_add_one,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        rfl
      simp only [runMDD]
      rw [hs, hreg]
      exact ih (p1 ++ [ins]) (by rw [List.append_assoc]; exact hp)
  simpa using key prog [] rfl

end E8Leech.Kron.ISLP
