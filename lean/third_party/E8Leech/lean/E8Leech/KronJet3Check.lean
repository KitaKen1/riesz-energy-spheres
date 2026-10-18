import E8Leech.KronJet3

/-!
# Checking the output of the jet transformation in pieces

The kernel cannot run `ISLP.tr3` on a long program in one declaration: the accumulator is a left
nested concatenation whose length is taken at every instruction. Here the transformed program is
written down and checked against the blocks instead, a range of instructions of the original
program at a time; the claimed program is only read from the front.

* `ISLP.tr3Chk`: the check of a range (decidable, linear in the length of the range).
* `ISLP.tr3Aux_of_chk`: a checked range is the transformation of the range.
* `ISLP.tr3Aux_append`: `tr3Aux` on a concatenation.
* `ISLP.tr3Aux_take_start`, `ISLP.tr3Aux_take_step`, `ISLP.tr3_of_take`: the transformation of
  the first `c` instructions, extended range by range, and the conclusion.
-/

namespace E8Leech.Kron.ISLP

/-- The claimed program `rest` (from the register `pos` on) consists of the blocks of the
instructions, and the positions of the jets are `outsF` at the end. -/
def tr3Chk (zleaf : ℕ → Block) :
    List IInstr → List ℕ → ℕ → List IInstr → List ℕ → Bool
  | [], outs, _, rest, outsF => decide (rest = [] ∧ outs = outsF)
  | ins :: p, outs, pos, rest, outsF =>
    decide (rest.take (blockOf zleaf outs ins).ts.length =
        (blockOf zleaf outs ins).ts.map (TInstr.reloc pos)) &&
      tr3Chk zleaf p (outs ++ [pos + (blockOf zleaf outs ins).pre])
        (pos + (blockOf zleaf outs ins).ts.length)
        (rest.drop (blockOf zleaf outs ins).ts.length) outsF

/-- A checked range is the transformation of the range. -/
theorem tr3Aux_of_chk (zleaf : ℕ → Block) :
    ∀ (p : List IInstr) (outs : List ℕ) (acc rest : List IInstr) (outsF : List ℕ),
      tr3Chk zleaf p outs acc.length rest outsF = true →
        tr3Aux zleaf p outs acc = (acc ++ rest, outsF)
  | [], outs, acc, rest, outsF, h => by
    simp only [tr3Chk, decide_eq_true_eq] at h
    rw [tr3Aux, h.1, h.2, List.append_nil]
  | ins :: p, outs, acc, rest, outsF, h => by
    simp only [tr3Chk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hlen : (acc ++ (blockOf zleaf outs ins).ts.map (TInstr.reloc acc.length)).length =
        acc.length + (blockOf zleaf outs ins).ts.length := by
      rw [List.length_append, List.length_map]
    have hrec := tr3Aux_of_chk zleaf p (outs ++ [acc.length + (blockOf zleaf outs ins).pre])
      (acc ++ (blockOf zleaf outs ins).ts.map (TInstr.reloc acc.length))
      (rest.drop (blockOf zleaf outs ins).ts.length) outsF (by rw [hlen]; exact h.2)
    rw [tr3Aux, hrec, List.append_assoc, ← h.1, List.take_append_drop]

/-- `tr3Aux` on a concatenation. -/
theorem tr3Aux_append (zleaf : ℕ → Block) :
    ∀ (p q : List IInstr) (outs : List ℕ) (acc : List IInstr),
      tr3Aux zleaf (p ++ q) outs acc =
        tr3Aux zleaf q (tr3Aux zleaf p outs acc).2 (tr3Aux zleaf p outs acc).1
  | [], _, _, _ => rfl
  | ins :: p, q, outs, acc => by
    rw [List.cons_append, tr3Aux, tr3Aux, tr3Aux_append zleaf p q]

/-- The transformation of no instruction: the prelude. -/
theorem tr3Aux_take_start {zleaf : ℕ → Block} {prog0 prog : List IInstr}
    (h : prog.take 5 = prelude3) :
    tr3Aux zleaf (prog0.take 0) [] prelude3 = (prog.take 5, []) := by
  rw [List.take_zero, tr3Aux, h]

/-- **One range of the check.** The transformation of the first `c + n` instructions from the
one of the first `c`. -/
theorem tr3Aux_take_step {zleaf : ℕ → Block} {prog0 prog : List IInstr} {outs outs' : List ℕ}
    {c n s m c' s' : ℕ}
    (hprev : tr3Aux zleaf (prog0.take c) [] prelude3 = (prog.take s, outs))
    (hs : s ≤ prog.length)
    (hchk : tr3Chk zleaf ((prog0.drop c).take n) outs s ((prog.drop s).take m) outs' = true)
    (hc : c + n = c') (hsm : s + m = s') :
    tr3Aux zleaf (prog0.take c') [] prelude3 = (prog.take s', outs') := by
  subst hc hsm
  have hlen : (prog.take s).length = s := by rw [List.length_take, Nat.min_eq_left hs]
  rw [List.take_add, tr3Aux_append, hprev]
  show tr3Aux zleaf ((prog0.drop c).take n) outs (prog.take s) = _
  rw [tr3Aux_of_chk zleaf _ outs (prog.take s) ((prog.drop s).take m) outs'
    (by rw [hlen]; exact hchk), List.take_add]

/-- **The checked transformation.** -/
theorem tr3_of_take {zleaf : ℕ → Block} {prog0 prog : List IInstr} {outs : List ℕ} {c s : ℕ}
    (h : tr3Aux zleaf (prog0.take c) [] prelude3 = (prog.take s, outs))
    (hc : prog0.length ≤ c) (hs : prog.length ≤ s) : tr3 zleaf prog0 = (prog, outs) := by
  rw [List.take_of_length_le hc, List.take_of_length_le hs] at h
  exact h

end E8Leech.Kron.ISLP
