import E8Leech.CKMRVKExpr

/-!
# Straight-line programs over the generators

A program is a list of instructions; instruction `k` defines register `k` from the generators,
constants, monomials or two earlier registers. Running a program with divided-difference Taylor
models shares common subexpressions (unlike evaluating a tree), which matters because the kernel
evaluates every product. `SLP.approx_run`: every register approximates its real meaning.
-/

namespace E8Leech.Taylor

open scoped Real

inductive Instr
  | zgen (i : Fin 5)
  | tgen (i : Fin 5)
  | zlog (j : Fin 3)
  | tlog (j : Fin 3)
  | cst (q : ℚ)
  | mono (m : Mono)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)

namespace SLP

def dd0 : DD := ⟨TM.zero, TM.zero, TM.zero⟩

/-- One instruction on divided-difference models. -/
def stepDD (B : Box) (Dg : ℕ) (G : Fin 5 → DD) (L : Fin 3 → DD) (regs : List DD) : Instr → DD
  | .zgen i => G i
  | .tgen i => DD.tau (G i).A
  | .zlog j => L j
  | .tlog j => DD.tau (L j).A
  | .cst q => DD.tau (TM.const q)
  | .mono m => DD.tau (TM.mono m 1)
  | .add i j => (regs.getD i dd0).add (regs.getD j dd0)
  | .sub i j => (regs.getD i dd0).sub (regs.getD j dd0)
  | .mul i j => DD.mul B Dg (regs.getD i dd0) (regs.getD j dd0)

/-- One instruction on real values; `side = true` is the `a`-version. -/
noncomputable def stepR (side : Bool) (e : Env) (regs : List ℝ) : Instr → ℝ
  | .zgen i => genFun i (if side then e.a else e.b)
  | .tgen i => genFun i e.a
  | .zlog j => logFun j (if side then e.a else e.b)
  | .tlog j => logFun j e.a
  | .cst q => q
  | .mono m => m.eval e
  | .add i j => regs.getD i 0 + regs.getD j 0
  | .sub i j => regs.getD i 0 - regs.getD j 0
  | .mul i j => regs.getD i 0 * regs.getD j 0

def runDD (B : Box) (Dg : ℕ) (G : Fin 5 → DD) (L : Fin 3 → DD) : List Instr → List DD → List DD
  | [], regs => regs
  | ins :: rest, regs => runDD B Dg G L rest (regs ++ [stepDD B Dg G L regs ins])

noncomputable def runR (side : Bool) (e : Env) : List Instr → List ℝ → List ℝ
  | [], regs => regs
  | ins :: rest, regs => runR side e rest (regs ++ [stepR side e regs ins])

theorem approx_dd0 {B : Box} {S : Env → Prop} : dd0.Approx B S (fun _ => 0) (fun _ => 0) := by
  refine ⟨TM.approx_zero, TM.approx_zero, ?_⟩
  exact TM.approx_congr TM.approx_zero fun e _ _ => by simp

theorem approx_stepDD {B : Box} (hB : B.Valid) (Dg : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b))
    {regs : List DD} {ra rb : Env → List ℝ}
    (hk : ∀ k, (regs.getD k dd0).Approx B S (fun e => (ra e).getD k 0) (fun e => (rb e).getD k 0))
    (ins : Instr) :
    (stepDD B Dg G L regs ins).Approx B S (fun e => stepR true e (ra e) ins)
      (fun e => stepR false e (rb e) ins) := by
  cases ins with
  | zgen i => simpa [stepDD, stepR] using hG i
  | tgen i => simpa [stepDD, stepR] using DD.approx_tau (hG i).1
  | zlog j => simpa [stepDD, stepR] using hL j
  | tlog j => simpa [stepDD, stepR] using DD.approx_tau (hL j).1
  | cst q => simpa [stepDD, stepR] using DD.approx_tau (S := S) (Bx := B) (TM.approx_const q)
  | mono m =>
    have hm : (TM.mono m 1).Approx B S (fun e => m.eval e) :=
      TM.approx_congr (TM.approx_mono m 1) fun e _ _ => by simp
    simpa [stepDD, stepR] using DD.approx_tau hm
  | add i j => simpa [stepDD, stepR] using DD.approx_add (hk i) (hk j)
  | sub i j => simpa [stepDD, stepR] using DD.approx_sub (hk i) (hk j)
  | mul i j => simpa [stepDD, stepR] using DD.approx_mul hB Dg (hk i) (hk j)

theorem getD_append_single {α : Type*} (l : List α) (x d : α) (k : ℕ) :
    (l ++ [x]).getD k d = if k < l.length then l.getD k d else if k = l.length then x else d := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => simp
    | succ k => simp
  | cons y l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons, ih]
      split_ifs <;> first | rfl | omega

theorem approx_runDD {B : Box} (hB : B.Valid) (Dg : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b)) :
    ∀ (prog : List Instr) (regs : List DD) (ra rb : Env → List ℝ),
      (∀ e, (ra e).length = regs.length ∧ (rb e).length = regs.length) →
      (∀ k, (regs.getD k dd0).Approx B S (fun e => (ra e).getD k 0) (fun e => (rb e).getD k 0)) →
      ∀ k, ((runDD B Dg G L prog regs).getD k dd0).Approx B S
        (fun e => (runR true e prog (ra e)).getD k 0) (fun e => (runR false e prog (rb e)).getD k 0)
  | [], regs, ra, rb, _, hk => hk
  | ins :: rest, regs, ra, rb, hlen, hk => by
    simp only [runDD, runR]
    refine approx_runDD hB Dg hG hL rest _ (fun e => ra e ++ [stepR true e (ra e) ins])
      (fun e => rb e ++ [stepR false e (rb e) ins]) (fun e => ?_) (fun k => ?_)
    · simp [(hlen e).1, (hlen e).2]
    · have hstep := approx_stepDD hB Dg hG hL hk ins
      have hfun : ∀ (f : Env → List ℝ) (g : Env → ℝ), (∀ e, (f e).length = regs.length) →
          (fun e => (f e ++ [g e]).getD k 0) =
            fun e => if k < regs.length then (f e).getD k 0 else if k = regs.length then g e else 0 := by
        intro f g hf
        funext e
        rw [getD_append_single, hf e]
      rw [hfun _ _ fun e => (hlen e).1, hfun _ _ fun e => (hlen e).2, getD_append_single]
      split_ifs with h1 h2
      · exact hk k
      · exact hstep
      · exact approx_dd0

/-- Run a program from the empty register file. -/
theorem approx_run {B : Box} (hB : B.Valid) (Dg : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b))
    (prog : List Instr) (k : ℕ) :
    ((runDD B Dg G L prog []).getD k dd0).Approx B S
      (fun e => (runR true e prog []).getD k 0) (fun e => (runR false e prog []).getD k 0) :=
  approx_runDD hB Dg hG hL prog [] (fun _ => []) (fun _ => []) (fun _ => by simp)
    (fun k => by simpa using approx_dd0) k

end SLP

end E8Leech.Taylor
