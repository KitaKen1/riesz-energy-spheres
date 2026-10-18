import E8Leech.KronSeries
import E8Leech.CKMRVSLP

/-!
# Integer expressions and straight-line programs over the nome generators

`IExpr` describes a numerator as an expression in a list of *atoms* (functions of the nome,
taken on the `z`-side or on the `τ`-side), integer constants and monomials with natural
exponents. The atoms of the hat kernel are the generators `x, θ₃, θ₄, η₁, E₂` and `Λ` times the
logarithms of `θ₃, θ₄, η₁`; further atoms can be appended without changing earlier certificates.
A program (`IInstr` list) shares common subexpressions; it is accepted for an expression only
after symbolic execution reproduces the expression (`ISLP.approx_checked`), exactly as in
`CKMRVKernelSLP`. Running a program with `MDD` models of the atoms gives polynomial models with
majorants of the `a`-version, the `b`-version and their divided difference.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

inductive IExpr
  | zat (i : ℕ)
  | tat (i : ℕ)
  | cst (c : ℤ)
  | mono (m : NMono)
  | add (x y : IExpr)
  | sub (x y : IExpr)
  | mul (x y : IExpr)
  deriving DecidableEq

namespace IExpr

/-- The `a`-version: everything at the nome `a`. `fs` lists the meanings of the atoms. -/
noncomputable def evalA (fs : List (ℝ → ℝ)) : IExpr → NEnv → ℝ
  | zat i, e => fs.getD i (fun _ => 0) e.a
  | tat i, e => fs.getD i (fun _ => 0) e.a
  | cst c, _ => c
  | mono m, e => m.eval e
  | add x y, e => evalA fs x e + evalA fs y e
  | sub x y, e => evalA fs x e - evalA fs y e
  | mul x y, e => evalA fs x e * evalA fs y e

/-- The `b`-version: `z`-side atoms at `b`, `τ`-side atoms at `a`. -/
noncomputable def evalB (fs : List (ℝ → ℝ)) : IExpr → NEnv → ℝ
  | zat i, e => fs.getD i (fun _ => 0) e.b
  | tat i, e => fs.getD i (fun _ => 0) e.a
  | cst c, _ => c
  | mono m, e => m.eval e
  | add x y, e => evalB fs x e + evalB fs y e
  | sub x y, e => evalB fs x e - evalB fs y e
  | mul x y, e => evalB fs x e * evalB fs y e

end IExpr

inductive IInstr
  | zat (i : ℕ)
  | tat (i : ℕ)
  | cst (c : ℤ)
  | mono (m : NMono)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  deriving DecidableEq

namespace ISLP

/-- One instruction on divided-difference models. `At` lists the models of the atoms. -/
def stepMDD (Bx : Bounds) (D Dcap : ℕ) (At : List MDD) (regs : List MDD) : IInstr → MDD
  | .zat i => At.getD i MDD.zero
  | .tat i => MDD.tau (At.getD i MDD.zero).A
  | .cst c => MDD.tau (MTM.const c)
  | .mono m => MDD.tau (MTM.mono m 1)
  | .add i j => (regs.getD i MDD.zero).add (regs.getD j MDD.zero)
  | .sub i j => (regs.getD i MDD.zero).sub (regs.getD j MDD.zero)
  | .mul i j => MDD.mul Bx D Dcap (regs.getD i MDD.zero) (regs.getD j MDD.zero)

/-- One instruction on real values; `side = true` is the `a`-version. -/
noncomputable def stepR (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (regs : List ℝ) :
    IInstr → ℝ
  | .zat i => fs.getD i (fun _ => 0) (if side then e.a else e.b)
  | .tat i => fs.getD i (fun _ => 0) e.a
  | .cst c => c
  | .mono m => m.eval e
  | .add i j => regs.getD i 0 + regs.getD j 0
  | .sub i j => regs.getD i 0 - regs.getD j 0
  | .mul i j => regs.getD i 0 * regs.getD j 0

def runMDD (Bx : Bounds) (D Dcap : ℕ) (At : List MDD) : List IInstr → List MDD → List MDD
  | [], regs => regs
  | ins :: rest, regs => runMDD Bx D Dcap At rest (regs ++ [stepMDD Bx D Dcap At regs ins])

noncomputable def runR (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) :
    List IInstr → List ℝ → List ℝ
  | [], regs => regs
  | ins :: rest, regs => runR fs side e rest (regs ++ [stepR fs side e regs ins])

variable {Bx : Bounds} {S : NEnv → Prop}

/-- The models `At` approximate the atoms `fs`, on both sides and with divided differences. -/
def AtomsOK (Bx : Bounds) (S : NEnv → Prop) (At : List MDD) (fs : List (ℝ → ℝ)) : Prop :=
  ∀ i, (At.getD i MDD.zero).Approx Bx S (fun e => fs.getD i (fun _ => 0) e.a)
    (fun e => fs.getD i (fun _ => 0) e.b)

/-- Atom lists are extended by appending: earlier indices keep their meaning. -/
theorem AtomsOK.append {At At' : List MDD} {fs fs' : List (ℝ → ℝ)}
    (hlen : At.length = fs.length) (h : AtomsOK Bx S At fs) (h' : AtomsOK Bx S At' fs') :
    AtomsOK Bx S (At ++ At') (fs ++ fs') := by
  intro i
  rcases Nat.lt_or_ge i At.length with hi | hi
  · have hi' : i < fs.length := hlen ▸ hi
    have e1 : (At ++ At').getD i MDD.zero = At.getD i MDD.zero := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have e2 : (fs ++ fs').getD i (fun _ => 0) = fs.getD i (fun _ => 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hi']
    rw [e1, e2]
    exact h i
  · have hi' : fs.length ≤ i := hlen ▸ hi
    have e1 : (At ++ At').getD i MDD.zero = At'.getD (i - At.length) MDD.zero := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hi]
    have e2 : (fs ++ fs').getD i (fun _ => 0) = fs'.getD (i - At.length) (fun _ => 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hi', hlen]
    rw [e1, e2]
    exact h' (i - At.length)

theorem approx_stepMDD (hB : Bx.Valid) (D Dcap : ℕ) {At : List MDD} {fs : List (ℝ → ℝ)}
    (hAt : AtomsOK Bx S At fs) {regs : List MDD} {ra rb : NEnv → List ℝ}
    (hk : ∀ k, (regs.getD k MDD.zero).Approx Bx S (fun e => (ra e).getD k 0)
      (fun e => (rb e).getD k 0)) (ins : IInstr) :
    (stepMDD Bx D Dcap At regs ins).Approx Bx S (fun e => stepR fs true e (ra e) ins)
      (fun e => stepR fs false e (rb e) ins) := by
  cases ins with
  | zat i => simpa [stepMDD, stepR] using hAt i
  | tat i => simpa [stepMDD, stepR] using MDD.approx_tau (hAt i).1
  | cst c => simpa [stepMDD, stepR] using MDD.approx_tau (S := S) (Bx := Bx) (MTM.approx_const c)
  | mono m =>
    have hm : (MTM.mono m 1).Approx Bx S (fun e => m.eval e) :=
      MTM.approx_congr (MTM.approx_mono m 1) fun e _ _ => by simp
    simpa [stepMDD, stepR] using MDD.approx_tau hm
  | add i j => simpa [stepMDD, stepR] using MDD.approx_add (hk i) (hk j)
  | sub i j => simpa [stepMDD, stepR] using MDD.approx_sub (hk i) (hk j)
  | mul i j => simpa [stepMDD, stepR] using MDD.approx_mul hB D Dcap (hk i) (hk j)

theorem approx_runMDD (hB : Bx.Valid) (D Dcap : ℕ) {At : List MDD} {fs : List (ℝ → ℝ)}
    (hAt : AtomsOK Bx S At fs) :
    ∀ (prog : List IInstr) (regs : List MDD) (ra rb : NEnv → List ℝ),
      (∀ e, (ra e).length = regs.length ∧ (rb e).length = regs.length) →
      (∀ k, (regs.getD k MDD.zero).Approx Bx S (fun e => (ra e).getD k 0)
        (fun e => (rb e).getD k 0)) →
      ∀ k, ((runMDD Bx D Dcap At prog regs).getD k MDD.zero).Approx Bx S
        (fun e => (runR fs true e prog (ra e)).getD k 0)
        (fun e => (runR fs false e prog (rb e)).getD k 0)
  | [], regs, ra, rb, _, hk => hk
  | ins :: rest, regs, ra, rb, hlen, hk => by
    simp only [runMDD, runR]
    refine approx_runMDD hB D Dcap hAt rest _ (fun e => ra e ++ [stepR fs true e (ra e) ins])
      (fun e => rb e ++ [stepR fs false e (rb e) ins]) (fun e => ?_) (fun k => ?_)
    · simp [(hlen e).1, (hlen e).2]
    · have hstep := approx_stepMDD hB D Dcap hAt hk ins
      have hfun : ∀ (f : NEnv → List ℝ) (g : NEnv → ℝ), (∀ e, (f e).length = regs.length) →
          (fun e => (f e ++ [g e]).getD k 0) =
            fun e => if k < regs.length then (f e).getD k 0
              else if k = regs.length then g e else 0 := by
        intro f g hf
        funext e
        rw [SLP.getD_append_single, hf e]
      rw [hfun _ _ fun e => (hlen e).1, hfun _ _ fun e => (hlen e).2, SLP.getD_append_single]
      split_ifs with h1 h2
      · exact hk k
      · exact hstep
      · exact MDD.approx_zero

/-- Run a program from the empty register file. -/
theorem approx_run (hB : Bx.Valid) (D Dcap : ℕ) {At : List MDD} {fs : List (ℝ → ℝ)}
    (hAt : AtomsOK Bx S At fs) (prog : List IInstr) (k : ℕ) :
    ((runMDD Bx D Dcap At prog []).getD k MDD.zero).Approx Bx S
      (fun e => (runR fs true e prog []).getD k 0) (fun e => (runR fs false e prog []).getD k 0) :=
  approx_runMDD hB D Dcap hAt prog [] (fun _ => []) (fun _ => []) (fun _ => by simp)
    (fun k => by simpa using MDD.approx_zero) k

/-! ## Checking a program against its source expression -/

def stepExpr (regs : List IExpr) : IInstr → IExpr
  | .zat i => .zat i
  | .tat i => .tat i
  | .cst c => .cst c
  | .mono m => .mono m
  | .add i j => .add (regs.getD i (.cst 0)) (regs.getD j (.cst 0))
  | .sub i j => .sub (regs.getD i (.cst 0)) (regs.getD j (.cst 0))
  | .mul i j => .mul (regs.getD i (.cst 0)) (regs.getD j (.cst 0))

def runExpr : List IInstr → List IExpr → List IExpr
  | [], regs => regs
  | ins :: rest, regs => runExpr rest (regs ++ [stepExpr regs ins])

noncomputable def eval (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (x : IExpr) : ℝ :=
  if side then IExpr.evalA fs x e else IExpr.evalB fs x e

theorem eval_getD (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (regs : List IExpr) (k : ℕ) :
    (regs.map (eval fs side e)).getD k 0 = eval fs side e (regs.getD k (.cst 0)) := by
  have h0 : eval fs side e (.cst 0) = 0 := by
    cases side <;> simp [eval, IExpr.evalA, IExpr.evalB]
  simpa only [h0] using List.getD_map (l := regs) (d := IExpr.cst 0) (n := k) (eval fs side e)

theorem eval_stepExpr (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (regs : List IExpr)
    (ins : IInstr) :
    eval fs side e (stepExpr regs ins) = stepR fs side e (regs.map (eval fs side e)) ins := by
  cases ins <;> simp only [stepExpr, stepR, eval_getD] <;> cases side <;> rfl

theorem eval_runExpr (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (prog : List IInstr)
    (regs : List IExpr) :
    (runExpr prog regs).map (eval fs side e) = runR fs side e prog (regs.map (eval fs side e)) := by
  induction prog generalizing regs with
  | nil => rfl
  | cons ins rest ih =>
    simp only [runExpr, runR, ih, List.map_append, List.map_cons, List.map_nil, eval_stepExpr]

theorem eval_runExpr_getD (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (prog : List IInstr)
    (k : ℕ) :
    eval fs side e ((runExpr prog []).getD k (.cst 0)) = (runR fs side e prog []).getD k 0 := by
  rw [← eval_getD, eval_runExpr]
  rfl

/-- A finite syntactic equality certifies the real meaning of a program output. -/
theorem approx_checked (hB : Bx.Valid) (D Dcap : ℕ) {At : List MDD} {fs : List (ℝ → ℝ)}
    (hAt : AtomsOK Bx S At fs) (prog : List IInstr) (k : ℕ) (x : IExpr)
    (h : (runExpr prog []).getD k (.cst 0) = x) :
    ((runMDD Bx D Dcap At prog []).getD k MDD.zero).Approx Bx S (IExpr.evalA fs x)
      (IExpr.evalB fs x) := by
  have ha : (fun e => (runR fs true e prog []).getD k 0) = IExpr.evalA fs x := by
    funext e
    rw [← eval_runExpr_getD, h]
    rfl
  have hb : (fun e => (runR fs false e prog []).getD k 0) = IExpr.evalB fs x := by
    funext e
    rw [← eval_runExpr_getD, h]
    rfl
  simpa only [ha, hb] using approx_run hB D Dcap hAt prog k

/-- Candidate compiler with exact sharing of common subexpressions. Only the check above is
trusted, not this search. -/
structure CompileState where
  expressions : List IExpr := []
  instructions : List IInstr := []

def emit (s : CompileState) (x : IExpr) (ins : IInstr) : CompileState × ℕ :=
  (⟨s.expressions ++ [x], s.instructions ++ [ins]⟩, s.instructions.length)

def compile (x : IExpr) (s : CompileState) : CompileState × ℕ :=
  match s.expressions.findIdx? (fun y => decide (y = x)) with
  | some k => (s, k)
  | none =>
    match x with
    | .zat i => emit s x (.zat i)
    | .tat i => emit s x (.tat i)
    | .cst c => emit s x (.cst c)
    | .mono m => emit s x (.mono m)
    | .add a b =>
      let (s, i) := compile a s
      let (s, j) := compile b s
      emit s x (.add i j)
    | .sub a b =>
      let (s, i) := compile a s
      let (s, j) := compile b s
      emit s x (.sub i j)
    | .mul a b =>
      let (s, i) := compile a s
      let (s, j) := compile b s
      emit s x (.mul i j)

end ISLP

end E8Leech.Kron
