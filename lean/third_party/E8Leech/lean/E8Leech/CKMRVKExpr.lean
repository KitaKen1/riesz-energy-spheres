import E8Leech.CKMRVGenDD

/-!
# Expressions in the generators and their divided-difference evaluation

`KExpr` describes the axis numerators as expressions in the generators
(`x`, `θ₃`, `θ₄`, `η₁`, `E₂` on the `z`-side or the `τ`-side), the logarithms of `θ₃, θ₄, η₁`,
rational constants and monomials in `u, t, π, log 2`. `KExpr.dd` evaluates an expression with
divided-difference Taylor models, and `KExpr.approx_dd` (one induction) shows that the result
approximates the pair (`a`-version, `b`-version) and their divided difference.
-/

namespace E8Leech.Taylor

open scoped Real

/-- The generator functions of the nome: `x`, `θ₃`, `θ₄`, `η₁`, `E₂`. -/
noncomputable def genFun : Fin 5 → ℝ → ℝ
  | 0 => id
  | 1 => nomeTheta3
  | 2 => nomeTheta4
  | 3 => nomeEta1
  | 4 => nomeE2

/-- The generators under a logarithm: `θ₃`, `θ₄`, `η₁`. -/
noncomputable def logFun : Fin 3 → ℝ → ℝ
  | 0 => fun x => Real.log (nomeTheta3 x)
  | 1 => fun x => Real.log (nomeTheta4 x)
  | 2 => fun x => Real.log (nomeEta1 x)

inductive KExpr
  | zgen (i : Fin 5)
  | tgen (i : Fin 5)
  | zlog (j : Fin 3)
  | tlog (j : Fin 3)
  | cst (q : ℚ)
  | mono (m : Mono)
  | add (x y : KExpr)
  | sub (x y : KExpr)
  | mul (x y : KExpr)

namespace KExpr

/-- The `a`-version: everything at the nome `a`. -/
noncomputable def evalA : KExpr → Env → ℝ
  | zgen i, e => genFun i e.a
  | tgen i, e => genFun i e.a
  | zlog j, e => logFun j e.a
  | tlog j, e => logFun j e.a
  | cst q, _ => q
  | mono m, e => m.eval e
  | add x y, e => evalA x e + evalA y e
  | sub x y, e => evalA x e - evalA y e
  | mul x y, e => evalA x e * evalA y e

/-- The `b`-version: `z`-side quantities at `b`, `τ`-side quantities at `a`. -/
noncomputable def evalB : KExpr → Env → ℝ
  | zgen i, e => genFun i e.b
  | tgen i, e => genFun i e.a
  | zlog j, e => logFun j e.b
  | tlog j, e => logFun j e.a
  | cst q, _ => q
  | mono m, e => m.eval e
  | add x y, e => evalB x e + evalB y e
  | sub x y, e => evalB x e - evalB y e
  | mul x y, e => evalB x e * evalB y e

/-- Divided-difference evaluation from generator triples `G` and log triples `L`. -/
def dd (B : Box) (Dg : ℕ) (G : Fin 5 → DD) (L : Fin 3 → DD) : KExpr → DD
  | zgen i => G i
  | tgen i => DD.tau (G i).A
  | zlog j => L j
  | tlog j => DD.tau (L j).A
  | cst q => DD.tau (TM.const q)
  | mono m => DD.tau (TM.mono m 1)
  | add x y => (dd B Dg G L x).add (dd B Dg G L y)
  | sub x y => (dd B Dg G L x).sub (dd B Dg G L y)
  | mul x y => DD.mul B Dg (dd B Dg G L x) (dd B Dg G L y)

theorem approx_dd {B : Box} (hB : B.Valid) (Dg : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b)) :
    ∀ x : KExpr, (dd B Dg G L x).Approx B S (evalA x) (evalB x)
  | zgen i => hG i
  | tgen i => DD.approx_tau (hG i).1
  | zlog j => hL j
  | tlog j => DD.approx_tau (hL j).1
  | cst q => DD.approx_tau (TM.approx_const q)
  | mono m => DD.approx_tau (TM.approx_congr (TM.approx_mono m 1) fun e _ _ => by simp [evalA])
  | add x y => DD.approx_add (approx_dd hB Dg hG hL x) (approx_dd hB Dg hG hL y)
  | sub x y => DD.approx_sub (approx_dd hB Dg hG hL x) (approx_dd hB Dg hG hL y)
  | mul x y => DD.approx_mul hB Dg (approx_dd hB Dg hG hL x) (approx_dd hB Dg hG hL y)

end KExpr

end E8Leech.Taylor
