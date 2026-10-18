import E8Leech.KronKernelSplit
import E8Leech.KronRedAtoms

/-!
# The numerators with the second variable inverted

For `t < 1` put `t = 1/s`. The generators at `i/s` are those at `is` after the modular inversion:
`E₂ ↦ −s² E₂ + 6s/π`, `V ↦ s² W`, `W ↦ s² V`, `L ↦ L_S`. With `p = 1/π`, the nome `x` of `is` and
the reduced quantities `Ṽ = V/x`, `W̃ = (W − 1)/x`, `Ẽ = (E₂ − 1)/x`, `r_S = Λ L_S / x` there, the
integer numerator becomes

`axE = s¹² x (axEtil − p² axG2Sr)`,

and the numerator of `𝒦` becomes `s¹² x (axEtil + p² axG2Sr)`. The variable `s` enters only through
the factor `s¹²` and the nome. Both `axEtil` and `axG2Sr` vanish when the generators of the second
variable equal those of the first, so the expressions below have vanishing `a`-versions and one
model of a divided difference decides the sign.

* `axPlus_S`, `axMinus_S`, `axE_S`, `axE12S_S`: the identities; `axG2Sr_diag`, `axNu_S`.
* `g2sE`, `rsE`, `ssE`: the expressions in the twelve atoms `sAtoms`.
* `rsE_evalA`, `ssE_evalA`: the `a`-versions vanish; `rsE_mul_evalB`, `ssE_mul_evalB`: the nome
  times the expressions are the numerators.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The real polynomials -/

/-- The logarithmic part with the second variable inverted, divided by `s¹¹ x p`. Here `x` is the
nome of the inverted variable, `Vt = V/x` and `rS = Λ L_S / x`. -/
def axG2Sr (Λ Va Wa lA lSA uh Vt Vb Wb rS : ℝ) : ℝ :=
  axD256 Va Wa * (3456 * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb * rS * uh +
      3456 * axPsi4h Λ Va Wa lA lSA uh * axE4 Vb Wb ^ 2 * Vt) +
    128 * axT2 Λ Va Wa lA lSA uh * Vt * (2 * axE4 Vb Wb ^ 2 + axF6 Vb Wb * (Vb + 2 * Wb))

/-- The quasimodular part under the inversion of the second variable: the terms with `t̂ = s p`
cancel against the inhomogeneous part of `E₂`. -/
theorem axPlus_S (Λ E2a Va Wa uh E V W s p : ℝ) :
    axE0 Λ E2a Va Wa uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V) -
        s * p * axPlus12 Λ E2a Va Wa uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V)
          (s * p) =
      s ^ 12 * axE0 Λ E2a Va Wa uh E V W := by
  simp only [axE0, axZ10, axPlus12, axD256, axF6, axE4]
  ring

/-- The logarithmic part under the inversion of the second variable. -/
theorem axMinus_S (Λ Va Wa lA lSA uh x Vt W rS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = x * rS * (s * p)) :
    s * p * axMinus12 Λ Va Wa lA lSA uh (s ^ 2 * W) (s ^ 2 * (x * Vt)) lB (s * p) =
      s ^ 12 * (x * (p ^ 2 * axG2Sr Λ Va Wa lA lSA uh Vt (x * Vt) W rS)) := by
  simp only [axMinus12, axG2Sr, axXb2, axF6, axE4, hlB]
  ring

/-- **The numerator with the second variable inverted**: `axE = s¹² x (axEtil − p² axG2Sr)`. -/
theorem axE_S (Λ E2a Va Wa lA lSA uh x Vt Wt Et rS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = x * rS * (s * p)) :
    axE Λ E2a Va Wa lA lSA uh (-s ^ 2 * (1 + x * Et) + 6 * s * p) (s ^ 2 * (1 + x * Wt))
        (s ^ 2 * (x * Vt)) lB (s * p) =
      s ^ 12 * (x * (axEtil Λ E2a Va Wa uh x Vt Wt Et (1 + x * Et) (x * Vt) (1 + x * Wt) -
        p ^ 2 * axG2Sr Λ Va Wa lA lSA uh Vt (x * Vt) (1 + x * Wt) rS)) := by
  have h1 := axPlus_S Λ E2a Va Wa uh (1 + x * Et) (x * Vt) (1 + x * Wt) s p
  have h2 := axMinus_S Λ Va Wa lA lSA uh x Vt (1 + x * Wt) rS lB s p hlB
  have h3 := axE0_eq_mul Λ E2a Va Wa uh x Vt Wt Et
  rw [axE_split, axE12]
  linear_combination h1 - h2 + s ^ 12 * h3

/-- **The numerator of `𝒦` with the second variable inverted**:
`axE0 − t̂ · axE12S = s¹² x (axEtil + p² axG2Sr)`. -/
theorem axE12S_S (Λ E2a Va Wa lA lSA uh x Vt Wt Et rS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = x * rS * (s * p)) :
    axE0 Λ E2a Va Wa uh (-s ^ 2 * (1 + x * Et) + 6 * s * p) (s ^ 2 * (1 + x * Wt))
          (s ^ 2 * (x * Vt)) -
        s * p * axE12S Λ E2a Va Wa lA lSA uh (-s ^ 2 * (1 + x * Et) + 6 * s * p)
          (s ^ 2 * (1 + x * Wt)) (s ^ 2 * (x * Vt)) lB (s * p) =
      s ^ 12 * (x * (axEtil Λ E2a Va Wa uh x Vt Wt Et (1 + x * Et) (x * Vt) (1 + x * Wt) +
        p ^ 2 * axG2Sr Λ Va Wa lA lSA uh Vt (x * Vt) (1 + x * Wt) rS)) := by
  have h1 := axPlus_S Λ E2a Va Wa uh (1 + x * Et) (x * Vt) (1 + x * Wt) s p
  have h2 := axMinus_S Λ Va Wa lA lSA uh x Vt (1 + x * Wt) rS lB s p hlB
  have h3 := axE0_eq_mul Λ E2a Va Wa uh x Vt Wt Et
  rw [axE12S]
  linear_combination h1 + h2 + s ^ 12 * h3

/-- The logarithmic part vanishes when the generators of the second variable equal those of the
first. -/
theorem axG2Sr_diag (Λ W lA uh x Vt rS : ℝ) :
    axG2Sr Λ (x * Vt) W lA (x * rS) uh Vt (x * Vt) W rS = 0 := by
  simp only [axG2Sr, axT2, axPsi2h, axPsi4h, axF6, axD256, axE4]
  ring

/-- The denominator polynomial under the inversion of the second variable. -/
theorem axNu_S (Va Wa V W s : ℝ) :
    axNu Va Wa (s ^ 2 * W) (s ^ 2 * V) = s ^ 12 * axNu Va Wa V W := by
  simp only [axNu, axDelta, axE4]
  ring

/-! ## The twelve atoms -/

section SAtoms

variable (Λ : ℕ)

@[simp] theorem evalA_zat8S (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 8) e = devTheta4 e.a := rfl
@[simp] theorem evalA_zat9S (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 9) e = devE2 e.a := rfl
@[simp] theorem evalA_zat10S (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 10) e = rlogTheta3 Λ e.a := rfl
@[simp] theorem evalA_zat11S (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 11) e = rlogTheta4 Λ e.a := rfl
@[simp] theorem evalB_zat8S (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 8) e = devTheta4 e.b := rfl
@[simp] theorem evalB_zat9S (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 9) e = devE2 e.b := rfl
@[simp] theorem evalB_zat10S (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 10) e = rlogTheta3 Λ e.b := rfl
@[simp] theorem evalB_zat11S (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (.zat 11) e = rlogTheta4 Λ e.b := rfl

end SAtoms

/-! ## The expressions -/

/-- The logarithmic part with the second variable inverted, in its building blocks. -/
def g2srE (Λ : ℕ) (Va Wa lA lSA Vt Vb Wb rS : IExpr) : IExpr :=
  d256E Va Wa * (3456 * e4E Va Wa * e4E Vb Wb * f6E Vb Wb * rS * uhE +
      3456 * psi4E Λ Va Wa lA lSA * e4E Vb Wb ^ 2 * Vt) +
    128 * t2E Λ Va Wa lA lSA * Vt * (2 * e4E Vb Wb ^ 2 + f6E Vb Wb * (Vb + 2 * Wb))

/-- `Λ L_S / x = 4 (Λ log θ₄ / x) − 4 (Λ log θ₃ / x)` on the `z`-side. -/
def rsZ : IExpr := 4 * .zat 11 - 4 * .zat 10

/-- The logarithmic part with the second variable inverted. -/
def g2sE (Λ : ℕ) : IExpr := g2srE Λ vT wT (l0T Λ) lSE vtilZ vZ wZ rsZ

/-- The reduced numerator of `𝒦̂` with the second variable inverted. The fourth slot of the
environment holds `p = 1/π`. -/
def rsE (Λ : ℕ) : IExpr := etilE Λ - thE ^ 2 * g2sE Λ

/-- The reduced numerator of `𝒦` with the second variable inverted, with the opposite sign. -/
def ssE (Λ : ℕ) : IExpr := netilE Λ - thE ^ 2 * g2sE Λ

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ)

theorem evalA_g2srE (Va Wa lA lSA Vt Vb Wb rS : IExpr) (e : NEnv) :
    IExpr.evalA fs (g2srE Λ Va Wa lA lSA Vt Vb Wb rS) e =
      axG2Sr Λ (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) (IExpr.evalA fs lA e)
        (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs Vt e) (IExpr.evalA fs Vb e)
        (IExpr.evalA fs Wb e) (IExpr.evalA fs rS e) := by
  simp only [g2srE, t2E, psi2E, psi4E, axG2Sr, axT2, axPsi2h, axPsi4h, IExpr.evalA_add,
    IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst,
    evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE]
  push_cast
  ring

theorem evalB_g2srE (Va Wa lA lSA Vt Vb Wb rS : IExpr) (e : NEnv) :
    IExpr.evalB fs (g2srE Λ Va Wa lA lSA Vt Vb Wb rS) e =
      axG2Sr Λ (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) (IExpr.evalB fs lA e)
        (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs Vt e) (IExpr.evalB fs Vb e)
        (IExpr.evalB fs Wb e) (IExpr.evalB fs rS e) := by
  simp only [g2srE, t2E, psi2E, psi4E, axG2Sr, axT2, axPsi2h, axPsi4h, IExpr.evalB_add,
    IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst,
    evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE]
  push_cast
  ring

end Eval

/-- `Λ L_S = x · (4 (Λ log θ₄ / x) − 4 (Λ log θ₃ / x))`. -/
theorem nomeLS_eq_mul (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (Λ : ℝ) * nomeLS x = x * (4 * rlogTheta4 Λ x - 4 * rlogTheta3 Λ x) := by
  have h3 := log_theta3_eq Λ hx0 hx1
  have h4 := log_theta4_eq Λ hx0 hx1
  simp only [nomeLS]
  linear_combination 4 * h4 - 4 * h3

section SEval

variable (Λ : ℕ)

theorem g2sE_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (g2sE Λ) e =
      axG2Sr Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (16 * nomeEta1 e.b ^ 4) (nomeV e.b) (nomeW e.b)
        (4 * rlogTheta4 Λ e.b - 4 * rlogTheta3 Λ e.b) := by
  rw [g2sE, evalB_g2srE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_lSE]
  simp [vtilZ, rsZ, genFun]

theorem g2sE_evalA (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (g2sE Λ) e =
      axG2Sr Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (16 * nomeEta1 e.a ^ 4) (nomeV e.a) (nomeW e.a)
        (4 * rlogTheta4 Λ e.a - 4 * rlogTheta3 Λ e.a) := by
  rw [g2sE, evalA_g2srE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T, evalA_lSE]
  simp [vtilZ, rsZ, genFun]

/-- The `a`-version of the logarithmic part vanishes. -/
theorem g2sE_evalA_eq_zero {e : NEnv} (ha0 : 0 ≤ e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (g2sE Λ) e = 0 := by
  have hV : nomeV e.a = e.a * (16 * nomeEta1 e.a ^ 4) := (reduced_spec ha0 ha1).2.1
  rw [g2sE_evalA, nomeLS_eq_mul Λ ha0 ha1, hV]
  exact axG2Sr_diag _ _ _ _ _ _ _

theorem etilE_evalB_auxS (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (etilE Λ) e =
      axEtil Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
        (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1))
        (devE2 e.b) (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  rw [etilE, evalB_numTilE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ]
  simp [vtilZ, wtilZ, genFun]

theorem etilE_evalA_auxS (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (etilE Λ) e =
      axEtil Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
        (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1))
        (devE2 e.a) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) := by
  rw [etilE, evalA_numTilE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ]
  simp [vtilZ, wtilZ, genFun]

/-- The `a`-version of the reduced quasimodular part vanishes, also over the twelve atoms. -/
theorem etilE_evalA_S {e : NEnv} (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (etilE Λ) e = 0 := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec ha0.le ha1
  have key := axE0_eq_mul Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
    (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1)) (devE2 e.a)
  rw [← h1, ← h2, ← h3, axE0_diag] at key
  rw [etilE_evalA_auxS]
  rcases mul_eq_zero.mp key.symm with h | h
  · exact absurd h ha0.ne'
  · exact h

/-- The `a`-version of `rsE` vanishes. -/
theorem rsE_evalA {e : NEnv} (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (rsE Λ) e = 0 := by
  rw [rsE, IExpr.evalA_sub, IExpr.evalA_mul, etilE_evalA_S Λ ha0 ha1,
    g2sE_evalA_eq_zero Λ ha0.le ha1]
  ring

/-- The `a`-version of `ssE` vanishes. -/
theorem ssE_evalA {e : NEnv} (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (ssE Λ) e = 0 := by
  rw [ssE, IExpr.evalA_sub, IExpr.evalA_mul, netilE, IExpr.evalA_neg, etilE_evalA_S Λ ha0 ha1,
    g2sE_evalA_eq_zero Λ ha0.le ha1]
  ring

/-- **The numerator of `𝒦̂` with the second variable inverted.** For every `s`, with the fourth
slot `p` of the environment and any `lB` with `lB · s p − Λ = Λ L_S(b) · s p`:
`s¹² · b · rsE` is `axE` at the inverted generators. -/
theorem rsE_mul_evalB {e : NEnv} (hb0 : 0 ≤ e.b) (hb1 : e.b < 1) (s lB : ℝ)
    (hlB : lB * (s * e.t) - Λ = Λ * nomeLS e.b * (s * e.t)) :
    s ^ 12 * (e.b * IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (rsE Λ) e) =
      axE Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (-s ^ 2 * nomeE2 e.b + 6 * s * e.t) (s ^ 2 * nomeW e.b) (s ^ 2 * nomeV e.b) lB
        (s * e.t) := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec hb0 hb1
  have hL := nomeLS_eq_mul Λ hb0 hb1
  rw [hL] at hlB
  have key := axE_S Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a)
    e.u e.b (16 * nomeEta1 e.b ^ 4)
    (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1)) (devE2 e.b)
    (4 * rlogTheta4 Λ e.b - 4 * rlogTheta3 Λ e.b) lB s e.t hlB
  rw [← h1, ← h2, ← h3] at key
  rw [key, rsE, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_pow, evalB_thE, etilE_evalB_auxS,
    g2sE_evalB]

/-- **The numerator of `𝒦` with the second variable inverted**: `−s¹² · b · ssE` is
`axE0 − t̂ · axE12S` at the inverted generators. -/
theorem ssE_mul_evalB {e : NEnv} (hb0 : 0 ≤ e.b) (hb1 : e.b < 1) (s lB : ℝ)
    (hlB : lB * (s * e.t) - Λ = Λ * nomeLS e.b * (s * e.t)) :
    -(s ^ 12 * (e.b * IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (ssE Λ) e)) =
      axE0 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (-s ^ 2 * nomeE2 e.b + 6 * s * e.t)
          (s ^ 2 * nomeW e.b) (s ^ 2 * nomeV e.b) -
        s * e.t * axE12S Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a)
          (Λ * nomeLS e.a) e.u (-s ^ 2 * nomeE2 e.b + 6 * s * e.t) (s ^ 2 * nomeW e.b)
          (s ^ 2 * nomeV e.b) lB (s * e.t) := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec hb0 hb1
  have hL := nomeLS_eq_mul Λ hb0 hb1
  rw [hL] at hlB
  have key := axE12S_S Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a)
    (Λ * nomeLS e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
    (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1)) (devE2 e.b)
    (4 * rlogTheta4 Λ e.b - 4 * rlogTheta3 Λ e.b) lB s e.t hlB
  rw [← h1, ← h2, ← h3] at key
  rw [key, ssE, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_pow, evalB_thE, netilE,
    IExpr.evalB_neg, etilE_evalB_auxS, g2sE_evalB]
  ring

end SEval

end E8Leech.Kron
