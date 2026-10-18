import E8Leech.KronKernelExpr
import E8Leech.KronDevAtoms

/-!
# The numerator split by powers of `t̂` and reduced at the cusp

The integer numerator is `axE = axE0 + t̂ · axE12`, where `axE0` does not contain `t̂`. At the
cusp of the second variable (`V = 0`, `W = E₂ = 1`) the part `axE0` vanishes; with
`V = x Ṽ`, `W = 1 + x W̃`, `E₂ = 1 + x Ẽ` it is `x · axEtil`. Both `axE12` and `axEtil` vanish when
the second variable is put equal to the first. Hence the divided difference of the numerator is

`t̂ · D₁₂ + b · D̃`,

with the divided differences `D₁₂, D̃` of `axE12, axEtil`. A model of each of them has a remainder
that is multiplied by `t̂` or by the nome `b`; this is what a single model of the numerator cannot
give when `t → ∞`, where the numerator is of the order of `t̂` and the nome `b` is far smaller.

* `axE_split`, `axE0_eq_mul`, `axE12_diag`, `axE0_diag`: the identities.
* `splitAtoms`, `splitAtomModels`, `splitAtoms_ok`: the ten atoms.
* `e12E`, `etilE`: the two expressions; `e12E_evalA`, `etilE_evalA`: their `a`-versions vanish.
  `e12E = −(plusE + minusE)`; the combination `e12SE = plusE − minusE` belongs to the kernel `𝒦`.
* `split_eval_axis`: `t̂ · e12E + b · etilE` is the positive multiple of `Φ'` on the axes.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The real polynomials -/

/-- The part of `axZ1` without `t̂`. -/
def axZ10 (E2a Va Wa uh E2b Vb Wb : ℝ) : ℝ :=
  -(axE4 Vb Wb ^ 3) * (axF6 Va Wa - 4 * (E2a - 3 * uh) * axE4 Va Wa) +
    (-2 * (E2a - 3 * uh) * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb * E2b +
      axF6 Va Wa * axE4 Vb Wb ^ 2 * E2b ^ 2)

/-- The part of the numerator without `t̂`. -/
def axE0 (Λ E2a Va Wa uh E2b Vb Wb : ℝ) : ℝ :=
  -(96 * Λ * (axD256 Vb Wb * axT1 E2a Va Wa uh + axD256 Va Wa * axZ10 E2a Va Wa uh E2b Vb Wb))

/-- The quasimodular part of the coefficient of `t̂` (from `K₊`), with the opposite sign. -/
def axPlus12 (Λ E2a Va Wa uh E2b Vb Wb th : ℝ) : ℝ :=
  96 * Λ * axD256 Va Wa *
    (12 * (E2a - 3 * uh) * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb -
      12 * axF6 Va Wa * axE4 Vb Wb ^ 2 * E2b + 36 * th * axF6 Va Wa * axE4 Vb Wb ^ 2)

/-- The logarithmic part of the coefficient of `t̂` (from `K₋`), with the opposite sign. -/
def axMinus12 (Λ Va Wa lA lSA uh Vb Wb lB th : ℝ) : ℝ :=
  axD256 Va Wa *
      (-3456 * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb * (lB * th - Λ) * uh +
        3456 * axPsi4h Λ Va Wa lA lSA uh * axE4 Vb Wb ^ 2 * Wb * th) +
    128 * axT2 Λ Va Wa lA lSA uh * axXb2 Vb Wb * th

/-- The coefficient of `t̂` in the numerator of `𝒦̂`. -/
def axE12 (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  -(axPlus12 Λ E2a Va Wa uh E2b Vb Wb th + axMinus12 Λ Va Wa lA lSA uh Vb Wb lB th)

/-- The coefficient of `t̂` in the numerator of `𝒦` (after the sign change of the whole
numerator): the two parts enter with opposite signs. -/
def axE12S (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  axPlus12 Λ E2a Va Wa uh E2b Vb Wb th - axMinus12 Λ Va Wa lA lSA uh Vb Wb lB th

/-- **The split**: `axE = axE0 + t̂ · axE12`. -/
theorem axE_split (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) :
    axE Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th =
      axE0 Λ E2a Va Wa uh E2b Vb Wb + th * axE12 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th := by
  simp only [axE, axZ1, axZ2, axE0, axZ10, axE12, axPlus12, axMinus12]
  ring

/-- The coefficient of `t̂` vanishes on the diagonal. -/
theorem axE12_diag (Λ E2 V W lA lSA uh th : ℝ) :
    axE12 Λ E2 V W lA lSA uh E2 V W lA th = 0 := by
  simp only [axE12, axPlus12, axMinus12, axT2, axXb2, axPsi2h, axPsi4h, axF6, axD256, axE4]
  ring

/-- The part without `t̂` vanishes on the diagonal. -/
theorem axE0_diag (Λ E2 V W uh : ℝ) : axE0 Λ E2 V W uh E2 V W = 0 := by
  simp only [axE0, axT1, axZ10]
  ring

/-- `(E₄ − 1)/x`. -/
def axEps4 (x Vt Wt Wb : ℝ) : ℝ := x * Vt ^ 2 + Vt * Wb + Wt * (Wb + 1)

/-- `(E₂² − E₄)/x`. -/
def axZeta1 (x Vt Wt Et E2b Wb : ℝ) : ℝ := Et * (E2b + 1) - axEps4 x Vt Wt Wb

/-- `(2E₆ − 2)/x`. -/
def axPhi6 (Vt Wt Vb Wb : ℝ) : ℝ :=
  (Vt + 2 * Wt) * (2 * Vb + Wb) * (Wb - Vb) + 2 * (2 * Vt + Wt) * (Wb - Vb) + 2 * (Wt - Vt)

/-- `(2E₄² − 2E₆E₂)/x`. -/
def axZeta2 (x Vt Wt Et E2b Vb Wb : ℝ) : ℝ :=
  2 * axEps4 x Vt Wt Wb * (axE4 Vb Wb + 1) - (axPhi6 Vt Wt Vb Wb * E2b + 2 * Et)

/-- `256Δ/x`. -/
def axD256r (Vt Vb Wb : ℝ) : ℝ := (Vb + Wb) * Vt * Wb * ((Vb + Wb) * Vb * Wb)

/-- `axE0 / x` in the reduced quantities `Ṽ = V/x`, `W̃ = (W − 1)/x`, `Ẽ = (E₂ − 1)/x`. -/
def axEtil (Λ E2a Va Wa uh x Vt Wt Et E2b Vb Wb : ℝ) : ℝ :=
  -(96 * Λ * (axD256r Vt Vb Wb * axT1 E2a Va Wa uh +
    axD256 Va Wa * (axF6 Va Wa * axE4 Vb Wb ^ 2 * axZeta1 x Vt Wt Et E2b Wb +
      2 * ((E2a - 3 * uh) * axE4 Va Wa) * axE4 Vb Wb * axZeta2 x Vt Wt Et E2b Vb Wb)))

theorem axZeta1_spec (x Vt Wt Et : ℝ) :
    (1 + x * Et) ^ 2 - axE4 (x * Vt) (1 + x * Wt) =
      x * axZeta1 x Vt Wt Et (1 + x * Et) (1 + x * Wt) := by
  simp only [axZeta1, axEps4, axE4]
  ring

theorem axZeta2_spec (x Vt Wt Et : ℝ) :
    2 * axE4 (x * Vt) (1 + x * Wt) ^ 2 - axF6 (x * Vt) (1 + x * Wt) * (1 + x * Et) =
      x * axZeta2 x Vt Wt Et (1 + x * Et) (x * Vt) (1 + x * Wt) := by
  simp only [axZeta2, axEps4, axPhi6, axE4, axF6]
  ring

theorem axD256r_spec (x Vt Wb : ℝ) : axD256 (x * Vt) Wb = x * axD256r Vt (x * Vt) Wb := by
  simp only [axD256, axD256r]
  ring

theorem axZ10_regroup (E2a Va Wa uh E2b Vb Wb : ℝ) :
    axZ10 E2a Va Wa uh E2b Vb Wb =
      axF6 Va Wa * axE4 Vb Wb ^ 2 * (E2b ^ 2 - axE4 Vb Wb) +
        2 * ((E2a - 3 * uh) * axE4 Va Wa) * axE4 Vb Wb *
          (2 * axE4 Vb Wb ^ 2 - axF6 Vb Wb * E2b) := by
  simp only [axZ10]
  ring

/-- **The reduction at the cusp**: `axE0 = x · axEtil`. -/
theorem axE0_eq_mul (Λ E2a Va Wa uh x Vt Wt Et : ℝ) :
    axE0 Λ E2a Va Wa uh (1 + x * Et) (x * Vt) (1 + x * Wt) =
      x * axEtil Λ E2a Va Wa uh x Vt Wt Et (1 + x * Et) (x * Vt) (1 + x * Wt) := by
  rw [axE0, axZ10_regroup, axZeta1_spec, axZeta2_spec, axD256r_spec, axEtil]
  ring

/-! ## The ten atoms -/

/-- The two further atoms `(θ₄ − 1)/x` and `(E₂ − 1)/x`, with the indices `8` and `9`. -/
noncomputable def devAtoms : List (ℝ → ℝ) := [devTheta4, devE2]

/-- The models of the two further atoms. -/
def devAtomModels (Bx : Bounds) (N' NE' : ℕ) : List MDD := [devTheta4MDD Bx N', devE2MDD Bx NE']

theorem devAtoms_ok {Bx : Bounds} {NE' : ℕ} (h : GenOK Bx NE') (N' : ℕ) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (devAtomModels Bx N' NE') devAtoms := by
  intro i
  rcases i with _ | _ | i
  · simpa [devAtomModels, devAtoms] using approx_devTheta4MDD h.1 N' (S := S)
  · simpa [devAtomModels, devAtoms] using approx_devE2MDD h (S := S)
  · simpa [devAtomModels, devAtoms] using MDD.approx_zero (Bx := Bx) (S := S)

/-- The models of the ten atoms. -/
def splitAtomModels (Bx : Bounds) (D Dcap Λ n K N NE N' NE' : ℕ) : List MDD :=
  kernelAtomModels Bx D Dcap Λ n K N NE ++ devAtomModels Bx N' NE'

theorem splitAtoms_ok {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE) (hG' : GenOK Bx NE')
    (D Dcap : ℕ) {Λ n : ℕ} (K N N' : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (splitAtomModels Bx D Dcap Λ n K N NE N' NE')
      (kernelAtoms Λ ++ devAtoms) :=
  ISLP.AtomsOK.append rfl (kernelAtoms_ok hG D Dcap K N hΛ hL) (devAtoms_ok hG' N')

section DevAtoms

variable (Λ : ℕ)

@[simp] theorem evalA_zat8 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (.zat 8) e = devTheta4 e.a := rfl
@[simp] theorem evalA_zat9 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (.zat 9) e = devE2 e.a := rfl
@[simp] theorem evalB_zat8 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (.zat 8) e = devTheta4 e.b := rfl
@[simp] theorem evalB_zat9 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (.zat 9) e = devE2 e.b := rfl

end DevAtoms

/-! ## The two expressions -/

/-- The quasimodular part of the coefficient of `t̂`, in its building blocks. -/
def plus12E (Λ : ℕ) (E2a Va Wa E2b Vb Wb : IExpr) : IExpr :=
  .cst (96 * Λ) * d256E Va Wa *
    (12 * (E2a - 3 * uhE) * e4E Va Wa * e4E Vb Wb * f6E Vb Wb -
      12 * f6E Va Wa * e4E Vb Wb ^ 2 * E2b + 36 * thE * f6E Va Wa * e4E Vb Wb ^ 2)

/-- The logarithmic part of the coefficient of `t̂`, in its building blocks. -/
def minus12E (Λ : ℕ) (Va Wa lA lSA Vb Wb lB : IExpr) : IExpr :=
  d256E Va Wa *
      (-3456 * e4E Va Wa * e4E Vb Wb * f6E Vb Wb * (lB * thE - .cst Λ) * uhE +
        3456 * psi4E Λ Va Wa lA lSA * e4E Vb Wb ^ 2 * Wb * thE) +
    128 * t2E Λ Va Wa lA lSA * xb2E Vb Wb * thE

/-- The reduced part without `t̂` as an expression in its building blocks. -/
def numTilE (Λ : ℕ) (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) : IExpr :=
  -(.cst (96 * Λ) * ((Vb + Wb) * Vt * Wb * ((Vb + Wb) * Vb * Wb) * t1E E2a Va Wa +
    d256E Va Wa * (f6E Va Wa * e4E Vb Wb ^ 2 *
        (Et * (E2b + 1) - (xz * Vt ^ 2 + Vt * Wb + Wt * (Wb + 1))) +
      2 * ((E2a - 3 * uhE) * e4E Va Wa) * e4E Vb Wb *
        (2 * (xz * Vt ^ 2 + Vt * Wb + Wt * (Wb + 1)) * (e4E Vb Wb + 1) -
          (((Vt + 2 * Wt) * (2 * Vb + Wb) * (Wb - Vb) + 2 * (2 * Vt + Wt) * (Wb - Vb) +
            2 * (Wt - Vt)) * E2b + 2 * Et)))))

/-- `Ṽ = 16 η₁⁴` on the `z`-side. -/
def vtilZ : IExpr := 16 * (.zat 3) ^ 4

/-- `W̃ = (θ₄⁴ − 1)/x = ((θ₄ − 1)/x)(θ₄³ + θ₄² + θ₄ + 1)` on the `z`-side. -/
def wtilZ : IExpr := .zat 8 * ((.zat 2) ^ 3 + (.zat 2) ^ 2 + .zat 2 + 1)

/-- The quasimodular part of the coefficient of `t̂`. -/
def plusE (Λ : ℕ) : IExpr := plus12E Λ (.tat 4) vT wT (.zat 4) vZ wZ

/-- The logarithmic part of the coefficient of `t̂`. -/
def minusE (Λ : ℕ) : IExpr := minus12E Λ vT wT (l0T Λ) lSE vZ wZ (l0Z Λ)

/-- The coefficient of `t̂` in the numerator of `𝒦̂`. -/
def e12E (Λ : ℕ) : IExpr := -(plusE Λ + minusE Λ)

/-- The coefficient of `t̂` in the numerator of `𝒦`, with the sign of the numerator changed. -/
def e12SE (Λ : ℕ) : IExpr := plusE Λ - minusE Λ

/-- The part of the numerator without `t̂`, divided by the nome of the second variable. -/
def etilE (Λ : ℕ) : IExpr :=
  numTilE Λ (.tat 4) vT wT (.zat 0) vtilZ wtilZ (.zat 9) (.zat 4) vZ wZ

/-- The same with the opposite sign, for the kernel `𝒦`. -/
def netilE (Λ : ℕ) : IExpr := -etilE Λ

/-- `256Δ · E₄² · 2E₆` on the `τ`-side: the factor of the diagonal value of `e12SE`. -/
def kE : IExpr := d256E vT wT * e4E vT wT ^ 2 * f6E vT wT

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ)

theorem evalA_plus12E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalA fs (plus12E Λ E2a Va Wa E2b Vb Wb) e =
      axPlus12 Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
        (IExpr.evalA fs E2b e) (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) e.t := by
  simp only [plus12E, axPlus12, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul,
    IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E,
    evalA_uhE, evalA_thE]
  push_cast
  ring

theorem evalB_plus12E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalB fs (plus12E Λ E2a Va Wa E2b Vb Wb) e =
      axPlus12 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
        (IExpr.evalB fs E2b e) (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) e.t := by
  simp only [plus12E, axPlus12, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul,
    IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E,
    evalB_uhE, evalB_thE]
  push_cast
  ring

theorem evalA_minus12E (Va Wa lA lSA Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalA fs (minus12E Λ Va Wa lA lSA Vb Wb lB) e =
      axMinus12 Λ (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) (IExpr.evalA fs lA e)
        (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e)
        (IExpr.evalA fs lB e) e.t := by
  simp only [minus12E, t2E, xb2E, psi2E, psi4E, axMinus12, axT2, axXb2, axPsi2h, axPsi4h,
    IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat,
    IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE, evalA_thE]
  push_cast
  ring

theorem evalB_minus12E (Va Wa lA lSA Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalB fs (minus12E Λ Va Wa lA lSA Vb Wb lB) e =
      axMinus12 Λ (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) (IExpr.evalB fs lA e)
        (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e)
        (IExpr.evalB fs lB e) e.t := by
  simp only [minus12E, t2E, xb2E, psi2E, psi4E, axMinus12, axT2, axXb2, axPsi2h, axPsi4h,
    IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat,
    IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE, evalB_thE]
  push_cast
  ring

theorem evalA_numTilE (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalA fs (numTilE Λ E2a Va Wa xz Vt Wt Et E2b Vb Wb) e =
      axEtil Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
        (IExpr.evalA fs xz e) (IExpr.evalA fs Vt e) (IExpr.evalA fs Wt e) (IExpr.evalA fs Et e)
        (IExpr.evalA fs E2b e) (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) := by
  simp only [numTilE, t1E, axEtil, axT1, axD256r, axZeta1, axZeta2, axEps4, axPhi6,
    IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat,
    IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE]
  push_cast
  ring

theorem evalB_numTilE (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalB fs (numTilE Λ E2a Va Wa xz Vt Wt Et E2b Vb Wb) e =
      axEtil Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
        (IExpr.evalB fs xz e) (IExpr.evalB fs Vt e) (IExpr.evalB fs Wt e) (IExpr.evalB fs Et e)
        (IExpr.evalB fs E2b e) (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) := by
  simp only [numTilE, t1E, axEtil, axT1, axD256r, axZeta1, axZeta2, axEps4, axPhi6,
    IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat,
    IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE]
  push_cast
  ring

theorem plusE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (plusE Λ) e =
      axPlus12 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.a) (nomeV e.a) (nomeW e.a)
        e.t := by
  rw [plusE, evalA_plus12E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_tat4, evalA_zat4]
  rfl

theorem plusE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (plusE Λ) e =
      axPlus12 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b)
        e.t := by
  rw [plusE, evalB_plus12E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_tat4, evalB_zat4]
  rfl

theorem minusE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (minusE Λ) e =
      axMinus12 Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u (nomeV e.a)
        (nomeW e.a) (Λ * nomeL0 e.l e.a) e.t := by
  rw [minusE, evalA_minus12E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T, evalA_l0Z,
    evalA_lSE]

theorem minusE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (minusE Λ) e =
      axMinus12 Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u (nomeV e.b)
        (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [minusE, evalB_minus12E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_l0Z,
    evalB_lSE]

/-- The `a`-version of the coefficient of `t̂` vanishes. -/
theorem e12E_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (e12E Λ) e = 0 := by
  rw [e12E, IExpr.evalA_neg, IExpr.evalA_add, plusE_evalA, minusE_evalA]
  have h := axE12_diag (Λ : ℝ) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a)
    (Λ * nomeLS e.a) e.u e.t
  rw [axE12] at h
  exact h

theorem e12E_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (e12E Λ) e =
      axE12 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [e12E, IExpr.evalB_neg, IExpr.evalB_add, plusE_evalB, minusE_evalB]
  rfl

end Eval

/-- The reduced quantities at a nome `x ∈ [0, 1)`. -/
theorem reduced_spec {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeE2 x = 1 + x * devE2 x ∧ nomeV x = x * (16 * nomeEta1 x ^ 4) ∧
      nomeW x = 1 + x * (devTheta4 x *
        (nomeTheta4 x ^ 3 + nomeTheta4 x ^ 2 + nomeTheta4 x + 1)) := by
  refine ⟨nomeE2_eq_one_add x, ?_, ?_⟩
  · simp only [nomeV]
    ring
  · have h := nomeTheta4_eq_one_add hx0 hx1
    simp only [nomeW]
    linear_combination (nomeTheta4 x ^ 3 + nomeTheta4 x ^ 2 + nomeTheta4 x + 1) * h

theorem etilE_evalB_aux (Λ : ℕ) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) e =
      axEtil Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
        (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1))
        (devE2 e.b) (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  rw [etilE, evalB_numTilE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ]
  simp [vtilZ, wtilZ, genFun]

theorem etilE_evalA_aux (Λ : ℕ) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (etilE Λ) e =
      axEtil Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
        (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1))
        (devE2 e.a) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) := by
  rw [etilE, evalA_numTilE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ]
  simp [vtilZ, wtilZ, genFun]

/-- The nome times the reduced expression is the part of the numerator without `t̂`. -/
theorem etilE_evalB (Λ : ℕ) {e : NEnv} (hb0 : 0 ≤ e.b) (hb1 : e.b < 1) :
    e.b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) e =
      axE0 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec hb0 hb1
  rw [etilE_evalB_aux]
  have key := axE0_eq_mul Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
    (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1)) (devE2 e.b)
  rw [← h1, ← h2, ← h3] at key
  exact key.symm

/-- The `a`-version of the reduced expression vanishes. -/
theorem etilE_evalA (Λ : ℕ) {e : NEnv} (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (etilE Λ) e = 0 := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec ha0.le ha1
  have key := axE0_eq_mul Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
    (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1)) (devE2 e.a)
  rw [← h1, ← h2, ← h3, axE0_diag] at key
  rw [etilE_evalA_aux]
  rcases mul_eq_zero.mp key.symm with h | h
  · exact absurd h ha0.ne'
  · exact h

/-- **The split numerator on the axes**: `t̂ · e12E + b · etilE` is a positive multiple of
`Φ'`. -/
theorem split_eval_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    (axisNEnv u t).t * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (e12E Λ) (axisNEnv u t) +
        (axisNEnv u t).b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) (axisNEnv u t) =
      1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
  have hb0 : 0 ≤ (axisNEnv u t).b := (Real.exp_pos _).le
  have hb1 : (axisNEnv u t).b < 1 := by
    have hπ := Real.pi_pos
    have hneg : -π * t < 0 := by nlinarith [mul_pos hπ ht]
    exact Real.exp_lt_one_iff.mpr hneg
  rw [etilE_evalB Λ hb0 hb1, e12E_evalB, ← kernelE_eval_axis Λ devAtoms hu ht, kernelE_evalB,
    axE_split]
  ring

end E8Leech.Kron
