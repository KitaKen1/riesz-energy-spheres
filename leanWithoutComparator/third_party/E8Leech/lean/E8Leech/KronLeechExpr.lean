import E8Leech.KronKernelSplit
import E8Leech.LeechAxisNumerator

/-!
# The Leech numerator as an integer bilinear form in reciprocal variables

With `û = 1/(πu)` and `t̂ = 1/(πt)` the axis numerator `Φ₂₄` of `𝒦̂⁽²⁴⁾` (`LeechAxisNumerator`)
satisfies

`axE24 Λ … = 24576 · Λ · π · û · t̂² · Φ₂₄`,

where `axE24 = −Σ_{k ≤ 6} A_k(τ) Z_k(z)` has integer coefficients in the generators, `Λ` times the
logarithms, `û` and `t̂`. The kernel is `O(q_τ²)`, so every `τ`-side factor `A_k` vanishes to the
fourth order in the nome of `τ`; for `A₁` and `A₅` this is a cancellation between their
summands. The factors are kept as separate subexpressions: the polynomial parts of their models
cancel exactly and the remainders of the Taylor models inherit the factor `a⁴`.

The numerator is split by powers of `t̂` as for `d = 8`: `axE24 = axE240 + t̂ · axE2412`. The part
`axE240` vanishes at the cusp of the second variable and is the nome times `axE24til` in the
reduced quantities of `KronKernelSplit`.

* `axE24_eq_axLeechPhi`: the reciprocal-variable identity (`24576 = 2¹³ · 3`).
* `axLPlus12_diag`, `axLMinus12_diag`, `axE2412_diag`, `axE240_diag`: the values on the diagonal.
* `axE240_eq_mul`: the reduction at the cusp.
* `leechE12E`, `leechEtilE`: the two expressions in the ten atoms of `KronKernelSplit`;
  `leechE12E_evalA`, `leechEtilE_evalA`: their `a`-versions vanish. `leechE12E = −(leechPlusE +
  leechMinusE)`; the combination `leechE12SE = leechPlusE − leechMinusE` belongs to `𝒦⁽²⁴⁾`.
* `leech_split_eval_axis`: `t̂ · leechE12E + b · leechEtilE` is the positive multiple of `Φ₂₄` on
  the axes.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The `τ`-side factors -/

/-- `axT1 / E₄²`, divisible by the square of the nome. -/
def axT1h (E2a Va Wa uh : ℝ) : ℝ :=
  axE4 Va Wa * axF6 Va Wa - 4 * (E2a - 3 * uh) * axE4 Va Wa ^ 2 +
    E2a * (E2a - 6 * uh) * axF6 Va Wa

/-- `axT2 / E₄²`, divisible by the square of the nome. -/
def axT2h (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  axPsi2h Λ Va Wa lA lSA uh * axF6 Va Wa - 2 * axPsi4h Λ Va Wa lA lSA uh * axE4 Va Wa

/-- The first factor; the terms of order `a²` of its two summands cancel. -/
def axLA1 (Λ E2a Va Wa uh : ℝ) : ℝ :=
  Λ * (8 * axE4 Va Wa ^ 4 * axT1h E2a Va Wa uh +
    9 * axD256 Va Wa * axE4 Va Wa *
      (10 * (E2a - 3 * uh) * axE4 Va Wa ^ 2 + E2a * (E2a - 6 * uh) * axF6 Va Wa))

def axLA2 (Λ E2a Va Wa uh : ℝ) : ℝ := Λ * axD256 Va Wa * axE4 Va Wa * axT1h E2a Va Wa uh

def axLA3 (Λ E2a Va Wa uh : ℝ) : ℝ := 18 * Λ * axD256 Va Wa ^ 2 * (E2a - 3 * uh)

def axLA4 (Va Wa uh : ℝ) : ℝ := -324 * axD256 Va Wa ^ 2 * uh

/-- The fifth factor; the terms of order `a²` of its two summands cancel. -/
def axLA5 (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  axE4 Va Wa ^ 2 * (72 * axE4 Va Wa ^ 2 * axT2h Λ Va Wa lA lSA uh +
    324 * axD256 Va Wa * (axPsi4h Λ Va Wa lA lSA uh - 2 * Λ * axE4 Va Wa * uh))

def axLA6 (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  -12 * axD256 Va Wa * axE4 Va Wa * axT2h Λ Va Wa lA lSA uh

/-! ## The `z`-side factors, split by powers of `t̂` -/

/-- The parts without `t̂`; each of them vanishes at the cusp. -/
def axLZ10 (E2b Vb Wb : ℝ) : ℝ := axD256 Vb Wb * (axE4 Vb Wb - E2b ^ 2)

def axLZ20 (E2b Vb Wb : ℝ) : ℝ :=
  9 * axD256 Vb Wb * E2b ^ 2 + 8 * axE4 Vb Wb ^ 3 * (E2b ^ 2 - axE4 Vb Wb)

def axLZ30 (E2b Vb Wb : ℝ) : ℝ :=
  axE4 Vb Wb ^ 2 * (7 * axE4 Vb Wb * (E2b ^ 2 - axE4 Vb Wb) +
    (2 * axE4 Vb Wb ^ 2 - axF6 Vb Wb * E2b))

/-- The coefficients of `t̂`. -/
def axLZ11 (E2b Vb Wb th : ℝ) : ℝ := 12 * axD256 Vb Wb * (E2b - 3 * th)

def axLZ21 (E2b Vb Wb th : ℝ) : ℝ :=
  -12 * (9 * axD256 Vb Wb + 8 * axE4 Vb Wb ^ 3) * (E2b - 3 * th)

def axLZ31 (E2b Vb Wb th : ℝ) : ℝ :=
  6 * axE4 Vb Wb ^ 2 * (axF6 Vb Wb - 14 * axE4 Vb Wb * (E2b - 3 * th))

/-- The logarithmic factor; its term of the first order in the nome vanishes. -/
def axLZ41 (Λ Vb Wb lB th : ℝ) : ℝ :=
  axE4 Vb Wb ^ 2 * axF6 Vb Wb * (lB * th - Λ) - 2 * Λ * th * axE4 Vb Wb ^ 3 * Wb

def axLZ51 (Vb Wb th : ℝ) : ℝ := th * axD256 Vb Wb * Wb

/-- Its term of the first order in the nome vanishes. -/
def axLZ61 (Vb Wb th : ℝ) : ℝ :=
  th * (axE4 Vb Wb * axF6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2) + 4 * axE4 Vb Wb ^ 3 * Wb)

/-! ## The numerator -/

/-- The quasimodular part without `t̂` (from `K₊`), with the opposite sign. -/
def axLPlus0 (Λ E2a Va Wa uh E2b Vb Wb : ℝ) : ℝ :=
  axLA1 Λ E2a Va Wa uh * axLZ10 E2b Vb Wb + axLA2 Λ E2a Va Wa uh * axLZ20 E2b Vb Wb +
    axLA3 Λ E2a Va Wa uh * axLZ30 E2b Vb Wb

/-- The quasimodular part of the coefficient of `t̂` (from `K₊`), with the opposite sign. -/
def axLPlus12 (Λ E2a Va Wa uh E2b Vb Wb th : ℝ) : ℝ :=
  axLA1 Λ E2a Va Wa uh * axLZ11 E2b Vb Wb th + axLA2 Λ E2a Va Wa uh * axLZ21 E2b Vb Wb th +
    axLA3 Λ E2a Va Wa uh * axLZ31 E2b Vb Wb th

/-- The logarithmic part of the coefficient of `t̂` (from `K₋`), with the opposite sign. -/
def axLMinus12 (Λ Va Wa lA lSA uh Vb Wb lB th : ℝ) : ℝ :=
  axLA4 Va Wa uh * axLZ41 Λ Vb Wb lB th + axLA5 Λ Va Wa lA lSA uh * axLZ51 Vb Wb th +
    axLA6 Λ Va Wa lA lSA uh * axLZ61 Vb Wb th

/-- The part of the numerator without `t̂`. -/
def axE240 (Λ E2a Va Wa uh E2b Vb Wb : ℝ) : ℝ := -axLPlus0 Λ E2a Va Wa uh E2b Vb Wb

/-- The coefficient of `t̂` in the numerator of `𝒦̂⁽²⁴⁾`. -/
def axE2412 (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  -(axLPlus12 Λ E2a Va Wa uh E2b Vb Wb th + axLMinus12 Λ Va Wa lA lSA uh Vb Wb lB th)

/-- The coefficient of `t̂` in the numerator of `𝒦⁽²⁴⁾` (after the sign change of the whole
numerator): the two parts enter with opposite signs. -/
def axE2412S (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  axLPlus12 Λ E2a Va Wa uh E2b Vb Wb th - axLMinus12 Λ Va Wa lA lSA uh Vb Wb lB th

/-- The integer-scaled numerator of `𝒦̂⁽²⁴⁾`. `lA, lSA, lB` are `Λ` times
`L₀(τ), L_S(τ), L₀(z)`. -/
def axE24 (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  axE240 Λ E2a Va Wa uh E2b Vb Wb + th * axE2412 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th

theorem axE6_eq_axF6 (V W : ℝ) : axE6 V W = axF6 V W / 2 := rfl

theorem axDelta_eq_axD256 (V W : ℝ) : axDelta V W = axD256 V W / 256 := rfl

/-- **The reciprocal-variable identity**: `axE24 = 24576 · Λ π û t̂² Φ₂₄`. -/
theorem axE24_eq_axLeechPhi (Λ E2a Va Wa L0a LSa uh E2b Vb Wb L0b th : ℝ) (hu : uh ≠ 0)
    (ht : th ≠ 0) :
    axE24 Λ E2a Va Wa (Λ * L0a) (Λ * LSa) uh E2b Vb Wb (Λ * L0b) th =
      24576 * Λ * π * uh * th ^ 2 *
        axLeechPhi E2a Va Wa (L0a - π * (1 / (π * uh))) LSa (1 / (π * uh)) E2b Vb Wb
          (L0b - π * (1 / (π * th))) (1 / (π * th)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axE24, axE240, axE2412, axLPlus0, axLPlus12, axLMinus12, axLA1, axLA2, axLA3, axLA4,
    axLA5, axLA6, axLZ10, axLZ20, axLZ30, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51, axLZ61, axT1h,
    axT2h, axPsi2h, axPsi4h, axLeechPhi, axLeechPlusNum, axLeechMinusNum, axNu, axPsiTwo,
    axPsiFour, axE6_eq_axF6, axDelta_eq_axD256]
  generalize axE4 Va Wa = e4a
  generalize axF6 Va Wa = f6a
  generalize axD256 Va Wa = da
  generalize axE4 Vb Wb = e4b
  generalize axF6 Vb Wb = f6b
  generalize axD256 Vb Wb = db
  field_simp
  ring

/-! ## The diagonal -/

/-- The quasimodular part of the coefficient of `t̂` on the diagonal. -/
theorem axLPlus12_diag (Λ E2 V W uh th : ℝ) :
    axLPlus12 Λ E2 V W uh E2 V W th =
      324 * Λ * axD256 V W ^ 2 * axE4 V W ^ 2 * axF6 V W * (th - uh) := by
  simp only [axLPlus12, axLA1, axLA2, axLA3, axLZ11, axLZ21, axLZ31, axT1h]
  ring

/-- The logarithmic part of the coefficient of `t̂` on the diagonal. -/
theorem axLMinus12_diag (Λ V W lA lSA uh th : ℝ) :
    axLMinus12 Λ V W lA lSA uh V W lA th =
      -(324 * Λ * axD256 V W ^ 2 * axE4 V W ^ 2 * axF6 V W * (th - uh)) := by
  simp only [axLMinus12, axLA4, axLA5, axLA6, axLZ41, axLZ51, axLZ61, axT2h, axPsi2h, axPsi4h,
    axF6, axD256, axE4]
  ring

/-- The coefficient of `t̂` vanishes on the diagonal. -/
theorem axE2412_diag (Λ E2 V W lA lSA uh th : ℝ) :
    axE2412 Λ E2 V W lA lSA uh E2 V W lA th = 0 := by
  rw [axE2412, axLPlus12_diag, axLMinus12_diag]
  ring

/-- The part without `t̂` vanishes on the diagonal. -/
theorem axE240_diag (Λ E2 V W uh : ℝ) : axE240 Λ E2 V W uh E2 V W = 0 := by
  simp only [axE240, axLPlus0, axLA1, axLA2, axLA3, axLZ10, axLZ20, axLZ30, axT1h]
  ring

/-- The numerator vanishes when the generators of the second variable equal those of the first,
for independent `û, t̂`. -/
theorem axE24_diag (Λ E2 V W lA lSA uh th : ℝ) : axE24 Λ E2 V W lA lSA uh E2 V W lA th = 0 := by
  rw [axE24, axE240_diag, axE2412_diag]
  ring

/-! ## The reduction at the cusp -/

def axLZ1t (Vt E2b Vb Wb : ℝ) : ℝ := axD256r Vt Vb Wb * (axE4 Vb Wb - E2b ^ 2)

def axLZ2t (x Vt Wt Et E2b Vb Wb : ℝ) : ℝ :=
  9 * axD256r Vt Vb Wb * E2b ^ 2 + 8 * axE4 Vb Wb ^ 3 * axZeta1 x Vt Wt Et E2b Wb

def axLZ3t (x Vt Wt Et E2b Vb Wb : ℝ) : ℝ :=
  axE4 Vb Wb ^ 2 * (7 * axE4 Vb Wb * axZeta1 x Vt Wt Et E2b Wb +
    axZeta2 x Vt Wt Et E2b Vb Wb)

/-- `axE240 / x` in the reduced quantities `Ṽ = V/x`, `W̃ = (W − 1)/x`, `Ẽ = (E₂ − 1)/x`. -/
def axE24til (Λ E2a Va Wa uh x Vt Wt Et E2b Vb Wb : ℝ) : ℝ :=
  -(axLA1 Λ E2a Va Wa uh * axLZ1t Vt E2b Vb Wb +
    axLA2 Λ E2a Va Wa uh * axLZ2t x Vt Wt Et E2b Vb Wb +
    axLA3 Λ E2a Va Wa uh * axLZ3t x Vt Wt Et E2b Vb Wb)

/-- **The reduction at the cusp**: `axE240 = x · axE24til`. -/
theorem axE240_eq_mul (Λ E2a Va Wa uh x Vt Wt Et : ℝ) :
    axE240 Λ E2a Va Wa uh (1 + x * Et) (x * Vt) (1 + x * Wt) =
      x * axE24til Λ E2a Va Wa uh x Vt Wt Et (1 + x * Et) (x * Vt) (1 + x * Wt) := by
  rw [axE240, axLPlus0, axLZ10, axLZ20, axLZ30, axZeta1_spec, axZeta2_spec, axD256r_spec, axE24til,
    axLZ1t, axLZ2t, axLZ3t]
  ring

/-! ## The expressions -/

def t1hE (E2a Va Wa : IExpr) : IExpr :=
  e4E Va Wa * f6E Va Wa - 4 * (E2a - 3 * uhE) * e4E Va Wa ^ 2 + E2a * (E2a - 6 * uhE) * f6E Va Wa

def t2hE (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  psi2E Λ Va Wa lA lSA * f6E Va Wa - 2 * psi4E Λ Va Wa lA lSA * e4E Va Wa

def la1E (Λ : ℕ) (E2a Va Wa : IExpr) : IExpr :=
  .cst Λ * (8 * e4E Va Wa ^ 4 * t1hE E2a Va Wa +
    9 * d256E Va Wa * e4E Va Wa *
      (10 * (E2a - 3 * uhE) * e4E Va Wa ^ 2 + E2a * (E2a - 6 * uhE) * f6E Va Wa))

def la2E (Λ : ℕ) (E2a Va Wa : IExpr) : IExpr :=
  .cst Λ * d256E Va Wa * e4E Va Wa * t1hE E2a Va Wa

def la3E (Λ : ℕ) (E2a Va Wa : IExpr) : IExpr :=
  .cst (18 * Λ) * d256E Va Wa ^ 2 * (E2a - 3 * uhE)

def la4E (Va Wa : IExpr) : IExpr := -324 * d256E Va Wa ^ 2 * uhE

def la5E (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  e4E Va Wa ^ 2 * (72 * e4E Va Wa ^ 2 * t2hE Λ Va Wa lA lSA +
    324 * d256E Va Wa * (psi4E Λ Va Wa lA lSA - .cst (2 * Λ) * e4E Va Wa * uhE))

def la6E (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  -12 * d256E Va Wa * e4E Va Wa * t2hE Λ Va Wa lA lSA

def lz11E (E2b Vb Wb : IExpr) : IExpr := 12 * d256E Vb Wb * (E2b - 3 * thE)

def lz21E (E2b Vb Wb : IExpr) : IExpr :=
  -12 * (9 * d256E Vb Wb + 8 * e4E Vb Wb ^ 3) * (E2b - 3 * thE)

def lz31E (E2b Vb Wb : IExpr) : IExpr :=
  6 * e4E Vb Wb ^ 2 * (f6E Vb Wb - 14 * e4E Vb Wb * (E2b - 3 * thE))

def lz41E (Λ : ℕ) (Vb Wb lB : IExpr) : IExpr :=
  e4E Vb Wb ^ 2 * f6E Vb Wb * (lB * thE - .cst Λ) - .cst (2 * Λ) * thE * e4E Vb Wb ^ 3 * Wb

def lz51E (Vb Wb : IExpr) : IExpr := thE * d256E Vb Wb * Wb

def lz61E (Vb Wb : IExpr) : IExpr :=
  thE * (e4E Vb Wb * f6E Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2) + 4 * e4E Vb Wb ^ 3 * Wb)

/-- `256Δ/x` in its building blocks. -/
def d256rE (Vt Vb Wb : IExpr) : IExpr := (Vb + Wb) * Vt * Wb * ((Vb + Wb) * Vb * Wb)

/-- `(E₄ − 1)/x`. -/
def eps4E (xz Vt Wt Wb : IExpr) : IExpr := xz * Vt ^ 2 + Vt * Wb + Wt * (Wb + 1)

/-- `(E₂² − E₄)/x`. -/
def zeta1E (xz Vt Wt Et E2b Wb : IExpr) : IExpr := Et * (E2b + 1) - eps4E xz Vt Wt Wb

/-- `(2E₄² − 2E₆E₂)/x`. -/
def zeta2E (xz Vt Wt Et E2b Vb Wb : IExpr) : IExpr :=
  2 * eps4E xz Vt Wt Wb * (e4E Vb Wb + 1) -
    (((Vt + 2 * Wt) * (2 * Vb + Wb) * (Wb - Vb) + 2 * (2 * Vt + Wt) * (Wb - Vb) + 2 * (Wt - Vt)) *
      E2b + 2 * Et)

def lz1tE (Vt E2b Vb Wb : IExpr) : IExpr := d256rE Vt Vb Wb * (e4E Vb Wb - E2b ^ 2)

def lz2tE (xz Vt Wt Et E2b Vb Wb : IExpr) : IExpr :=
  9 * d256rE Vt Vb Wb * E2b ^ 2 + 8 * e4E Vb Wb ^ 3 * zeta1E xz Vt Wt Et E2b Wb

def lz3tE (xz Vt Wt Et E2b Vb Wb : IExpr) : IExpr :=
  e4E Vb Wb ^ 2 * (7 * e4E Vb Wb * zeta1E xz Vt Wt Et E2b Wb + zeta2E xz Vt Wt Et E2b Vb Wb)

/-- The quasimodular part of the coefficient of `t̂`, in its building blocks. -/
def leechPlus12E (Λ : ℕ) (E2a Va Wa E2b Vb Wb : IExpr) : IExpr :=
  la1E Λ E2a Va Wa * lz11E E2b Vb Wb + la2E Λ E2a Va Wa * lz21E E2b Vb Wb +
    la3E Λ E2a Va Wa * lz31E E2b Vb Wb

/-- The logarithmic part of the coefficient of `t̂`, in its building blocks. -/
def leechMinus12E (Λ : ℕ) (Va Wa lA lSA Vb Wb lB : IExpr) : IExpr :=
  la4E Va Wa * lz41E Λ Vb Wb lB + la5E Λ Va Wa lA lSA * lz51E Vb Wb +
    la6E Λ Va Wa lA lSA * lz61E Vb Wb

/-- The reduced part without `t̂`, in its building blocks. -/
def leechTilE (Λ : ℕ) (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) : IExpr :=
  -(la1E Λ E2a Va Wa * lz1tE Vt E2b Vb Wb + la2E Λ E2a Va Wa * lz2tE xz Vt Wt Et E2b Vb Wb +
    la3E Λ E2a Va Wa * lz3tE xz Vt Wt Et E2b Vb Wb)

/-- The quasimodular part of the coefficient of `t̂`. -/
def leechPlusE (Λ : ℕ) : IExpr := leechPlus12E Λ (.tat 4) vT wT (.zat 4) vZ wZ

/-- The logarithmic part of the coefficient of `t̂`. -/
def leechMinusE (Λ : ℕ) : IExpr := leechMinus12E Λ vT wT (l0T Λ) lSE vZ wZ (l0Z Λ)

/-- The coefficient of `t̂` in the numerator of `𝒦̂⁽²⁴⁾`. -/
def leechE12E (Λ : ℕ) : IExpr := -(leechPlusE Λ + leechMinusE Λ)

/-- The coefficient of `t̂` in the numerator of `𝒦⁽²⁴⁾`, with the sign of the numerator
changed. -/
def leechE12SE (Λ : ℕ) : IExpr := leechPlusE Λ - leechMinusE Λ

/-- The part of the numerator without `t̂`, divided by the nome of the second variable. -/
def leechEtilE (Λ : ℕ) : IExpr :=
  leechTilE Λ (.tat 4) vT wT (.zat 0) vtilZ wtilZ (.zat 9) (.zat 4) vZ wZ

/-- The same with the opposite sign, for the kernel `𝒦⁽²⁴⁾`. -/
def leechNetilE (Λ : ℕ) : IExpr := -leechEtilE Λ

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ)

theorem evalA_leechPlus12E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalA fs (leechPlus12E Λ E2a Va Wa E2b Vb Wb) e =
      axLPlus12 Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
        (IExpr.evalA fs E2b e) (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) e.t := by
  simp only [leechPlus12E, la1E, la2E, la3E, lz11E, lz21E, lz31E, t1hE, axLPlus12, axLA1, axLA2,
    axLA3, axLZ11, axLZ21, axLZ31, axT1h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul,
    IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E,
    evalA_d256E, evalA_uhE, evalA_thE]
  push_cast
  ring

theorem evalB_leechPlus12E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalB fs (leechPlus12E Λ E2a Va Wa E2b Vb Wb) e =
      axLPlus12 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
        (IExpr.evalB fs E2b e) (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) e.t := by
  simp only [leechPlus12E, la1E, la2E, la3E, lz11E, lz21E, lz31E, t1hE, axLPlus12, axLA1, axLA2,
    axLA3, axLZ11, axLZ21, axLZ31, axT1h, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul,
    IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E,
    evalB_d256E, evalB_uhE, evalB_thE]
  push_cast
  ring

theorem evalA_leechMinus12E (Va Wa lA lSA Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalA fs (leechMinus12E Λ Va Wa lA lSA Vb Wb lB) e =
      axLMinus12 Λ (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) (IExpr.evalA fs lA e)
        (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e)
        (IExpr.evalA fs lB e) e.t := by
  simp only [leechMinus12E, la4E, la5E, la6E, lz41E, lz51E, lz61E, t2hE, psi2E, psi4E, axLMinus12,
    axLA4, axLA5, axLA6, axLZ41, axLZ51, axLZ61, axT2h, axPsi2h, axPsi4h, IExpr.evalA_add,
    IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow,
    IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE, evalA_thE]
  push_cast
  ring

theorem evalB_leechMinus12E (Va Wa lA lSA Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalB fs (leechMinus12E Λ Va Wa lA lSA Vb Wb lB) e =
      axLMinus12 Λ (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) (IExpr.evalB fs lA e)
        (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e)
        (IExpr.evalB fs lB e) e.t := by
  simp only [leechMinus12E, la4E, la5E, la6E, lz41E, lz51E, lz61E, t2hE, psi2E, psi4E, axLMinus12,
    axLA4, axLA5, axLA6, axLZ41, axLZ51, axLZ61, axT2h, axPsi2h, axPsi4h, IExpr.evalB_add,
    IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow,
    IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE, evalB_thE]
  push_cast
  ring

theorem evalA_leechTilE (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalA fs (leechTilE Λ E2a Va Wa xz Vt Wt Et E2b Vb Wb) e =
      axE24til Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
        (IExpr.evalA fs xz e) (IExpr.evalA fs Vt e) (IExpr.evalA fs Wt e) (IExpr.evalA fs Et e)
        (IExpr.evalA fs E2b e) (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) := by
  simp only [leechTilE, la1E, la2E, la3E, lz1tE, lz2tE, lz3tE, d256rE, eps4E, zeta1E, zeta2E, t1hE,
    axE24til, axLA1, axLA2, axLA3, axLZ1t, axLZ2t, axLZ3t, axT1h, axD256r, axZeta1, axZeta2,
    axEps4, axPhi6, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg,
    IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E,
    evalA_uhE]
  push_cast
  ring

theorem evalB_leechTilE (E2a Va Wa xz Vt Wt Et E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalB fs (leechTilE Λ E2a Va Wa xz Vt Wt Et E2b Vb Wb) e =
      axE24til Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
        (IExpr.evalB fs xz e) (IExpr.evalB fs Vt e) (IExpr.evalB fs Wt e) (IExpr.evalB fs Et e)
        (IExpr.evalB fs E2b e) (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) := by
  simp only [leechTilE, la1E, la2E, la3E, lz1tE, lz2tE, lz3tE, d256rE, eps4E, zeta1E, zeta2E, t1hE,
    axE24til, axLA1, axLA2, axLA3, axLZ1t, axLZ2t, axLZ3t, axT1h, axD256r, axZeta1, axZeta2,
    axEps4, axPhi6, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg,
    IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E,
    evalB_uhE]
  push_cast
  ring

theorem leechPlusE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechPlusE Λ) e =
      axLPlus12 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.a) (nomeV e.a) (nomeW e.a)
        e.t := by
  rw [leechPlusE, evalA_leechPlus12E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_tat4,
    evalA_zat4]
  rfl

theorem leechPlusE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechPlusE Λ) e =
      axLPlus12 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b)
        e.t := by
  rw [leechPlusE, evalB_leechPlus12E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_tat4,
    evalB_zat4]
  rfl

theorem leechMinusE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechMinusE Λ) e =
      axLMinus12 Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u (nomeV e.a)
        (nomeW e.a) (Λ * nomeL0 e.l e.a) e.t := by
  rw [leechMinusE, evalA_leechMinus12E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T,
    evalA_l0Z, evalA_lSE]

theorem leechMinusE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechMinusE Λ) e =
      axLMinus12 Λ (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u (nomeV e.b)
        (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [leechMinusE, evalB_leechMinus12E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T,
    evalB_l0Z, evalB_lSE]

/-- The `a`-version of the coefficient of `t̂` vanishes. -/
theorem leechE12E_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechE12E Λ) e = 0 := by
  rw [leechE12E, IExpr.evalA_neg, IExpr.evalA_add, leechPlusE_evalA, leechMinusE_evalA]
  have h := axE2412_diag (Λ : ℝ) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a)
    (Λ * nomeLS e.a) e.u e.t
  rw [axE2412] at h
  exact h

theorem leechE12E_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechE12E Λ) e =
      axE2412 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [leechE12E, IExpr.evalB_neg, IExpr.evalB_add, leechPlusE_evalB, leechMinusE_evalB]
  rfl

/-- The `a`-version of `leechE12SE`: twice the diagonal value of the quasimodular part. -/
theorem leechE12SE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechE12SE Λ) e =
      648 * Λ * axD256 (nomeV e.a) (nomeW e.a) ^ 2 * axE4 (nomeV e.a) (nomeW e.a) ^ 2 *
        axF6 (nomeV e.a) (nomeW e.a) * (e.t - e.u) := by
  rw [leechE12SE, IExpr.evalA_sub, leechPlusE_evalA, leechMinusE_evalA, axLPlus12_diag,
    axLMinus12_diag]
  ring

theorem leechE12SE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechE12SE Λ) e =
      axE2412S Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [leechE12SE, IExpr.evalB_sub, leechPlusE_evalB, leechMinusE_evalB]
  rfl

end Eval

theorem leechEtilE_evalB_aux (Λ : ℕ) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) e =
      axE24til Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
        (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1))
        (devE2 e.b) (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  rw [leechEtilE, evalB_leechTilE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ]
  simp [vtilZ, wtilZ, genFun]

theorem leechEtilE_evalA_aux (Λ : ℕ) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) e =
      axE24til Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
        (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1))
        (devE2 e.a) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) := by
  rw [leechEtilE, evalA_leechTilE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ]
  simp [vtilZ, wtilZ, genFun]

/-- The nome times the reduced expression is the part of the numerator without `t̂`. -/
theorem leechEtilE_evalB (Λ : ℕ) {e : NEnv} (hb0 : 0 ≤ e.b) (hb1 : e.b < 1) :
    e.b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) e =
      axE240 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec hb0 hb1
  rw [leechEtilE_evalB_aux]
  have key := axE240_eq_mul Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.b (16 * nomeEta1 e.b ^ 4)
    (devTheta4 e.b * (nomeTheta4 e.b ^ 3 + nomeTheta4 e.b ^ 2 + nomeTheta4 e.b + 1)) (devE2 e.b)
  rw [← h1, ← h2, ← h3] at key
  exact key.symm

/-- The `a`-version of the reduced expression vanishes. -/
theorem leechEtilE_evalA (Λ : ℕ) {e : NEnv} (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) e = 0 := by
  obtain ⟨h1, h2, h3⟩ := reduced_spec ha0.le ha1
  have key := axE240_eq_mul Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u e.a (16 * nomeEta1 e.a ^ 4)
    (devTheta4 e.a * (nomeTheta4 e.a ^ 3 + nomeTheta4 e.a ^ 2 + nomeTheta4 e.a + 1)) (devE2 e.a)
  rw [← h1, ← h2, ← h3, axE240_diag] at key
  rw [leechEtilE_evalA_aux]
  rcases mul_eq_zero.mp key.symm with h | h
  · exact absurd h ha0.ne'
  · exact h

/-- The numerator on the axes in reciprocal variables: a positive multiple of `Φ₂₄`. -/
theorem axE24_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    axE24 Λ (nomeE2 (axisNEnv u t).a) (nomeV (axisNEnv u t).a) (nomeW (axisNEnv u t).a)
        (Λ * nomeL0 (axisNEnv u t).l (axisNEnv u t).a) (Λ * nomeLS (axisNEnv u t).a)
        (axisNEnv u t).u (nomeE2 (axisNEnv u t).b) (nomeV (axisNEnv u t).b)
        (nomeW (axisNEnv u t).b) (Λ * nomeL0 (axisNEnv u t).l (axisNEnv u t).b)
        (axisNEnv u t).t =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
          t := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : (1 : ℝ) / (π * t) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ ht.ne')
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr : (1 : ℝ) / (π * (1 / (π * t))) = t := by field_simp
  simp only [axisNEnv]
  rw [axE24_eq_axLeechPhi _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_eq_nome hu,
    axE2_eq_nome ht, axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht,
    axL_eq_nome hu, axL_eq_nome ht, axLS_eq_nome hu]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-- **The split Leech numerator on the axes**: `t̂ · leechE12E + b · leechEtilE` is a positive
multiple of `Φ₂₄`. -/
theorem leech_split_eval_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    (axisNEnv u t).t * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechE12E Λ) (axisNEnv u t) +
        (axisNEnv u t).b *
          IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) (axisNEnv u t) =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
          t := by
  have hb0 : 0 ≤ (axisNEnv u t).b := (Real.exp_pos _).le
  have hb1 : (axisNEnv u t).b < 1 := by
    have hπ := Real.pi_pos
    have hneg : -π * t < 0 := by nlinarith [mul_pos hπ ht]
    exact Real.exp_lt_one_iff.mpr hneg
  rw [leechEtilE_evalB Λ hb0 hb1, leechE12E_evalB, ← axE24_axis Λ hu ht, axE24]
  ring

end E8Leech.Kron
