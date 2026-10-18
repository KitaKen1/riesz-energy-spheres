import E8Leech.KronLeechSignS
import E8Leech.KronLeechCusp

/-!
# The numerator of the truncated Leech kernel inequality (6.4)(2)

With `a₁ t e^{2πt} + a₀ e^{2πt}` the growing part of the cusp profile of `𝒦̂⁽²⁴⁾(iu, i·)`,
`b = e^{−πt}`, `𝒩 = Δ(it) E₄(iu)³ − Δ(iu) E₄(it)³`, `D̃ = 256 Δ(it)/b²` and the integer numerator
`axE24 = 24576 Λ π û t̂² Φ₂₄` of `KronLeechExpr`, put

`H₂ := 256 axE24 + t̂ (ε₁ − t̂ ε₂) D̃ · 256 𝒩
     = 21743271936 · Λ π û t̂² Δ(it) 𝒩 · (𝒦̂(iu, it) − e^{2πt}(a₁ t + a₀))`,

where `ε₁ = −331776 Λ û a₁` and `ε₂ = 331776 Λ π û a₀` are polynomials in the generators at `iu`.
Since `axE24 = −Σ Aₖ Zₖ` and `256 Δ(iu) (ε₁ − t̂ ε₂) = −Σ Aₖ Zₖ¹(∞)` with the values at the cusp of
the coefficients `Zₖ¹` of `t̂` of the `z`-side factors (`axH2_cusp`),

`H₂ = X₀ + t̂ X₁`, `X₀ = 256 · axE240`,
`X₁ = −Σ Aₖ (256 Zₖ¹ − D̃ E₄(it)³ Zₖ¹(∞)) + b² D̃² E₄(iu)³ (ε₁ − t̂ ε₂)`.

Every `z`-side factor of `X₁` vanishes to the second order at the cusp `b = 0`, and those of `X₀`
to the fourth order; both parts vanish when the generators of the second variable equal those of
the first.

* `axH2_cusp`, `axH21_eq`, `axH2_split`: the algebraic identities.
* `leechH20E`, `leechH21E`: the two expressions; `leechH20E_evalA`, `leechH21E_evalA`: their
  `a`-versions vanish.
* `leechH2_eval_axis`: `X₀ + t̂ X₁` on the axes is the multiple above of the truncated kernel.

Nothing about signs is proved in this file.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The real polynomials -/

/-- `ε₁ = −331776 Λ û a₁`. -/
def axEps1 (Λ E2 V W uh : ℝ) : ℝ := -(8 * Λ * axCuspF E2 V W uh)

/-- `ε₂ = 331776 Λ π û a₀`. -/
def axEps2 (Λ E2 V W lA lSA uh l : ℝ) : ℝ :=
  8 * (-(3 * Λ * axCuspF E2 V W uh) + 81 * Λ * E2 * axD256 V W - 9 * axCA2 Λ V W lA lSA uh -
    81 * Λ * (4 * l - 1) * uh * axD256 V W)

theorem axEps1_eq (Λ E2 V W : ℝ) {u : ℝ} (hu : u ≠ 0) :
    axEps1 Λ E2 V W (1 / (π * u)) = -(331776 * Λ * (1 / (π * u)) * axCuspA1 E2 V W u) := by
  rw [axEps1, axCuspF_eq E2 V W hu]
  ring

theorem axEps2_eq (Λ E2 V W L0 LS : ℝ) {u : ℝ} (hu : u ≠ 0) :
    axEps2 Λ E2 V W (Λ * L0) (Λ * LS) (1 / (π * u)) (Real.log 2) =
      331776 * Λ * π * (1 / (π * u)) * axCuspA0 E2 V W (L0 - π * u) LS u := by
  have hπ := Real.pi_ne_zero
  have h := axCuspH_eq Λ 0 1 E2 V W L0 LS hu
  have e : axCuspH Λ 0 1 E2 V W (Λ * L0) (Λ * LS) (1 / (π * u)) (1 / π) (Real.log 2) =
      1 / π * (axEps2 Λ E2 V W (Λ * L0) (Λ * LS) (1 / (π * u)) (Real.log 2) / 8) := by
    simp only [axCuspH, axEps2]
    ring
  rw [e] at h
  field_simp at h ⊢
  linarith

/-- `256 Δ / x²` in the generators: `256 η₁⁸ (V + W)² W²`. -/
def axDtil (η V W : ℝ) : ℝ := 256 * η ^ 8 * (V + W) ^ 2 * W ^ 2

theorem axD256_eq_sq_mul (x η W : ℝ) :
    axD256 (16 * x * η ^ 4) W = x ^ 2 * axDtil η (16 * x * η ^ 4) W := by
  simp only [axD256, axDtil]
  ring

/-- The part of the truncated numerator without `t̂`. -/
def axH20 (Λ E2a Va Wa uh E2b Vb Wb : ℝ) : ℝ :=
  -(256 * (axLA1 Λ E2a Va Wa uh * axLZ10 E2b Vb Wb + axLA2 Λ E2a Va Wa uh * axLZ20 E2b Vb Wb +
    axLA3 Λ E2a Va Wa uh * axLZ30 E2b Vb Wb))

/-- The coefficient of `t̂` of the truncated numerator; `Dt` stands for `D̃` and `l` for `log 2`. -/
def axH21 (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) : ℝ :=
  -(axLA1 Λ E2a Va Wa uh * (256 * axLZ11 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ11 1 0 1 th) +
      axLA2 Λ E2a Va Wa uh *
        (256 * axLZ21 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ21 1 0 1 th) +
      axLA3 Λ E2a Va Wa uh *
        (256 * axLZ31 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ31 1 0 1 th) +
      axLA4 Va Wa uh *
        (256 * axLZ41 Λ Vb Wb lB th - Dt * axE4 Vb Wb ^ 3 * axLZ41 Λ 0 1 (4 * Λ * l) th) +
      axLA5 Λ Va Wa lA lSA uh * (256 * axLZ51 Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ51 0 1 th) +
      axLA6 Λ Va Wa lA lSA uh * (256 * axLZ61 Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ61 0 1 th)) +
    axD256 Vb Wb * Dt * axE4 Va Wa ^ 3 *
      (axEps1 Λ E2a Va Wa uh - th * axEps2 Λ E2a Va Wa lA lSA uh l)

/-- **The cusp identity.** The pairing of the `τ`-side factors with the values at the cusp of the
coefficients of `t̂` is `−256 Δ (ε₁ − t̂ ε₂)`. -/
theorem axH2_cusp (Λ E2a Va Wa lA lSA uh th l : ℝ) :
    axLA1 Λ E2a Va Wa uh * axLZ11 1 0 1 th + axLA2 Λ E2a Va Wa uh * axLZ21 1 0 1 th +
        axLA3 Λ E2a Va Wa uh * axLZ31 1 0 1 th +
        axLA4 Va Wa uh * axLZ41 Λ 0 1 (4 * Λ * l) th +
        axLA5 Λ Va Wa lA lSA uh * axLZ51 0 1 th + axLA6 Λ Va Wa lA lSA uh * axLZ61 0 1 th =
      -(axD256 Va Wa * (axEps1 Λ E2a Va Wa uh - th * axEps2 Λ E2a Va Wa lA lSA uh l)) := by
  simp only [axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51,
    axLZ61, axEps1, axEps2, axCuspF, axCY2, axCZ4, axCA2, axT1h, axT2h, axPsi2h, axPsi4h, axF6,
    axD256, axE4]
  ring

theorem axH20_eq (Λ E2a Va Wa uh E2b Vb Wb : ℝ) :
    axH20 Λ E2a Va Wa uh E2b Vb Wb = 256 * axE240 Λ E2a Va Wa uh E2b Vb Wb := by
  simp only [axH20, axE240, axLPlus0]
  ring

/-- The coefficient of `t̂` in terms of the one of the numerator. -/
theorem axH21_eq (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) :
    axH21 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt =
      256 * axE2412 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th +
        (axEps1 Λ E2a Va Wa uh - th * axEps2 Λ E2a Va Wa lA lSA uh l) * Dt *
          (axD256 Vb Wb * axE4 Va Wa ^ 3 - axD256 Va Wa * axE4 Vb Wb ^ 3) := by
  have hC := axH2_cusp Λ E2a Va Wa lA lSA uh th l
  simp only [axH21, axE2412, axLPlus12, axLMinus12]
  linear_combination (Dt * axE4 Vb Wb ^ 3) * hC

/-- **The truncated numerator is split by powers of `t̂`.** -/
theorem axH2_split (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) :
    axH20 Λ E2a Va Wa uh E2b Vb Wb +
        th * axH21 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt =
      256 * axE24 Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th +
        th * (axEps1 Λ E2a Va Wa uh - th * axEps2 Λ E2a Va Wa lA lSA uh l) * Dt *
          (axD256 Vb Wb * axE4 Va Wa ^ 3 - axD256 Va Wa * axE4 Vb Wb ^ 3) := by
  rw [axH20_eq, axH21_eq, axE24]
  ring

/-- The part without `t̂` vanishes on the diagonal. -/
theorem axH20_diag (Λ E2 V W uh : ℝ) : axH20 Λ E2 V W uh E2 V W = 0 := by
  rw [axH20_eq, axE240_diag, mul_zero]

/-- The coefficient of `t̂` vanishes on the diagonal. -/
theorem axH21_diag (Λ E2 V W lA lSA uh th l Dt : ℝ) :
    axH21 Λ E2 V W lA lSA uh E2 V W lA th l Dt = 0 := by
  rw [axH21_eq, axE2412_diag]
  ring

/-! ## The expressions -/

/-- `ε₁` in the atoms of the first variable. -/
def eps1E (Λ : ℕ) (E2a Va Wa : IExpr) : IExpr := -(.cst (8 * Λ) * cuspFE E2a Va Wa)

/-- `ε₂` in the atoms of the first variable. -/
def eps2E (Λ : ℕ) (E2a Va Wa lA lSA : IExpr) : IExpr :=
  8 * (-(.cst (3 * Λ) * cuspFE E2a Va Wa) + .cst (81 * Λ) * E2a * d256E Va Wa -
    9 * ca2E Λ Va Wa lA lSA - .cst (81 * Λ) * (4 * l2E - 1) * uhE * d256E Va Wa)

/-- The parts without `t̂` of the first three `z`-side factors. -/
def lz10E (E2b Vb Wb : IExpr) : IExpr := d256E Vb Wb * (e4E Vb Wb - E2b ^ 2)

def lz20E (E2b Vb Wb : IExpr) : IExpr :=
  9 * d256E Vb Wb * E2b ^ 2 + 8 * e4E Vb Wb ^ 3 * (E2b ^ 2 - e4E Vb Wb)

def lz30E (E2b Vb Wb : IExpr) : IExpr :=
  e4E Vb Wb ^ 2 * (7 * e4E Vb Wb * (E2b ^ 2 - e4E Vb Wb) + (2 * e4E Vb Wb ^ 2 - f6E Vb Wb * E2b))

/-- The part of the truncated numerator without `t̂`. -/
def h20E (Λ : ℕ) (E2a Va Wa E2b Vb Wb : IExpr) : IExpr :=
  -(256 * (la1E Λ E2a Va Wa * lz10E E2b Vb Wb + la2E Λ E2a Va Wa * lz20E E2b Vb Wb +
    la3E Λ E2a Va Wa * lz30E E2b Vb Wb))

/-- The coefficient of `t̂` of the truncated numerator; `Dt` is the expression of `D̃`. -/
def h21E (Λ : ℕ) (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) : IExpr :=
  -(la1E Λ E2a Va Wa * (256 * lz11E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz11E 1 0 1) +
      la2E Λ E2a Va Wa * (256 * lz21E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz21E 1 0 1) +
      la3E Λ E2a Va Wa * (256 * lz31E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz31E 1 0 1) +
      la4E Va Wa *
        (256 * lz41E Λ Vb Wb lB - Dt * e4E Vb Wb ^ 3 * lz41E Λ 0 1 (.cst (4 * Λ) * l2E)) +
      la5E Λ Va Wa lA lSA * (256 * lz51E Vb Wb - Dt * e4E Vb Wb ^ 3 * lz51E 0 1) +
      la6E Λ Va Wa lA lSA * (256 * lz61E Vb Wb - Dt * e4E Vb Wb ^ 3 * lz61E 0 1)) +
    d256E Vb Wb * Dt * e4E Va Wa ^ 3 * (eps1E Λ E2a Va Wa - thE * eps2E Λ E2a Va Wa lA lSA)

/-- `256 Δ / x²` at the second variable: `256 η₁⁸ (V + W)² W²`. -/
def dtilZ : IExpr := 256 * (.zat 3) ^ 8 * (vZ + wZ) ^ 2 * wZ ^ 2

/-- **The part without `t̂` of the truncated Leech numerator.** -/
def leechH20E (Λ : ℕ) : IExpr := h20E Λ (.tat 4) vT wT (.zat 4) vZ wZ

/-- **The coefficient of `t̂` of the truncated Leech numerator.** -/
def leechH21E (Λ : ℕ) : IExpr :=
  h21E Λ (.tat 4) vT wT (l0T Λ) lSE (.zat 4) vZ wZ (l0Z Λ) dtilZ

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ) (ex : List (ℝ → ℝ))

theorem evalB_h20E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalB fs (h20E Λ E2a Va Wa E2b Vb Wb) e =
      axH20 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
        (IExpr.evalB fs E2b e) (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) := by
  simp only [h20E, la1E, la2E, la3E, lz10E, lz20E, lz30E, t1hE, axH20, axLA1, axLA2, axLA3,
    axLZ10, axLZ20, axLZ30, axT1h, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul,
    IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E,
    evalB_d256E, evalB_uhE]
  push_cast
  ring

theorem evalA_h20E (E2a Va Wa E2b Vb Wb : IExpr) (e : NEnv) :
    IExpr.evalA fs (h20E Λ E2a Va Wa E2b Vb Wb) e =
      axH20 Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
        (IExpr.evalA fs E2b e) (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) := by
  simp only [h20E, la1E, la2E, la3E, lz10E, lz20E, lz30E, t1hE, axH20, axLA1, axLA2, axLA3,
    axLZ10, axLZ20, axLZ30, axT1h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul,
    IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E,
    evalA_d256E, evalA_uhE]
  push_cast
  ring

theorem evalB_h21E (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) (e : NEnv) :
    IExpr.evalB fs (h21E Λ E2a Va Wa lA lSA E2b Vb Wb lB Dt) e =
      axH21 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e)
        (IExpr.evalB fs lA e) (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs E2b e)
        (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) (IExpr.evalB fs lB e) e.t e.l
        (IExpr.evalB fs Dt e) := by
  simp only [h21E, eps1E, eps2E, cuspFE, cy2E, cz4E, ca2E, la1E, la2E, la3E, la4E, la5E, la6E,
    lz11E, lz21E, lz31E, lz41E, lz51E, lz61E, t1hE, t2hE, psi2E, psi4E, axH21, axEps1, axEps2,
    axCuspF, axCY2, axCZ4, axCA2, axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31,
    axLZ41, axLZ51, axLZ61, axT1h, axT2h, axPsi2h, axPsi4h, IExpr.evalB_add, IExpr.evalB_sub,
    IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst,
    evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE, evalB_thE, evalB_l2E]
  push_cast
  ring

theorem evalA_h21E (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) (e : NEnv) :
    IExpr.evalA fs (h21E Λ E2a Va Wa lA lSA E2b Vb Wb lB Dt) e =
      axH21 Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e)
        (IExpr.evalA fs lA e) (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs E2b e)
        (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) (IExpr.evalA fs lB e) e.t e.l
        (IExpr.evalA fs Dt e) := by
  simp only [h21E, eps1E, eps2E, cuspFE, cy2E, cz4E, ca2E, la1E, la2E, la3E, la4E, la5E, la6E,
    lz11E, lz21E, lz31E, lz41E, lz51E, lz61E, t1hE, t2hE, psi2E, psi4E, axH21, axEps1, axEps2,
    axCuspF, axCY2, axCZ4, axCA2, axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31,
    axLZ41, axLZ51, axLZ61, axT1h, axT2h, axPsi2h, axPsi4h, IExpr.evalA_add, IExpr.evalA_sub,
    IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst,
    evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE, evalA_thE, evalA_l2E]
  push_cast
  ring

theorem evalB_dtilZ (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) dtilZ e = axDtil (nomeEta1 e.b) (nomeV e.b) (nomeW e.b) := by
  simp only [dtilZ, axDtil, IExpr.evalB_mul, IExpr.evalB_add, IExpr.evalB_pow, IExpr.evalB_nat,
    evalB_vZ, evalB_wZ, evalB_zat3, genFun]
  push_cast
  ring

/-- The part without `t̂` on the two sides. -/
theorem leechH20E_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechH20E Λ) e =
      axH20 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  rw [leechH20E, evalB_h20E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_tat4, evalB_zat4]
  rfl

/-- The `a`-version of the part without `t̂` vanishes. -/
theorem leechH20E_evalA (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechH20E Λ) e = 0 := by
  rw [leechH20E, evalA_h20E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_tat4, evalA_zat4]
  exact axH20_diag _ _ _ _ _

/-- The coefficient of `t̂` on the two sides. -/
theorem leechH21E_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechH21E Λ) e =
      axH21 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t e.l
        (axDtil (nomeEta1 e.b) (nomeV e.b) (nomeW e.b)) := by
  rw [leechH21E, evalB_h21E, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_l0Z,
    evalB_lSE, evalB_tat4, evalB_zat4, evalB_dtilZ]
  rfl

/-- The `a`-version of the coefficient of `t̂` vanishes. -/
theorem leechH21E_evalA (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechH21E Λ) e = 0 := by
  rw [leechH21E, evalA_h21E, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T, evalA_l0Z,
    evalA_lSE, evalA_tat4, evalA_zat4]
  exact axH21_diag _ _ _ _ _ _ _ _ _ _

end Eval

/-! ## The truncated kernel on the axes -/

/-- **The truncated numerator on the axes.** Off the singular curves, `X₀ + t̂ X₁` is the multiple
`21743271936 Λ π û t̂² Δ(it) 𝒩` of `𝒦̂⁽²⁴⁾(iu, it) − e^{2πt}(a₁ t + a₀)`. -/
theorem leechH2_eval_axis (Λ : ℕ) (ex : List (ℝ → ℝ)) {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechH20E Λ) (axisNEnv u t) +
        (axisNEnv u t).t * IExpr.evalB (kernelAtoms Λ ++ ex) (leechH21E Λ) (axisNEnv u t) =
      21743271936 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 * axDelta (axV t) (axW t) *
        axNu (axV u) (axW u) (axV t) (axW t) *
        ((ckmrvLeechHatKernel (imagPt u) (imagPt t)).re -
          Real.exp (2 * π * t) *
            ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hb : Real.exp (-π * t) ≠ 0 := (Real.exp_pos _).ne'
  have hexp : Real.exp (2 * π * t) * Real.exp (-π * t) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hΔ := axDelta_ne_zero ht
  have hN : axNu (axV u) (axW u) (axV t) (axW t) ≠ 0 := by
    intro h0
    have hden := leechDenominator_axis hu ht
    rw [h0, mul_zero, Complex.ofReal_zero] at hden
    exact (mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _))) (sub_ne_zero.mpr hJ)) hden
  -- the generators of the nome in terms of those on the axis
  have hEu : nomeE2 (Real.exp (-π * u)) = axE2 u := (axE2_eq_nome hu).symm
  have hVu : nomeV (Real.exp (-π * u)) = axV u := (axV_eq_nome hu).symm
  have hWu : nomeW (Real.exp (-π * u)) = axW u := (axW_eq_nome hu).symm
  have hVt : nomeV (Real.exp (-π * t)) = axV t := (axV_eq_nome ht).symm
  have hWt : nomeW (Real.exp (-π * t)) = axW t := (axW_eq_nome ht).symm
  have hLSu : nomeLS (Real.exp (-π * u)) = axLS u := (axLS_eq_nomeLS hu).symm
  have h1 := axEps1_eq (Λ : ℝ) (axE2 u) (axV u) (axW u) hu.ne'
  have h2 := axEps2_eq (Λ : ℝ) (axE2 u) (axV u) (axW u) (nomeL0 (Real.log 2) (Real.exp (-π * u)))
    (axLS u) hu.ne'
  rw [← axL_eq_nomeL0 hu] at h2
  have hD : axD256 (nomeV (Real.exp (-π * t))) (nomeW (Real.exp (-π * t))) =
      Real.exp (-π * t) ^ 2 * axDtil (nomeEta1 (Real.exp (-π * t)))
        (nomeV (Real.exp (-π * t))) (nomeW (Real.exp (-π * t))) :=
    axD256_eq_sq_mul _ _ _
  rw [hVt, hWt] at hD
  have hE := axE24_axis Λ hu ht
  simp only [axisNEnv] at hE
  -- the kernel and the cusp coefficients as real expressions
  rw [ckmrvLeechHatKernel_axis hu ht (sub_ne_zero.mpr hJ), Complex.ofReal_re,
    leechAxisCusp_zero_re hu, leechAxisCusp_one_re hu, leechH20E_evalB, leechH21E_evalB, axH2_split]
  simp only [axisNEnv]
  have key : ∀ c Δ N Φ R : ℝ, Δ * N ≠ 0 →
      c * Δ * N * (Φ / (3456 * (Δ * N)) - R) = c * Φ / 3456 - c * Δ * N * R := by
    intro c Δ N Φ R h
    have hΔ' : Δ ≠ 0 := left_ne_zero_of_mul h
    have hN' : N ≠ 0 := right_ne_zero_of_mul h
    have h1 : Δ * N * (Φ / (3456 * (Δ * N))) = Φ / 3456 := by field_simp
    linear_combination c * h1
  rw [key _ _ _ _ _ (mul_ne_zero hΔ hN), hE, hEu, hVu, hWu, hVt, hWt, hLSu, h1, h2]
  simp only [axNu, axDelta_eq_axD256] at hN hΔ ⊢
  rw [hD] at hN hΔ ⊢
  generalize axDtil (nomeEta1 (Real.exp (-π * t))) (axV t) (axW t) = Dt at hN hΔ ⊢
  generalize axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t)
    (axL t) t = Φ
  generalize axCuspA1 (axE2 u) (axV u) (axW u) u = A1
  generalize axCuspA0 (axE2 u) (axV u) (axW u) (axL u) (axLS u) u = A0
  generalize axD256 (axV u) (axW u) = Da at hN ⊢
  generalize axE4 (axV u) (axW u) = Ea at hN ⊢
  generalize axE4 (axV t) (axW t) = Eb at hN ⊢
  have hE2 : Real.exp (2 * π * t) = (Real.exp (-π * t) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hexp
  rw [hE2]
  generalize Real.exp (-π * t) = b at hb hN hΔ ⊢
  have hDt : Dt ≠ 0 := by
    rintro rfl
    simp at hΔ
  field_simp
  ring

end E8Leech.Kron
