import E8Leech.KronLeechH2
import E8Leech.KronLeechSignK

/-!
# The numerator of the truncated Leech kernel inequality (6.4)(2), first variable inverted

For `q = 1/v` the hat kernel is `𝒦̂⁽²⁴⁾(i/v, ·) = −v¹² 𝒦⁽²⁴⁾(iv, ·)`, the numerator of `𝒦⁽²⁴⁾` is
`axE240 − t̂ · axE2412S = 24576 Λ π û t̂² Φ₂₄ᴷ` (`KronLeechSignK`), and the cusp coefficients at
`1/v` are `a₁(1/v) = π v¹³ Fm / 41472`, `a₀(1/v) = v¹³ Gm / (41472 Λ)` with the polynomials
`Fm = axCuspFm` and `Gm = axGm` in the generators at `iv`. With `D̃ = 256 Δ(it)/b²` and
`M = 256 Δ(it) E₄(iv)³ − 256 Δ(iv) E₄(it)³ = 256 𝒩`,

`H₂ᴷ := 256 (axE240 − t̂ axE2412S) + 8 t̂ (Λ Fm + t̂ Gm) D̃ M
      = −21743271936 · Λ π û t̂² Δ(it) 𝒩 v⁻¹² · (𝒦̂(i/v, it) − e^{2πt}(a₁(1/v) t + a₀(1/v)))`.

The values at the cusp of the coefficients `Zₖ¹` of `t̂` of the `z`-side factors pair with the
`τ`-side factors to `−8 · 256 Δ(iv) (Λ Fm + t̂ Gm)` when the three logarithmic factors enter with
the opposite sign (`axH2K_cusp`). Hence `−H₂ᴷ = N₀ + t̂ N₁` with `N₀ = −256 · axE240` and a
coefficient `N₁` all of whose `z`-side factors vanish to the second order at the cusp `b = 0`.
`N₀` vanishes when the generators of the second variable equal those of the first; `N₁` does not:
its value there is `165888 Λ K (t̂ − û)` with `K = (256Δ)² E₄² · 2E₆` (`leechKE`), as for the
numerator of `𝒦⁽²⁴⁾` itself (`KronLeechSignK`).

* `axGm`, `axGm_eq`: the polynomial of `a₀(1/v)`.
* `axH2K_cusp`, `axN21K_eq`, `axH2K_split`, `axN21K_diag`: the algebraic identities.
* `leechN20E`, `leechN21KE`: the two expressions; `leechN20E_evalA`, `leechN21KE_evalA`: their
  `a`-versions.
* `leechH2K_eval_axis`: `N₀ + t̂ N₁` on the axes is the multiple above of the truncated kernel at
  `(1/v, t)`.

Nothing about signs is proved in this file.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The real polynomials -/

/-- `Gm`, with `v¹⁴ Gm = 41472 Λ v a₀(1/v)`, in the generators at `iv`. -/
def axGm (Λ E2 V W lA lSA uh l : ℝ) : ℝ :=
  -(3 * Λ * axCuspFm E2 V W uh) - 81 * Λ * (E2 - 6 * uh) * axD256 V W -
    9 * axCA2 Λ V W lA lSA uh - 81 * Λ * (4 * l - 1) * uh * axD256 V W

/-- `v¹⁴ Gm = 41472 Λ v a₀(1/v)`; the two logarithms are exchanged by the inversion. -/
theorem axGm_eq (Λ E2 V W L0 LS : ℝ) {v : ℝ} (hv : v ≠ 0) :
    v ^ 14 * axGm Λ E2 V W (Λ * L0) (Λ * LS) (1 / (π * v)) (Real.log 2) =
      41472 * Λ * v *
        axCuspA0 (-v ^ 2 * E2 + 6 * v / π) (v ^ 2 * W) (v ^ 2 * V) LS (L0 - π * v) v⁻¹ := by
  have hπ := Real.pi_ne_zero
  have h := axCuspHm_eq Λ 0 1 E2 V W L0 LS hv
  have e : axCuspHm Λ 0 1 E2 V W (Λ * L0) (Λ * LS) (1 / (π * v)) (1 / π) (Real.log 2) =
      1 / π * axGm Λ E2 V W (Λ * L0) (Λ * LS) (1 / (π * v)) (Real.log 2) := by
    simp only [axCuspHm, axGm]
    ring
  rw [e] at h
  field_simp at h ⊢
  linarith

/-- The coefficient of `t̂` of the truncated numerator at the inverted first variable, with the
opposite sign; `Dt` stands for `D̃` and `l` for `log 2`. -/
def axN21K (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) : ℝ :=
  axLA1 Λ E2a Va Wa uh * (256 * axLZ11 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ11 1 0 1 th) +
      axLA2 Λ E2a Va Wa uh *
        (256 * axLZ21 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ21 1 0 1 th) +
      axLA3 Λ E2a Va Wa uh *
        (256 * axLZ31 E2b Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ31 1 0 1 th) -
      (axLA4 Va Wa uh *
          (256 * axLZ41 Λ Vb Wb lB th - Dt * axE4 Vb Wb ^ 3 * axLZ41 Λ 0 1 (4 * Λ * l) th) +
        axLA5 Λ Va Wa lA lSA uh * (256 * axLZ51 Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ51 0 1 th) +
        axLA6 Λ Va Wa lA lSA uh * (256 * axLZ61 Vb Wb th - Dt * axE4 Vb Wb ^ 3 * axLZ61 0 1 th)) -
    axD256 Vb Wb * Dt * axE4 Va Wa ^ 3 *
      (8 * (Λ * axCuspFm E2a Va Wa uh + th * axGm Λ E2a Va Wa lA lSA uh l))

/-- **The cusp identity at the inverted first variable.** With the three logarithmic factors of
the opposite sign, the pairing of the `τ`-side factors with the values at the cusp of the
coefficients of `t̂` is `−8 · 256 Δ (Λ Fm + t̂ Gm)`. -/
theorem axH2K_cusp (Λ E2a Va Wa lA lSA uh th l : ℝ) :
    axLA1 Λ E2a Va Wa uh * axLZ11 1 0 1 th + axLA2 Λ E2a Va Wa uh * axLZ21 1 0 1 th +
        axLA3 Λ E2a Va Wa uh * axLZ31 1 0 1 th -
        (axLA4 Va Wa uh * axLZ41 Λ 0 1 (4 * Λ * l) th +
          axLA5 Λ Va Wa lA lSA uh * axLZ51 0 1 th + axLA6 Λ Va Wa lA lSA uh * axLZ61 0 1 th) =
      -(8 * axD256 Va Wa *
        (Λ * axCuspFm E2a Va Wa uh + th * axGm Λ E2a Va Wa lA lSA uh l)) := by
  simp only [axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51,
    axLZ61, axGm, axCuspFm, axCY2, axCZ4, axCA2, axT1h, axT2h, axPsi2h, axPsi4h, axF6, axD256,
    axE4]
  ring

/-- The coefficient of `t̂` of the numerator of `𝒦⁽²⁴⁾` on the diagonal. -/
theorem axE2412S_diag (Λ E2 V W lA lSA uh th : ℝ) :
    axE2412S Λ E2 V W lA lSA uh E2 V W lA th =
      648 * Λ * axD256 V W ^ 2 * axE4 V W ^ 2 * axF6 V W * (th - uh) := by
  rw [axE2412S, axLPlus12_diag, axLMinus12_diag]
  ring

/-- The coefficient of `t̂` in terms of the one of the numerator of `𝒦⁽²⁴⁾`. -/
theorem axN21K_eq (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) :
    axN21K Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt =
      256 * axE2412S Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th -
        8 * (Λ * axCuspFm E2a Va Wa uh + th * axGm Λ E2a Va Wa lA lSA uh l) * Dt *
          (axD256 Vb Wb * axE4 Va Wa ^ 3 - axD256 Va Wa * axE4 Vb Wb ^ 3) := by
  have hC := axH2K_cusp Λ E2a Va Wa lA lSA uh th l
  simp only [axN21K, axE2412S, axLPlus12, axLMinus12]
  linear_combination (-(Dt * axE4 Vb Wb ^ 3)) * hC

/-- **The truncated numerator at the inverted first variable is split by powers of `t̂`.** -/
theorem axH2K_split (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt : ℝ) :
    -axH20 Λ E2a Va Wa uh E2b Vb Wb +
        th * axN21K Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th l Dt =
      -(256 * (axE240 Λ E2a Va Wa uh E2b Vb Wb -
            th * axE2412S Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th) +
          8 * th * (Λ * axCuspFm E2a Va Wa uh + th * axGm Λ E2a Va Wa lA lSA uh l) * Dt *
            (axD256 Vb Wb * axE4 Va Wa ^ 3 - axD256 Va Wa * axE4 Vb Wb ^ 3)) := by
  rw [axH20_eq, axN21K_eq]
  ring

/-- The coefficient of `t̂` on the diagonal: `165888 Λ K (t̂ − û)` with `K = (256Δ)² E₄² · 2E₆`. -/
theorem axN21K_diag (Λ E2 V W lA lSA uh th l Dt : ℝ) :
    axN21K Λ E2 V W lA lSA uh E2 V W lA th l Dt =
      165888 * Λ * (axD256 V W ^ 2 * axE4 V W ^ 2 * axF6 V W) * (th - uh) := by
  rw [axN21K_eq, axE2412S_diag]
  ring

/-! ## The expressions -/

/-- `Gm` in the atoms of the first variable. -/
def gmE (Λ : ℕ) (E2a Va Wa lA lSA : IExpr) : IExpr :=
  -(.cst (3 * Λ) * cuspFmE E2a Va Wa) - .cst (81 * Λ) * (E2a - 6 * uhE) * d256E Va Wa -
    9 * ca2E Λ Va Wa lA lSA - .cst (81 * Λ) * (4 * l2E - 1) * uhE * d256E Va Wa

/-- The coefficient of `t̂` at the inverted first variable; `Dt` is the expression of `D̃`. -/
def n21KE (Λ : ℕ) (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) : IExpr :=
  la1E Λ E2a Va Wa * (256 * lz11E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz11E 1 0 1) +
      la2E Λ E2a Va Wa * (256 * lz21E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz21E 1 0 1) +
      la3E Λ E2a Va Wa * (256 * lz31E E2b Vb Wb - Dt * e4E Vb Wb ^ 3 * lz31E 1 0 1) -
      (la4E Va Wa *
          (256 * lz41E Λ Vb Wb lB - Dt * e4E Vb Wb ^ 3 * lz41E Λ 0 1 (.cst (4 * Λ) * l2E)) +
        la5E Λ Va Wa lA lSA * (256 * lz51E Vb Wb - Dt * e4E Vb Wb ^ 3 * lz51E 0 1) +
        la6E Λ Va Wa lA lSA * (256 * lz61E Vb Wb - Dt * e4E Vb Wb ^ 3 * lz61E 0 1)) -
    d256E Vb Wb * Dt * e4E Va Wa ^ 3 *
      (8 * (.cst Λ * cuspFmE E2a Va Wa + thE * gmE Λ E2a Va Wa lA lSA))

/-- **The part without `t̂`, with the opposite sign.** -/
def leechN20E (Λ : ℕ) : IExpr := -leechH20E Λ

/-- **The coefficient of `t̂` at the inverted first variable**, with the opposite sign. -/
def leechN21KE (Λ : ℕ) : IExpr :=
  n21KE Λ (.tat 4) vT wT (l0T Λ) lSE (.zat 4) vZ wZ (l0Z Λ) dtilZ

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ) (ex : List (ℝ → ℝ))

theorem evalB_n21KE (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) (e : NEnv) :
    IExpr.evalB fs (n21KE Λ E2a Va Wa lA lSA E2b Vb Wb lB Dt) e =
      axN21K Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e)
        (IExpr.evalB fs lA e) (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs E2b e)
        (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) (IExpr.evalB fs lB e) e.t e.l
        (IExpr.evalB fs Dt e) := by
  simp only [n21KE, gmE, cuspFmE, cy2E, cz4E, ca2E, la1E, la2E, la3E, la4E, la5E, la6E, lz11E,
    lz21E, lz31E, lz41E, lz51E, lz61E, t1hE, t2hE, psi2E, psi4E, axN21K, axGm, axCuspFm, axCY2,
    axCZ4, axCA2, axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51,
    axLZ61, axT1h, axT2h, axPsi2h, axPsi4h, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul,
    IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E,
    evalB_d256E, evalB_uhE, evalB_thE, evalB_l2E]
  push_cast
  ring

theorem evalA_n21KE (E2a Va Wa lA lSA E2b Vb Wb lB Dt : IExpr) (e : NEnv) :
    IExpr.evalA fs (n21KE Λ E2a Va Wa lA lSA E2b Vb Wb lB Dt) e =
      axN21K Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e)
        (IExpr.evalA fs lA e) (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs E2b e)
        (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) (IExpr.evalA fs lB e) e.t e.l
        (IExpr.evalA fs Dt e) := by
  simp only [n21KE, gmE, cuspFmE, cy2E, cz4E, ca2E, la1E, la2E, la3E, la4E, la5E, la6E, lz11E,
    lz21E, lz31E, lz41E, lz51E, lz61E, t1hE, t2hE, psi2E, psi4E, axN21K, axGm, axCuspFm, axCY2,
    axCZ4, axCA2, axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51,
    axLZ61, axT1h, axT2h, axPsi2h, axPsi4h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul,
    IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E,
    evalA_d256E, evalA_uhE, evalA_thE, evalA_l2E]
  push_cast
  ring

/-- The part without `t̂` on the two sides. -/
theorem leechN20E_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechN20E Λ) e =
      -axH20 Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) e.u (nomeE2 e.b) (nomeV e.b) (nomeW e.b) := by
  rw [leechN20E, IExpr.evalB_neg, leechH20E_evalB]

/-- The `a`-version of the part without `t̂` vanishes. -/
theorem leechN20E_evalA (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechN20E Λ) e = 0 := by
  rw [leechN20E, IExpr.evalA_neg, leechH20E_evalA, neg_zero]

/-- The coefficient of `t̂` on the two sides. -/
theorem leechN21KE_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechN21KE Λ) e =
      axN21K Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t e.l
        (axDtil (nomeEta1 e.b) (nomeV e.b) (nomeW e.b)) := by
  rw [leechN21KE, evalB_n21KE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_l0Z,
    evalB_lSE, evalB_tat4, evalB_zat4, evalB_dtilZ]
  rfl

/-- The `a`-version of the coefficient of `t̂`: `165888 Λ K (t̂ − û)`. -/
theorem leechN21KE_evalA (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechN21KE Λ) e =
      165888 * Λ * IExpr.evalA (kernelAtoms Λ ++ ex) leechKE e * (e.t - e.u) := by
  rw [leechN21KE, evalA_n21KE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T, evalA_l0Z,
    evalA_lSE, evalA_tat4, evalA_zat4, leechKE_evalA]
  exact axN21K_diag _ _ _ _ _ _ _ _ _ _

end Eval

/-! ## The truncated kernel on the axes -/

/-- The numerator of `𝒦⁽²⁴⁾` on the axes in reciprocal variables: a positive multiple of `Φ₂₄ᴷ`. -/
theorem axE24K_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    axE240 Λ (nomeE2 (axisNEnv u t).a) (nomeV (axisNEnv u t).a) (nomeW (axisNEnv u t).a)
        (axisNEnv u t).u (nomeE2 (axisNEnv u t).b) (nomeV (axisNEnv u t).b)
        (nomeW (axisNEnv u t).b) -
      (axisNEnv u t).t *
        axE2412S Λ (nomeE2 (axisNEnv u t).a) (nomeV (axisNEnv u t).a) (nomeW (axisNEnv u t).a)
          (Λ * nomeL0 (axisNEnv u t).l (axisNEnv u t).a) (Λ * nomeLS (axisNEnv u t).a)
          (axisNEnv u t).u (nomeE2 (axisNEnv u t).b) (nomeV (axisNEnv u t).b)
          (nomeW (axisNEnv u t).b) (Λ * nomeL0 (axisNEnv u t).l (axisNEnv u t).b)
          (axisNEnv u t).t =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
          t := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : (1 : ℝ) / (π * t) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ ht.ne')
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr : (1 : ℝ) / (π * (1 / (π * t))) = t := by field_simp
  simp only [axisNEnv]
  rw [axE2412S_eq_axLeechPhiK _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_eq_nome hu,
    axE2_eq_nome ht, axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht,
    axL_eq_nome hu, axL_eq_nome ht, axLS_eq_nome hu]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-- **The truncated numerator at the inverted first variable, on the axes.** Off the singular
curves, `N₀ + t̂ N₁` is the multiple `21743271936 Λ π û t̂² Δ(it) 𝒩 v⁻¹²` of
`𝒦̂⁽²⁴⁾(i/v, it) − e^{2πt}(a₁(1/v) t + a₀(1/v))`. -/
theorem leechH2K_eval_axis (Λ : ℕ) (ex : List (ℝ → ℝ)) {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt v) ≠ kleinModularJ (imagPt t)) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (leechN20E Λ) (axisNEnv v t) +
        (axisNEnv v t).t * IExpr.evalB (kernelAtoms Λ ++ ex) (leechN21KE Λ) (axisNEnv v t) =
      21743271936 * Λ * π * (1 / (π * v)) * (1 / (π * t)) ^ 2 * axDelta (axV t) (axW t) *
        axNu (axV v) (axW v) (axV t) (axW t) * (v ^ 12)⁻¹ *
        ((ckmrvLeechHatKernel (imagPt v⁻¹) (imagPt t)).re -
          Real.exp (2 * π * t) *
            ((leechAxisCusp (-1) v⁻¹ 0).re * t + (leechAxisCusp (-1) v⁻¹ 1).re)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hv' : 0 < v⁻¹ := inv_pos.mpr hv
  have hb : Real.exp (-π * t) ≠ 0 := (Real.exp_pos _).ne'
  have hexp : Real.exp (2 * π * t) * Real.exp (-π * t) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hΔ := axDelta_ne_zero ht
  have hN : axNu (axV v) (axW v) (axV t) (axW t) ≠ 0 := by
    intro h0
    have hden := leechDenominator_axis hv ht
    rw [h0, mul_zero, Complex.ofReal_zero] at hden
    exact (mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _))) (sub_ne_zero.mpr hJ)) hden
  -- the generators of the nome in terms of those on the axis
  have hEv : nomeE2 (Real.exp (-π * v)) = axE2 v := (axE2_eq_nome hv).symm
  have hVv : nomeV (Real.exp (-π * v)) = axV v := (axV_eq_nome hv).symm
  have hWv : nomeW (Real.exp (-π * v)) = axW v := (axW_eq_nome hv).symm
  have hVt : nomeV (Real.exp (-π * t)) = axV t := (axV_eq_nome ht).symm
  have hWt : nomeW (Real.exp (-π * t)) = axW t := (axW_eq_nome ht).symm
  have hLSv : nomeLS (Real.exp (-π * v)) = axLS v := (axLS_eq_nomeLS hv).symm
  -- the cusp coefficients at `1/v` in the generators at `iv`
  have h1 := axCuspFm_eq (axE2 v) (axV v) (axW v) hv.ne'
  have h2 := axGm_eq (Λ : ℝ) (axE2 v) (axV v) (axW v) (nomeL0 (Real.log 2) (Real.exp (-π * v)))
    (axLS v) hv.ne'
  rw [← axL_eq_nomeL0 hv] at h2
  have hF : axCuspFm (axE2 v) (axV v) (axW v) (1 / (π * v)) =
      41472 * (v / π) *
        axCuspA1 (-v ^ 2 * axE2 v + 6 * v / π) (v ^ 2 * axW v) (v ^ 2 * axV v) v⁻¹ / v ^ 14 := by
    rw [eq_div_iff (pow_ne_zero 14 hv.ne'), mul_comm]
    exact h1
  have hG : axGm (Λ : ℝ) (axE2 v) (axV v) (axW v)
      (Λ * nomeL0 (Real.log 2) (Real.exp (-π * v))) (Λ * axLS v) (1 / (π * v)) (Real.log 2) =
      41472 * Λ * v *
        axCuspA0 (-v ^ 2 * axE2 v + 6 * v / π) (v ^ 2 * axW v) (v ^ 2 * axV v) (axLS v) (axL v)
          v⁻¹ / v ^ 14 := by
    rw [eq_div_iff (pow_ne_zero 14 hv.ne'), mul_comm]
    exact h2
  have hD : axD256 (nomeV (Real.exp (-π * t))) (nomeW (Real.exp (-π * t))) =
      Real.exp (-π * t) ^ 2 * axDtil (nomeEta1 (Real.exp (-π * t)))
        (nomeV (Real.exp (-π * t))) (nomeW (Real.exp (-π * t))) :=
    axD256_eq_sq_mul _ _ _
  rw [hVt, hWt] at hD
  have hE := axE24K_axis Λ hv ht
  simp only [axisNEnv] at hE
  have hv12 : (v⁻¹ ^ 12)⁻¹ = v ^ 12 := by rw [inv_pow, inv_inv]
  -- the kernel and the cusp coefficients as real expressions
  rw [ckmrvLeechHatKernel_imagPt_re hv', hv12, inv_inv,
    ckmrvLeechKernel_axis hv ht (sub_ne_zero.mpr hJ), Complex.ofReal_re,
    leechAxisCusp_zero_re hv', leechAxisCusp_one_re hv', axE2_inv hv, axV_inv hv, axW_inv hv,
    axL_inv hv, axLS_inv hv, leechN20E_evalB, leechN21KE_evalB]
  simp only [axisNEnv]
  rw [axH2K_split, hE, hEv, hVv, hWv, hVt, hWt, hLSv, hF, hG]
  have key : ∀ c Δ N w Φ R : ℝ, Δ * N ≠ 0 → w ≠ 0 →
      c * Δ * N * w⁻¹ * (-w * (Φ / (3456 * (Δ * N))) - R) =
        -(c * Φ / 3456) - c * Δ * N * w⁻¹ * R := by
    intro c Δ N w Φ R h hw
    have hΔ' : Δ ≠ 0 := left_ne_zero_of_mul h
    have hN' : N ≠ 0 := right_ne_zero_of_mul h
    have h1 : Δ * N * (Φ / (3456 * (Δ * N))) = Φ / 3456 := by field_simp
    have h2 : w⁻¹ * w = 1 := inv_mul_cancel₀ hw
    linear_combination (-(c * (w⁻¹ * w))) * h1 - (c * Φ / 3456) * h2
  rw [key _ _ _ _ _ _ (mul_ne_zero hΔ hN) (pow_ne_zero 12 hv.ne')]
  simp only [axNu, axDelta_eq_axD256] at hN hΔ ⊢
  rw [hD] at hN hΔ ⊢
  generalize axDtil (nomeEta1 (Real.exp (-π * t))) (axV t) (axW t) = Dt at hN hΔ ⊢
  generalize axLeechPhiK (axE2 v) (axV v) (axW v) (axL v) (axLS v) v (axE2 t) (axV t) (axW t)
    (axL t) t = Φ
  generalize axCuspA1 (-v ^ 2 * axE2 v + 6 * v / π) (v ^ 2 * axW v) (v ^ 2 * axV v) v⁻¹ = A1
  generalize axCuspA0 (-v ^ 2 * axE2 v + 6 * v / π) (v ^ 2 * axW v) (v ^ 2 * axV v) (axLS v)
    (axL v) v⁻¹ = A0
  generalize axD256 (axV v) (axW v) = Da at hN ⊢
  generalize axE4 (axV v) (axW v) = Ea at hN ⊢
  generalize axE4 (axV t) (axW t) = Eb at hN ⊢
  have hE2 : Real.exp (2 * π * t) = (Real.exp (-π * t) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hexp
  rw [hE2]
  generalize Real.exp (-π * t) = b at hb hN hΔ ⊢
  have hDt : Dt ≠ 0 := by
    rintro rfl
    simp at hΔ
  have hv0 : v ≠ 0 := hv.ne'
  field_simp
  ring

end E8Leech.Kron
