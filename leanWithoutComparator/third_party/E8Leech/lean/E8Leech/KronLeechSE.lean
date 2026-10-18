import E8Leech.KronLeechS
import E8Leech.KronLeechJet3
import E8Leech.KronLeechCorner
import E8Leech.KronKernelSignS
import E8Leech.KronLeechSignK

/-!
# The Leech numerator at `(iu, i/s)` as a bilinear form of expressions

With the second variable inverted (`KronLeechS`) the numerator of `𝒦̂⁽²⁴⁾(iu, i/s)` is `−s¹⁶` times
the pairing of the six `τ`-side factors `leechTauE` with six `z`-side factors `leechZSE`, which are
expressions in the generators of `is`, the logarithm `Λ L_S` and the constant `p = 1/π` (the
fourth slot of the environment `axisNEnvS`). For `𝒦⁽²⁴⁾` the three logarithmic factors change
their sign (`leechZKE`).

Each of the six `z`-side factors vanishes to the third order at the cusp of `is`; the third-order
jets of `KronJet3` remove the cube of the nome.

* `lSZ`, `leechZSPart`, `leechZSE`, `leechZKE`: the expressions.
* `bil_leechS`, `bilA_leechS`: the pairing in terms of `axLPlus0`, `axLMinusS`.
* `bilA_leechZSE`, `bilA_leechZKE`: the `a`-versions of the pairings vanish.
* `leechRS_eval_axis`, `leechSS_eval_axis`: the pairings on the axes.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-- `Λ L_S = 4 (Λ log θ₄) − 4 (Λ log θ₃)` on the `z`-side. -/
def lSZ : IExpr := 4 * .zat 6 - 4 * .zat 5

/-- The six `z`-side factors with the second variable inverted, divided by `s¹⁶`; `σ = 1` for the
kernel `𝒦̂` and `σ = −1` for the kernel `𝒦`. -/
def leechZSPart (Λ : ℕ) (σ : ℤ) (E V W lS : IExpr) : List IExpr :=
  [d256E V W * (e4E V W - E ^ 2),
    9 * d256E V W * E ^ 2 + 8 * e4E V W ^ 3 * (E ^ 2 - e4E V W),
    e4E V W ^ 2 * (7 * e4E V W * (E ^ 2 - e4E V W) + (2 * e4E V W ^ 2 - f6E V W * E)),
    .cst (-σ) * (thE ^ 2 * (e4E V W ^ 2 * f6E V W * lS + .cst (2 * Λ) * e4E V W ^ 3 * V)),
    .cst σ * (thE ^ 2 * (d256E V W * V)),
    .cst σ * (thE ^ 2 *
      (4 * e4E V W ^ 3 * V - e4E V W * f6E V W * ((V + W) ^ 2 - W ^ 2)))]

/-- The `z`-side factors of the kernel `𝒦̂` at `(iu, i/s)`. -/
def leechZSE (Λ : ℕ) : List IExpr := leechZSPart Λ 1 (.zat 4) vZ wZ lSZ

/-- The `z`-side factors of the kernel `𝒦` at `(iu, i/s)`. -/
def leechZKE (Λ : ℕ) : List IExpr := leechZSPart Λ (-1) (.zat 4) vZ wZ lSZ

section Pairing

variable (fs : List (ℝ → ℝ)) (Λ : ℕ)

/-- **The pairing of the factors**, `b`-version. -/
theorem bil_leechS (σ : ℤ) (E2a Va Wa lA lSA E V W lS : IExpr) (e : NEnv) :
    bil ((leechTauPart Λ E2a Va Wa lA lSA).map fun x => IExpr.evalB fs x e)
        ((leechZSPart Λ σ E V W lS).map fun x => IExpr.evalB fs x e) =
      axLPlus0 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) e.u
          (IExpr.evalB fs E e) (IExpr.evalB fs V e) (IExpr.evalB fs W e) +
        σ * axLMinusS Λ (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e) (IExpr.evalB fs lA e)
          (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs V e) (IExpr.evalB fs W e)
          (IExpr.evalB fs lS e) e.t := by
  simp only [leechTauPart, leechZSPart, la1E, la2E, la3E, la4E, la5E, la6E, t1hE, t2hE, psi2E,
    psi4E, List.map_cons, List.map_nil, bil, axLPlus0, axLMinusS, axLA1, axLA2, axLA3, axLA4,
    axLA5, axLA6, axLZ10, axLZ20, axLZ30, axLZS4, axLZS5, axLZS6, axT1h, axT2h, axPsi2h, axPsi4h,
    IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat,
    IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE, evalB_thE]
  push_cast
  ring

/-- **The pairing of the factors**, `a`-version. -/
theorem bilA_leechS (σ : ℤ) (E2a Va Wa lA lSA E V W lS : IExpr) (e : NEnv) :
    bil ((leechTauPart Λ E2a Va Wa lA lSA).map fun x => IExpr.evalA fs x e)
        ((leechZSPart Λ σ E V W lS).map fun x => IExpr.evalA fs x e) =
      axLPlus0 Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) e.u
          (IExpr.evalA fs E e) (IExpr.evalA fs V e) (IExpr.evalA fs W e) +
        σ * axLMinusS Λ (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e) (IExpr.evalA fs lA e)
          (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs V e) (IExpr.evalA fs W e)
          (IExpr.evalA fs lS e) e.t := by
  simp only [leechTauPart, leechZSPart, la1E, la2E, la3E, la4E, la5E, la6E, t1hE, t2hE, psi2E,
    psi4E, List.map_cons, List.map_nil, bil, axLPlus0, axLMinusS, axLA1, axLA2, axLA3, axLA4,
    axLA5, axLA6, axLZ10, axLZ20, axLZ30, axLZS4, axLZS5, axLZS6, axT1h, axT2h, axPsi2h, axPsi4h,
    IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat,
    IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE, evalA_thE]
  push_cast
  ring

/-- The `a`-version of the pairing vanishes: both parts vanish on the diagonal. -/
theorem bilA_leechZS (σ : ℤ) (e : NEnv) :
    bil ((leechTauE Λ).map fun x => IExpr.evalA fs x e)
      ((leechZSPart Λ σ (.zat 4) vZ wZ lSZ).map fun x => IExpr.evalA fs x e) = 0 := by
  have h4 : IExpr.evalA fs (.zat 4) e = IExpr.evalA fs (.tat 4) e := rfl
  have hV : IExpr.evalA fs vZ e = IExpr.evalA fs vT e := rfl
  have hW : IExpr.evalA fs wZ e = IExpr.evalA fs wT e := rfl
  have hS : IExpr.evalA fs lSZ e = IExpr.evalA fs lSE e := rfl
  have h0 := axE240_diag (Λ : ℝ) (IExpr.evalA fs (.tat 4) e) (IExpr.evalA fs vT e)
    (IExpr.evalA fs wT e) e.u
  rw [axE240, neg_eq_zero] at h0
  rw [leechTauE, bilA_leechS, h4, hV, hW, hS, h0, axLMinusS_diag]
  ring

end Pairing

/-! ## The pairings on the axes -/

theorem evalB_lSZ (Λ : ℕ) (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) lSZ e = Λ * nomeLS e.b := by
  simp only [lSZ, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat, evalB_zat5, evalB_zat6,
    logFun, nomeLS]
  push_cast
  ring

/-- The pairing at `axisNEnvS u s` in terms of the numerator of `KronLeechExpr` at the inverted
second variable. -/
theorem bil_leechS_axis (Λ : ℕ) (σ : ℤ) (u s : ℝ) :
    bil ((leechTauE Λ).map fun x => IExpr.evalB (tAtoms Λ) x (axisNEnvS u s))
        ((leechZSPart Λ σ (.zat 4) vZ wZ lSZ).map fun x =>
          IExpr.evalB (tAtoms Λ) x (axisNEnvS u s)) =
      axLPlus0 Λ (nomeE2 (Real.exp (-π * u))) (nomeV (Real.exp (-π * u)))
          (nomeW (Real.exp (-π * u))) (1 / (π * u)) (nomeE2 (Real.exp (-π * s)))
          (nomeV (Real.exp (-π * s))) (nomeW (Real.exp (-π * s))) +
        σ * axLMinusS Λ (nomeV (Real.exp (-π * u))) (nomeW (Real.exp (-π * u)))
          (Λ * nomeL0 (Real.log 2) (Real.exp (-π * u))) (Λ * nomeLS (Real.exp (-π * u)))
          (1 / (π * u)) (nomeV (Real.exp (-π * s))) (nomeW (Real.exp (-π * s)))
          (Λ * nomeLS (Real.exp (-π * s))) (1 / π) := by
  rw [leechTauE, bil_leechS]
  show axLPlus0 Λ (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) (.tat 4) (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) vT (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) wT (axisNEnvS u s)) (axisNEnvS u s).u
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) (.zat 4) (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) vZ (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) wZ (axisNEnvS u s)) +
    σ * axLMinusS Λ (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) vT (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) wT (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) (l0T Λ) (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) lSE (axisNEnvS u s)) (axisNEnvS u s).u
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) vZ (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) wZ (axisNEnvS u s))
      (IExpr.evalB (kernelAtoms Λ ++ red3Atoms Λ) lSZ (axisNEnvS u s)) (axisNEnvS u s).t = _
  rw [evalB_tat4, evalB_zat4, evalB_vT, evalB_wT, evalB_vZ, evalB_wZ, evalB_l0T, evalB_lSE,
    evalB_lSZ]
  rfl

/-- **The numerator of `𝒦̂⁽²⁴⁾` at `(iu, i/s)`**: `−s¹⁶` times the pairing is a positive multiple
of `Φ₂₄`. -/
theorem leechRS_eval_axis (Λ : ℕ) {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    -(s ^ 16 * bil ((leechTauE Λ).map fun x => IExpr.evalB (tAtoms Λ) x (axisNEnvS u s))
        ((leechZSE Λ).map fun x => IExpr.evalB (tAtoms Λ) x (axisNEnvS u s))) =
      24576 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 *
        axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 s⁻¹) (axV s⁻¹) (axW s⁻¹)
          (axL s⁻¹) s⁻¹ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : s * (1 / π) ≠ 0 := mul_ne_zero hs.ne' (one_div_ne_zero hπ)
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr := inv_pi_mul s
  have hlB := axisNEnvS_lB Λ (u := u) hs
  have hlB' : (Λ : ℝ) * (axLS s + π / s) * (s * (1 / π)) - Λ =
      Λ * nomeLS (Real.exp (-π * s)) * (s * (1 / π)) := hlB
  rw [leechZSE, bil_leechS_axis Λ 1 u s, Int.cast_one, one_mul,
    ← axE24_S (Λ : ℝ) _ _ _ _ _ _ _ _ _ _ _ s (1 / π) hlB',
    axE24_eq_axLeechPhi _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_inv hs, axV_inv hs,
    axW_inv hs, axL_inv hs, axE2_eq_nome hu, axE2_eq_nome hs, axV_eq_nome hu, axV_eq_nome hs,
    axW_eq_nome hu, axW_eq_nome hs, axL_eq_nome hu, axLS_eq_nome hu, axLS_eq_nome hs]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-- **The numerator of `𝒦⁽²⁴⁾` at `(iu, i/s)`**: `−s¹⁶` times the pairing with the factors
`leechZKE` is a positive multiple of `Φ₂₄ᴷ`. -/
theorem leechSS_eval_axis (Λ : ℕ) {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    -(s ^ 16 * bil ((leechTauE Λ).map fun x => IExpr.evalB (tAtoms Λ) x (axisNEnvS u s))
        ((leechZKE Λ).map fun x => IExpr.evalB (tAtoms Λ) x (axisNEnvS u s))) =
      24576 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 *
        axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 s⁻¹) (axV s⁻¹)
          (axW s⁻¹) (axL s⁻¹) s⁻¹ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : s * (1 / π) ≠ 0 := mul_ne_zero hs.ne' (one_div_ne_zero hπ)
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr := inv_pi_mul s
  have hlB := axisNEnvS_lB Λ (u := u) hs
  have hlB' : (Λ : ℝ) * (axLS s + π / s) * (s * (1 / π)) - Λ =
      Λ * nomeLS (Real.exp (-π * s)) * (s * (1 / π)) := hlB
  have hK := axE24K_S (Λ : ℝ) (nomeE2 (Real.exp (-π * u))) (nomeV (Real.exp (-π * u)))
    (nomeW (Real.exp (-π * u))) (Λ * nomeL0 (Real.log 2) (Real.exp (-π * u)))
    (Λ * nomeLS (Real.exp (-π * u))) (1 / (π * u)) (nomeE2 (Real.exp (-π * s)))
    (nomeV (Real.exp (-π * s))) (nomeW (Real.exp (-π * s))) (Λ * nomeLS (Real.exp (-π * s)))
    (Λ * (axLS s + π / s)) s (1 / π) hlB'
  rw [leechZKE, bil_leechS_axis Λ (-1) u s]
  have hsig : ((-1 : ℤ) : ℝ) = -1 := by norm_num
  rw [hsig, neg_one_mul, ← sub_eq_add_neg, ← hK,
    axE2412S_eq_axLeechPhiK _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_inv hs, axV_inv hs,
    axW_inv hs, axL_inv hs, axE2_eq_nome hu, axE2_eq_nome hs, axV_eq_nome hu, axV_eq_nome hs,
    axW_eq_nome hu, axW_eq_nome hs, axL_eq_nome hu, axLS_eq_nome hu, axLS_eq_nome hs]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

end E8Leech.Kron
