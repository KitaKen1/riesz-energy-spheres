import E8Leech.LeechCuspAxis
import E8Leech.KronKernelSignS
import E8Leech.CKMRVAxisInversion

/-!
# The cusp coefficients of the Leech kernel as expressions in the nome generators

`a₁(u)` and `a₀(u)` are the coefficients of the growing part `e^{2πt}(a₁ t + a₀)` of the cusp
profile of `𝒦̂⁽²⁴⁾(iu, i·)` (`LeechCuspAxis`). With `û = 1/(πu)`, `p = 1/π`, `l = log 2`,
`F₆ = 2E₆`, `D = 256Δ` and `Λ` times the logarithms, integer multiples are polynomials:

* `axCuspF = 2·(2Y) + û·(4Z) = 41472 û a₁`;
* `axCuspH Λ cn cd = 41472 Λ û (cd a₀ + cn a₁)`, for the inequalities `a₀ + (cn/cd) a₁ ≶ 0`.

For `u = 1/v ≤ 1` the same quantities are, up to the factor `v¹⁴`, the polynomials `axCuspFm`,
`axCuspHm` in the generators at `iv` (`E₂` enters through `E₂ − 6û`).

* `axCuspF_eq`, `axCuspH_eq`, `axCuspFm_eq`, `axCuspHm_eq`: the four algebraic identities.
* `leechCuspFE`, `leechCuspHE`, `leechCuspFmE`, `leechCuspHmE`: the expressions (`τ`-side atoms).
* `leechCuspFE_eval_axis`, …: their values on the axis are positive multiples of the cusp
  coefficients at `u`, respectively at `1/v`.

Nothing about signs is proved in this file.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The integer forms -/

/-- `2Y = 3 (2E₂E₄ − F₆)(2E₄² − E₂F₆)`. -/
def axCY2 (E2 V W : ℝ) : ℝ :=
  3 * (2 * E2 * axE4 V W - axF6 V W) * (2 * axE4 V W ^ 2 - E2 * axF6 V W)

/-- `4Z = 3 (24 E₂E₄F₆ − 20 E₄³ − 7 F₆²)`. -/
def axCZ4 (E2 V W : ℝ) : ℝ :=
  3 * (24 * E2 * axE4 V W * axF6 V W - 20 * axE4 V W ^ 3 - 7 * axF6 V W ^ 2)

/-- `2Λ û α`. -/
def axCA2 (Λ V W lA lSA uh : ℝ) : ℝ :=
  axPsi2h Λ V W lA lSA uh * axE4 V W * axF6 V W - 2 * axPsi4h Λ V W lA lSA uh * axE4 V W ^ 2

/-- `4 (Y + û Z)`, which is `41472 û a₁`. -/
def axCuspF (E2 V W uh : ℝ) : ℝ := 2 * axCY2 E2 V W + uh * axCZ4 E2 V W

/-- `41472 Λ û (cd a₀ + cn a₁)`. The arguments `lA`, `lSA` are `Λ` times `L₀`, `L_S`; `th` stands
for `1/π` and `l` for `log 2`. -/
def axCuspH (Λ cn cd E2 V W lA lSA uh th l : ℝ) : ℝ :=
  (cn - 3 * cd * th) * Λ * axCuspF E2 V W uh +
    cd * th * (81 * Λ * E2 * axD256 V W - 9 * axCA2 Λ V W lA lSA uh -
      81 * Λ * (4 * l - 1) * uh * axD256 V W)

/-- The form of `axCuspF` at the inverted point, in the generators of `iv`. -/
def axCuspFm (E2 V W uh : ℝ) : ℝ :=
  -(2 * axCY2 (E2 - 6 * uh) V W) + uh * axCZ4 (E2 - 6 * uh) V W

/-- The form of `axCuspH` at the inverted point, in the generators of `iv`. -/
def axCuspHm (Λ cn cd E2 V W lA lSA uh th l : ℝ) : ℝ :=
  (cn - 3 * cd * th) * Λ * axCuspFm E2 V W uh +
    cd * th * (-(81 * Λ * (E2 - 6 * uh) * axD256 V W) - 9 * axCA2 Λ V W lA lSA uh -
      81 * Λ * (4 * l - 1) * uh * axD256 V W)

/-- `axCuspF = 41472 û a₁`. -/
theorem axCuspF_eq (E2 V W : ℝ) {u : ℝ} (hu : u ≠ 0) :
    axCuspF E2 V W (1 / (π * u)) = 41472 * (1 / (π * u)) * axCuspA1 E2 V W u := by
  have hπ := Real.pi_ne_zero
  simp only [axCuspF, axCY2, axCZ4, axCuspA1, axCuspY, axCuspZ, axF6, axE4, axE6]
  field_simp
  ring

/-- `axCuspH = 41472 Λ û (cd a₀ + cn a₁)`; `L₀ − πu` is the logarithm `L`. -/
theorem axCuspH_eq (Λ cn cd E2 V W L0 LS : ℝ) {u : ℝ} (hu : u ≠ 0) :
    axCuspH Λ cn cd E2 V W (Λ * L0) (Λ * LS) (1 / (π * u)) (1 / π) (Real.log 2) =
      41472 * Λ * (1 / (π * u)) *
        (cd * axCuspA0 E2 V W (L0 - π * u) LS u + cn * axCuspA1 E2 V W u) := by
  have hπ := Real.pi_ne_zero
  simp only [axCuspH, axCuspF, axCA2, axCY2, axCZ4, axPsi2h, axPsi4h, axCuspA0, axCuspA1, axCuspY,
    axCuspZ, axCuspAlpha, axPsiTwo, axPsiFour, axF6, axD256, axE4, axE6, axDelta]
  field_simp
  ring

/-- `v¹⁴ axCuspFm = 41472 (v/π) a₁(1/v)`, with the generators at `i/v` written through those at
`iv`. -/
theorem axCuspFm_eq (E2 V W : ℝ) {v : ℝ} (hv : v ≠ 0) :
    v ^ 14 * axCuspFm E2 V W (1 / (π * v)) =
      41472 * (v / π) *
        axCuspA1 (-v ^ 2 * E2 + 6 * v / π) (v ^ 2 * W) (v ^ 2 * V) v⁻¹ := by
  have hπ := Real.pi_ne_zero
  simp only [axCuspFm, axCY2, axCZ4, axCuspA1, axCuspY, axCuspZ, axF6, axE4, axE6]
  field_simp
  ring

/-- `v¹⁴ axCuspHm = 41472 Λ (v/π) (cd a₀ + cn a₁)(1/v)`; the two logarithms are exchanged by the
inversion. -/
theorem axCuspHm_eq (Λ cn cd E2 V W L0 LS : ℝ) {v : ℝ} (hv : v ≠ 0) :
    v ^ 14 * axCuspHm Λ cn cd E2 V W (Λ * L0) (Λ * LS) (1 / (π * v)) (1 / π) (Real.log 2) =
      41472 * Λ * (v / π) *
        (cd * axCuspA0 (-v ^ 2 * E2 + 6 * v / π) (v ^ 2 * W) (v ^ 2 * V) LS (L0 - π * v) v⁻¹ +
          cn * axCuspA1 (-v ^ 2 * E2 + 6 * v / π) (v ^ 2 * W) (v ^ 2 * V) v⁻¹) := by
  have hπ := Real.pi_ne_zero
  simp only [axCuspHm, axCuspFm, axCA2, axCY2, axCZ4, axPsi2h, axPsi4h, axCuspA0, axCuspA1,
    axCuspY, axCuspZ, axCuspAlpha, axPsiTwo, axPsiFour, axF6, axD256, axE4, axE6, axDelta]
  field_simp
  ring

/-! ## The expressions -/

def cy2E (E2 V W : IExpr) : IExpr :=
  3 * (2 * E2 * e4E V W - f6E V W) * (2 * e4E V W ^ 2 - E2 * f6E V W)

def cz4E (E2 V W : IExpr) : IExpr :=
  3 * (24 * E2 * e4E V W * f6E V W - 20 * e4E V W ^ 3 - 7 * f6E V W ^ 2)

def ca2E (Λ : ℕ) (V W lA lSA : IExpr) : IExpr :=
  psi2E Λ V W lA lSA * e4E V W * f6E V W - 2 * psi4E Λ V W lA lSA * e4E V W ^ 2

def cuspFE (E2 V W : IExpr) : IExpr := 2 * cy2E E2 V W + uhE * cz4E E2 V W

def cuspHE (Λ : ℕ) (cn cd : ℤ) (E2 V W lA lSA : IExpr) : IExpr :=
  (.cst cn - .cst (3 * cd) * thE) * .cst Λ * cuspFE E2 V W +
    .cst cd * thE * (.cst (81 * Λ) * E2 * d256E V W - 9 * ca2E Λ V W lA lSA -
      .cst (81 * Λ) * (4 * l2E - 1) * uhE * d256E V W)

def cuspFmE (E2 V W : IExpr) : IExpr :=
  -(2 * cy2E (E2 - 6 * uhE) V W) + uhE * cz4E (E2 - 6 * uhE) V W

def cuspHmE (Λ : ℕ) (cn cd : ℤ) (E2 V W lA lSA : IExpr) : IExpr :=
  (.cst cn - .cst (3 * cd) * thE) * .cst Λ * cuspFmE E2 V W +
    .cst cd * thE * (-(.cst (81 * Λ) * (E2 - 6 * uhE) * d256E V W) - 9 * ca2E Λ V W lA lSA -
      .cst (81 * Λ) * (4 * l2E - 1) * uhE * d256E V W)

/-- `41472 û a₁` in the atoms of the first variable. -/
def leechCuspFE : IExpr := cuspFE (.tat 4) vT wT

/-- `41472 Λ û (cd a₀ + cn a₁)` in the atoms of the first variable. -/
def leechCuspHE (Λ : ℕ) (cn cd : ℤ) : IExpr := cuspHE Λ cn cd (.tat 4) vT wT (l0T Λ) lSE

/-- The inverted form of `leechCuspFE`. -/
def leechCuspFmE : IExpr := cuspFmE (.tat 4) vT wT

/-- The inverted form of `leechCuspHE`. -/
def leechCuspHmE (Λ : ℕ) (cn cd : ℤ) : IExpr := cuspHmE Λ cn cd (.tat 4) vT wT (l0T Λ) lSE

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ) (ex : List (ℝ → ℝ))

theorem evalA_cuspFE (E2 V W : IExpr) (e : NEnv) :
    IExpr.evalA fs (cuspFE E2 V W) e =
      axCuspF (IExpr.evalA fs E2 e) (IExpr.evalA fs V e) (IExpr.evalA fs W e) e.u := by
  simp only [cuspFE, cy2E, cz4E, axCuspF, axCY2, axCZ4, IExpr.evalA_add, IExpr.evalA_sub,
    IExpr.evalA_mul, IExpr.evalA_nat, IExpr.evalA_pow, evalA_e4E, evalA_f6E, evalA_uhE]
  push_cast
  ring

theorem evalA_cuspHE (cn cd : ℤ) (E2 V W lA lSA : IExpr) (e : NEnv) :
    IExpr.evalA fs (cuspHE Λ cn cd E2 V W lA lSA) e =
      axCuspH Λ cn cd (IExpr.evalA fs E2 e) (IExpr.evalA fs V e) (IExpr.evalA fs W e)
        (IExpr.evalA fs lA e) (IExpr.evalA fs lSA e) e.u e.t e.l := by
  simp only [cuspHE, cuspFE, ca2E, cy2E, cz4E, psi2E, psi4E, axCuspH, axCuspF, axCA2, axCY2, axCZ4,
    axPsi2h, axPsi4h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_nat,
    IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E, evalA_uhE, evalA_thE,
    evalA_l2E]
  push_cast
  ring

theorem evalA_cuspFmE (E2 V W : IExpr) (e : NEnv) :
    IExpr.evalA fs (cuspFmE E2 V W) e =
      axCuspFm (IExpr.evalA fs E2 e) (IExpr.evalA fs V e) (IExpr.evalA fs W e) e.u := by
  simp only [cuspFmE, cy2E, cz4E, axCuspFm, axCY2, axCZ4, IExpr.evalA_add, IExpr.evalA_sub,
    IExpr.evalA_mul, IExpr.evalA_neg, IExpr.evalA_nat, IExpr.evalA_pow, evalA_e4E, evalA_f6E,
    evalA_uhE]
  push_cast
  ring

theorem evalA_cuspHmE (cn cd : ℤ) (E2 V W lA lSA : IExpr) (e : NEnv) :
    IExpr.evalA fs (cuspHmE Λ cn cd E2 V W lA lSA) e =
      axCuspHm Λ cn cd (IExpr.evalA fs E2 e) (IExpr.evalA fs V e) (IExpr.evalA fs W e)
        (IExpr.evalA fs lA e) (IExpr.evalA fs lSA e) e.u e.t e.l := by
  simp only [cuspHmE, cuspFmE, ca2E, cy2E, cz4E, psi2E, psi4E, axCuspHm, axCuspFm, axCA2, axCY2,
    axCZ4, axPsi2h, axPsi4h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg,
    IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E,
    evalA_uhE, evalA_thE, evalA_l2E]
  push_cast
  ring

end Eval

/-! ## The values on the axis -/

section Axis

variable (Λ : ℕ) (ex : List (ℝ → ℝ))

/-- The logarithm `L` on the axis in terms of `L₀` of the nome. -/
theorem axL_eq_nomeL0 {u : ℝ} (hu : 0 < u) :
    axL u = nomeL0 (Real.log 2) (Real.exp (-π * u)) - π * u := by
  rw [axL_eq_nome hu, nomeL0]
  ring

theorem axLS_eq_nomeLS {u : ℝ} (hu : 0 < u) : axLS u = nomeLS (Real.exp (-π * u)) := by
  rw [axLS_eq_nome hu, nomeLS]

/-- **`41472 û a₁(u)` on the axis.** -/
theorem leechCuspFE_eval_axis {u : ℝ} (hu : 0 < u) (s : ℝ) :
    IExpr.evalA (kernelAtoms Λ ++ ex) leechCuspFE (axisNEnvS u s) =
      41472 * (1 / (π * u)) * (leechAxisCusp (-1) u 0).re := by
  rw [leechCuspFE, evalA_cuspFE, evalA_vT, evalA_wT, evalA_tat4, leechAxisCusp_zero_re hu,
    axE2_eq_nome hu, axV_eq_nome hu, axW_eq_nome hu]
  exact axCuspF_eq _ _ _ hu.ne'

/-- **`41472 Λ û (cd a₀(u) + cn a₁(u))` on the axis.** -/
theorem leechCuspHE_eval_axis (cn cd : ℤ) {u : ℝ} (hu : 0 < u) (s : ℝ) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (leechCuspHE Λ cn cd) (axisNEnvS u s) =
      41472 * Λ * (1 / (π * u)) *
        (cd * (leechAxisCusp (-1) u 1).re + cn * (leechAxisCusp (-1) u 0).re) := by
  rw [leechCuspHE, evalA_cuspHE, evalA_vT, evalA_wT, evalA_tat4, evalA_l0T, evalA_lSE,
    leechAxisCusp_zero_re hu, leechAxisCusp_one_re hu, axE2_eq_nome hu, axV_eq_nome hu,
    axW_eq_nome hu, axL_eq_nomeL0 hu, axLS_eq_nomeLS hu]
  exact axCuspH_eq _ _ _ _ _ _ _ _ hu.ne'

/-- **`41472 (v/π) a₁(1/v)` on the axis**, in the generators of `iv`. -/
theorem leechCuspFmE_eval_axis {v : ℝ} (hv : 0 < v) (s : ℝ) :
    v ^ 14 * IExpr.evalA (kernelAtoms Λ ++ ex) leechCuspFmE (axisNEnvS v s) =
      41472 * (v / π) * (leechAxisCusp (-1) v⁻¹ 0).re := by
  rw [leechCuspFmE, evalA_cuspFmE, evalA_vT, evalA_wT, evalA_tat4,
    leechAxisCusp_zero_re (inv_pos.mpr hv), axE2_inv hv, axV_inv hv, axW_inv hv, axE2_eq_nome hv,
    axV_eq_nome hv, axW_eq_nome hv]
  exact axCuspFm_eq _ _ _ hv.ne'

/-- **`41472 Λ (v/π) (cd a₀ + cn a₁)(1/v)` on the axis**, in the generators of `iv`. -/
theorem leechCuspHmE_eval_axis (cn cd : ℤ) {v : ℝ} (hv : 0 < v) (s : ℝ) :
    v ^ 14 * IExpr.evalA (kernelAtoms Λ ++ ex) (leechCuspHmE Λ cn cd) (axisNEnvS v s) =
      41472 * Λ * (v / π) *
        (cd * (leechAxisCusp (-1) v⁻¹ 1).re + cn * (leechAxisCusp (-1) v⁻¹ 0).re) := by
  rw [leechCuspHmE, evalA_cuspHmE, evalA_vT, evalA_wT, evalA_tat4, evalA_l0T, evalA_lSE,
    leechAxisCusp_zero_re (inv_pos.mpr hv), leechAxisCusp_one_re (inv_pos.mpr hv), axE2_inv hv,
    axV_inv hv, axW_inv hv, axL_inv hv, axLS_inv hv, axE2_eq_nome hv, axV_eq_nome hv,
    axW_eq_nome hv, axL_eq_nomeL0 hv, axLS_eq_nomeLS hv]
  exact axCuspHm_eq _ _ _ _ _ _ _ _ hv.ne'

end Axis

end E8Leech.Kron
