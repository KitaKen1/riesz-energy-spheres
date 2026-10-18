import E8Leech.CKMRVGeneratorModels
import E8Leech.CKMRVAxisIdentities

/-!
# The actual E8 kernel numerators as certificate expressions

The expressions use only the five nome generators, three logarithms, and rational arithmetic.
`kernelPhiExpr_eval_axis` and `kernelNuExpr_eval_axis` connect their meanings to the actual
imaginary-axis kernel. The `a`-version of both expressions vanishes algebraically, so their
divided-difference models can be used without dividing a remainder by `b - a`.
-/

namespace E8Leech.Taylor

open scoped Real

namespace KExpr

instance : Add KExpr := ⟨KExpr.add⟩
instance : Sub KExpr := ⟨KExpr.sub⟩
instance : Mul KExpr := ⟨KExpr.mul⟩
instance : Neg KExpr := ⟨fun x => .mul (.cst (-1)) x⟩
instance (n : ℕ) : OfNat KExpr n := ⟨.cst n⟩

def pow : KExpr → ℕ → KExpr
  | _, 0 => 1
  | x, n + 1 => pow x n * x

instance : Pow KExpr ℕ := ⟨pow⟩

@[simp] theorem evalA_add (x y : KExpr) (e : Env) : evalA (x + y) e = evalA x e + evalA y e := rfl
@[simp] theorem evalB_add (x y : KExpr) (e : Env) : evalB (x + y) e = evalB x e + evalB y e := rfl
@[simp] theorem evalA_sub (x y : KExpr) (e : Env) : evalA (x - y) e = evalA x e - evalA y e := rfl
@[simp] theorem evalB_sub (x y : KExpr) (e : Env) : evalB (x - y) e = evalB x e - evalB y e := rfl
@[simp] theorem evalA_mul (x y : KExpr) (e : Env) : evalA (x * y) e = evalA x e * evalA y e := rfl
@[simp] theorem evalB_mul (x y : KExpr) (e : Env) : evalB (x * y) e = evalB x e * evalB y e := rfl
@[simp] theorem evalA_neg (x : KExpr) (e : Env) : evalA (-x) e = -evalA x e := by
  change ((-1 : ℚ) : ℝ) * evalA x e = -evalA x e
  norm_num
@[simp] theorem evalB_neg (x : KExpr) (e : Env) : evalB (-x) e = -evalB x e := by
  change ((-1 : ℚ) : ℝ) * evalB x e = -evalB x e
  norm_num
@[simp] theorem evalA_nat (n : ℕ) (e : Env) : evalA (ofNat(n) : KExpr) e = n := by
  change ((n : ℚ) : ℝ) = n
  simp
@[simp] theorem evalB_nat (n : ℕ) (e : Env) : evalB (ofNat(n) : KExpr) e = n := by
  change ((n : ℚ) : ℝ) = n
  simp
@[simp] theorem evalA_pow (x : KExpr) (n : ℕ) (e : Env) : evalA (x ^ n) e = evalA x e ^ n := by
  induction n with
  | zero => change ((1 : ℚ) : ℝ) = _; simp
  | succ n ih =>
    change evalA (pow x n) e = evalA x e ^ n at ih
    change evalA (pow x n * x) e = _
    rw [evalA_mul, ih, pow_succ]
@[simp] theorem evalB_pow (x : KExpr) (n : ℕ) (e : Env) : evalB (x ^ n) e = evalB x e ^ n := by
  induction n with
  | zero => change ((1 : ℚ) : ℝ) = _; simp
  | succ n ih =>
    change evalB (pow x n) e = evalB x e ^ n at ih
    change evalB (pow x n * x) e = _
    rw [evalB_mul, ih, pow_succ]

@[simp] private theorem evalA_cst (q : ℚ) (e : Env) :
    evalA (.cst q) e = q := rfl

@[simp] private theorem evalA_mono (m : Mono) (e : Env) :
    evalA (.mono m) e = m.eval e := rfl

@[simp] private theorem evalA_zgen (i : Fin 5) (e : Env) :
    evalA (.zgen i) e = genFun i e.a := rfl

@[simp] private theorem evalA_tgen (i : Fin 5) (e : Env) :
    evalA (.tgen i) e = genFun i e.a := rfl

@[simp] private theorem evalA_zlog (j : Fin 3) (e : Env) :
    evalA (.zlog j) e = logFun j e.a := rfl

@[simp] private theorem evalA_tlog (j : Fin 3) (e : Env) :
    evalA (.tlog j) e = logFun j e.a := rfl

@[simp] private theorem evalB_cst (q : ℚ) (e : Env) :
    evalB (.cst q) e = q := rfl

@[simp] private theorem evalB_mono (m : Mono) (e : Env) :
    evalB (.mono m) e = m.eval e := rfl

@[simp] private theorem evalB_zgen (i : Fin 5) (e : Env) :
    evalB (.zgen i) e = genFun i e.b := rfl

@[simp] private theorem evalB_tgen (i : Fin 5) (e : Env) :
    evalB (.tgen i) e = genFun i e.a := rfl

@[simp] private theorem evalB_zlog (j : Fin 3) (e : Env) :
    evalB (.zlog j) e = logFun j e.b := rfl

@[simp] private theorem evalB_tlog (j : Fin 3) (e : Env) :
    evalB (.tlog j) e = logFun j e.a := rfl

end KExpr

def uExpr : KExpr := .mono ⟨0, 0, 1, 0, 0, 0⟩
def tExpr : KExpr := .mono ⟨0, 0, 0, 1, 0, 0⟩
def piExpr : KExpr := .mono ⟨0, 0, 0, 0, 1, 0⟩
def piInvExpr : KExpr := .mono ⟨0, 0, 0, 0, -1, 0⟩
def tInvExpr : KExpr := .mono ⟨0, 0, 0, -1, 0, 0⟩
def logTwoExpr : KExpr := .mono ⟨0, 0, 0, 0, 0, 1⟩

def nomeVExpr (side : Bool) : KExpr :=
  16 * (if side then .tgen 0 else .zgen 0) * (if side then .tgen 3 else .zgen 3) ^ 4

def nomeWExpr (side : Bool) : KExpr := (if side then .tgen 2 else .zgen 2) ^ 4

def nomeL0Expr (side : Bool) : KExpr :=
  4 * logTwoExpr + 4 * (if side then .tlog 2 else .zlog 2) -
    4 * (if side then .tlog 0 else .zlog 0)

def nomeLSExpr : KExpr := 4 * .tlog 1 - 4 * .tlog 0

def e4Expr (V W : KExpr) : KExpr := V ^ 2 + V * W + W ^ 2
def e6Expr (V W : KExpr) : KExpr := .cst (1 / 2) * (V + 2 * W) * (2 * V + W) * (W - V)
def deltaExpr (V W : KExpr) : KExpr := .cst (1 / 256) * ((V + W) * V * W) ^ 2

def nuExpr (Va Wa Vb Wb : KExpr) : KExpr :=
  deltaExpr Vb Wb * e4Expr Va Wa ^ 3 - deltaExpr Va Wa * e4Expr Vb Wb ^ 3

def plusExpr (E2a Va Wa E2b Vb Wb : KExpr) : KExpr :=
  nuExpr Va Wa Vb Wb * (uExpr * e6Expr Va Wa - 2 * (uExpr * E2a - 3 * piInvExpr) * e4Expr Va Wa) +
    deltaExpr Vb Wb * E2a * (uExpr * E2a - 6 * piInvExpr) * e4Expr Va Wa ^ 2 * e6Expr Va Wa +
    deltaExpr Va Wa * (-2 * (uExpr * E2a - 3 * piInvExpr) * e4Expr Va Wa * e4Expr Vb Wb *
      e6Expr Vb Wb * (E2b - 6 * piInvExpr * tInvExpr) + uExpr * e6Expr Va Wa * e4Expr Vb Wb ^ 2 *
      (E2b - 6 * piInvExpr * tInvExpr) ^ 2)

def minusExpr (Va Wa La LSa Vb Wb Lb : KExpr) : KExpr :=
  -3456 * deltaExpr Va Wa * e4Expr Va Wa * (e4Expr Vb Wb * e6Expr Vb Wb * Lb) +
    ((Va + Wa + Wa) * La - (Va + Wa + Va) * LSa) * e4Expr Va Wa ^ 2 * e6Expr Va Wa *
      (e4Expr Vb Wb ^ 2 * Wb - e6Expr Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2)) +
    (((Va + Wa) ^ 2 + Wa ^ 2 - 2 * Va ^ 2) * La +
      ((Va + Wa) ^ 2 + Va ^ 2 - 2 * Wa ^ 2) * LSa) *
      (1728 * deltaExpr Va Wa * (e4Expr Vb Wb ^ 2 * Wb) +
        e4Expr Va Wa ^ 3 * (e6Expr Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2) - e4Expr Vb Wb ^ 2 * Wb))

def kernelPhiExpr : KExpr :=
  -(.cst (1 / 36) * piExpr ^ 2 * tExpr ^ 2) *
      plusExpr (.tgen 4) (nomeVExpr true) (nomeWExpr true) (.zgen 4) (nomeVExpr false) (nomeWExpr false) -
    .cst (1 / 3456) * piInvExpr *
      minusExpr (nomeVExpr true) (nomeWExpr true) (nomeL0Expr true - piExpr * uExpr) nomeLSExpr
        (nomeVExpr false) (nomeWExpr false) (nomeL0Expr false - piExpr * tExpr)

def kernelNuExpr : KExpr := nuExpr (nomeVExpr true) (nomeWExpr true) (nomeVExpr false) (nomeWExpr false)

noncomputable def nomeV (x : ℝ) : ℝ := 16 * x * nomeEta1 x ^ 4
noncomputable def nomeW (x : ℝ) : ℝ := nomeTheta4 x ^ 4
noncomputable def nomeL0 (l x : ℝ) : ℝ := 4 * l + 4 * Real.log (nomeEta1 x) - 4 * Real.log (nomeTheta3 x)
noncomputable def nomeLS (x : ℝ) : ℝ := 4 * Real.log (nomeTheta4 x) - 4 * Real.log (nomeTheta3 x)

@[simp] private theorem evalA_e4 (V W : KExpr) (e : Env) :
    KExpr.evalA (e4Expr V W) e = axE4 (KExpr.evalA V e) (KExpr.evalA W e) := by
  simp [e4Expr, axE4]

@[simp] private theorem evalA_e6 (V W : KExpr) (e : Env) :
    KExpr.evalA (e6Expr V W) e = axE6 (KExpr.evalA V e) (KExpr.evalA W e) := by
  simp [e6Expr, axE6, KExpr.evalA]
  all_goals norm_num
  all_goals ring

@[simp] private theorem evalA_delta (V W : KExpr) (e : Env) :
    KExpr.evalA (deltaExpr V W) e = axDelta (KExpr.evalA V e) (KExpr.evalA W e) := by
  simp [deltaExpr, axDelta, KExpr.evalA, div_eq_mul_inv, mul_comm]

@[simp] private theorem evalA_nu (Va Wa Vb Wb : KExpr) (e : Env) :
    KExpr.evalA (nuExpr Va Wa Vb Wb) e =
      axNu (KExpr.evalA Va e) (KExpr.evalA Wa e) (KExpr.evalA Vb e) (KExpr.evalA Wb e) := by
  simp [nuExpr, axNu]

@[simp] private theorem evalB_e4 (V W : KExpr) (e : Env) :
    KExpr.evalB (e4Expr V W) e = axE4 (KExpr.evalB V e) (KExpr.evalB W e) := by
  simp [e4Expr, axE4]

@[simp] private theorem evalB_e6 (V W : KExpr) (e : Env) :
    KExpr.evalB (e6Expr V W) e = axE6 (KExpr.evalB V e) (KExpr.evalB W e) := by
  simp [e6Expr, axE6, KExpr.evalB]
  all_goals norm_num
  all_goals ring

@[simp] private theorem evalB_delta (V W : KExpr) (e : Env) :
    KExpr.evalB (deltaExpr V W) e = axDelta (KExpr.evalB V e) (KExpr.evalB W e) := by
  simp [deltaExpr, axDelta, KExpr.evalB, div_eq_mul_inv, mul_comm]

@[simp] private theorem evalB_nu (Va Wa Vb Wb : KExpr) (e : Env) :
    KExpr.evalB (nuExpr Va Wa Vb Wb) e =
      axNu (KExpr.evalB Va e) (KExpr.evalB Wa e) (KExpr.evalB Vb e) (KExpr.evalB Wb e) := by
  simp [nuExpr, axNu]

private theorem evalA_phi (e : Env) (hp : e.p = π) :
    KExpr.evalA kernelPhiExpr e =
      axPhi (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (nomeL0 e.l e.a - π * e.u) (nomeLS e.a) e.u
        (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (nomeL0 e.l e.a - π * e.t) e.t := by
  simp [kernelPhiExpr, plusExpr, minusExpr, axPhi, axPlusNum, axMinusNum, axPsiTwo,
    axPsiFour, axNu, nomeVExpr, nomeWExpr, nomeL0Expr, nomeLSExpr, uExpr, tExpr, piExpr,
    piInvExpr, tInvExpr, logTwoExpr, genFun, logFun, Mono.eval, nomeV, nomeW, nomeL0,
    nomeLS, hp, div_eq_mul_inv, mul_inv_rev]
  all_goals norm_num
  all_goals ring

private theorem evalB_phi (e : Env) (hp : e.p = π) :
    KExpr.evalB kernelPhiExpr e =
      axPhi (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (nomeL0 e.l e.a - π * e.u) (nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (nomeL0 e.l e.b - π * e.t) e.t := by
  simp [kernelPhiExpr, plusExpr, minusExpr, axPhi, axPlusNum, axMinusNum, axPsiTwo,
    axPsiFour, axNu, nomeVExpr, nomeWExpr, nomeL0Expr, nomeLSExpr, uExpr, tExpr, piExpr,
    piInvExpr, tInvExpr, logTwoExpr, genFun, logFun, Mono.eval, nomeV, nomeW, nomeL0,
    nomeLS, hp, div_eq_mul_inv, mul_inv_rev]
  all_goals norm_num
  all_goals ring

theorem kernelPhiExpr_evalA_zero (e : Env) (hp : e.p = π) (ht : e.t ≠ 0) :
    KExpr.evalA kernelPhiExpr e = 0 := by
  rw [evalA_phi e hp]
  exact axPhi_diag _ _ _ _ _ _ _ ht

theorem kernelNuExpr_evalA_zero (e : Env) : KExpr.evalA kernelNuExpr e = 0 := by
  simp [kernelNuExpr, nomeVExpr, nomeWExpr, genFun, axNu]

theorem kernelNuExpr_evalB (e : Env) :
    KExpr.evalB kernelNuExpr e = axNu (nomeV e.a) (nomeW e.a) (nomeV e.b) (nomeW e.b) := by
  simp [kernelNuExpr, nomeVExpr, nomeWExpr, genFun, nomeV, nomeW]

/-- The environment belonging to an actual pair of imaginary-axis parameters. -/
noncomputable def axisEnv (u t : ℝ) : Env := ⟨Real.exp (-π * u), Real.exp (-π * t), u, t, π, Real.log 2⟩

theorem kernelPhiExpr_eval_axis {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    KExpr.evalB kernelPhiExpr (axisEnv u t) =
      axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
  rw [evalB_phi _ rfl, axE2_eq_nome hu, axE2_eq_nome ht, axV_eq_nome hu, axV_eq_nome ht,
    axW_eq_nome hu, axW_eq_nome ht, axL_eq_nome hu, axL_eq_nome ht, axLS_eq_nome hu]
  simp only [axisEnv, nomeV, nomeW, nomeL0, nomeLS]
  congr 1 <;> ring

theorem kernelNuExpr_eval_axis {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    KExpr.evalB kernelNuExpr (axisEnv u t) = axNu (axV u) (axW u) (axV t) (axW t) := by
  rw [kernelNuExpr_evalB, axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht]
  rfl

end E8Leech.Taylor
