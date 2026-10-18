import E8Leech.KronExpr
import E8Leech.KronGenerators
import E8Leech.CKMRVKernelExpr

/-!
# The E8 numerator as an integer expression in reciprocal variables

With `û = 1/(πu)` and `t̂ = 1/(πt)` the axis numerator `Φ'` of the hat kernel satisfies

`axE Λ … = 1769472 · Λ · π · û · t̂² · Φ'`,

where `axE` is a polynomial with integer coefficients in the generators, `Λ` times the
logarithms, `û` and `t̂`, without `π` and without negative powers. The expression is grouped so
that every summand carries a `τ`-side factor that is divisible by the square of the nome; this is
what makes the remainders of the Taylor models divisible by `a²`.

* `axE_eq_axPhi`: the algebraic identity above (`1769472 = 512 · 3456`).
* `axE_diag`: `axE` vanishes when the `z`-side generators equal the `τ`-side ones, for
  independent `û, t̂`.
* `kernelAtoms`, `kernelAtomModels`, `kernelAtoms_ok`: the eight atoms and their models.
* `kernelE`: the expression; `kernelE_evalA`, `kernelE_evalB`, `kernelE_eval_axis`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The real polynomial -/

/-- `2 E₆ = (V + 2W)(2V + W)(W − V)`. -/
def axF6 (V W : ℝ) : ℝ := (V + 2 * W) * (2 * V + W) * (W - V)

/-- `256 Δ = ((V + W) V W)²`. -/
def axD256 (V W : ℝ) : ℝ := ((V + W) * V * W) ^ 2

/-- `2 E₄² [(E₄E₆ − 2E₂E₄² + E₂²E₆) + 6û(E₄² − E₂E₆)]`, divisible by the square of the nome. -/
def axT1 (E2a Va Wa uh : ℝ) : ℝ :=
  axE4 Va Wa ^ 2 * ((axE4 Va Wa * axF6 Va Wa - 4 * E2a * axE4 Va Wa ^ 2 + E2a ^ 2 * axF6 Va Wa) +
    6 * uh * (2 * axE4 Va Wa ^ 2 - E2a * axF6 Va Wa))

def axZ1 (E2a Va Wa uh E2b Vb Wb th : ℝ) : ℝ :=
  -(axE4 Vb Wb ^ 3) * (axF6 Va Wa - 4 * (E2a - 3 * uh) * axE4 Va Wa) +
    (-2 * (E2a - 3 * uh) * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb * (E2b - 6 * th) +
      axF6 Va Wa * axE4 Vb Wb ^ 2 * (E2b - 6 * th) ^ 2)

/-- `Λ ψ₂ / u'`. -/
def axPsi2h (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  (Va + Wa + Wa) * (lA * uh - Λ) - (Va + Wa + Va) * lSA * uh

/-- `Λ ψ₄ / u'`. -/
def axPsi4h (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  ((Va + Wa) ^ 2 + Wa ^ 2 - 2 * Va ^ 2) * (lA * uh - Λ) +
    ((Va + Wa) ^ 2 + Va ^ 2 - 2 * Wa ^ 2) * lSA * uh

def axZ2 (Λ Va Wa lA lSA uh Vb Wb lB th : ℝ) : ℝ :=
  -3456 * axE4 Va Wa * axE4 Vb Wb * axF6 Vb Wb * (lB * th - Λ) * uh * th +
    3456 * axPsi4h Λ Va Wa lA lSA uh * axE4 Vb Wb ^ 2 * Wb * th ^ 2

/-- Divisible by the square of the nome. -/
def axT2 (Λ Va Wa lA lSA uh : ℝ) : ℝ :=
  axE4 Va Wa ^ 2 * (axPsi2h Λ Va Wa lA lSA uh * axF6 Va Wa -
    2 * axPsi4h Λ Va Wa lA lSA uh * axE4 Va Wa)

def axXb2 (Vb Wb : ℝ) : ℝ :=
  2 * axE4 Vb Wb ^ 2 * Wb - axF6 Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2)

/-- The integer-scaled numerator. `lA, lSA, lB` are `Λ` times `L₀(τ), L_S(τ), L₀(z)`. -/
def axE (Λ E2a Va Wa lA lSA uh E2b Vb Wb lB th : ℝ) : ℝ :=
  -(96 * Λ * (axD256 Vb Wb * axT1 E2a Va Wa uh + axD256 Va Wa * axZ1 E2a Va Wa uh E2b Vb Wb th) +
    axD256 Va Wa * axZ2 Λ Va Wa lA lSA uh Vb Wb lB th +
    128 * axT2 Λ Va Wa lA lSA uh * axXb2 Vb Wb * th ^ 2)

/-- **The reciprocal-variable identity**: `axE = 512 · 3456 · Λ π û t̂² Φ'`. -/
theorem axE_eq_axPhi (Λ E2a Va Wa L0a LSa uh E2b Vb Wb L0b th : ℝ) (hu : uh ≠ 0) (ht : th ≠ 0) :
    axE Λ E2a Va Wa (Λ * L0a) (Λ * LSa) uh E2b Vb Wb (Λ * L0b) th =
      1769472 * Λ * π * uh * th ^ 2 *
        axPhi E2a Va Wa (L0a - π * (1 / (π * uh))) LSa (1 / (π * uh)) E2b Vb Wb
          (L0b - π * (1 / (π * th))) (1 / (π * th)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axE, axT1, axZ1, axZ2, axT2, axXb2, axPsi2h, axPsi4h, axF6, axD256, axPhi,
    axPlusNum, axMinusNum, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

/-- The `a`-version vanishes, for independent `û, t̂`. -/
theorem axE_diag (Λ E2 V W lA lSA uh th : ℝ) : axE Λ E2 V W lA lSA uh E2 V W lA th = 0 := by
  simp only [axE, axT1, axZ1, axZ2, axT2, axXb2, axPsi2h, axPsi4h, axF6, axD256, axE4]
  ring

/-! ## The expression -/

namespace IExpr

instance : Add IExpr := ⟨IExpr.add⟩
instance : Sub IExpr := ⟨IExpr.sub⟩
instance : Mul IExpr := ⟨IExpr.mul⟩
instance : Neg IExpr := ⟨fun x => .mul (.cst (-1)) x⟩
instance (n : ℕ) : OfNat IExpr n := ⟨.cst n⟩

def pow : IExpr → ℕ → IExpr
  | _, 0 => 1
  | x, n + 1 => pow x n * x

instance : Pow IExpr ℕ := ⟨pow⟩

variable (fs : List (ℝ → ℝ))

@[simp] theorem evalA_add (x y : IExpr) (e : NEnv) :
    evalA fs (x + y) e = evalA fs x e + evalA fs y e := rfl
@[simp] theorem evalB_add (x y : IExpr) (e : NEnv) :
    evalB fs (x + y) e = evalB fs x e + evalB fs y e := rfl
@[simp] theorem evalA_sub (x y : IExpr) (e : NEnv) :
    evalA fs (x - y) e = evalA fs x e - evalA fs y e := rfl
@[simp] theorem evalB_sub (x y : IExpr) (e : NEnv) :
    evalB fs (x - y) e = evalB fs x e - evalB fs y e := rfl
@[simp] theorem evalA_mul (x y : IExpr) (e : NEnv) :
    evalA fs (x * y) e = evalA fs x e * evalA fs y e := rfl
@[simp] theorem evalB_mul (x y : IExpr) (e : NEnv) :
    evalB fs (x * y) e = evalB fs x e * evalB fs y e := rfl
@[simp] theorem evalA_neg (x : IExpr) (e : NEnv) : evalA fs (-x) e = -evalA fs x e := by
  change ((-1 : ℤ) : ℝ) * evalA fs x e = -evalA fs x e
  norm_num
@[simp] theorem evalB_neg (x : IExpr) (e : NEnv) : evalB fs (-x) e = -evalB fs x e := by
  change ((-1 : ℤ) : ℝ) * evalB fs x e = -evalB fs x e
  norm_num
@[simp] theorem evalA_nat (n : ℕ) (e : NEnv) : evalA fs (ofNat(n) : IExpr) e = n := by
  change (((n : ℕ) : ℤ) : ℝ) = n
  simp
@[simp] theorem evalB_nat (n : ℕ) (e : NEnv) : evalB fs (ofNat(n) : IExpr) e = n := by
  change (((n : ℕ) : ℤ) : ℝ) = n
  simp
@[simp] theorem evalA_pow (x : IExpr) (n : ℕ) (e : NEnv) :
    evalA fs (x ^ n) e = evalA fs x e ^ n := by
  induction n with
  | zero => change (((1 : ℕ) : ℤ) : ℝ) = _; simp
  | succ n ih =>
    change evalA fs (pow x n) e = evalA fs x e ^ n at ih
    change evalA fs (pow x n * x) e = _
    rw [evalA_mul, ih, pow_succ]
@[simp] theorem evalB_pow (x : IExpr) (n : ℕ) (e : NEnv) :
    evalB fs (x ^ n) e = evalB fs x e ^ n := by
  induction n with
  | zero => change (((1 : ℕ) : ℤ) : ℝ) = _; simp
  | succ n ih =>
    change evalB fs (pow x n) e = evalB fs x e ^ n at ih
    change evalB fs (pow x n * x) e = _
    rw [evalB_mul, ih, pow_succ]

@[simp] theorem evalA_cst (c : ℤ) (e : NEnv) : evalA fs (.cst c) e = c := rfl
@[simp] theorem evalB_cst (c : ℤ) (e : NEnv) : evalB fs (.cst c) e = c := rfl
@[simp] theorem evalA_mono (m : NMono) (e : NEnv) : evalA fs (.mono m) e = m.eval e := rfl
@[simp] theorem evalB_mono (m : NMono) (e : NEnv) : evalB fs (.mono m) e = m.eval e := rfl
end IExpr

/-! ## The atoms of the hat kernel -/

/-- The atoms: the five generators and `Λ` times the three logarithms. Certificates may append
further atoms; the lemmas below hold for every extension `kernelAtoms Λ ++ ex`. -/
noncomputable def kernelAtoms (Λ : ℕ) : List (ℝ → ℝ) :=
  [genFun 0, genFun 1, genFun 2, genFun 3, genFun 4, fun x => Λ * logFun 0 x,
    fun x => Λ * logFun 1 x, fun x => Λ * logFun 2 x]

/-- The models of the atoms. -/
def kernelAtomModels (Bx : Bounds) (D Dcap Λ n K N NE : ℕ) : List MDD :=
  [generatorMDD Bx N NE 0, generatorMDD Bx N NE 1, generatorMDD Bx N NE 2,
    generatorMDD Bx N NE 3, generatorMDD Bx N NE 4, logarithmMDD Bx D Dcap Λ n K N NE 0,
    logarithmMDD Bx D Dcap Λ n K N NE 1, logarithmMDD Bx D Dcap Λ n K N NE 2]

theorem kernelAtoms_ok {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) (D Dcap : ℕ) {Λ n : ℕ}
    (K N : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ) (hL : LogsOK Bx D Dcap K N NE)
    {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (kernelAtomModels Bx D Dcap Λ n K N NE) (kernelAtoms Λ) := by
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa [kernelAtomModels, kernelAtoms] using approx_generatorMDD hG N (S := S) 0
  · simpa [kernelAtomModels, kernelAtoms] using approx_generatorMDD hG N (S := S) 1
  · simpa [kernelAtomModels, kernelAtoms] using approx_generatorMDD hG N (S := S) 2
  · simpa [kernelAtomModels, kernelAtoms] using approx_generatorMDD hG N (S := S) 3
  · simpa [kernelAtomModels, kernelAtoms] using approx_generatorMDD hG N (S := S) 4
  · simpa [kernelAtomModels, kernelAtoms] using
      approx_logarithmMDD hG D Dcap K N hΛ hL (S := S) 0
  · simpa [kernelAtomModels, kernelAtoms] using
      approx_logarithmMDD hG D Dcap K N hΛ hL (S := S) 1
  · simpa [kernelAtomModels, kernelAtoms] using
      approx_logarithmMDD hG D Dcap K N hΛ hL (S := S) 2
  · simpa [kernelAtomModels, kernelAtoms] using MDD.approx_zero (Bx := Bx) (S := S)

section Atoms

variable (Λ : ℕ) (ex : List (ℝ → ℝ))

@[simp] theorem evalA_zat0 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 0) e = genFun 0 e.a := rfl
@[simp] theorem evalA_zat2 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 2) e = genFun 2 e.a := rfl
@[simp] theorem evalA_zat3 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 3) e = genFun 3 e.a := rfl
@[simp] theorem evalA_zat4 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 4) e = genFun 4 e.a := rfl
@[simp] theorem evalA_zat5 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 5) e = Λ * logFun 0 e.a := rfl
@[simp] theorem evalA_zat7 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.zat 7) e = Λ * logFun 2 e.a := rfl
@[simp] theorem evalA_tat0 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 0) e = genFun 0 e.a := rfl
@[simp] theorem evalA_tat2 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 2) e = genFun 2 e.a := rfl
@[simp] theorem evalA_tat3 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 3) e = genFun 3 e.a := rfl
@[simp] theorem evalA_tat4 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 4) e = genFun 4 e.a := rfl
@[simp] theorem evalA_tat5 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 5) e = Λ * logFun 0 e.a := rfl
@[simp] theorem evalA_tat6 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 6) e = Λ * logFun 1 e.a := rfl
@[simp] theorem evalA_tat7 (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (.tat 7) e = Λ * logFun 2 e.a := rfl
@[simp] theorem evalB_zat0 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 0) e = genFun 0 e.b := rfl
@[simp] theorem evalB_zat2 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 2) e = genFun 2 e.b := rfl
@[simp] theorem evalB_zat3 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 3) e = genFun 3 e.b := rfl
@[simp] theorem evalB_zat4 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 4) e = genFun 4 e.b := rfl
@[simp] theorem evalB_zat5 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 5) e = Λ * logFun 0 e.b := rfl
@[simp] theorem evalB_zat7 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 7) e = Λ * logFun 2 e.b := rfl
@[simp] theorem evalB_tat0 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 0) e = genFun 0 e.a := rfl
@[simp] theorem evalB_tat2 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 2) e = genFun 2 e.a := rfl
@[simp] theorem evalB_tat3 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 3) e = genFun 3 e.a := rfl
@[simp] theorem evalB_tat4 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 4) e = genFun 4 e.a := rfl
@[simp] theorem evalB_tat5 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 5) e = Λ * logFun 0 e.a := rfl
@[simp] theorem evalB_tat6 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 6) e = Λ * logFun 1 e.a := rfl
@[simp] theorem evalB_tat7 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.tat 7) e = Λ * logFun 2 e.a := rfl

end Atoms

def uhE : IExpr := .mono ⟨0, 0, 1, 0, 0⟩
def thE : IExpr := .mono ⟨0, 0, 0, 1, 0⟩
def l2E : IExpr := .mono ⟨0, 0, 0, 0, 1⟩

/-- `V = 16 x η₁⁴` on the `τ`-side. -/
def vT : IExpr := 16 * .tat 0 * (.tat 3) ^ 4

/-- `V = 16 x η₁⁴` on the `z`-side. -/
def vZ : IExpr := 16 * .zat 0 * (.zat 3) ^ 4

/-- `W = θ₄⁴` on the `τ`-side. -/
def wT : IExpr := (.tat 2) ^ 4

/-- `W = θ₄⁴` on the `z`-side. -/
def wZ : IExpr := (.zat 2) ^ 4

/-- `Λ L₀ = 4Λ log 2 + 4 (Λ log η₁) − 4 (Λ log θ₃)` on the `τ`-side. -/
def l0T (Λ : ℕ) : IExpr := .cst (4 * Λ) * l2E + 4 * .tat 7 - 4 * .tat 5

/-- `Λ L₀` on the `z`-side. -/
def l0Z (Λ : ℕ) : IExpr := .cst (4 * Λ) * l2E + 4 * .zat 7 - 4 * .zat 5

/-- `Λ L_S = 4 (Λ log θ₄) − 4 (Λ log θ₃)` on the `τ`-side. -/
def lSE : IExpr := 4 * .tat 6 - 4 * .tat 5

def e4E (V W : IExpr) : IExpr := V ^ 2 + V * W + W ^ 2
def f6E (V W : IExpr) : IExpr := (V + 2 * W) * (2 * V + W) * (W - V)
def d256E (V W : IExpr) : IExpr := ((V + W) * V * W) ^ 2

def t1E (E2a Va Wa : IExpr) : IExpr :=
  e4E Va Wa ^ 2 * ((e4E Va Wa * f6E Va Wa - 4 * E2a * e4E Va Wa ^ 2 + E2a ^ 2 * f6E Va Wa) +
    6 * uhE * (2 * e4E Va Wa ^ 2 - E2a * f6E Va Wa))

def z1E (E2a Va Wa E2b Vb Wb : IExpr) : IExpr :=
  -(e4E Vb Wb ^ 3) * (f6E Va Wa - 4 * (E2a - 3 * uhE) * e4E Va Wa) +
    (-2 * (E2a - 3 * uhE) * e4E Va Wa * e4E Vb Wb * f6E Vb Wb * (E2b - 6 * thE) +
      f6E Va Wa * e4E Vb Wb ^ 2 * (E2b - 6 * thE) ^ 2)

def psi2E (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  (Va + Wa + Wa) * (lA * uhE - .cst Λ) - (Va + Wa + Va) * lSA * uhE

def psi4E (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  ((Va + Wa) ^ 2 + Wa ^ 2 - 2 * Va ^ 2) * (lA * uhE - .cst Λ) +
    ((Va + Wa) ^ 2 + Va ^ 2 - 2 * Wa ^ 2) * lSA * uhE

def z2E (Λ : ℕ) (Va Wa lA lSA Vb Wb lB : IExpr) : IExpr :=
  -3456 * e4E Va Wa * e4E Vb Wb * f6E Vb Wb * (lB * thE - .cst Λ) * uhE * thE +
    3456 * psi4E Λ Va Wa lA lSA * e4E Vb Wb ^ 2 * Wb * thE ^ 2

def t2E (Λ : ℕ) (Va Wa lA lSA : IExpr) : IExpr :=
  e4E Va Wa ^ 2 * (psi2E Λ Va Wa lA lSA * f6E Va Wa - 2 * psi4E Λ Va Wa lA lSA * e4E Va Wa)

def xb2E (Vb Wb : IExpr) : IExpr :=
  2 * e4E Vb Wb ^ 2 * Wb - f6E Vb Wb * ((Vb + Wb) ^ 2 - Vb ^ 2)

def numE (Λ : ℕ) (E2a Va Wa lA lSA E2b Vb Wb lB : IExpr) : IExpr :=
  -(.cst (96 * Λ) * (d256E Vb Wb * t1E E2a Va Wa + d256E Va Wa * z1E E2a Va Wa E2b Vb Wb) +
    d256E Va Wa * z2E Λ Va Wa lA lSA Vb Wb lB +
    128 * t2E Λ Va Wa lA lSA * xb2E Vb Wb * thE ^ 2)

/-- The integer numerator of the E8 hat kernel in reciprocal variables. -/
def kernelE (Λ : ℕ) : IExpr :=
  numE Λ (.tat 4) vT wT (l0T Λ) lSE (.zat 4) vZ wZ (l0Z Λ)

section Eval

variable (fs : List (ℝ → ℝ)) (Λ : ℕ) (ex : List (ℝ → ℝ))

@[simp] theorem evalA_e4E (V W : IExpr) (e : NEnv) :
    IExpr.evalA fs (e4E V W) e = axE4 (IExpr.evalA fs V e) (IExpr.evalA fs W e) := by
  simp [e4E, axE4]
@[simp] theorem evalB_e4E (V W : IExpr) (e : NEnv) :
    IExpr.evalB fs (e4E V W) e = axE4 (IExpr.evalB fs V e) (IExpr.evalB fs W e) := by
  simp [e4E, axE4]
@[simp] theorem evalA_f6E (V W : IExpr) (e : NEnv) :
    IExpr.evalA fs (f6E V W) e = axF6 (IExpr.evalA fs V e) (IExpr.evalA fs W e) := by
  simp [f6E, axF6]
@[simp] theorem evalB_f6E (V W : IExpr) (e : NEnv) :
    IExpr.evalB fs (f6E V W) e = axF6 (IExpr.evalB fs V e) (IExpr.evalB fs W e) := by
  simp [f6E, axF6]
@[simp] theorem evalA_d256E (V W : IExpr) (e : NEnv) :
    IExpr.evalA fs (d256E V W) e = axD256 (IExpr.evalA fs V e) (IExpr.evalA fs W e) := by
  simp [d256E, axD256]
@[simp] theorem evalB_d256E (V W : IExpr) (e : NEnv) :
    IExpr.evalB fs (d256E V W) e = axD256 (IExpr.evalB fs V e) (IExpr.evalB fs W e) := by
  simp [d256E, axD256]

@[simp] theorem evalA_uhE (e : NEnv) : IExpr.evalA fs uhE e = e.u := by
  simp [uhE, NMono.eval]
@[simp] theorem evalB_uhE (e : NEnv) : IExpr.evalB fs uhE e = e.u := by
  simp [uhE, NMono.eval]
@[simp] theorem evalA_thE (e : NEnv) : IExpr.evalA fs thE e = e.t := by
  simp [thE, NMono.eval]
@[simp] theorem evalB_thE (e : NEnv) : IExpr.evalB fs thE e = e.t := by
  simp [thE, NMono.eval]
@[simp] theorem evalA_l2E (e : NEnv) : IExpr.evalA fs l2E e = e.l := by
  simp [l2E, NMono.eval]
@[simp] theorem evalB_l2E (e : NEnv) : IExpr.evalB fs l2E e = e.l := by
  simp [l2E, NMono.eval]

theorem evalA_numE (E2a Va Wa lA lSA E2b Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalA fs (numE Λ E2a Va Wa lA lSA E2b Vb Wb lB) e =
      axE Λ (IExpr.evalA fs E2a e) (IExpr.evalA fs Va e) (IExpr.evalA fs Wa e)
        (IExpr.evalA fs lA e) (IExpr.evalA fs lSA e) e.u (IExpr.evalA fs E2b e)
        (IExpr.evalA fs Vb e) (IExpr.evalA fs Wb e) (IExpr.evalA fs lB e) e.t := by
  simp only [numE, t1E, z1E, z2E, t2E, xb2E, psi2E, psi4E, axE, axT1, axZ1, axZ2, axT2, axXb2,
    axPsi2h, axPsi4h, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_neg,
    IExpr.evalA_nat, IExpr.evalA_pow, IExpr.evalA_cst, evalA_e4E, evalA_f6E, evalA_d256E,
    evalA_uhE, evalA_thE]
  push_cast
  ring

theorem evalB_numE (E2a Va Wa lA lSA E2b Vb Wb lB : IExpr) (e : NEnv) :
    IExpr.evalB fs (numE Λ E2a Va Wa lA lSA E2b Vb Wb lB) e =
      axE Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e)
        (IExpr.evalB fs lA e) (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs E2b e)
        (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) (IExpr.evalB fs lB e) e.t := by
  simp only [numE, t1E, z1E, z2E, t2E, xb2E, psi2E, psi4E, axE, axT1, axZ1, axZ2, axT2, axXb2,
    axPsi2h, axPsi4h, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg,
    IExpr.evalB_nat, IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E,
    evalB_uhE, evalB_thE]
  push_cast
  ring

theorem evalA_vT (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) vT e = nomeV e.a := by
  simp [vT, genFun, nomeV]

theorem evalA_vZ (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) vZ e = nomeV e.a := by
  simp [vZ, genFun, nomeV]

theorem evalB_vT (e : NEnv) : IExpr.evalB (kernelAtoms Λ ++ ex) vT e = nomeV e.a := by
  simp [vT, genFun, nomeV]

theorem evalB_vZ (e : NEnv) : IExpr.evalB (kernelAtoms Λ ++ ex) vZ e = nomeV e.b := by
  simp [vZ, genFun, nomeV]

theorem evalA_wT (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) wT e = nomeW e.a := by
  simp [wT, genFun, nomeW]

theorem evalA_wZ (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) wZ e = nomeW e.a := by
  simp [wZ, genFun, nomeW]

theorem evalB_wT (e : NEnv) : IExpr.evalB (kernelAtoms Λ ++ ex) wT e = nomeW e.a := by
  simp [wT, genFun, nomeW]

theorem evalB_wZ (e : NEnv) : IExpr.evalB (kernelAtoms Λ ++ ex) wZ e = nomeW e.b := by
  simp [wZ, genFun, nomeW]

theorem evalA_l0T (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (l0T Λ) e = Λ * nomeL0 e.l e.a := by
  simp only [l0T, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_nat,
    IExpr.evalA_cst, evalA_tat5, evalA_tat7, evalA_l2E, logFun, nomeL0]
  push_cast
  ring

theorem evalA_l0Z (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (l0Z Λ) e = Λ * nomeL0 e.l e.a := by
  simp only [l0Z, IExpr.evalA_add, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_nat,
    IExpr.evalA_cst, evalA_zat5, evalA_zat7, evalA_l2E, logFun, nomeL0]
  push_cast
  ring

theorem evalB_l0T (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (l0T Λ) e = Λ * nomeL0 e.l e.a := by
  simp only [l0T, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat,
    IExpr.evalB_cst, evalB_tat5, evalB_tat7, evalB_l2E, logFun, nomeL0]
  push_cast
  ring

theorem evalB_l0Z (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (l0Z Λ) e = Λ * nomeL0 e.l e.b := by
  simp only [l0Z, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat,
    IExpr.evalB_cst, evalB_zat5, evalB_zat7, evalB_l2E, logFun, nomeL0]
  push_cast
  ring

theorem evalA_lSE (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) lSE e = Λ * nomeLS e.a := by
  simp only [lSE, IExpr.evalA_sub, IExpr.evalA_mul, IExpr.evalA_nat, evalA_tat5, evalA_tat6,
    logFun, nomeLS]
  push_cast
  ring

theorem evalB_lSE (e : NEnv) : IExpr.evalB (kernelAtoms Λ ++ ex) lSE e = Λ * nomeLS e.a := by
  simp only [lSE, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat, evalB_tat5, evalB_tat6,
    logFun, nomeLS]
  push_cast
  ring

/-- The `a`-version of the numerator vanishes identically. -/
theorem kernelE_evalA (e : NEnv) : IExpr.evalA (kernelAtoms Λ ++ ex) (kernelE Λ) e = 0 := by
  rw [kernelE, evalA_numE, evalA_vT, evalA_vZ, evalA_wT, evalA_wZ, evalA_l0T, evalA_l0Z,
    evalA_tat4, evalA_zat4]
  exact axE_diag _ _ _ _ _ _ _ _

theorem kernelE_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (kernelE Λ) e =
      axE Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [kernelE, evalB_numE, evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_l0Z,
    evalB_lSE, evalB_tat4, evalB_zat4]
  rfl

end Eval

/-- The environment of an actual pair of imaginary-axis parameters, in reciprocal variables. -/
noncomputable def axisNEnv (u t : ℝ) : NEnv :=
  ⟨Real.exp (-π * u), Real.exp (-π * t), 1 / (π * u), 1 / (π * t), Real.log 2⟩

/-- **The numerator on the axes**: a positive multiple of `Φ'`. -/
theorem kernelE_eval_axis (Λ : ℕ) (ex : List (ℝ → ℝ)) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (kernelE Λ) (axisNEnv u t) =
      1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : (1 : ℝ) / (π * t) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ ht.ne')
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr : (1 : ℝ) / (π * (1 / (π * t))) = t := by field_simp
  rw [kernelE_evalB]
  simp only [axisNEnv]
  rw [axE_eq_axPhi _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_eq_nome hu, axE2_eq_nome ht,
    axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht, axL_eq_nome hu,
    axL_eq_nome ht, axLS_eq_nome hu]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

end E8Leech.Kron
