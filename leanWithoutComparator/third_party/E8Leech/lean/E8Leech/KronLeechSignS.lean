import E8Leech.KronLeechSE

/-!
# The sign of the Leech kernels with the second variable inverted

For `t = 1/s < 1` the numerators of `𝒦̂⁽²⁴⁾(iu, i/s)` and of `𝒦⁽²⁴⁾(iu, i/s)` are `−s¹⁶` times the
pairings of `KronLeechSE`. The pairing is computed by a program; the transformation of `KronJet3`
turns its register into a jet `(c₀, c₁, c₂, r)` in the nome `b` of `is`. The first three
components vanish (the certificate checks that their models are zero), so the pairing is `b³ r`,
and its `a`-version vanishes, so `r = (b − a) · DD(r)`. The denominator is `s¹²` times the one at
`(u, s)`, which has the sign of `b − a`. Hence the kernel inequality is the positivity of the
divided difference of `r`.

* `bilE`, `leechRSE`, `leechSSE`: the pairings as expressions.
* `MDD.eq_zero_of_approx`: a register whose model is zero vanishes.
* `leechS_cube`: the pairing is the cube of the nome times the last component of the jet.
* `leechHatKernel_pos_of_rs`, `leechKernelK_neg_of_ss`: the signs of the kernels from the sign of
  the divided difference.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The pairings as expressions -/

/-- The pairing of two lists of expressions. -/
def bilE : List IExpr → List IExpr → IExpr
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => a * b + bilE as bs

theorem evalB_bilE (fs : List (ℝ → ℝ)) (e : NEnv) : ∀ as bs : List IExpr,
    IExpr.evalB fs (bilE as bs) e =
      bil (as.map fun x => IExpr.evalB fs x e) (bs.map fun x => IExpr.evalB fs x e)
  | [], _ => by
    show IExpr.evalB fs (0 : IExpr) e = _
    rw [IExpr.evalB_nat]
    simp [bil]
  | _ :: _, [] => by
    show IExpr.evalB fs (0 : IExpr) e = _
    rw [IExpr.evalB_nat]
    simp [bil]
  | a :: as, b :: bs => by
    show IExpr.evalB fs (a * b + bilE as bs) e = _
    rw [IExpr.evalB_add, IExpr.evalB_mul, evalB_bilE fs e as bs]
    rfl

theorem evalA_bilE (fs : List (ℝ → ℝ)) (e : NEnv) : ∀ as bs : List IExpr,
    IExpr.evalA fs (bilE as bs) e =
      bil (as.map fun x => IExpr.evalA fs x e) (bs.map fun x => IExpr.evalA fs x e)
  | [], _ => by
    show IExpr.evalA fs (0 : IExpr) e = _
    rw [IExpr.evalA_nat]
    simp [bil]
  | _ :: _, [] => by
    show IExpr.evalA fs (0 : IExpr) e = _
    rw [IExpr.evalA_nat]
    simp [bil]
  | a :: as, b :: bs => by
    show IExpr.evalA fs (a * b + bilE as bs) e = _
    rw [IExpr.evalA_add, IExpr.evalA_mul, evalA_bilE fs e as bs]
    rfl

/-- Minus the pairing of the kernel `𝒦̂⁽²⁴⁾` at `(iu, i/s)`. -/
def leechRSE (Λ : ℕ) : IExpr := -bilE (leechTauE Λ) (leechZSE Λ)

/-- The pairing of the kernel `𝒦⁽²⁴⁾` at `(iu, i/s)`. -/
def leechSSE (Λ : ℕ) : IExpr := bilE (leechTauE Λ) (leechZKE Λ)

theorem leechRSE_evalA (fs : List (ℝ → ℝ)) (Λ : ℕ) (e : NEnv) :
    IExpr.evalA fs (leechRSE Λ) e = 0 := by
  rw [leechRSE, IExpr.evalA_neg, evalA_bilE, leechZSE, bilA_leechZS, neg_zero]

theorem leechSSE_evalA (fs : List (ℝ → ℝ)) (Λ : ℕ) (e : NEnv) :
    IExpr.evalA fs (leechSSE Λ) e = 0 := by
  rw [leechSSE, evalA_bilE, leechZKE, bilA_leechZS]

/-! ## Registers with zero models -/

/-- A function with the zero model vanishes. -/
theorem MTM.eq_zero_of_approx {Bx : Bounds} {S : NEnv → Prop} {f : NEnv → ℝ}
    (h : (⟨[], []⟩ : MTM).Approx Bx S f) {e : NEnv} (he : Bx.Mem e) (hs : S e) : f e = 0 := by
  have h1 := h e he hs
  have h2 : |f e - 0| ≤ 0 := by simpa [IPoly.eval] using h1
  rw [sub_zero] at h2
  exact abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))

/-! ## The cube of the nome -/

section Cube

variable {Λ : ℕ} {prog : List IInstr} {k : ℕ}

/-- **The value of a register is the cube of the nome times the last component of its jet**, when
the first three components vanish. -/
theorem leechS_cube (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hc : ∀ j, j < 3 → (ISLP.runR (tAtoms Λ) side e (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
      ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j) 0 = 0) :
    ISLP.eval (tAtoms Λ) side e ((ISLP.runExpr prog []).getD k (.cst 0)) =
      (if side then e.a else e.b) ^ 3 *
        (ISLP.runR (tAtoms Λ) side e (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 := by
  have hf : (tAtoms Λ).getD 0 (fun _ => 0) = id := rfl
  have hz := ISLP.zleafL_ok Λ h2 side e hx0 hx4 hs3 hs4
  have hjet := ISLP.sim3_tr3 hf hz prog k
  have hn := ISLP.tr3_nome hf hz prog
  rw [ISLP.eval_runExpr_getD, ← hjet, ISLP.jet3Val, hn]
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  have c2 := hc 2 (by norm_num)
  rw [Nat.add_zero] at c0
  rw [c0, c1, c2]
  ring

end Cube

/-! ## The signs of the kernels -/

/-- The real-number core of the sign arguments: `K = Φ/(3456 D (σ N))`, `c Φ = τ (b³ Y)`. -/
theorem sign_of_cube_ratio {b Y δ c K N D Φ σ τ : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hτ : 0 < τ)
    (hc : 0 < c) (hD : 0 < D) (hY : 0 < Y / δ) (hN : 0 < N / δ) (hΦ : c * Φ = τ * (b ^ 3 * Y))
    (hK : K = Φ / (3456 * (D * (σ * N)))) : 0 < K := by
  have hδ : δ ≠ 0 := by
    rintro rfl
    simp at hY
  have hΦ' : Φ = τ * (b ^ 3 * Y) / c := by
    rw [eq_div_iff hc.ne', mul_comm]
    exact hΦ
  have e : K = τ * b ^ 3 * (Y / δ) / (c * (3456 * (D * (σ * (N / δ))))) := by
    rw [hK, hΦ']
    have hN0 : N ≠ 0 := by
      rintro rfl
      simp at hN
    field_simp
  rw [e]
  exact div_pos (mul_pos (mul_pos hτ (pow_pos hb 3)) hY)
    (mul_pos hc (mul_pos (by norm_num) (mul_pos hD (mul_pos hσ hN))))

section Signs

variable {Λ : ℕ} {prog : List IInstr} {k : ℕ}

/-- The conditions on the two nomes under which the jets of the atoms are sound. -/
def NomeSmall (e : NEnv) : Prop :=
  4 * e.a < 1 ∧ 4 * e.b < 1 ∧ |e.a * devTheta3 e.a| < 1 ∧ |e.a * devTheta4 e.a| < 1 ∧
    |e.b * devTheta3 e.b| < 1 ∧ |e.b * devTheta4 e.b| < 1

/-- **Positivity of `𝒦̂⁽²⁴⁾(iu, i/s)`** from the positivity of the divided difference of the last
component of the jet of `leechRSE`. -/
theorem leechHatKernel_pos_of_rs (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechRSE Λ) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hsmall : NomeSmall (axisNEnvS u s))
    (hc : ∀ side : Bool, ∀ j, j < 3 →
      (ISLP.runR (tAtoms Λ) side (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j) 0 = 0)
    (hDD : 0 <
      ((ISLP.runR (tAtoms Λ) false (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 -
        (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0) /
        ((axisNEnvS u s).b - (axisNEnvS u s).a)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt s⁻¹)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  obtain ⟨ha4, hb4, ha3s, ha4s, hb3s, hb4s⟩ := hsmall
  have ha : 0 < (axisNEnvS u s).a := Real.exp_pos _
  have hb : 0 < (axisNEnvS u s).b := Real.exp_pos _
  -- the two versions of the pairing
  have hB := leechS_cube (prog := prog) (k := k) h2 false (axisNEnvS u s) hb.le hb4 hb3s hb4s
    (hc false)
  have hA := leechS_cube (prog := prog) (k := k) h2 true (axisNEnvS u s) ha.le ha4 ha3s ha4s
    (hc true)
  rw [hprog] at hB hA
  have hA0 : (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1
      []).getD ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 = 0 := by
    have h : IExpr.evalA (tAtoms Λ) (leechRSE Λ) (axisNEnvS u s) = (axisNEnvS u s).a ^ 3 *
        (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 := hA
    rw [leechRSE_evalA] at h
    have h3 : (axisNEnvS u s).a ^ 3 ≠ 0 := pow_ne_zero 3 ha.ne'
    exact (mul_eq_zero.mp h.symm).resolve_left h3
  rw [hA0, sub_zero] at hDD
  have hB' : IExpr.evalB (tAtoms Λ) (leechRSE Λ) (axisNEnvS u s) = (axisNEnvS u s).b ^ 3 *
      (ISLP.runR (tAtoms Λ) false (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 := hB
  rw [leechRSE, IExpr.evalB_neg, evalB_bilE] at hB'
  -- the numerator and the denominator
  have hnum := leechRS_eval_axis Λ hu hs
  have hden : 0 < axNu (axV u) (axW u) (axV s) (axW s) /
      ((axisNEnvS u s).b - (axisNEnvS u s).a) := ckmrvAxisDividedDenominator_pos hu hs hus hprod
  have haxis := ckmrvLeechHatKernel_axis hu (inv_pos.mpr hs) (sub_ne_zero.mpr hJ)
  rw [axNu_inv hs] at haxis
  rw [haxis, Complex.ofReal_re]
  have hc0 : (0 : ℝ) < 24576 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 := by positivity
  refine sign_of_cube_ratio hb (pow_pos hs 12) (pow_pos hs 16) hc0 (axDelta_pos (inv_pos.mpr hs))
    hDD hden ?_ rfl
  rw [← hnum, ← hB']
  ring

/-- **Negativity of `𝒦⁽²⁴⁾(iu, i/s)`** from the positivity of the divided difference of the last
component of the jet of `leechSSE`. -/
theorem leechKernelK_neg_of_ss (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechSSE Λ) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hsmall : NomeSmall (axisNEnvS u s))
    (hc : ∀ side : Bool, ∀ j, j < 3 →
      (ISLP.runR (tAtoms Λ) side (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j) 0 = 0)
    (hDD : 0 <
      ((ISLP.runR (tAtoms Λ) false (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 -
        (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0) /
        ((axisNEnvS u s).b - (axisNEnvS u s).a)) :
    (ckmrvLeechKernel (imagPt u) (imagPt s⁻¹)).re < 0 := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  obtain ⟨ha4, hb4, ha3s, ha4s, hb3s, hb4s⟩ := hsmall
  have ha : 0 < (axisNEnvS u s).a := Real.exp_pos _
  have hb : 0 < (axisNEnvS u s).b := Real.exp_pos _
  have hB := leechS_cube (prog := prog) (k := k) h2 false (axisNEnvS u s) hb.le hb4 hb3s hb4s
    (hc false)
  have hA := leechS_cube (prog := prog) (k := k) h2 true (axisNEnvS u s) ha.le ha4 ha3s ha4s
    (hc true)
  rw [hprog] at hB hA
  have hA0 : (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1
      []).getD ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 = 0 := by
    have h : IExpr.evalA (tAtoms Λ) (leechSSE Λ) (axisNEnvS u s) = (axisNEnvS u s).a ^ 3 *
        (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 := hA
    rw [leechSSE_evalA] at h
    have h3 : (axisNEnvS u s).a ^ 3 ≠ 0 := pow_ne_zero 3 ha.ne'
    exact (mul_eq_zero.mp h.symm).resolve_left h3
  rw [hA0, sub_zero] at hDD
  have hB' : IExpr.evalB (tAtoms Λ) (leechSSE Λ) (axisNEnvS u s) = (axisNEnvS u s).b ^ 3 *
      (ISLP.runR (tAtoms Λ) false (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 := hB
  rw [leechSSE, evalB_bilE] at hB'
  have hnum := leechSS_eval_axis Λ hu hs
  have hden : 0 < axNu (axV u) (axW u) (axV s) (axW s) /
      ((axisNEnvS u s).b - (axisNEnvS u s).a) := ckmrvAxisDividedDenominator_pos hu hs hus hprod
  have haxis := ckmrvLeechKernel_axis hu (inv_pos.mpr hs) (sub_ne_zero.mpr hJ)
  rw [axNu_inv hs] at haxis
  rw [haxis, Complex.ofReal_re]
  have hc0 : (0 : ℝ) < 24576 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 := by positivity
  have hpos : 0 < -(axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 s⁻¹) (axV s⁻¹)
      (axW s⁻¹) (axL s⁻¹) s⁻¹ /
      (3456 * (axDelta (axV s⁻¹) (axW s⁻¹) * (s ^ 12 * axNu (axV u) (axW u) (axV s) (axW s))))) := by
    refine sign_of_cube_ratio hb (pow_pos hs 12) (pow_pos hs 16) hc0
      (axDelta_pos (inv_pos.mpr hs)) hDD hden (Φ := -axLeechPhiK (axE2 u) (axV u) (axW u) (axL u)
        (axLS u) u (axE2 s⁻¹) (axV s⁻¹) (axW s⁻¹) (axL s⁻¹) s⁻¹) ?_ (by ring)
    rw [mul_neg, ← hnum, ← hB']
    ring
  linarith

end Signs

end E8Leech.Kron
