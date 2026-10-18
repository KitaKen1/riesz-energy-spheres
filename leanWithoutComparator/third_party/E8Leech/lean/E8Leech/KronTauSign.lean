import E8Leech.KronLeechCusp

/-!
# Signs of functions of one variable from a model and a cover

A function of the first variable only (an expression in the `τ`-side atoms and in `û`, `1/π`,
`log 2`) is positive on an interval of reciprocal parameters if the first component of its model
has all terms divisible by a power of the nome and the quotient is positive on the cells of a
cover. The machinery is the two-dimensional one (`Cover`, `cellOKSb`, `sCellOK`) with the second
reciprocal parameter fixed.

* `pos_of_cover_x`: the statement for a model `T` of a function `f` of the environment.
* `expr_pos_of_cover_x`: the same for the register of a program that computes an expression.
* `leechCusp_combo_neg_of_pos`, `leechCusp_combo_pos_of_pos`, `leechCusp_lead_pos_of_pos` and
  their inverted forms: the signs of `cd a₀ + cn a₁` and of `a₁` from the signs of the expressions
  of `KronLeechCusp`.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-- **Positivity on a cover in the first variable.** The rectangle of the cover is degenerate in
the second variable (`y = y₀ < c`, so that no corner leaf can occur). -/
theorem pos_of_cover_x {Bx : Bounds} {f : NEnv → ℝ} {T : MTM}
    (hT : T.Approx Bx (fun _ => True) f) {i : ℕ} (hd : T.Divisible i 0) {Q : Quots}
    (hQ : T.quots i 0 = Q) {kc n : ℕ} {c x0 x1 y0 : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c ⟨x0, x1, y0, y0⟩ = true)
    (hy0 : 0 < y0) (hc : y0 < c) {x : ℝ} (hx : 0 < x) (hx0 : (x0 : ℝ) ≤ x) (hx1 : x ≤ x1) :
    0 < f (recNEnvS x y0) := by
  subst hQ
  have hy : (0 : ℝ) < y0 := by exact_mod_cast hy0
  have h := Cover.sound (env := recNEnvS) (P := fun x y => 0 < f (recNEnvS x y))
    (cellOKSb_spec kc n)
    (fun C _ _ hC hok x y _ _ hmem => by
      simp only [sCellOK, decide_eq_true_eq] at hok
      have h := MTM.pos_of_posOK hT hd hC hok.1 hok.2 hmem trivial (Real.exp_pos _)
        (Real.exp_pos _) (g := 0) (by simp)
      simpa using h)
    cov ⟨x0, x1, y0, y0⟩ hcov x y0 hx hy ⟨hx0, hx1, le_rfl, le_rfl⟩
  rcases h with h | h
  · exact absurd h.2 (not_le.mpr (by exact_mod_cast hc))
  · exact h

/-- **Positivity of an expression on a cover in the first variable**, for the register `k` of a
program that computes it. -/
theorem expr_pos_of_cover_x {Bx : Bounds} (hB : Bx.Valid) {D Dcap : ℕ} {At : List MDD}
    {fs : List (ℝ → ℝ)} (hAt : ISLP.AtomsOK Bx (fun _ => True) At fs) {prog : List IInstr}
    {k : ℕ} {x : IExpr} (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = x) {T : MTM}
    (hTk : ((ISLP.runMDD Bx D Dcap At prog []).getD k MDD.zero).A = T) {i : ℕ}
    (hd : T.Divisible i 0) {Q : Quots} (hQ : T.quots i 0 = Q) {kc n : ℕ} {c x0 x1 y0 : ℚ}
    {cov : Cover}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c ⟨x0, x1, y0, y0⟩ = true)
    (hy0 : 0 < y0) (hc : y0 < c) {v : ℝ} (hv : 0 < v) (hx0 : (x0 : ℝ) ≤ v) (hx1 : v ≤ x1) :
    0 < IExpr.evalA fs x (recNEnvS v y0) := by
  have hT := (ISLP.approx_checked hB D Dcap hAt prog k x hprog).1
  rw [hTk] at hT
  exact pos_of_cover_x hT hd hQ hcov hy0 hc hv hx0 hx1

/-- The environment of a cover in the first variable is an axis environment. -/
theorem recNEnvS_eq_axisNEnvS (u : ℝ) {y0 : ℝ} (hy0 : 0 < y0) :
    recNEnvS (1 / (π * u)) y0 = axisNEnvS u (1 / (π * y0)) := by
  have hπ := Real.pi_pos
  rw [axisNEnvS_eq_recNEnvS]
  congr 1
  field_simp

/-! ## The cusp coefficients -/

section Cusp

variable {Λ : ℕ} {ex : List (ℝ → ℝ)}

/-- `cd a₀(u) + cn a₁(u) < 0` from the positivity of `−leechCuspHE`. -/
theorem leechCusp_combo_neg_of_pos (hΛ : 0 < Λ) {cn cd : ℤ} {u : ℝ} (hu : 0 < u) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) (-(leechCuspHE Λ cn cd)) (axisNEnvS u s)) :
    cd * (leechAxisCusp (-1) u 1).re + cn * (leechAxisCusp (-1) u 0).re < 0 := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  rw [IExpr.evalA_neg, leechCuspHE_eval_axis Λ ex cn cd hu s] at h
  have hpos : 0 < 41472 * (Λ : ℝ) * (1 / (π * u)) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le hneg]

/-- `cd a₀(u) + cn a₁(u) > 0` from the positivity of `leechCuspHE`. -/
theorem leechCusp_combo_pos_of_pos (hΛ : 0 < Λ) {cn cd : ℤ} {u : ℝ} (hu : 0 < u) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) (leechCuspHE Λ cn cd) (axisNEnvS u s)) :
    0 < cd * (leechAxisCusp (-1) u 1).re + cn * (leechAxisCusp (-1) u 0).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  rw [leechCuspHE_eval_axis Λ ex cn cd hu s] at h
  have hpos : 0 < 41472 * (Λ : ℝ) * (1 / (π * u)) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr hneg)]

/-- `a₁(u) > 0` from the positivity of `leechCuspFE`. -/
theorem leechCusp_lead_pos_of_pos {u : ℝ} (hu : 0 < u) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) leechCuspFE (axisNEnvS u s)) :
    0 < (leechAxisCusp (-1) u 0).re := by
  have hπ := Real.pi_pos
  rw [leechCuspFE_eval_axis Λ ex hu s] at h
  have hpos : 0 < 41472 * (1 / (π * u)) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr hneg)]

/-- `cd a₀(1/v) + cn a₁(1/v) < 0` from the positivity of `−leechCuspHmE` at `v`. -/
theorem leechCusp_combo_neg_inv_of_pos (hΛ : 0 < Λ) {cn cd : ℤ} {v : ℝ} (hv : 0 < v) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) (-(leechCuspHmE Λ cn cd)) (axisNEnvS v s)) :
    cd * (leechAxisCusp (-1) v⁻¹ 1).re + cn * (leechAxisCusp (-1) v⁻¹ 0).re < 0 := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  rw [IExpr.evalA_neg] at h
  have hE := leechCuspHmE_eval_axis Λ ex cn cd hv s
  have hv14 : 0 < v ^ 14 := pow_pos hv 14
  have hpos : 0 < 41472 * (Λ : ℝ) * (v / π) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le hneg, mul_pos hv14 h]

/-- `cd a₀(1/v) + cn a₁(1/v) > 0` from the positivity of `leechCuspHmE` at `v`. -/
theorem leechCusp_combo_pos_inv_of_pos (hΛ : 0 < Λ) {cn cd : ℤ} {v : ℝ} (hv : 0 < v) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) (leechCuspHmE Λ cn cd) (axisNEnvS v s)) :
    0 < cd * (leechAxisCusp (-1) v⁻¹ 1).re + cn * (leechAxisCusp (-1) v⁻¹ 0).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hE := leechCuspHmE_eval_axis Λ ex cn cd hv s
  have hv14 : 0 < v ^ 14 := pow_pos hv 14
  have hpos : 0 < 41472 * (Λ : ℝ) * (v / π) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr hneg), mul_pos hv14 h]

/-- `a₁(1/v) > 0` from the positivity of `leechCuspFmE` at `v`. -/
theorem leechCusp_lead_pos_inv_of_pos {v : ℝ} (hv : 0 < v) {s : ℝ}
    (h : 0 < IExpr.evalA (kernelAtoms Λ ++ ex) leechCuspFmE (axisNEnvS v s)) :
    0 < (leechAxisCusp (-1) v⁻¹ 0).re := by
  have hπ := Real.pi_pos
  have hE := leechCuspFmE_eval_axis Λ ex hv s
  have hv14 : 0 < v ^ 14 := pow_pos hv 14
  have hpos : 0 < 41472 * (v / π) := by positivity
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr hneg), mul_pos hv14 h]

end Cusp

end E8Leech.Kron
