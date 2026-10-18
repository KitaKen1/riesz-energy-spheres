import E8Leech.KronKernelSplit
import E8Leech.KronCells
import E8Leech.CKMRVAxisDenominatorSign

/-!
# The sign of the E8 hat kernel from models of the split numerator

On the axes the numerator is `t̂ · e12E + b · etilE` (`KronKernelSplit`), and both expressions
vanish in their `a`-versions. With models `T₁, T₂` of their divided differences `D₁₂, D̃` the
divided numerator is `t̂ (D₁₂ + w D̃)` with `w = b / t̂ ≥ 0`. On the side `ut > 1` it has the sign
of the kernel: `2 𝒦̂ 𝒩 = Φ'` and `𝒩 / (b − a) > 0`. The factor `t̂` is exact, so the cells may
reach `t = ∞`; the quotient `w` is bounded on a cell either by the bounds of the cell or, for
cells at `t = ∞`, by `b = exp (−1/t̂) ≤ 2 √b · t̂`.

* `SplitModels`, `splitModels_of_run`: the two models.
* `WOK`, `WOK.le`: a certified bound of `b / t̂`.
* `kernel_pos_of_split`: positivity of the kernel on a cell that passes the sign check.
* `kernel_pos_of_cover`, `kernel_pos_of_cover_ge_one`: the same on a checked cover in reciprocal
  coordinates, and the statement for `u, t ≥ 1` outside a corner box.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

theorem axisNEnv_eq_recNEnv (u t : ℝ) :
    axisNEnv u t = recNEnv (1 / (π * u)) (1 / (π * t)) := by
  simp [axisNEnv, recNEnv]

/-- The divided difference of an expression in the ten atoms. -/
noncomputable def splitDD (Λ : ℕ) (x : IExpr) (e : NEnv) : ℝ :=
  (IExpr.evalB (kernelAtoms Λ ++ devAtoms) x e - IExpr.evalA (kernelAtoms Λ ++ devAtoms) x e) /
    (e.b - e.a)

/-- `T₁, T₂` are models of the divided differences of the two parts of the numerator. -/
def SplitModels (Bx : Bounds) (Λ : ℕ) (T₁ T₂ : MTM) : Prop :=
  T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (e12E Λ)) ∧
    T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (etilE Λ))

/-- The divided-difference parts of two registers of a checked program run are models. -/
theorem splitModels_of_run {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE) (hG' : GenOK Bx NE')
    (D Dcap : ℕ) {Λ n : ℕ} (K N N' : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k₁ k₂ : ℕ)
    (h₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = e12E Λ)
    (h₂ : (ISLP.runExpr prog []).getD k₂ (.cst 0) = etilE Λ) :
    SplitModels Bx Λ
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₁
        MDD.zero).D
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₂
        MDD.zero).D :=
  ⟨(ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₁ _ h₁).2.2,
    (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₂ _ h₂).2.2⟩

/-! ## The quotient `b / t̂` -/

/-- `exp (−1/y) ≤ 2 s y` if `exp (−1/y) ≤ s²`: the square root of the nome is at most `2y`. -/
theorem exp_neg_inv_le {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) (h : Real.exp (-y⁻¹) ≤ s ^ 2) :
    Real.exp (-y⁻¹) ≤ 2 * s * y := by
  have hr0 : 0 ≤ Real.exp (-(2 * y)⁻¹) := (Real.exp_pos _).le
  have hsq : Real.exp (-(2 * y)⁻¹) * Real.exp (-(2 * y)⁻¹) = Real.exp (-y⁻¹) := by
    rw [← Real.exp_add]
    congr 1
    rw [mul_inv]
    ring
  have h1 : Real.exp (-(2 * y)⁻¹) ≤ s := by
    by_contra hcon
    have hlt : s < Real.exp (-(2 * y)⁻¹) := not_le.mp hcon
    have h3 := mul_lt_mul'' hlt hlt hs hs
    rw [hsq] at h3
    have h4 : Real.exp (-y⁻¹) ≤ s * s := by rwa [sq] at h
    linarith
  have h2 : Real.exp (-(2 * y)⁻¹) ≤ 2 * y := by
    have hpos : 0 < (2 * y)⁻¹ := by positivity
    have hexp : (2 * y)⁻¹ ≤ Real.exp ((2 * y)⁻¹) := by
      have := Real.add_one_le_exp ((2 * y)⁻¹)
      linarith
    have h5 := inv_anti₀ hpos hexp
    rw [inv_inv] at h5
    rw [Real.exp_neg]
    exact h5
  have h6 := mul_le_mul h1 h2 hr0 hs
  rw [hsq] at h6
  linarith

/-- `w` bounds the quotient `b / t̂` on the cell: by the bounds of the cell if `t̂` stays away from
`0`, or by `(w/2)² ≥ b`. -/
def WOK (C : Cell) (w : ℚ) : Prop :=
  0 ≤ w ∧ ((0 < C.lo.tn ∧ (C.hi.bn : ℚ) * C.lo.td ≤ w * (C.hi.bd * C.lo.tn)) ∨
    4 * (C.hi.bn : ℚ) ≤ w ^ 2 * C.hi.bd)

instance (C : Cell) (w : ℚ) : Decidable (WOK C w) := by
  unfold WOK
  infer_instance

theorem WOK.le {C : Cell} {w : ℚ} (hw : WOK C w) (hC : C.Valid) {x y : ℝ} (hy : 0 < y)
    (hmem : C.Mem (recNEnv x y)) : Real.exp (-y⁻¹) ≤ (w : ℝ) * y := by
  obtain ⟨hw0, hcase⟩ := hw
  have hw0' : (0 : ℝ) ≤ w := by exact_mod_cast hw0
  obtain ⟨-, -, -, lt, -, hhi⟩ := hmem
  obtain ⟨-, -, -, hb', -⟩ := hhi
  obtain ⟨⟨-, -, -, dt, -⟩, ⟨-, eb, -⟩⟩ := hC
  have lt' : (C.lo.tn : ℝ) ≤ y * C.lo.td := lt
  have hb'' : Real.exp (-y⁻¹) * C.hi.bd ≤ C.hi.bn := hb'
  have heb : (0 : ℝ) < C.hi.bd := by exact_mod_cast eb
  rcases hcase with ⟨-, h⟩ | h
  · have hdt : (0 : ℝ) < C.lo.td := by exact_mod_cast dt
    have h' : (((C.hi.bn : ℚ) * C.lo.td : ℚ) : ℝ) ≤ ((w * (C.hi.bd * C.lo.tn) : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    push_cast at h'
    have k1 := mul_le_mul_of_nonneg_right hb'' hdt.le
    have k2 := mul_le_mul_of_nonneg_left lt' (mul_nonneg hw0' heb.le)
    have k3 : Real.exp (-y⁻¹) * (C.hi.bd * C.lo.td) ≤ (w : ℝ) * y * (C.hi.bd * C.lo.td) := by
      nlinarith [k1, k2, h']
    exact le_of_mul_le_mul_right k3 (mul_pos heb hdt)
  · have h' : ((4 * (C.hi.bn : ℚ) : ℚ) : ℝ) ≤ ((w ^ 2 * C.hi.bd : ℚ) : ℝ) := Rat.cast_le.mpr h
    push_cast at h'
    have hb2 : Real.exp (-y⁻¹) ≤ ((w : ℝ) / 2) ^ 2 := by
      have k : Real.exp (-y⁻¹) * C.hi.bd ≤ ((w : ℝ) / 2) ^ 2 * C.hi.bd := by
        nlinarith [hb'', h']
      exact le_of_mul_le_mul_right k heb
    have h7 := exp_neg_inv_le hy (div_nonneg hw0' (by norm_num)) hb2
    linarith

theorem mul_min_le {W w m : ℝ} (hW0 : 0 ≤ W) (hWw : W ≤ w) : w * min m 0 ≤ W * m := by
  rcases le_total m 0 with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hWw) h]
  · rw [min_eq_right h, mul_zero]
    exact mul_nonneg hW0 h

/-! ## Positivity on a cell -/

/-- **Positivity on a cell.** A cell inside the bounds of the models that passes the sign check
(pivots `a²b` and `a³`) contains no point `(u, t)` with `ut > 1`, `u ≠ t` where the kernel is not
positive. -/
theorem kernel_pos_of_split {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : SplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w : ℚ} (hw : WOK C w)
    (hOK : C.PosOK ((T₁.quots 2 0).marginB C + w * min ((T₂.quots 2 0).marginB C) 0)
      ((T₁.quots 2 0).marginA C + w * min ((T₂.quots 2 0).marginA C) 0) 0)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  have ha1 : (axisNEnv u t).a < 1 := by
    have hneg : -π * u < 0 := by nlinarith [mul_pos hπ hu]
    exact Real.exp_lt_one_iff.mpr hneg
  have hY : 0 < (axisNEnv u t).t := by
    have h : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [h]
    positivity
  have hab : (axisNEnv u t).a ≠ (axisNEnv u t).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * t) := h
    exact hut (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  -- the two lower bounds in pivot form
  have l₁ := MTM.lower_of_divisible hT.1 hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible hT.2 hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  -- the quotient `W = b / t̂`
  have hwb : (axisNEnv u t).b ≤ (w : ℝ) * (axisNEnv u t).t := by
    have hmem' : C.Mem (recNEnv (1 / (π * u)) (1 / (π * t))) := by
      rw [← axisNEnv_eq_recNEnv]
      exact hmem
    have h := hw.le hC (y := 1 / (π * t)) (by positivity) hmem'
    have hb' : (axisNEnv u t).b = Real.exp (-(1 / (π * t))⁻¹) := by
      rw [axisNEnv_eq_recNEnv]
      rfl
    have ht' : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [hb', ht']
    exact h
  obtain ⟨W, hWdef, hW0, hWw⟩ : ∃ W : ℝ, W * (axisNEnv u t).t = (axisNEnv u t).b ∧ 0 ≤ W ∧
      W ≤ (w : ℝ) :=
    ⟨(axisNEnv u t).b / (axisNEnv u t).t, div_mul_cancel₀ _ hY.ne', div_nonneg hb.le hY.le,
      (div_le_iff₀ hY).mpr hwb⟩
  -- the weighted margins
  have hkey := Cell.pos_of_posOK hC hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots 2 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots 2 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ 2 * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hpos : 0 < splitDD Λ (e12E Λ) (axisNEnv u t) +
      W * splitDD Λ (etilE Λ) (axisNEnv u t) := by
    have hin : 0 < (axisNEnv u t).b * (((T₁.quots 2 0).marginB C : ℚ) : ℝ) +
        (axisNEnv u t).a * (((T₁.quots 2 0).marginA C : ℚ) : ℝ) +
        W * ((axisNEnv u t).b * (((T₂.quots 2 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((T₂.quots 2 0).marginA C : ℚ) : ℝ)) := by
      nlinarith [hkey, kB, kA]
    have hmul := mul_pos hc hin
    nlinarith [hmul, l₁, k2]
  -- back to the numerator
  have hD₁ : splitDD Λ (e12E Λ) (axisNEnv u t) =
      IExpr.evalB (kernelAtoms Λ ++ devAtoms) (e12E Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, e12E_evalA, sub_zero]
  have hD₂ : splitDD Λ (etilE Λ) (axisNEnv u t) =
      IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, etilE_evalA Λ ha ha1, sub_zero]
  have hlin : (axisNEnv u t).t * splitDD Λ (e12E Λ) (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ (etilE Λ) (axisNEnv u t) =
      (axisNEnv u t).t * (splitDD Λ (e12E Λ) (axisNEnv u t) +
        W * splitDD Λ (etilE Λ) (axisNEnv u t)) := by
    rw [← hWdef]
    ring
  have hsum : (axisNEnv u t).t * splitDD Λ (e12E Λ) (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ (etilE Λ) (axisNEnv u t) =
      1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        (axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t /
          (Real.exp (-π * t) - Real.exp (-π * u))) := by
    have hδ : (axisNEnv u t).b - (axisNEnv u t).a = Real.exp (-π * t) - Real.exp (-π * u) := rfl
    have e2 : ∀ p q X Z δ : ℝ, p * (X / δ) + q * (Z / δ) = (p * X + q * Z) / δ :=
      fun p q X Z δ => by ring
    rw [hD₁, hD₂, hδ, e2, split_eval_axis Λ hu ht]
    ring
  have hc' : (0 : ℝ) < 1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 := by positivity
  have hΦ : 0 < axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t)
      (axL t) t / (Real.exp (-π * t) - Real.exp (-π * u)) := by
    have h := mul_pos hY hpos
    rw [← hlin, hsum] at h
    exact (mul_pos_iff_of_pos_left hc').mp h
  have hden := ckmrvAxisDividedDenominator_pos hu ht hut hprod
  rw [← ckmrvEightHatKernel_axis hu ht hJ, mul_div_assoc] at hΦ
  have h2 := (mul_pos_iff_of_pos_right hden).mp hΦ
  linarith

/-- The cell test of the split numerator. `w` bounds `b / t̂` on the cell; the second auxiliary
number of a leaf is not used. -/
def splitCellOK (Bx : Bounds) (Q₁ Q₂ : Quots) (C : Cell) (w _ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧
    C.PosOK (Q₁.marginB C + w * min (Q₂.marginB C) 0) (Q₁.marginA C + w * min (Q₂.marginA C) 0) 0)

/-- **Positivity on a cover**, in reciprocal coordinates, outside the corner. -/
theorem kernel_pos_of_cover {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : SplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 2 0 = Q₁) (hQ₂ : T₂.quots 2 0 = Q₂) {k n : ℕ} {c : ℚ}
    {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKb k n) (splitCellOK Bx Q₁ Q₂) c r = true) {u t : ℝ} (hu : 0 < u)
    (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  subst hQ₁ hQ₂
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 0 < u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      1 < u * t → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) →
      0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (cellOKb_spec k n)
    (fun C w _ hC hok x y _ _ hmem u t hu ht hxu hyt hut hprod hJ => by
      simp only [splitCellOK, decide_eq_true_eq] at hok
      refine kernel_pos_of_split hΛ hT hd₁ hd₂ hC hok.1 hok.2.1 hok.2.2 hu ht hut hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hprod hJ)

/-- **Positivity for `u, t ≥ 1` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁`; its corner `x, y ≥ c` lies inside `u, t ≤ c₀`. -/
theorem kernel_pos_of_cover_ge_one {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : SplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 2 0 = Q₁) (hQ₂ : T₂.quots 2 0 = Q₂) {k n : ℕ} {c x₁ : ℚ}
    {cov : Cover}
    (hcov : cov.check (cellOKb k n) (splitCellOK Bx Q₁ Q₂) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {u t : ℝ}
    (hu : 1 ≤ u) (ht : 1 ≤ t) (hut : u ≠ t) (hout : c₀ < u ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hx₁0 : (0 : ℝ) < x₁ := by
    by_contra hcon
    have := mul_nonpos_of_nonneg_of_nonpos hπ.le (not_lt.mp hcon)
    linarith
  have hprod : 1 < u * t := by
    rcases lt_or_gt_of_ne hut with h | h
    · nlinarith
    · nlinarith
  have hrec : ∀ v : ℝ, 1 ≤ v → (0 : ℝ) ≤ 1 / (π * v) ∧ 1 / (π * v) ≤ x₁ := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos hπ hx₁0).le]
  have hr : (⟨0, x₁, 0, x₁⟩ : Rect).Mem (1 / (π * u)) (1 / (π * t)) := by
    refine ⟨?_, (hrec u hu).2, ?_, (hrec t ht).2⟩
    · simpa using (hrec u hu).1
    · simpa using (hrec t ht).1
  have hcorner : ∀ v : ℝ, 0 < v → (c : ℝ) ≤ 1 / (π * v) → v ≤ c₀ := by
    intro v hv hcv
    rw [le_div_iff₀ (by positivity)] at hcv
    have hπc : 0 < π * c := mul_pos hπ hc
    have h1 : π * c * v ≤ π * c * c₀ := by nlinarith
    exact le_of_mul_le_mul_left h1 hπc
  rcases kernel_pos_of_cover hΛ hT hd₁ hd₂ hQ₁ hQ₂ hcov hu0 ht0 hr hut hprod hJ with h | h
  · rcases hout with h' | h'
    · exact absurd (hcorner u hu0 h.1) (not_le.mpr h')
    · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
  · exact h

end E8Leech.Kron
