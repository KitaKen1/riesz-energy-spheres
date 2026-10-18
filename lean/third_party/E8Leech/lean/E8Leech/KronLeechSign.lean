import E8Leech.KronLeechExpr
import E8Leech.KronVertex

/-!
# The sign of the Leech hat kernel from models of the split numerator

On the axes the numerator of `𝒦̂⁽²⁴⁾` is `t̂ · leechE12E + b · leechEtilE` (`KronLeechExpr`), and
both expressions vanish in their `a`-versions. As for `d = 8`, models `T₁, T₂` of the divided
differences decide the sign of the kernel on the side `ut > 1`. There are two changes. The kernel
is `O(q_τ²)`, so the divided numerator has the form `a⁴b · Q₁ + a⁵ · Q₂`. And the coefficients of
the nome monomials cancel strongly near the corner `u = t = 1`, so the cells are tested with the
vertex check of `KronVertex`.

* `leechHatKernel_pos_of_phi`: the sign of the kernel from the sign of the divided numerator.
* `LeechSplitModels`, `leechSplitModels_of_run`: the two models.
* `leechKernel_pos_of_dd`, `leechKernel_pos_of_split`: positivity of the kernel on a cell that
  passes the vertex check.
* `leechKernel_pos_of_cover`, `leechKernel_pos_of_cover_ge_one`: the same on a checked cover in
  reciprocal coordinates, and the statement for `u, t ≥ 1` outside a corner box.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The sign of the kernel from the sign of the divided numerator -/

/-- On the side `ut > 1` the kernel `𝒦̂⁽²⁴⁾` has the sign of the divided numerator
`Φ₂₄ / (b − a)`. -/
theorem leechHatKernel_pos_of_phi {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t)
    (hprod : 1 < u * t) (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hΦ : 0 < axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t)
      (axL t) t / (Real.exp (-π * t) - Real.exp (-π * u))) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  have hden := ckmrvAxisDividedDenominator_pos hu ht hut hprod
  have hΔ := axDelta_pos ht
  rw [ckmrvLeechHatKernel_axis hu ht (sub_ne_zero.mpr hJ), Complex.ofReal_re]
  generalize axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t)
    (axL t) t = Φ at hΦ ⊢
  generalize axNu (axV u) (axW u) (axV t) (axW t) = N at hden ⊢
  generalize axDelta (axV t) (axW t) = D at hΔ ⊢
  generalize Real.exp (-π * t) - Real.exp (-π * u) = δ at hΦ hden
  have hδ : δ ≠ 0 := by
    rintro rfl
    simp at hden
  have hN : N ≠ 0 := by
    rintro rfl
    simp at hden
  have e : Φ / (3456 * (D * N)) = Φ / δ / (3456 * (D * (N / δ))) := by
    field_simp
  rw [e]
  exact div_pos hΦ (mul_pos (by norm_num) (mul_pos hΔ hden))

/-! ## The models of the Leech numerator -/

/-- `T₁, T₂` are models of the divided differences of the two parts of the Leech numerator. -/
def LeechSplitModels (Bx : Bounds) (Λ : ℕ) (T₁ T₂ : MTM) : Prop :=
  T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (leechE12E Λ)) ∧
    T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (leechEtilE Λ))

/-- The divided-difference parts of two registers of a checked program run are models. -/
theorem leechSplitModels_of_run {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE)
    (hG' : GenOK Bx NE') (D Dcap : ℕ) {Λ n : ℕ} (K N N' : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k₁ k₂ : ℕ)
    (h₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechE12E Λ)
    (h₂ : (ISLP.runExpr prog []).getD k₂ (.cst 0) = leechEtilE Λ) :
    LeechSplitModels Bx Λ
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₁
        MDD.zero).D
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₂
        MDD.zero).D :=
  ⟨(ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₁ _ h₁).2.2,
    (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₂ _ h₂).2.2⟩

/-! ## Positivity on a cell -/

/-- The kernel is positive where the split divided numerator `t̂ · D₁ + b · D₂` is positive
(`ut > 1`, off the diagonal). -/
theorem leechKernel_pos_of_dd {Λ : ℕ} (hΛ : 0 < Λ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hpos : 0 < (axisNEnv u t).t * splitDD Λ (leechE12E Λ) (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ (leechEtilE Λ) (axisNEnv u t)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have ha1 : (axisNEnv u t).a < 1 := by
    have hneg : -π * u < 0 := by nlinarith [mul_pos hπ hu]
    exact Real.exp_lt_one_iff.mpr hneg
  have hD₁ : splitDD Λ (leechE12E Λ) (axisNEnv u t) =
      IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechE12E Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, leechE12E_evalA, sub_zero]
  have hD₂ : splitDD Λ (leechEtilE Λ) (axisNEnv u t) =
      IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, leechEtilE_evalA Λ ha ha1, sub_zero]
  have hsum : (axisNEnv u t).t * splitDD Λ (leechE12E Λ) (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ (leechEtilE Λ) (axisNEnv u t) =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        (axLeechPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
          t / (Real.exp (-π * t) - Real.exp (-π * u))) := by
    have hδ : (axisNEnv u t).b - (axisNEnv u t).a = Real.exp (-π * t) - Real.exp (-π * u) := rfl
    have e2 : ∀ p q X Z δ : ℝ, p * (X / δ) + q * (Z / δ) = (p * X + q * Z) / δ :=
      fun p q X Z δ => by ring
    rw [hD₁, hD₂, hδ, e2, leech_split_eval_axis Λ hu ht]
    ring
  have hc' : (0 : ℝ) < 24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 := by positivity
  rw [hsum] at hpos
  exact leechHatKernel_pos_of_phi hu ht hut hprod hJ ((mul_pos_iff_of_pos_left hc').mp hpos)

/-- **Positivity on a cell.** A cell inside the bounds of the models that passes the vertex
check (pivots `a⁴b` and `a⁵`) contains no point `(u, t)` with `ut > 1`, `u ≠ t` where the kernel
`𝒦̂⁽²⁴⁾` is not positive. -/
theorem leechKernel_pos_of_split {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : LeechSplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hPB : (T₁.quots 4 0).PB.MultiAffine) (hPA : (T₁.quots 4 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots 4 0).marginBv C p q r + w * min ((T₂.quots 4 0).marginB C) 0)
        ((T₁.quots 4 0).marginAv C p q r + w * min ((T₂.quots 4 0).marginA C) 0) 0)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re :=
  leechKernel_pos_of_dd hΛ hu ht hut hprod hJ
    (splitDD_combination_pos_vertex hT.1 hT.2 hd₁ hd₂ hPB hPA hC hsub hw hOK ht hut hmem)

/-- **Positivity on a cover**, in reciprocal coordinates, outside the corner. The cell test is
`vertexCellOK` with the quotients of the Leech models by the pivots `a⁴b`, `a⁵`. -/
theorem leechKernel_pos_of_cover {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : LeechSplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 4 0 = Q₁) (hQ₂ : T₂.quots 4 0 = Q₂)
    (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c : ℚ}
    {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKb k n) (vertexCellOK Bx Q₁ Q₂) c r = true) {u t : ℝ} (hu : 0 < u)
    (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  subst hQ₁ hQ₂
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 0 < u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      1 < u * t → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) →
      0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re)
    (cellOKb_spec k n)
    (fun C w _ hC hok x y _ _ hmem u t hu ht hxu hyt hut hprod hJ => by
      simp only [vertexCellOK, decide_eq_true_eq] at hok
      refine leechKernel_pos_of_split hΛ hT hd₁ hd₂ hPB hPA hC hok.1 hok.2.1 hok.2.2 hu ht hut
        hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hprod hJ)

/-- **Positivity for `u, t ≥ 1` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁`; its corner `x, y ≥ c` lies inside `u, t ≤ c₀`. -/
theorem leechKernel_pos_of_cover_ge_one {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ : MTM}
    (hT : LeechSplitModels Bx Λ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 4 0 = Q₁) (hQ₂ : T₂.quots 4 0 = Q₂)
    (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c x₁ : ℚ}
    {cov : Cover}
    (hcov : cov.check (cellOKb k n) (vertexCellOK Bx Q₁ Q₂) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {u t : ℝ}
    (hu : 1 ≤ u) (ht : 1 ≤ t) (hut : u ≠ t) (hout : c₀ < u ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
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
  rcases leechKernel_pos_of_cover hΛ hT hd₁ hd₂ hQ₁ hQ₂ hPB hPA hcov hu0 ht0 hr hut hprod hJ with
    h | h
  · rcases hout with h' | h'
    · exact absurd (hcorner u hu0 h.1) (not_le.mpr h')
    · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
  · exact h

end E8Leech.Kron
