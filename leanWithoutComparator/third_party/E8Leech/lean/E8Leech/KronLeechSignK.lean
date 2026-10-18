import E8Leech.KronLeechSign
import E8Leech.KronKernelSignK

/-!
# The sign of the kernel `𝒦⁽²⁴⁾` from models of its split numerator

By `ckmrvLeechHatKernel_imagPt` the hat kernel at `iq` is `−q⁻¹² 𝒦(i/q, ·)`, so the inequality
(6.4)(1) for `q ≤ 1 ≤ t` is `𝒦(iu, it) < 0` for `u, t ≥ 1`. On the axes
`3456 Δ(it) 𝒩 · 𝒦 = axLeechPhiK`, and in the split form of `KronLeechExpr` the numerator is

`b · leechEtilE − t̂ · leechE12SE`,  `leechE12SE = leechPlusE − leechMinusE`.

The `a`-version of `leechE12SE` is `648 Λ K (t̂ − û)` with `K = (256Δ)² · E₄² · 2E₆ ≥ 0`, so the
divided numerator is `t̂ (D₁ + w D₂ + 648 Λ K q)`, `q = (t̂ − û)/(b − a) > 0`, exactly as for
`d = 8` (`KronKernelSignK`), with the pivots `a⁴b`, `a⁵` and the vertex check of `KronVertex`.

* `axLeechPhiK`, `ckmrvLeechKernel_axis`: the kernel on the axes.
* `axE2412S_eq_axLeechPhiK`, `leech_splitK_eval_axis`: the numerator in reciprocal variables.
* `Cell.pos_of_vertices_add`: the vertex sign lemma with a constant term.
* `leechKernelK_neg_of_split`: negativity of `𝒦` on a cell that passes the check.
* `leechKernelK_neg_of_cover`, `leechKernel_pos_of_coverK`: the same on a checked cover, and the
  positivity of the hat kernel for `q ≤ 1 ≤ t` outside a corner box.
-/

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

/-- `Φ₂₄ᴷ = 3456 · Δ(z) 𝒩 · 𝒦⁽²⁴⁾` on the axes. -/
noncomputable def axLeechPhiK (E2a Va Wa La LSa u E2b Vb Wb Lb t : ℝ) : ℝ :=
  π ^ 2 / 36 * axLeechPlusNum E2a Va Wa u E2b Vb Wb t +
    axLeechMinusNum Va Wa La LSa Vb Wb Lb / (2 * π)

/-- **`𝒦⁽²⁴⁾(iu, it)` as an explicit real expression**, off the singular curves. -/
theorem ckmrvLeechKernel_axis {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hreg : kleinModularJ (imagPt u) - kleinModularJ (imagPt t) ≠ 0) :
    ckmrvLeechKernel (imagPt u) (imagPt t) =
      ((axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
        t / (3456 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
  have hden := leechDenominator_axis hu ht
  have hp := ckmrvLeechPlusKernel_mul_den (imagPt u) (imagPt t) hreg
  have hm := ckmrvLeechMinusKernel_mul_den (imagPt u) (imagPt t) hreg
  rw [leechPlusContraction_axis hu ht, hden] at hp
  rw [leechMinusContraction_axis hu ht, hden] at hm
  have hd0 : ((axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t) : ℝ) : ℂ) ≠ 0 := by
    rw [← hden]
    exact mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _))) hreg
  have hd0' : axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t) ≠ 0 := by
    exact_mod_cast hd0
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hD : (axDelta (axV t) (axW t) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hd0').1
  have hN : (axNu (axV u) (axW u) (axV t) (axW t) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hd0').2
  have hpl : ckmrvLeechPlusKernel (imagPt u) (imagPt t) =
      ((π ^ 2 * axLeechPlusNum (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t /
        (1728 * 36 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
    have hsc : (1728 * ckmrvPlusScale)⁻¹ * I = (π : ℂ) ^ 2 / (1728 * 36) := by
      rw [ckmrvPlusScale, zpow_neg, zpow_two]
      field_simp
    rw [← mul_assoc, hsc] at hp
    apply mul_left_cancel₀ hd0
    rw [hp]
    push_cast
    field_simp
  have hmi : ckmrvLeechMinusKernel (imagPt u) (imagPt t) =
      ((axLeechMinusNum (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t) /
        (2 * 1728 * π * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hd0
    rw [hm, ckmrvMinusScale]
    push_cast
    field_simp
  rw [ckmrvLeechKernel, hpl, hmi, axLeechPhiK]
  push_cast
  field_simp
  ring

namespace Kron

open E8Leech.Taylor

/-! ## The identities -/

/-- **The numerator of `𝒦⁽²⁴⁾` in reciprocal variables**:
`axE240 − t̂ · axE2412S = 24576 · Λ π û t̂² Φ₂₄ᴷ`. -/
theorem axE2412S_eq_axLeechPhiK (Λ E2a Va Wa L0a LSa uh E2b Vb Wb L0b th : ℝ) (hu : uh ≠ 0)
    (ht : th ≠ 0) :
    axE240 Λ E2a Va Wa uh E2b Vb Wb -
        th * axE2412S Λ E2a Va Wa (Λ * L0a) (Λ * LSa) uh E2b Vb Wb (Λ * L0b) th =
      24576 * Λ * π * uh * th ^ 2 *
        axLeechPhiK E2a Va Wa (L0a - π * (1 / (π * uh))) LSa (1 / (π * uh)) E2b Vb Wb
          (L0b - π * (1 / (π * th))) (1 / (π * th)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axE240, axE2412S, axLPlus0, axLPlus12, axLMinus12, axLA1, axLA2, axLA3, axLA4,
    axLA5, axLA6, axLZ10, axLZ20, axLZ30, axLZ11, axLZ21, axLZ31, axLZ41, axLZ51, axLZ61, axT1h,
    axT2h, axPsi2h, axPsi4h, axLeechPhiK, axLeechPlusNum, axLeechMinusNum, axNu, axPsiTwo,
    axPsiFour, axE6_eq_axF6, axDelta_eq_axD256]
  generalize axE4 Va Wa = e4a
  generalize axF6 Va Wa = f6a
  generalize axD256 Va Wa = da
  generalize axE4 Vb Wb = e4b
  generalize axF6 Vb Wb = f6b
  generalize axD256 Vb Wb = db
  field_simp
  ring

/-- `(256Δ)² · E₄² · 2E₆` on the `τ`-side: the factor of the diagonal value of `leechE12SE`. -/
def leechKE : IExpr := d256E vT wT ^ 2 * e4E vT wT ^ 2 * f6E vT wT

section Eval

variable (Λ : ℕ)

theorem leechKE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) leechKE e =
      axD256 (nomeV e.a) (nomeW e.a) ^ 2 * axE4 (nomeV e.a) (nomeW e.a) ^ 2 *
        axF6 (nomeV e.a) (nomeW e.a) := by
  rw [leechKE, IExpr.evalA_mul, IExpr.evalA_mul, IExpr.evalA_pow, IExpr.evalA_pow, evalA_d256E,
    evalA_e4E, evalA_f6E, evalA_vT, evalA_wT]

theorem leechNetilE_evalA (e : NEnv) (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (leechNetilE Λ) e = 0 := by
  rw [leechNetilE, IExpr.evalA_neg, leechEtilE_evalA Λ ha0 ha1, neg_zero]

theorem leechNetilE_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechNetilE Λ) e =
      -IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) e := by
  rw [leechNetilE, IExpr.evalB_neg]

end Eval

/-- **The split numerator of `𝒦⁽²⁴⁾` on the axes**: `b · leechEtilE − t̂ · leechE12SE` is a
positive multiple of `Φ₂₄ᴷ`. -/
theorem leech_splitK_eval_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    (axisNEnv u t).b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) (axisNEnv u t) -
        (axisNEnv u t).t *
          IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechE12SE Λ) (axisNEnv u t) =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
          t := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hπ0 := Real.pi_pos
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : (1 : ℝ) / (π * t) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ ht.ne')
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr : (1 : ℝ) / (π * (1 / (π * t))) = t := by field_simp
  have hb0 : 0 ≤ (axisNEnv u t).b := (Real.exp_pos _).le
  have hb1 : (axisNEnv u t).b < 1 := by
    have hneg : -π * t < 0 := by nlinarith [mul_pos hπ0 ht]
    exact Real.exp_lt_one_iff.mpr hneg
  rw [leechEtilE_evalB Λ hb0 hb1, leechE12SE_evalB]
  simp only [axisNEnv]
  rw [axE2412S_eq_axLeechPhiK _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_eq_nome hu,
    axE2_eq_nome ht, axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht,
    axL_eq_nome hu, axL_eq_nome ht, axLS_eq_nome hu]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-! ## The vertex sign lemma with a constant term -/

namespace Cell

open IPoly

/-- **The sign from the vertex margins, with a constant term.** As `Cell.pos_of_vertices`, with
the third argument `γ` of the pivot check. -/
theorem pos_of_vertices_add {C : Cell} (hC : C.Valid) {Q : Quots} (hPB : Q.PB.MultiAffine)
    (hPA : Q.PA.MultiAffine) {γB γA γ : ℚ}
    (hOK : ∀ p q r : Bool, C.PosOK (Q.marginBv C p q r + γB) (Q.marginAv C p q r + γA) γ)
    {e : NEnv} (he : C.Mem e) (ha : 0 < e.a) (hb : 0 < e.b) :
    0 < e.b * (eval Q.PB e - (evalUB C.hi Q.RB : ℝ) + γB) +
      e.a * (eval Q.PA e - (evalUB C.hi Q.RA : ℝ) + γA) + γ := by
  have he' := he
  have hC' := hC
  obtain ⟨-, -, lu, lt, ll, hhi⟩ := he
  obtain ⟨-, -, -, -, -, hu', -, ht', -, hl'⟩ := hhi
  obtain ⟨⟨-, -, du, dt, dl⟩, ⟨-, -, eu, et, el⟩⟩ := hC
  have hdu : (0 : ℝ) < C.lo.ud := by exact_mod_cast du
  have hdt : (0 : ℝ) < C.lo.td := by exact_mod_cast dt
  have hdl : (0 : ℝ) < C.lo.ld := by exact_mod_cast dl
  have heu : (0 : ℝ) < C.hi.ud := by exact_mod_cast eu
  have het : (0 : ℝ) < C.hi.td := by exact_mod_cast et
  have hel : (0 : ℝ) < C.hi.ld := by exact_mod_cast el
  set F : ℝ → ℝ → ℝ → ℝ := fun u t l =>
    e.b * eval Q.PB ⟨e.a, e.b, u, t, l⟩ + e.a * eval Q.PA ⟨e.a, e.b, u, t, l⟩ with hF
  have hgoal : e.b * ((evalUB C.hi Q.RB : ℝ) - γB) + e.a * ((evalUB C.hi Q.RA : ℝ) - γA) - γ <
      F e.u e.t e.l := by
    refine lt_of_vertices (F := F)
      (fun t l => (affine_u hPB e.a e.b t l).comb (affine_u hPA e.a e.b t l) e.b e.a)
      (fun u l => (affine_t hPB e.a e.b u l).comb (affine_t hPA e.a e.b u l) e.b e.a)
      (fun u t => (affine_l hPB e.a e.b u t).comb (affine_l hPA e.a e.b u t) e.b e.a)
      (u₀ := ((C.vu false : ℚ) : ℝ)) (u₁ := ((C.vu true : ℚ) : ℝ))
      (t₀ := ((C.vt false : ℚ) : ℝ)) (t₁ := ((C.vt true : ℚ) : ℝ))
      (l₀ := ((C.vl false : ℚ) : ℝ)) (l₁ := ((C.vl true : ℚ) : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [vu, cond_false]
      push_cast
      exact (div_le_iff₀ hdu).mpr lu
    · simp only [vu, cond_true]
      push_cast
      exact (le_div_iff₀ heu).mpr hu'
    · simp only [vt, cond_false]
      push_cast
      exact (div_le_iff₀ hdt).mpr lt
    · simp only [vt, cond_true]
      push_cast
      exact (le_div_iff₀ het).mpr ht'
    · simp only [vl, cond_false]
      push_cast
      exact (div_le_iff₀ hdl).mpr ll
    · simp only [vl, cond_true]
      push_cast
      exact (le_div_iff₀ hel).mpr hl'
    · intro p q r
      have hp : (bif p then ((C.vu true : ℚ) : ℝ) else ((C.vu false : ℚ) : ℝ)) =
          ((C.vu p : ℚ) : ℝ) := by
        cases p <;> rfl
      have hq : (bif q then ((C.vt true : ℚ) : ℝ) else ((C.vt false : ℚ) : ℝ)) =
          ((C.vt q : ℚ) : ℝ) := by
        cases q <;> rfl
      have hr : (bif r then ((C.vl true : ℚ) : ℝ) else ((C.vl false : ℚ) : ℝ)) =
          ((C.vl r : ℚ) : ℝ) := by
        cases r <;> rfl
      rw [hp, hq, hr]
      have hkey := Cell.pos_of_posOK hC' (hOK p q r) he' ha hb
      have lB := evalLBv_le hC' he' (C.vu p) (C.vt q) (C.vl r) Q.PB
      have lA := evalLBv_le hC' he' (C.vu p) (C.vt q) (C.vl r) Q.PA
      simp only [Quots.marginBv, Quots.marginAv] at hkey
      push_cast at hkey
      have kB := mul_le_mul_of_nonneg_left lB hb.le
      have kA := mul_le_mul_of_nonneg_left lA ha.le
      simp only [hF]
      linarith
  have hFe : F e.u e.t e.l = e.b * eval Q.PB e + e.a * eval Q.PA e := rfl
  rw [hFe] at hgoal
  linarith

end Cell

/-! ## The models and the sign on a cell -/

/-- Models of the divided differences of `leechE12SE` and `leechNetilE`, and of the factor
`leechKE`. -/
def LeechSplitModelsK (Bx : Bounds) (Λ : ℕ) (T₁ T₂ TK : MTM) : Prop :=
  T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (leechE12SE Λ)) ∧
    T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (leechNetilE Λ)) ∧
    TK.Approx Bx (fun _ => True) (IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE)

theorem leechSplitModelsK_of_run {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE)
    (hG' : GenOK Bx NE') (D Dcap : ℕ) {Λ n : ℕ} (K N N' : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k₁ k₂ k₃ : ℕ)
    (h₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechE12SE Λ)
    (h₂ : (ISLP.runExpr prog []).getD k₂ (.cst 0) = leechNetilE Λ)
    (h₃ : (ISLP.runExpr prog []).getD k₃ (.cst 0) = leechKE) :
    LeechSplitModelsK Bx Λ
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₁
        MDD.zero).D
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₂
        MDD.zero).D
      ((ISLP.runMDD Bx D Dcap (splitAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k₃
        MDD.zero).A :=
  ⟨(ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₁ _ h₁).2.2,
    (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₂ _ h₂).2.2,
    (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap
      (splitAtoms_ok hG hG' D Dcap K N N' hΛ hL) prog k₃ _ h₃).1⟩

/-- `K = (256Δ)² · E₄² · 2E₆ ≥ 0` at the nome of `iu`, `u ≥ 1`. -/
theorem leechKE_nonneg (Λ : ℕ) {u : ℝ} (hu : 1 ≤ u) (t : ℝ) :
    0 ≤ IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have h6 : 0 ≤ (ModularForm.E₆ (imagPt u)).re := eisensteinSix_imaginary_re_nonneg hu
  rw [E6_imagPt_eq_ax hu0, Complex.ofReal_re] at h6
  have ea : (axisNEnv u t).a = Real.exp (-π * u) := rfl
  have hF : axF6 (axV u) (axW u) = 2 * axE6 (axV u) (axW u) := by
    simp only [axF6, axE6]
    ring
  have hK : IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) =
      axD256 (axV u) (axW u) ^ 2 * axE4 (axV u) (axW u) ^ 2 * axF6 (axV u) (axW u) := by
    rw [leechKE_evalA, ea, axV_eq_nome hu0, axW_eq_nome hu0]
    rfl
  rw [hK, hF]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg (by norm_num) h6)

/-- The common part of the cell argument: if the bracket `D₁ + W D₂ + 648 Λ K q` is positive at
a point of the axes, then `𝒦⁽²⁴⁾ < 0` there. -/
theorem leechKernelK_neg_of_bracket {Λ : ℕ} (hΛ : 0 < Λ) {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) {W : ℝ}
    (hWdef : W * (axisNEnv u t).t = (axisNEnv u t).b)
    (hpos : 0 < splitDD Λ (leechE12SE Λ) (axisNEnv u t) +
      W * splitDD Λ (leechNetilE Λ) (axisNEnv u t) +
      648 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) :
    (ckmrvLeechKernel (imagPt u) (imagPt t)).re < 0 := by
  have hπ := Real.pi_pos
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have ha1 : (axisNEnv u t).a < 1 := by
    have hneg : -π * u < 0 := by nlinarith [mul_pos hπ hu0]
    exact Real.exp_lt_one_iff.mpr hneg
  have hY : 0 < (axisNEnv u t).t := by
    have h : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [h]
    positivity
  have hD₁ : splitDD Λ (leechE12SE Λ) (axisNEnv u t) =
      (IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechE12SE Λ) (axisNEnv u t) -
        648 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) *
          ((axisNEnv u t).t - (axisNEnv u t).u)) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, leechE12SE_evalA, leechKE_evalA]
    ring
  have hD₂ : splitDD Λ (leechNetilE Λ) (axisNEnv u t) =
      -IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, leechNetilE_evalA Λ _ ha ha1, sub_zero, leechNetilE_evalB]
  have hnum : (axisNEnv u t).t * (splitDD Λ (leechE12SE Λ) (axisNEnv u t) +
      W * splitDD Λ (leechNetilE Λ) (axisNEnv u t) +
      648 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) =
      -(((axisNEnv u t).b *
          IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechEtilE Λ) (axisNEnv u t) -
        (axisNEnv u t).t *
          IExpr.evalB (kernelAtoms Λ ++ devAtoms) (leechE12SE Λ) (axisNEnv u t)) /
        ((axisNEnv u t).b - (axisNEnv u t).a)) := by
    rw [hD₁, hD₂, ← hWdef]
    ring
  have h := mul_pos hY hpos
  rw [hnum, leech_splitK_eval_axis Λ hu0 ht] at h
  -- the kernel on the axes
  have hΔ := axDelta_pos ht
  have hden : 0 < axNu (axV u) (axW u) (axV t) (axW t) /
      ((axisNEnv u t).b - (axisNEnv u t).a) := ckmrvAxisDividedDenominator_pos hu0 ht hut hprod
  have hNne : axNu (axV u) (axW u) (axV t) (axW t) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hden
    exact lt_irrefl _ hden
  have haxis : (ckmrvLeechKernel (imagPt u) (imagPt t)).re *
      (3456 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t))) =
      axLeechPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t)
        t := by
    rw [ckmrvLeechKernel_axis hu0 ht (sub_ne_zero.mpr hJ), Complex.ofReal_re]
    exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) (mul_ne_zero hΔ.ne' hNne))
  rw [← haxis] at h
  have hc' : (0 : ℝ) < 24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
      (3456 * axDelta (axV t) (axW t)) := by positivity
  have h5 := mul_pos hc' hden
  have h4 : 24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
      ((ckmrvLeechKernel (imagPt u) (imagPt t)).re *
        (3456 * (axDelta (axV t) (axW t) * axNu (axV u) (axW u) (axV t) (axW t)))) /
        ((axisNEnv u t).b - (axisNEnv u t).a) =
      24576 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 * (3456 * axDelta (axV t) (axW t)) *
        (axNu (axV u) (axW u) (axV t) (axW t) / ((axisNEnv u t).b - (axisNEnv u t).a)) *
          (ckmrvLeechKernel (imagPt u) (imagPt t)).re := by
    ring
  rw [h4] at h
  by_contra hcon
  have := mul_nonneg h5.le (not_lt.mp hcon)
  linarith

/-- **Negativity of `𝒦⁽²⁴⁾` on a cell.** The divided differences enter with their pivot margins
(the first one at the eight vertices); the explicit diagonal term enters with the lower bounds
`κ` of `K/a⁴` and `q₀` of `q`. -/
theorem leechKernelK_neg_of_split {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : LeechSplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hdK : TK.Divisible 3 0) (hPB : (T₁.quots 4 0).PB.MultiAffine)
    (hPA : (T₁.quots 4 0).PA.MultiAffine) {C : Cell} (hC : C.Valid) (hsub : C.hi.le Bx)
    {w q₀ : ℚ} (hw : WOK C w) (hq : QOK C q₀) (hKB : 0 ≤ (TK.quots 3 0).marginB C)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots 4 0).marginBv C p q r + w * min ((T₂.quots 4 0).marginB C) 0)
        ((T₁.quots 4 0).marginAv C p q r + w * min ((T₂.quots 4 0).marginA C) 0)
        (648 * Λ * max ((TK.quots 3 0).marginA C) 0 * q₀))
    {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) :
    (ckmrvLeechKernel (imagPt u) (imagPt t)).re < 0 := by
  have hπ := Real.pi_pos
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  have hY : 0 < (axisNEnv u t).t := by
    have h : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [h]
    positivity
  have hab : (axisNEnv u t).a ≠ (axisNEnv u t).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * t) := h
    exact hut (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  -- the three lower bounds in pivot form
  have l₁ := MTM.lower_of_divisible_eval hT.1 hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible hT.2.1 hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have lK := MTM.lower_of_divisible hT.2.2 hdK hC hsub hmem trivial ha.le hb.le
  have hmem' : C.Mem (recNEnv (1 / (π * u)) (1 / (π * t))) := by
    rw [← axisNEnv_eq_recNEnv]
    exact hmem
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  -- the quotient `W = b / t̂`
  have hwb : (axisNEnv u t).b ≤ (w : ℝ) * (axisNEnv u t).t := by
    have h := hw.le hC hy hmem'
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
  -- the quotient `q`
  have hxy' : 1 / (π * u) ≠ 1 / (π * t) := by
    intro h
    rw [one_div, one_div] at h
    exact hut (mul_left_cancel₀ hπ.ne' (inv_injective h))
  have hq1 := hq.le hC hx hy hxy' hmem'
  have hqe : (q₀ : ℝ) ≤ ((axisNEnv u t).t - (axisNEnv u t).u) /
      ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [axisNEnv_eq_recNEnv]
    exact hq1
  have hq0' : (0 : ℝ) ≤ q₀ := by exact_mod_cast hq.1
  -- the factor `K`
  have hK0 := leechKE_nonneg Λ hu t
  have hKB' : (0 : ℝ) ≤ ((TK.quots 3 0).marginB C : ℝ) := by exact_mod_cast hKB
  have hKκ : (axisNEnv u t).a ^ 4 * (((TK.quots 3 0).marginA C : ℚ) : ℝ) ≤
      IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) := by
    have e : (axisNEnv u t).a ^ 3 * (axisNEnv u t).b ^ 0 *
        ((axisNEnv u t).b * (((TK.quots 3 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((TK.quots 3 0).marginA C : ℚ) : ℝ)) =
        (axisNEnv u t).a ^ 3 * (axisNEnv u t).b * (((TK.quots 3 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a ^ 4 * (((TK.quots 3 0).marginA C : ℚ) : ℝ) := by
      ring
    have hnn := mul_nonneg (mul_nonneg (pow_nonneg ha.le 3) hb.le) hKB'
    rw [e] at lK
    linarith
  have hKmax : (axisNEnv u t).a ^ 4 * max (((TK.quots 3 0).marginA C : ℚ) : ℝ) 0 ≤
      IExpr.evalA (kernelAtoms Λ ++ devAtoms) leechKE (axisNEnv u t) := by
    rcases le_total (((TK.quots 3 0).marginA C : ℚ) : ℝ) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact hK0
    · rw [max_eq_left h]
      exact hKκ
  have hKq := mul_le_mul hKmax hqe hq0' hK0
  have hKq' := mul_le_mul_of_nonneg_left hKq (by positivity : (0 : ℝ) ≤ 648 * Λ)
  -- the weighted margins at the vertices
  have hkey := Cell.pos_of_vertices_add hC hPB hPA hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots 4 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots 4 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ 4 * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hin : 0 < (axisNEnv u t).b * (IPoly.eval (T₁.quots 4 0).PB (axisNEnv u t) -
        (IPoly.evalUB C.hi (T₁.quots 4 0).RB : ℝ)) +
      (axisNEnv u t).a * (IPoly.eval (T₁.quots 4 0).PA (axisNEnv u t) -
        (IPoly.evalUB C.hi (T₁.quots 4 0).RA : ℝ)) +
      W * ((axisNEnv u t).b * (((T₂.quots 4 0).marginB C : ℚ) : ℝ) +
        (axisNEnv u t).a * (((T₂.quots 4 0).marginA C : ℚ) : ℝ)) +
      648 * Λ * max (((TK.quots 3 0).marginA C : ℚ) : ℝ) 0 * q₀ := by
    nlinarith [hkey, kB, kA]
  have hmul := mul_pos hc hin
  refine leechKernelK_neg_of_bracket hΛ hu ht hut hprod hJ hWdef ?_
  nlinarith [hmul, l₁, k2, hKq']

/-! ## Covers -/

/-- The cell test of the split numerator of `𝒦⁽²⁴⁾`, with the vertex check: `w` bounds `b / t̂`
from above and `q₀` bounds `q` from below on the cell. -/
def vertexKCellOK (Bx : Bounds) (Λ : ℕ) (Q₁ Q₂ QK : Quots) (C : Cell) (w q₀ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧ QOK C q₀ ∧ 0 ≤ QK.marginB C ∧ ∀ p q r : Bool,
    C.PosOK (Q₁.marginBv C p q r + w * min (Q₂.marginB C) 0)
      (Q₁.marginAv C p q r + w * min (Q₂.marginA C) 0) (648 * Λ * max (QK.marginA C) 0 * q₀))

/-- **Negativity of `𝒦⁽²⁴⁾` on a cover**, in reciprocal coordinates, outside the corner. -/
theorem leechKernelK_neg_of_cover {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : LeechSplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hdK : TK.Divisible 3 0) {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 4 0 = Q₁)
    (hQ₂ : T₂.quots 4 0 = Q₂) (hQK : TK.quots 3 0 = QK) (hPB : Q₁.PB.MultiAffine)
    (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKb k n) (vertexKCellOK Bx Λ Q₁ Q₂ QK) c r = true)
    {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t)
    (hprod : 1 < u * t) (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      (ckmrvLeechKernel (imagPt u) (imagPt t)).re < 0 := by
  subst hQ₁ hQ₂ hQK
  have hπ := Real.pi_pos
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 1 ≤ u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      1 < u * t → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) →
      (ckmrvLeechKernel (imagPt u) (imagPt t)).re < 0)
    (cellOKb_spec k n)
    (fun C w q₀ hC hok x y _ _ hmem u t hu ht hxu hyt hut hprod hJ => by
      simp only [vertexKCellOK, decide_eq_true_eq] at hok
      refine leechKernelK_neg_of_split hΛ hT hd₁ hd₂ hdK hPB hPA hC hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2.1 hok.2.2.2.2 hu ht hut hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hprod hJ)

/-- The real part of the hat kernel at `iq` is `−q⁻¹²` times that of `𝒦⁽²⁴⁾` at `i/q`. -/
theorem ckmrvLeechHatKernel_imagPt_re {q : ℝ} (hq : 0 < q) (z : UpperHalfPlane) :
    (ckmrvLeechHatKernel (imagPt q) z).re =
      -(q ^ 12)⁻¹ * (ckmrvLeechKernel (imagPt q⁻¹) z).re := by
  rw [ckmrvLeechHatKernel_imagPt hq]
  have hc : -((q : ℂ) ^ 12)⁻¹ = ((-(q ^ 12)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.re_ofReal_mul]

/-- **Positivity for `q ≤ 1 ≤ t` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁` in the variables `1/q` and `t`; its corner `x, y ≥ c` lies
inside `1/q, t ≤ c₀`. -/
theorem leechKernel_pos_of_coverK {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : LeechSplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hdK : TK.Divisible 3 0) {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 4 0 = Q₁)
    (hQ₂ : T₂.quots 4 0 = Q₂) (hQK : TK.quots 3 0 = QK) (hPB : Q₁.PB.MultiAffine)
    (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKb k n) (vertexKCellOK Bx Λ Q₁ Q₂ QK) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1) (ht : 1 ≤ t) (hout : c₀ < q⁻¹ ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hu : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).mpr hq
  have hu0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hJ' : kleinModularJ (imagPt q⁻¹) ≠ kleinModularJ (imagPt t) := by
    rw [← S_smul_imagPt hq0, kleinModularJ_S]
    exact hJ
  have hut : q⁻¹ ≠ t := fun h => hJ' (by rw [h])
  have hx₁0 : (0 : ℝ) < x₁ := by
    by_contra hcon
    have := mul_nonpos_of_nonneg_of_nonpos hπ.le (not_lt.mp hcon)
    linarith
  have hprod : 1 < q⁻¹ * t := by
    rcases lt_or_gt_of_ne hut with h | h
    · nlinarith
    · nlinarith
  have hrec : ∀ v : ℝ, 1 ≤ v → (0 : ℝ) ≤ 1 / (π * v) ∧ 1 / (π * v) ≤ x₁ := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos hπ hx₁0).le]
  have hr : (⟨0, x₁, 0, x₁⟩ : Rect).Mem (1 / (π * q⁻¹)) (1 / (π * t)) := by
    refine ⟨?_, (hrec q⁻¹ hu).2, ?_, (hrec t ht).2⟩
    · simpa using (hrec q⁻¹ hu).1
    · simpa using (hrec t ht).1
  have hcorner : ∀ v : ℝ, 0 < v → (c : ℝ) ≤ 1 / (π * v) → v ≤ c₀ := by
    intro v hv hcv
    rw [le_div_iff₀ (by positivity)] at hcv
    have hπc : 0 < π * c := mul_pos hπ hc
    have h1 : π * c * v ≤ π * c * c₀ := by nlinarith
    exact le_of_mul_le_mul_left h1 hπc
  have hneg : (ckmrvLeechKernel (imagPt q⁻¹) (imagPt t)).re < 0 := by
    rcases leechKernelK_neg_of_cover hΛ hT hd₁ hd₂ hdK hQ₁ hQ₂ hQK hPB hPA hcov hu ht0 hr hut
      hprod hJ' with h | h
    · rcases hout with h' | h'
      · exact absurd (hcorner q⁻¹ hu0 h.1) (not_le.mpr h')
      · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
    · exact h
  rw [ckmrvLeechHatKernel_imagPt_re hq0]
  have hq12 : 0 < (q ^ 12)⁻¹ := by positivity
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hq12) hneg

end Kron

end E8Leech
