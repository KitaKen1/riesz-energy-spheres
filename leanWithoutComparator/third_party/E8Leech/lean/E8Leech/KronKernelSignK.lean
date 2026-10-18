import E8Leech.KronKernelSign
import E8Leech.CKMRVAxisKernelK
import E8Leech.EisensteinSixSigns

/-!
# The sign of the kernel `𝒦⁽⁸⁾` from models of its split numerator

By `ckmrvEightHatKernel_imagPt` the hat kernel at `i/u` is `−u⁴ 𝒦(iu, ·)`, so the inequality
(6.4)(1) for `u < 1 < t` is `𝒦(iu, it) < 0` for `u, t > 1`. On the axes
`2 𝒦 𝒩 = axPhiK`, and in the split form of `KronKernelSplit` the numerator is

`b · etilE − t̂ · e12SE`,  `e12SE = plusE − minusE`.

The `a`-version of `e12SE` does not vanish: it is `6912 Λ K (t̂ − û)` with
`K = 256Δ · E₄² · 2E₆ ≥ 0`. Hence the divided numerator is

`t̂ (D₁ + w D₂ + 6912 Λ K q)`,  `q = (t̂ − û)/(b − a) > 0`,

with the divided differences `D₁, D₂` of `e12SE, netilE`. The divided differences are negative
to leading order; the sign comes from the explicit term. A lower bound of `q` on a cell is either
a quotient of the bounds of the cell (off the diagonal) or `û t̂ / max(a, b)`.

Everywhere `q ≥ 1/8`, which settles the cells at `u = t = ∞`.

* `axMinus12_eq`, `axE12S_eq_axPhiK`, `splitK_eval_axis`: the identities.
* `quot_ge`, `QOK`, `QOK.le`: a certified lower bound of `q`.
* `kernelK_neg_of_split`: negativity of `𝒦` on a cell that passes the sign check.
* `kernelK_neg_of_cover`, `kernel_pos_of_coverK`: the same on a checked cover, and the positivity
  of the hat kernel for `u ≤ 1 ≤ t` outside a corner box.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The identities -/

/-- The logarithmic part on the axes, in reciprocal variables. -/
theorem axMinus12_eq (Λ Va Wa L0a LSa uh Vb Wb L0b th : ℝ) (hu : uh ≠ 0) (ht : th ≠ 0) :
    th * axMinus12 Λ Va Wa (Λ * L0a) (Λ * LSa) uh Vb Wb (Λ * L0b) th =
      1769472 * Λ * π * uh * th ^ 2 *
        (axMinusNum Va Wa (L0a - π * (1 / (π * uh))) LSa Vb Wb (L0b - π * (1 / (π * th))) /
          (3456 * π)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axMinus12, axT2, axXb2, axPsi2h, axPsi4h, axF6, axD256, axMinusNum, axPsiTwo,
    axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

/-- **The numerator of `𝒦` in reciprocal variables**:
`axE0 − t̂ · axE12S = 512 · 3456 · Λ π û t̂² Φ_𝒦`. -/
theorem axE12S_eq_axPhiK (Λ E2a Va Wa L0a LSa uh E2b Vb Wb L0b th : ℝ) (hu : uh ≠ 0)
    (ht : th ≠ 0) :
    axE0 Λ E2a Va Wa uh E2b Vb Wb -
        th * axE12S Λ E2a Va Wa (Λ * L0a) (Λ * LSa) uh E2b Vb Wb (Λ * L0b) th =
      1769472 * Λ * π * uh * th ^ 2 *
        axPhiK E2a Va Wa (L0a - π * (1 / (π * uh))) LSa (1 / (π * uh)) E2b Vb Wb
          (L0b - π * (1 / (π * th))) (1 / (π * th)) := by
  have hE := axE_eq_axPhi Λ E2a Va Wa L0a LSa uh E2b Vb Wb L0b th hu ht
  have hS := axE_split Λ E2a Va Wa (Λ * L0a) (Λ * LSa) uh E2b Vb Wb (Λ * L0b) th
  have hM := axMinus12_eq Λ Va Wa L0a LSa uh Vb Wb L0b th hu ht
  simp only [axPhi] at hE
  simp only [axE12] at hS
  simp only [axE12S, axPhiK]
  linear_combination hE - hS + 2 * hM

/-- The diagonal value of the coefficient of `t̂`. -/
theorem axE12S_diag (Λ E2 V W lA lSA uh th : ℝ) :
    axE12S Λ E2 V W lA lSA uh E2 V W lA th =
      6912 * Λ * (axD256 V W * axE4 V W ^ 2 * axF6 V W) * (th - uh) := by
  simp only [axE12S, axPlus12, axMinus12, axT2, axXb2, axPsi2h, axPsi4h, axF6, axD256, axE4]
  ring

section Eval

variable (Λ : ℕ)

theorem e12SE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) (e12SE Λ) e =
      6912 * Λ * (axD256 (nomeV e.a) (nomeW e.a) * axE4 (nomeV e.a) (nomeW e.a) ^ 2 *
        axF6 (nomeV e.a) (nomeW e.a)) * (e.t - e.u) := by
  rw [e12SE, IExpr.evalA_sub, plusE_evalA, minusE_evalA]
  have h := axE12S_diag (Λ : ℝ) (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a)
    (Λ * nomeLS e.a) e.u e.t
  rw [axE12S] at h
  exact h

theorem e12SE_evalB (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (e12SE Λ) e =
      axE12S Λ (nomeE2 e.a) (nomeV e.a) (nomeW e.a) (Λ * nomeL0 e.l e.a) (Λ * nomeLS e.a) e.u
        (nomeE2 e.b) (nomeV e.b) (nomeW e.b) (Λ * nomeL0 e.l e.b) e.t := by
  rw [e12SE, IExpr.evalB_sub, plusE_evalB, minusE_evalB]
  rfl

theorem kE_evalA (ex : List (ℝ → ℝ)) (e : NEnv) :
    IExpr.evalA (kernelAtoms Λ ++ ex) kE e =
      axD256 (nomeV e.a) (nomeW e.a) * axE4 (nomeV e.a) (nomeW e.a) ^ 2 *
        axF6 (nomeV e.a) (nomeW e.a) := by
  rw [kE, IExpr.evalA_mul, IExpr.evalA_mul, IExpr.evalA_pow, evalA_d256E, evalA_e4E, evalA_f6E,
    evalA_vT, evalA_wT]

theorem netilE_evalA (e : NEnv) (ha0 : 0 < e.a) (ha1 : e.a < 1) :
    IExpr.evalA (kernelAtoms Λ ++ devAtoms) (netilE Λ) e = 0 := by
  rw [netilE, IExpr.evalA_neg, etilE_evalA Λ ha0 ha1, neg_zero]

theorem netilE_evalB (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ devAtoms) (netilE Λ) e =
      -IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) e := by
  rw [netilE, IExpr.evalB_neg]

end Eval

/-- **The split numerator of `𝒦` on the axes**: `b · etilE − t̂ · e12SE` is a positive multiple
of `Φ_𝒦`. -/
theorem splitK_eval_axis (Λ : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    (axisNEnv u t).b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) (axisNEnv u t) -
        (axisNEnv u t).t * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (e12SE Λ) (axisNEnv u t) =
      1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        axPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
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
  rw [etilE_evalB Λ hb0 hb1, e12SE_evalB]
  simp only [axisNEnv]
  rw [axE12S_eq_axPhiK _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_eq_nome hu,
    axE2_eq_nome ht, axV_eq_nome hu, axV_eq_nome ht, axW_eq_nome hu, axW_eq_nome ht,
    axL_eq_nome hu, axL_eq_nome ht, axLS_eq_nome hu]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-! ## The quotient `q = (t̂ − û)/(b − a)` -/

/-- `exp (−1/y) − exp (−1/x) ≤ (y − x) exp (−1/y) / (x y)` for `0 < x ≤ y`. -/
theorem exp_neg_inv_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.exp (-y⁻¹) - Real.exp (-x⁻¹) ≤ (y - x) / (x * y) * Real.exp (-y⁻¹) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hs : (y - x) / (x * y) = x⁻¹ - y⁻¹ := by
    field_simp
  have h1 := Real.add_one_le_exp (-(x⁻¹ - y⁻¹))
  have h2 : Real.exp (-x⁻¹) = Real.exp (-y⁻¹) * Real.exp (-(x⁻¹ - y⁻¹)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos := Real.exp_pos (-y⁻¹)
  rw [hs, h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

/-- The bounds of a cell as real inequalities between fractions and the four variables. -/
theorem Cell.Mem.frac {C : Cell} (hC : C.Valid) {e : NEnv} (he : C.Mem e) :
    (((C.lo.an : ℚ) / C.lo.ad : ℚ) : ℝ) ≤ e.a ∧ e.a ≤ (((C.hi.an : ℚ) / C.hi.ad : ℚ) : ℝ) ∧
      (((C.lo.bn : ℚ) / C.lo.bd : ℚ) : ℝ) ≤ e.b ∧ e.b ≤ (((C.hi.bn : ℚ) / C.hi.bd : ℚ) : ℝ) ∧
      (((C.lo.un : ℚ) / C.lo.ud : ℚ) : ℝ) ≤ e.u ∧ e.u ≤ (((C.hi.un : ℚ) / C.hi.ud : ℚ) : ℝ) ∧
      (((C.lo.tn : ℚ) / C.lo.td : ℚ) : ℝ) ≤ e.t ∧ e.t ≤ (((C.hi.tn : ℚ) / C.hi.td : ℚ) : ℝ) := by
  obtain ⟨la, lb, lu, lt, -, hhi⟩ := he
  obtain ⟨-, ha, -, hb, -, hu, -, ht, -⟩ := hhi
  obtain ⟨⟨da, db, du, dt, -⟩, ⟨ea, eb, eu, et, -⟩⟩ := hC
  have hda : (0 : ℝ) < C.lo.ad := by exact_mod_cast da
  have hdb : (0 : ℝ) < C.lo.bd := by exact_mod_cast db
  have hdu : (0 : ℝ) < C.lo.ud := by exact_mod_cast du
  have hdt : (0 : ℝ) < C.lo.td := by exact_mod_cast dt
  have hea : (0 : ℝ) < C.hi.ad := by exact_mod_cast ea
  have heb : (0 : ℝ) < C.hi.bd := by exact_mod_cast eb
  have heu : (0 : ℝ) < C.hi.ud := by exact_mod_cast eu
  have het : (0 : ℝ) < C.hi.td := by exact_mod_cast et
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast
    exact (div_le_iff₀ hda).mpr la
  · push_cast
    exact (le_div_iff₀ hea).mpr ha
  · push_cast
    exact (div_le_iff₀ hdb).mpr lb
  · push_cast
    exact (le_div_iff₀ heb).mpr hb
  · push_cast
    exact (div_le_iff₀ hdu).mpr lu
  · push_cast
    exact (le_div_iff₀ heu).mpr hu
  · push_cast
    exact (div_le_iff₀ hdt).mpr lt
  · push_cast
    exact (le_div_iff₀ het).mpr ht

/-- `q₀` is a lower bound of `q = (y − x)/(exp (−1/y) − exp (−1/x))` on the cell: the universal
bound `1/8`, off the diagonal the bounds of the cell, or `x y / max(a, b)` in general. -/
def QOK (C : Cell) (q₀ : ℚ) : Prop :=
  0 ≤ q₀ ∧
    (q₀ ≤ 1 / 8 ∨
      ((C.hi.un : ℚ) / C.hi.ud < (C.lo.tn : ℚ) / C.lo.td ∧
        q₀ * ((C.hi.bn : ℚ) / C.hi.bd - (C.lo.an : ℚ) / C.lo.ad) ≤
          (C.lo.tn : ℚ) / C.lo.td - (C.hi.un : ℚ) / C.hi.ud) ∨
      ((C.hi.tn : ℚ) / C.hi.td < (C.lo.un : ℚ) / C.lo.ud ∧
        q₀ * ((C.hi.an : ℚ) / C.hi.ad - (C.lo.bn : ℚ) / C.lo.bd) ≤
          (C.lo.un : ℚ) / C.lo.ud - (C.hi.tn : ℚ) / C.hi.td) ∨
      (q₀ * ((C.hi.an : ℚ) / C.hi.ad) ≤ (C.lo.un : ℚ) / C.lo.ud * ((C.lo.tn : ℚ) / C.lo.td) ∧
        q₀ * ((C.hi.bn : ℚ) / C.hi.bd) ≤ (C.lo.un : ℚ) / C.lo.ud * ((C.lo.tn : ℚ) / C.lo.td)))

instance (C : Cell) (q₀ : ℚ) : Decidable (QOK C q₀) := by
  unfold QOK
  infer_instance

theorem exp_neg_inv_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    Real.exp (-x⁻¹) < Real.exp (-y⁻¹) := by
  have hy : 0 < y := hx.trans hxy
  exact Real.exp_lt_exp.mpr (neg_lt_neg ((inv_lt_inv₀ hy hx).mpr hxy))

/-- The quotient `q` is positive and has the general lower bound `x y / max(a, b)`:
`q · exp (−1/x) ≥ x y` and `q · exp (−1/y) ≥ x y`. -/
theorem quot_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < (y - x) / (Real.exp (-y⁻¹) - Real.exp (-x⁻¹)) ∧
      x * y ≤ (y - x) / (Real.exp (-y⁻¹) - Real.exp (-x⁻¹)) * max (Real.exp (-x⁻¹))
        (Real.exp (-y⁻¹)) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have hlt := exp_neg_inv_lt hx h
    have hd : 0 < Real.exp (-y⁻¹) - Real.exp (-x⁻¹) := sub_pos.mpr hlt
    have hle := exp_neg_inv_sub_le hx h.le
    have hxy0 : 0 < x * y := mul_pos hx hy
    refine ⟨div_pos (sub_pos.mpr h) hd, ?_⟩
    rw [max_eq_right hlt.le, div_mul_eq_mul_div, le_div_iff₀ hd]
    have h2 : (y - x) / (x * y) * Real.exp (-y⁻¹) * (x * y) = (y - x) * Real.exp (-y⁻¹) := by
      rw [mul_right_comm, div_mul_cancel₀ _ hxy0.ne']
    have h3 := mul_le_mul_of_nonneg_right hle hxy0.le
    linarith
  · have hlt := exp_neg_inv_lt hy h
    have hd : Real.exp (-y⁻¹) - Real.exp (-x⁻¹) < 0 := sub_neg.mpr hlt
    have hle := exp_neg_inv_sub_le hy h.le
    have hxy0 : 0 < y * x := mul_pos hy hx
    refine ⟨div_pos_of_neg_of_neg (sub_neg.mpr h) hd, ?_⟩
    rw [max_eq_left hlt.le, div_mul_eq_mul_div, le_div_iff_of_neg hd]
    have h2 : (x - y) / (y * x) * Real.exp (-x⁻¹) * (y * x) = (x - y) * Real.exp (-x⁻¹) := by
      rw [mul_right_comm, div_mul_cancel₀ _ hxy0.ne']
    have h3 := mul_le_mul_of_nonneg_right hle hxy0.le
    linarith

/-- `exp (−1/y) ≤ y`. -/
theorem exp_neg_inv_le_self {y : ℝ} (hy : 0 < y) : Real.exp (-y⁻¹) ≤ y := by
  have hpos : 0 < y⁻¹ := inv_pos.mpr hy
  have hexp : y⁻¹ ≤ Real.exp y⁻¹ := by
    have := Real.add_one_le_exp y⁻¹
    linarith
  have h5 := inv_anti₀ hpos hexp
  rw [inv_inv] at h5
  rw [Real.exp_neg]
  exact h5

/-- `exp (−1/y) ≤ 4y²`. -/
theorem exp_neg_inv_le_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y⁻¹) ≤ 4 * y ^ 2 := by
  have hy2 : 0 < 2 * y := by positivity
  have h := exp_neg_inv_le_self hy2
  have hr0 : 0 ≤ Real.exp (-(2 * y)⁻¹) := (Real.exp_pos _).le
  have hsq : Real.exp (-(2 * y)⁻¹) * Real.exp (-(2 * y)⁻¹) = Real.exp (-y⁻¹) := by
    rw [← Real.exp_add]
    congr 1
    rw [mul_inv]
    ring
  have h6 := mul_le_mul h h hr0 hy2.le
  rw [hsq] at h6
  have h7 : 2 * y * (2 * y) = 4 * y ^ 2 := by ring
  rw [h7] at h6
  exact h6

/-- The divided difference of `exp (−1/·)` is at most `8`. -/
theorem exp_neg_inv_sub_le_eight {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    Real.exp (-y⁻¹) - Real.exp (-x⁻¹) ≤ 8 * (y - x) := by
  have hy : 0 < y := hx.trans hxy
  have ha := Real.exp_pos (-x⁻¹)
  rcases le_total (2 * x) y with h | h
  · have h1 := exp_neg_inv_le_self hy
    linarith
  · have hle := exp_neg_inv_sub_le hx hxy.le
    have hxy0 : 0 < x * y := mul_pos hx hy
    have h2 : (y - x) / (x * y) * Real.exp (-y⁻¹) * (x * y) = (y - x) * Real.exp (-y⁻¹) := by
      rw [mul_right_comm, div_mul_cancel₀ _ hxy0.ne']
    have h3 := mul_le_mul_of_nonneg_right hle hxy0.le
    rw [h2] at h3
    have h4 := mul_le_mul_of_nonneg_left (exp_neg_inv_le_sq hy) (sub_nonneg.mpr hxy.le)
    have h5 : (y - x) * (4 * y ^ 2) ≤ 8 * (y - x) * (x * y) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy.le) hy.le) (sub_nonneg.mpr h)]
    exact le_of_mul_le_mul_right (h3.trans (h4.trans h5)) hxy0

/-- The quotient `q` is at least `1/8` everywhere. -/
theorem quot_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    1 / 8 ≤ (y - x) / (Real.exp (-y⁻¹) - Real.exp (-x⁻¹)) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have hd : 0 < Real.exp (-y⁻¹) - Real.exp (-x⁻¹) := sub_pos.mpr (exp_neg_inv_lt hx h)
    rw [le_div_iff₀ hd]
    linarith [exp_neg_inv_sub_le_eight hx h]
  · have hd : Real.exp (-y⁻¹) - Real.exp (-x⁻¹) < 0 := sub_neg.mpr (exp_neg_inv_lt hy h)
    rw [le_div_iff_of_neg hd]
    linarith [exp_neg_inv_sub_le_eight hy h]

theorem QOK.le {C : Cell} {q₀ : ℚ} (hq : QOK C q₀) (hC : C.Valid) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (hxy : x ≠ y) (hmem : C.Mem (recNEnv x y)) :
    (q₀ : ℝ) ≤ (y - x) / (Real.exp (-y⁻¹) - Real.exp (-x⁻¹)) := by
  obtain ⟨hq0, hcase⟩ := hq
  have hq0' : (0 : ℝ) ≤ q₀ := by exact_mod_cast hq0
  obtain ⟨aL, aH, bL, bH, uL, uH, tL, tH⟩ := Cell.Mem.frac hC hmem
  have ea : (recNEnv x y).a = Real.exp (-x⁻¹) := rfl
  have eb : (recNEnv x y).b = Real.exp (-y⁻¹) := rfl
  have eu : (recNEnv x y).u = x := rfl
  have et : (recNEnv x y).t = y := rfl
  rw [ea] at aL aH
  rw [eb] at bL bH
  rw [eu] at uL uH
  rw [et] at tL tH
  obtain ⟨-, hgen⟩ := quot_bounds hx hy hxy
  rcases hcase with h0 | ⟨hlt, hb⟩ | ⟨hlt, hb⟩ | ⟨h1, h2⟩
  · have h0' : (q₀ : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := Rat.cast_le.mpr h0
    have e : ((1 / 8 : ℚ) : ℝ) = 1 / 8 := by norm_num
    rw [e] at h0'
    exact h0'.trans (quot_ge hx hy hxy)
  · have hlt' : (((C.hi.un : ℚ) / C.hi.ud : ℚ) : ℝ) < (((C.lo.tn : ℚ) / C.lo.td : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hlt
    have hb' := (Rat.cast_le (K := ℝ)).mpr hb
    rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_sub] at hb'
    have hxy' : x < y := lt_of_le_of_lt uH (lt_of_lt_of_le hlt' tL)
    have hd : 0 < Real.exp (-y⁻¹) - Real.exp (-x⁻¹) := sub_pos.mpr (exp_neg_inv_lt hx hxy')
    rw [le_div_iff₀ hd]
    have k1 : (q₀ : ℝ) * (Real.exp (-y⁻¹) - Real.exp (-x⁻¹)) ≤
        (q₀ : ℝ) * ((((C.hi.bn : ℚ) / C.hi.bd : ℚ) : ℝ) - (((C.lo.an : ℚ) / C.lo.ad : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0'
    linarith
  · have hlt' : (((C.hi.tn : ℚ) / C.hi.td : ℚ) : ℝ) < (((C.lo.un : ℚ) / C.lo.ud : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hlt
    have hb' := (Rat.cast_le (K := ℝ)).mpr hb
    rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_sub] at hb'
    have hxy' : y < x := lt_of_le_of_lt tH (lt_of_lt_of_le hlt' uL)
    have hd : Real.exp (-y⁻¹) - Real.exp (-x⁻¹) < 0 := sub_neg.mpr (exp_neg_inv_lt hy hxy')
    rw [le_div_iff_of_neg hd]
    have k1 : (q₀ : ℝ) * (Real.exp (-x⁻¹) - Real.exp (-y⁻¹)) ≤
        (q₀ : ℝ) * ((((C.hi.an : ℚ) / C.hi.ad : ℚ) : ℝ) - (((C.lo.bn : ℚ) / C.lo.bd : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0'
    linarith
  · have h1' := (Rat.cast_le (K := ℝ)).mpr h1
    have h2' := (Rat.cast_le (K := ℝ)).mpr h2
    rw [Rat.cast_mul, Rat.cast_mul] at h1' h2'
    have huL0 : (0 : ℝ) ≤ (((C.lo.un : ℚ) / C.lo.ud : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
      positivity
    have htL0 : (0 : ℝ) ≤ (((C.lo.tn : ℚ) / C.lo.td : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
      positivity
    have hxyL : (((C.lo.un : ℚ) / C.lo.ud : ℚ) : ℝ) * (((C.lo.tn : ℚ) / C.lo.td : ℚ) : ℝ) ≤
        x * y := mul_le_mul uL tL htL0 hx.le
    have hmax : (q₀ : ℝ) * max (Real.exp (-x⁻¹)) (Real.exp (-y⁻¹)) ≤ x * y := by
      rcases max_cases (Real.exp (-x⁻¹)) (Real.exp (-y⁻¹)) with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm]
        have := mul_le_mul_of_nonneg_left aH hq0'
        linarith
      · rw [hm]
        have := mul_le_mul_of_nonneg_left bH hq0'
        linarith
    have hm0 : 0 < max (Real.exp (-x⁻¹)) (Real.exp (-y⁻¹)) :=
      lt_max_of_lt_left (Real.exp_pos _)
    exact le_of_mul_le_mul_right (hmax.trans hgen) hm0

/-! ## The models and the sign on a cell -/

/-- Models of the divided differences of `e12SE` and `netilE`, and of the factor `K`. -/
def SplitModelsK (Bx : Bounds) (Λ : ℕ) (T₁ T₂ TK : MTM) : Prop :=
  T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (e12SE Λ)) ∧
    T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ (netilE Λ)) ∧
    TK.Approx Bx (fun _ => True) (IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE)

theorem splitModelsK_of_run {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE) (hG' : GenOK Bx NE')
    (D Dcap : ℕ) {Λ n : ℕ} (K N N' : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k₁ k₂ k₃ : ℕ)
    (h₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = e12SE Λ)
    (h₂ : (ISLP.runExpr prog []).getD k₂ (.cst 0) = netilE Λ)
    (h₃ : (ISLP.runExpr prog []).getD k₃ (.cst 0) = kE) :
    SplitModelsK Bx Λ
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

/-- `K = 256Δ · E₄² · 2E₆ ≥ 0` at the nome of `iu`, `u ≥ 1`. -/
theorem kE_nonneg (Λ : ℕ) {u : ℝ} (hu : 1 ≤ u) (t : ℝ) :
    0 ≤ IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have h6 : 0 ≤ (ModularForm.E₆ (imagPt u)).re := eisensteinSix_imaginary_re_nonneg hu
  rw [E6_imagPt_eq_ax hu0, Complex.ofReal_re] at h6
  have ea : (axisNEnv u t).a = Real.exp (-π * u) := rfl
  have hF : axF6 (axV u) (axW u) = 2 * axE6 (axV u) (axW u) := by
    simp only [axF6, axE6]
    ring
  have hD : 0 ≤ axD256 (axV u) (axW u) := by
    simp only [axD256]
    exact sq_nonneg _
  have hK : IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) =
      axD256 (axV u) (axW u) * axE4 (axV u) (axW u) ^ 2 * axF6 (axV u) (axW u) := by
    rw [kE_evalA, ea, axV_eq_nome hu0, axW_eq_nome hu0]
    rfl
  rw [hK, hF]
  exact mul_nonneg (mul_nonneg hD (sq_nonneg _)) (mul_nonneg (by norm_num) h6)

/-- The common part of the two cell arguments: if the bracket
`D₁ + W D₂ + 6912 Λ K q` is positive at a point of the axes, then `𝒦 < 0` there. -/
theorem kernelK_neg_of_bracket {Λ : ℕ} (hΛ : 0 < Λ) {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) {W : ℝ}
    (hWdef : W * (axisNEnv u t).t = (axisNEnv u t).b)
    (hpos : 0 < splitDD Λ (e12SE Λ) (axisNEnv u t) + W * splitDD Λ (netilE Λ) (axisNEnv u t) +
      6912 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) :
    (ckmrvEightKernel (imagPt u) (imagPt t)).re < 0 := by
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
  have hD₁ : splitDD Λ (e12SE Λ) (axisNEnv u t) =
      (IExpr.evalB (kernelAtoms Λ ++ devAtoms) (e12SE Λ) (axisNEnv u t) -
        6912 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) *
          ((axisNEnv u t).t - (axisNEnv u t).u)) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, e12SE_evalA, kE_evalA]
  have hD₂ : splitDD Λ (netilE Λ) (axisNEnv u t) =
      -IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) (axisNEnv u t) /
        ((axisNEnv u t).b - (axisNEnv u t).a) := by
    rw [splitDD, netilE_evalA Λ _ ha ha1, sub_zero, netilE_evalB]
  have hnum : (axisNEnv u t).t * (splitDD Λ (e12SE Λ) (axisNEnv u t) +
      W * splitDD Λ (netilE Λ) (axisNEnv u t) +
      6912 * Λ * IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) =
      -(((axisNEnv u t).b * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (etilE Λ) (axisNEnv u t) -
        (axisNEnv u t).t * IExpr.evalB (kernelAtoms Λ ++ devAtoms) (e12SE Λ) (axisNEnv u t)) /
        ((axisNEnv u t).b - (axisNEnv u t).a)) := by
    rw [hD₁, hD₂, ← hWdef]
    ring
  have h := mul_pos hY hpos
  rw [hnum, splitK_eval_axis Λ hu0 ht, ← ckmrvEightKernel_axis hu0 ht hJ] at h
  have hc' : (0 : ℝ) < 1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 := by positivity
  have hden : 0 < axNu (axV u) (axW u) (axV t) (axW t) /
      ((axisNEnv u t).b - (axisNEnv u t).a) := ckmrvAxisDividedDenominator_pos hu0 ht hut hprod
  have h5 := mul_pos hc' hden
  have h4 : 1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
      (2 * (ckmrvEightKernel (imagPt u) (imagPt t)).re * axNu (axV u) (axW u) (axV t) (axW t)) /
        ((axisNEnv u t).b - (axisNEnv u t).a) =
      1769472 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 *
        (axNu (axV u) (axW u) (axV t) (axW t) / ((axisNEnv u t).b - (axisNEnv u t).a)) *
          (2 * (ckmrvEightKernel (imagPt u) (imagPt t)).re) := by
    ring
  rw [h4] at h
  by_contra hcon
  have hre : 0 ≤ 2 * (ckmrvEightKernel (imagPt u) (imagPt t)).re := by linarith [not_lt.mp hcon]
  have := mul_nonneg h5.le hre
  linarith

/-- **Negativity of `𝒦` on a cell.** The divided differences enter with their pivot margins; the
explicit diagonal term enters with the lower bounds `κ` of `K/a²` and `q₀` of `q`. -/
theorem kernelK_neg_of_split {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : SplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0)
    (hdK : TK.Divisible 1 0) {C : Cell} (hC : C.Valid) (hsub : C.hi.le Bx) {w q₀ : ℚ}
    (hw : WOK C w) (hq : QOK C q₀) (hKB : 0 ≤ (TK.quots 1 0).marginB C)
    (hOK : C.PosOK ((T₁.quots 2 0).marginB C + w * min ((T₂.quots 2 0).marginB C) 0)
      ((T₁.quots 2 0).marginA C + w * min ((T₂.quots 2 0).marginA C) 0)
      (6912 * Λ * max ((TK.quots 1 0).marginA C) 0 * q₀))
    {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) :
    (ckmrvEightKernel (imagPt u) (imagPt t)).re < 0 := by
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
  have l₁ := MTM.lower_of_divisible hT.1 hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
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
  have hK0 := kE_nonneg Λ hu t
  have hKB' : (0 : ℝ) ≤ ((TK.quots 1 0).marginB C : ℝ) := by exact_mod_cast hKB
  have hKκ : (axisNEnv u t).a ^ 2 * (((TK.quots 1 0).marginA C : ℚ) : ℝ) ≤
      IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) := by
    nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) hKB', lK]
  have hKmax : (axisNEnv u t).a ^ 2 * max (((TK.quots 1 0).marginA C : ℚ) : ℝ) 0 ≤
      IExpr.evalA (kernelAtoms Λ ++ devAtoms) kE (axisNEnv u t) := by
    rcases le_total (((TK.quots 1 0).marginA C : ℚ) : ℝ) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact hK0
    · rw [max_eq_left h]
      exact hKκ
  have hKq := mul_le_mul hKmax hqe hq0' hK0
  have hKq' := mul_le_mul_of_nonneg_left hKq (by positivity : (0 : ℝ) ≤ 6912 * Λ)
  -- the weighted margins
  have hkey := Cell.pos_of_posOK hC hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots 2 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots 2 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ 2 * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hin : 0 < (axisNEnv u t).b * (((T₁.quots 2 0).marginB C : ℚ) : ℝ) +
      (axisNEnv u t).a * (((T₁.quots 2 0).marginA C : ℚ) : ℝ) +
      W * ((axisNEnv u t).b * (((T₂.quots 2 0).marginB C : ℚ) : ℝ) +
        (axisNEnv u t).a * (((T₂.quots 2 0).marginA C : ℚ) : ℝ)) +
      6912 * Λ * max (((TK.quots 1 0).marginA C : ℚ) : ℝ) 0 * q₀ := by
    nlinarith [hkey, kB, kA]
  have hmul := mul_pos hc hin
  refine kernelK_neg_of_bracket hΛ hu ht hut hprod hJ hWdef ?_
  nlinarith [hmul, l₁, k2, hKq']

/-! ## Covers -/

/-- The cell test of the split numerator of `𝒦`: `w` bounds `b / t̂` from above and `q₀` bounds
`q` from below on the cell. -/
def splitKCellOK (Bx : Bounds) (Λ : ℕ) (Q₁ Q₂ QK : Quots) (C : Cell) (w q₀ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧ QOK C q₀ ∧ 0 ≤ QK.marginB C ∧
    C.PosOK (Q₁.marginB C + w * min (Q₂.marginB C) 0) (Q₁.marginA C + w * min (Q₂.marginA C) 0)
      (6912 * Λ * max (QK.marginA C) 0 * q₀))

/-- **Negativity of `𝒦` on a cover**, in reciprocal coordinates, outside the corner. -/
theorem kernelK_neg_of_cover {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : SplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0)
    (hdK : TK.Divisible 1 0) {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 2 0 = Q₁)
    (hQ₂ : T₂.quots 2 0 = Q₂) (hQK : TK.quots 1 0 = QK) {k n : ℕ} {c : ℚ} {cov : Cover}
    {r : Rect} (hcov : cov.check (cellOKb k n) (splitKCellOK Bx Λ Q₁ Q₂ QK) c r = true)
    {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t)
    (hprod : 1 < u * t) (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      (ckmrvEightKernel (imagPt u) (imagPt t)).re < 0 := by
  subst hQ₁ hQ₂ hQK
  have hπ := Real.pi_pos
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 1 ≤ u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      1 < u * t → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) →
      (ckmrvEightKernel (imagPt u) (imagPt t)).re < 0)
    (cellOKb_spec k n)
    (fun C w q₀ hC hok x y _ _ hmem u t hu ht hxu hyt hut hprod hJ => by
      simp only [splitKCellOK, decide_eq_true_eq] at hok
      refine kernelK_neg_of_split hΛ hT hd₁ hd₂ hdK hC hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1
        hok.2.2.2.2 hu ht hut hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hprod hJ)

/-- The real part of the hat kernel at `iq` is `−q⁻⁴` times that of `𝒦` at `i/q`. -/
theorem ckmrvEightHatKernel_imagPt_re {q : ℝ} (hq : 0 < q) (z : UpperHalfPlane) :
    (ckmrvEightHatKernel (imagPt q) z).re = -(q ^ 4)⁻¹ * (ckmrvEightKernel (imagPt q⁻¹) z).re := by
  rw [ckmrvEightHatKernel_imagPt hq]
  have hc : -((q : ℂ) ^ 4)⁻¹ = ((-(q ^ 4)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.re_ofReal_mul]

/-- **Positivity for `q ≤ 1 ≤ t` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁` in the variables `1/q` and `t`; its corner `x, y ≥ c` lies
inside `1/q, t ≤ c₀`. -/
theorem kernel_pos_of_coverK {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T₁ T₂ TK : MTM}
    (hT : SplitModelsK Bx Λ T₁ T₂ TK) (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0)
    (hdK : TK.Divisible 1 0) {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 2 0 = Q₁)
    (hQ₂ : T₂.quots 2 0 = Q₂) (hQK : TK.quots 1 0 = QK) {k n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKb k n) (splitKCellOK Bx Λ Q₁ Q₂ QK) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1) (ht : 1 ≤ t) (hout : c₀ < q⁻¹ ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re := by
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
  have hneg : (ckmrvEightKernel (imagPt q⁻¹) (imagPt t)).re < 0 := by
    rcases kernelK_neg_of_cover hΛ hT hd₁ hd₂ hdK hQ₁ hQ₂ hQK hcov hu ht0 hr hut hprod hJ'
      with h | h
    · rcases hout with h' | h'
      · exact absurd (hcorner q⁻¹ hu0 h.1) (not_le.mpr h')
      · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
    · exact h
  rw [ckmrvEightHatKernel_imagPt_re hq0]
  have hq4 : 0 < (q ^ 4)⁻¹ := by positivity
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hq4) hneg

end E8Leech.Kron
