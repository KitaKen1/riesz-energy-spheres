import E8Leech.KronKernelS
import E8Leech.KronKernelSignK
import E8Leech.CKMRVAxisInversion

/-!
# The sign of the kernels with the second variable inverted

For `t = 1/s < 1` the numerators of `𝒦̂(iu, i/s)` and of `𝒦(iu, i/s)` are `s¹² b` times the
expressions `rsE` and `−ssE` of `KronKernelS`, with `b` the nome of `is` and with `1/π` in the
fourth slot of the environment. The denominator is `s¹²` times the one at `(u, s)`, which has the
sign of `b − a`. Hence the inequality (6.4)(1) is the positivity of the divided difference of
`rsE` (for `u ≥ 1`) and of `ssE` (for `u ≤ 1`, in the variable `1/u`), and one model of each
divided difference with the pivots `a²b`, `a³` decides it on a cell.

* `rs_eval_axis`, `ss_eval_axis`: the numerators on the axes.
* `SModel`, `sModel_of_run`, `sDD_pos_of_posOK`: the model and the pivot check.
* `kernel_pos_of_rs`, `kernelK_neg_of_ss`: the signs on a cell.
* `kernel_pos_of_coverRS`, `kernel_pos_of_coverSS`: positivity of the hat kernel for
  `t ≤ 1 ≤ u` and for `u, t ≤ 1`, outside a corner box.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-- The environment of `iu` and `i/s`: the nomes of `iu` and `is`, the reciprocal `1/(πu)` and the
constant `1/π`. -/
noncomputable def axisNEnvS (u s : ℝ) : NEnv :=
  ⟨Real.exp (-π * u), Real.exp (-π * s), 1 / (π * u), 1 / π, Real.log 2⟩

theorem axisNEnvS_eq_recNEnvS (u s : ℝ) :
    axisNEnvS u s = recNEnvS (1 / (π * u)) (1 / (π * s)) := by
  simp [axisNEnvS, recNEnvS]

/-! ## The numerators on the axes -/

/-- The logarithm of the inverted second variable in the form required by `rsE_mul_evalB`:
`L(i/s) + π/s = L_S(is) + π/s`. -/
theorem axisNEnvS_lB (Λ : ℕ) {u s : ℝ} (hs : 0 < s) :
    (Λ : ℝ) * (axLS s + π / s) * (s * (axisNEnvS u s).t) - Λ =
      Λ * nomeLS (axisNEnvS u s).b * (s * (axisNEnvS u s).t) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hLS : nomeLS (axisNEnvS u s).b = axLS s := by
    rw [axLS_eq_nome hs]
    rfl
  have h1 : π / s * s = π := div_mul_cancel₀ π hs.ne'
  have hone : π / s * (s * (1 / π)) = 1 := by
    calc π / s * (s * (1 / π)) = π / s * s * (1 / π) := by ring
      _ = π * (1 / π) := by rw [h1]
      _ = 1 := mul_one_div_cancel hπ
  have ht : (axisNEnvS u s).t = 1 / π := rfl
  rw [hLS, ht]
  linear_combination (Λ : ℝ) * hone

/-- The reciprocal variable `t̂ = s/π` of `t = 1/s`. -/
theorem inv_pi_mul (s : ℝ) : (1 : ℝ) / (π * (s * (1 / π))) = s⁻¹ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h1 : π * (s * (1 / π)) = s := by
    calc π * (s * (1 / π)) = s * (π * (1 / π)) := by ring
      _ = s := by rw [mul_one_div_cancel hπ, mul_one]
  rw [h1, one_div]

/-- **The numerator of `𝒦̂` at `(iu, i/s)`**: `s¹² · b · rsE` is a positive multiple of `Φ'`. -/
theorem rs_eval_axis (Λ : ℕ) {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    s ^ 12 * ((axisNEnvS u s).b *
        IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (rsE Λ) (axisNEnvS u s)) =
      1769472 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 *
        axPhi (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 s⁻¹) (axV s⁻¹) (axW s⁻¹)
          (axL s⁻¹) s⁻¹ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hπ0 := Real.pi_pos
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : s * (1 / π) ≠ 0 := mul_ne_zero hs.ne' (one_div_ne_zero hπ)
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr := inv_pi_mul s
  have hb0 : 0 ≤ (axisNEnvS u s).b := (Real.exp_pos _).le
  have hb1 : (axisNEnvS u s).b < 1 := by
    have hneg : -π * s < 0 := by nlinarith [mul_pos hπ0 hs]
    exact Real.exp_lt_one_iff.mpr hneg
  have hlB := axisNEnvS_lB Λ (u := u) hs
  rw [rsE_mul_evalB Λ hb0 hb1 s _ hlB]
  simp only [axisNEnvS]
  rw [axE_eq_axPhi _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_inv hs, axV_inv hs, axW_inv hs,
    axL_inv hs, axE2_eq_nome hu, axE2_eq_nome hs, axV_eq_nome hu, axV_eq_nome hs, axW_eq_nome hu,
    axW_eq_nome hs, axL_eq_nome hu, axLS_eq_nome hu, axLS_eq_nome hs]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-- **The numerator of `𝒦` at `(iu, i/s)`**: `−s¹² · b · ssE` is a positive multiple of `Φ_𝒦`. -/
theorem ss_eval_axis (Λ : ℕ) {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    -(s ^ 12 * ((axisNEnvS u s).b *
        IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) (ssE Λ) (axisNEnvS u s))) =
      1769472 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 *
        axPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 s⁻¹) (axV s⁻¹) (axW s⁻¹)
          (axL s⁻¹) s⁻¹ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hπ0 := Real.pi_pos
  have hu' : (1 : ℝ) / (π * u) ≠ 0 := one_div_ne_zero (mul_ne_zero hπ hu.ne')
  have ht' : s * (1 / π) ≠ 0 := mul_ne_zero hs.ne' (one_div_ne_zero hπ)
  have hur : (1 : ℝ) / (π * (1 / (π * u))) = u := by field_simp
  have htr := inv_pi_mul s
  have hb0 : 0 ≤ (axisNEnvS u s).b := (Real.exp_pos _).le
  have hb1 : (axisNEnvS u s).b < 1 := by
    have hneg : -π * s < 0 := by nlinarith [mul_pos hπ0 hs]
    exact Real.exp_lt_one_iff.mpr hneg
  have hlB := axisNEnvS_lB Λ (u := u) hs
  rw [ssE_mul_evalB Λ hb0 hb1 s _ hlB]
  simp only [axisNEnvS]
  rw [axE12S_eq_axPhiK _ _ _ _ _ _ _ _ _ _ _ _ hu' ht', hur, htr, axE2_inv hs, axV_inv hs,
    axW_inv hs, axL_inv hs, axE2_eq_nome hu, axE2_eq_nome hs, axV_eq_nome hu, axV_eq_nome hs,
    axW_eq_nome hu, axW_eq_nome hs, axL_eq_nome hu, axLS_eq_nome hu, axLS_eq_nome hs]
  simp only [nomeV, nomeW, nomeL0, nomeLS]
  congr 2 <;> ring

/-! ## The model and the pivot check -/

/-- The divided difference of an expression in the twelve atoms. -/
noncomputable def sDD (Λ : ℕ) (x : IExpr) (e : NEnv) : ℝ :=
  (IExpr.evalB (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) x e -
    IExpr.evalA (kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)) x e) / (e.b - e.a)

/-- `T` is a model of the divided difference of `x`. -/
def SModel (Bx : Bounds) (Λ : ℕ) (x : IExpr) (T : MTM) : Prop :=
  T.Approx Bx (fun e => True ∧ e.a ≠ e.b) (sDD Λ x)

/-- The divided-difference part of a register of a checked program run is a model. -/
theorem sModel_of_run {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE) (hG' : GenOK Bx NE')
    {D Dcap N' : ℕ} (hR : RedOK Bx D Dcap N') {Λ n : ℕ} (K N : ℕ)
    (hΛ : ∀ i, i < n + 1 → (i + 1) ∣ Λ) (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr)
    (k : ℕ) (x : IExpr) (h : (ISLP.runExpr prog []).getD k (.cst 0) = x) :
    SModel Bx Λ x
      ((ISLP.runMDD Bx D Dcap (sAtomModels Bx D Dcap Λ n K N NE N' NE') prog []).getD k
        MDD.zero).D :=
  (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap (sAtoms_ok hG hG' hR K N hΛ hL) prog k
    x h).2.2

/-- **The pivot check of one model**: the divided difference is positive on the cell. -/
theorem sDD_pos_of_posOK {Bx : Bounds} {Λ : ℕ} {x : IExpr} {T : MTM} (hT : SModel Bx Λ x T)
    (hd : T.Divisible 2 0) {C : Cell} (hC : C.Valid) (hsub : C.hi.le Bx)
    (hOK : C.PosOK ((T.quots 2 0).marginB C) ((T.quots 2 0).marginA C) 0) {e : NEnv}
    (hmem : C.Mem e) (ha : 0 < e.a) (hb : 0 < e.b) (hab : e.a ≠ e.b) : 0 < sDD Λ x e := by
  have l := MTM.lower_of_divisible hT hd hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have hkey := Cell.pos_of_posOK hC hOK hmem ha hb
  rw [Rat.cast_zero, add_zero] at hkey
  have hc : 0 < e.a ^ 2 * e.b ^ 0 := by positivity
  exact lt_of_lt_of_le (mul_pos hc hkey) l

/-- The sign bookkeeping of the inverted regions: numerator `σ b X = c · 2K · σ N` with positive
`σ, b, c` and with `X/δ, N/δ > 0` gives `K > 0`. -/
theorem sign_of_ratio {b X δ c K N σ : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hc : 0 < c)
    (hX : 0 < X / δ) (hN : 0 < N / δ) (h : σ * (b * X) = c * (2 * K * (σ * N))) : 0 < K := by
  have hbX : b * X = c * (2 * K * N) := by
    have h' : σ * (b * X) = σ * (c * (2 * K * N)) := by
      rw [h]
      ring
    exact mul_left_cancel₀ hσ.ne' h'
  have h1 : b * (X / δ) = c * (2 * K) * (N / δ) := by
    calc b * (X / δ) = b * X / δ := by ring
      _ = c * (2 * K * N) / δ := by rw [hbX]
      _ = c * (2 * K) * (N / δ) := by ring
  have hpos : 0 < b * (X / δ) := mul_pos hb hX
  rw [h1] at hpos
  have h2 : 0 < c * (2 * K) := (mul_pos_iff_of_pos_right hN).mp hpos
  have h3 : 0 < 2 * K := (mul_pos_iff_of_pos_left hc).mp h2
  linarith

theorem sign_of_ratio_neg {b X δ c K N σ : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hc : 0 < c)
    (hX : 0 < X / δ) (hN : 0 < N / δ) (h : -(σ * (b * X)) = c * (2 * K * (σ * N))) : K < 0 := by
  have h' : σ * (b * X) = c * (2 * (-K) * (σ * N)) := by linear_combination (-1 : ℝ) * h
  have := sign_of_ratio hb hσ hc hX hN h'
  linarith

/-- The denominator at `(u, 1/s)` is `s¹²` times the one at `(u, s)`. -/
theorem axNu_inv {u s : ℝ} (hs : 0 < s) :
    axNu (axV u) (axW u) (axV s⁻¹) (axW s⁻¹) =
      s ^ 12 * axNu (axV u) (axW u) (axV s) (axW s) := by
  rw [axV_inv hs, axW_inv hs, axNu_S]

/-! ## The signs on a cell -/

/-- **Positivity of `𝒦̂(iu, i/s)` on a cell.** -/
theorem kernel_pos_of_rs {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (rsE Λ) T) (hd : T.Divisible 2 0) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) (hOK : C.PosOK ((T.quots 2 0).marginB C) ((T.quots 2 0).marginA C) 0)
    {u s : ℝ} (hu : 0 < u) (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hmem : C.Mem (axisNEnvS u s)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt s⁻¹)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnvS u s).a := Real.exp_pos _
  have hb : 0 < (axisNEnvS u s).b := Real.exp_pos _
  have ha1 : (axisNEnvS u s).a < 1 := by
    have hneg : -π * u < 0 := by nlinarith [mul_pos hπ hu]
    exact Real.exp_lt_one_iff.mpr hneg
  have hab : (axisNEnvS u s).a ≠ (axisNEnvS u s).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * s) := h
    exact hus (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  have hDD := sDD_pos_of_posOK hT hd hC hsub hOK hmem ha hb hab
  rw [sDD, rsE_evalA Λ ha ha1, sub_zero] at hDD
  have hden : 0 < axNu (axV u) (axW u) (axV s) (axW s) /
      ((axisNEnvS u s).b - (axisNEnvS u s).a) := ckmrvAxisDividedDenominator_pos hu hs hus hprod
  have haxis := ckmrvEightHatKernel_axis hu (inv_pos.mpr hs) hJ
  rw [axNu_inv hs] at haxis
  have h := rs_eval_axis Λ hu hs
  rw [← haxis] at h
  have hc : (0 : ℝ) < 1769472 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 := by positivity
  exact sign_of_ratio hb (pow_pos hs 12) hc hDD hden h

/-- **Negativity of `𝒦(iu, i/s)` on a cell.** -/
theorem kernelK_neg_of_ss {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (ssE Λ) T) (hd : T.Divisible 2 0) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) (hOK : C.PosOK ((T.quots 2 0).marginB C) ((T.quots 2 0).marginA C) 0)
    {u s : ℝ} (hu : 0 < u) (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hmem : C.Mem (axisNEnvS u s)) :
    (ckmrvEightKernel (imagPt u) (imagPt s⁻¹)).re < 0 := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have ha : 0 < (axisNEnvS u s).a := Real.exp_pos _
  have hb : 0 < (axisNEnvS u s).b := Real.exp_pos _
  have ha1 : (axisNEnvS u s).a < 1 := by
    have hneg : -π * u < 0 := by nlinarith [mul_pos hπ hu]
    exact Real.exp_lt_one_iff.mpr hneg
  have hab : (axisNEnvS u s).a ≠ (axisNEnvS u s).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * s) := h
    exact hus (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  have hDD := sDD_pos_of_posOK hT hd hC hsub hOK hmem ha hb hab
  rw [sDD, ssE_evalA Λ ha ha1, sub_zero] at hDD
  have hden : 0 < axNu (axV u) (axW u) (axV s) (axW s) /
      ((axisNEnvS u s).b - (axisNEnvS u s).a) := ckmrvAxisDividedDenominator_pos hu hs hus hprod
  have haxis := ckmrvEightKernel_axis hu (inv_pos.mpr hs) hJ
  rw [axNu_inv hs] at haxis
  have h := ss_eval_axis Λ hu hs
  rw [← haxis] at h
  have hc : (0 : ℝ) < 1769472 * Λ * π * (1 / (π * u)) * (s * (1 / π)) ^ 2 := by positivity
  exact sign_of_ratio_neg hb (pow_pos hs 12) hc hDD hden h

/-! ## Covers -/

/-- The cell test of a reduced numerator; the auxiliary numbers of a leaf are not used. -/
def sCellOK (Bx : Bounds) (Q : Quots) (C : Cell) (_ _ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ C.PosOK (Q.marginB C) (Q.marginA C) 0)

/-- The reciprocal of a parameter `v ≥ 1` lies in `[0, x₁]` if `1/π ≤ x₁`. -/
theorem rec_mem_of_one_le {x₁ : ℚ} (hx₁ : (1 : ℝ) ≤ π * x₁) {v : ℝ} (hv : 1 ≤ v) :
    ((0 : ℚ) : ℝ) ≤ 1 / (π * v) ∧ 1 / (π * v) ≤ x₁ := by
  have hπ := Real.pi_pos
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hx₁0 : (0 : ℝ) < x₁ := by
    by_contra hcon
    have := mul_nonpos_of_nonneg_of_nonpos hπ.le (not_lt.mp hcon)
    linarith
  constructor
  · rw [Rat.cast_zero]
    positivity
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos hπ hx₁0).le]

/-- A reciprocal at least `c` belongs to a parameter at most `c₀`. -/
theorem le_of_rec_ge {c c₀ : ℝ} (hc : 0 < c) (hc₀ : 1 ≤ π * c * c₀) {v : ℝ} (hv : 0 < v)
    (hcv : c ≤ 1 / (π * v)) : v ≤ c₀ := by
  have hπ := Real.pi_pos
  rw [le_div_iff₀ (by positivity)] at hcv
  have hπc : 0 < π * c := mul_pos hπ hc
  have h1 : π * c * v ≤ π * c * c₀ := by nlinarith
  exact le_of_mul_le_mul_left h1 hπc

/-- **Positivity of `𝒦̂(iu, i/s)` on a cover**, in the reciprocal coordinates of `u` and `s`,
outside the corner. -/
theorem kernel_pos_of_cover_rs {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (rsE Λ) T) (hd : T.Divisible 2 0) {Q : Quots} (hQ : T.quots 2 0 = Q)
    {k n : ℕ} {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKSb k n) (sCellOK Bx Q) c r = true) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hr : r.Mem (1 / (π * u)) (1 / (π * s))) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * s)) ∨
      0 < (ckmrvEightHatKernel (imagPt u) (imagPt s⁻¹)).re := by
  subst hQ
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * s) := by positivity
  have h := Cover.sound (env := recNEnvS)
    (P := fun x y => ∀ u s : ℝ, 0 < u → 0 < s → x = 1 / (π * u) → y = 1 / (π * s) → u ≠ s →
      1 < u * s → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹) →
      0 < (ckmrvEightHatKernel (imagPt u) (imagPt s⁻¹)).re)
    (cellOKSb_spec k n)
    (fun C _ _ hC hok x y _ _ hmem u s hu hs hxu hys hus hprod hJ => by
      simp only [sCellOK, decide_eq_true_eq] at hok
      refine kernel_pos_of_rs hΛ hT hd hC hok.1 hok.2 hu hs hus hprod hJ ?_
      rw [axisNEnvS_eq_recNEnvS, ← hxu, ← hys]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u s hu hs rfl rfl hus hprod hJ)

/-- **Negativity of `𝒦(iu, i/s)` on a cover**, outside the corner. -/
theorem kernelK_neg_of_cover_ss {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (ssE Λ) T) (hd : T.Divisible 2 0) {Q : Quots} (hQ : T.quots 2 0 = Q)
    {k n : ℕ} {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKSb k n) (sCellOK Bx Q) c r = true) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hr : r.Mem (1 / (π * u)) (1 / (π * s))) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * s)) ∨
      (ckmrvEightKernel (imagPt u) (imagPt s⁻¹)).re < 0 := by
  subst hQ
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * s) := by positivity
  have h := Cover.sound (env := recNEnvS)
    (P := fun x y => ∀ u s : ℝ, 0 < u → 0 < s → x = 1 / (π * u) → y = 1 / (π * s) → u ≠ s →
      1 < u * s → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹) →
      (ckmrvEightKernel (imagPt u) (imagPt s⁻¹)).re < 0)
    (cellOKSb_spec k n)
    (fun C _ _ hC hok x y _ _ hmem u s hu hs hxu hys hus hprod hJ => by
      simp only [sCellOK, decide_eq_true_eq] at hok
      refine kernelK_neg_of_ss hΛ hT hd hC hok.1 hok.2 hu hs hus hprod hJ ?_
      rw [axisNEnvS_eq_recNEnvS, ← hxu, ← hys]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u s hu hs rfl rfl hus hprod hJ)

/-- `j(i/t) = j(it)`. -/
theorem kleinModularJ_imagPt_inv {t : ℝ} (ht : 0 < t) :
    kleinModularJ (imagPt t⁻¹) = kleinModularJ (imagPt t) := by
  rw [← S_smul_imagPt ht, kleinModularJ_S]

/-- **Positivity for `t ≤ 1 ≤ q` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁` in the variables `q` and `1/t`; its corner `x, y ≥ c` lies inside
`q, 1/t ≤ c₀`. -/
theorem kernel_pos_of_coverRS {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (rsE Λ) T) (hd : T.Divisible 2 0) {Q : Quots} (hQ : T.quots 2 0 = Q)
    {k n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKSb k n) (sCellOK Bx Q) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq : 1 ≤ q) (ht0 : 0 < t) (ht : t ≤ 1) (hout : c₀ < q ∨ c₀ < t⁻¹)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht
  have hs0 : 0 < t⁻¹ := inv_pos.mpr ht0
  have hus : q ≠ t⁻¹ := fun h => hJ (by rw [h, kleinModularJ_imagPt_inv ht0])
  have hJ' : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t⁻¹⁻¹) := by
    rw [inv_inv]
    exact hJ
  have hprod : 1 < q * t⁻¹ := by
    rcases lt_or_gt_of_ne hus with h | h
    · nlinarith
    · nlinarith
  have hr : (⟨0, x₁, 0, x₁⟩ : Rect).Mem (1 / (π * q)) (1 / (π * t⁻¹)) :=
    ⟨(rec_mem_of_one_le hx₁ hq).1, (rec_mem_of_one_le hx₁ hq).2, (rec_mem_of_one_le hx₁ hs).1,
      (rec_mem_of_one_le hx₁ hs).2⟩
  have key := kernel_pos_of_cover_rs hΛ hT hd hQ hcov hq0 hs0 hr hus hprod hJ'
  rw [inv_inv] at key
  rcases key with h | h
  · rcases hout with h' | h'
    · exact absurd (le_of_rec_ge hc hc₀ hq0 h.1) (not_le.mpr h')
    · exact absurd (le_of_rec_ge hc hc₀ hs0 h.2) (not_le.mpr h')
  · exact h

/-- **Positivity for `q, t ≤ 1` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` in the variables `1/q` and `1/t`. -/
theorem kernel_pos_of_coverSS {Bx : Bounds} {Λ : ℕ} (hΛ : 0 < Λ) {T : MTM}
    (hT : SModel Bx Λ (ssE Λ) T) (hd : T.Divisible 2 0) {Q : Quots} (hQ : T.quots 2 0 = Q)
    {k n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKSb k n) (sCellOK Bx Q) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1) (ht0 : 0 < t) (ht : t ≤ 1) (hout : c₀ < q⁻¹ ∨ c₀ < t⁻¹)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re := by
  have hu : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).mpr hq
  have hu0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht
  have hs0 : 0 < t⁻¹ := inv_pos.mpr ht0
  have hus : q⁻¹ ≠ t⁻¹ := fun h => hJ (by rw [inv_injective h])
  have hJ' : kleinModularJ (imagPt q⁻¹) ≠ kleinModularJ (imagPt t⁻¹⁻¹) := by
    rw [inv_inv, kleinModularJ_imagPt_inv hq0]
    exact hJ
  have hprod : 1 < q⁻¹ * t⁻¹ := by
    rcases lt_or_gt_of_ne hus with h | h
    · nlinarith
    · nlinarith
  have hr : (⟨0, x₁, 0, x₁⟩ : Rect).Mem (1 / (π * q⁻¹)) (1 / (π * t⁻¹)) :=
    ⟨(rec_mem_of_one_le hx₁ hu).1, (rec_mem_of_one_le hx₁ hu).2, (rec_mem_of_one_le hx₁ hs).1,
      (rec_mem_of_one_le hx₁ hs).2⟩
  have key := kernelK_neg_of_cover_ss hΛ hT hd hQ hcov hu0 hs0 hr hus hprod hJ'
  rw [inv_inv] at key
  have hneg : (ckmrvEightKernel (imagPt q⁻¹) (imagPt t)).re < 0 := by
    rcases key with h | h
    · rcases hout with h' | h'
      · exact absurd (le_of_rec_ge hc hc₀ hu0 h.1) (not_le.mpr h')
      · exact absurd (le_of_rec_ge hc hc₀ hs0 h.2) (not_le.mpr h')
    · exact h
  rw [ckmrvEightHatKernel_imagPt_re hq0]
  have hq4 : 0 < (q ^ 4)⁻¹ := by positivity
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hq4) hneg

end E8Leech.Kron
