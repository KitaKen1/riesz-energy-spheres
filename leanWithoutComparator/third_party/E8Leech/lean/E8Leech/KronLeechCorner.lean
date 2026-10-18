import E8Leech.KronCorner
import E8Leech.KronLeechSign

/-!
# The corner `u = t = 1` for the Leech kernel: concavity in the second variable

As for `d = 8` (`KronCorner`), the numerator `Φ₂₄(u, ·)` vanishes at `t = u` and at `t = 1/u`,
and near the corner no cell bound decides the sign of its divided difference. The function
`G_u(t) = π² t² · axE24` is a positive multiple of `Φ₂₄(u, t)`; if it is strictly concave in `t` on
a box around `1`, it is positive between its two zeros and negative outside, which is the sign of
`𝒩 = Δ(u)Δ(t)(j(u) − j(t))`.

The numerator is the bilinear form `−Σ_{k ≤ 6} A_k(τ) Z_k(z)` of `KronLeechExpr`, so
`G_u'' = −(π⁴t²/144) Σ_k A_k(u) · hOf(Z_k)(t)` by the derivation of `KronDeriv`. The hypothesis
`LeechCornerPos` is the positivity of this bilinear form of twelve functions of one variable on
the box; it is to be certified separately on a grid of intervals.

* `axLeechPlusNum_anti`, `axLeechMinusNum_anti`, `axLeechPhi_anti`: the numerator vanishes at the
  inverted second variable.
* `leechTauE`, `leechZE`, `neg_bil_leech`: the bilinear form.
* `LeechCornerPos`: the certificate. `leechCornerG_strictConcaveOn`: concavity.
* `leechKernel_pos_of_corner`: (6.4)(1) for `d = 24` on the box, off the singular curves.
-/

namespace E8Leech

open scoped Real

/-! ## The numerator at the inverted second variable -/

theorem axE4_swap (V W s : ℝ) : axE4 (s ^ 2 * W) (s ^ 2 * V) = s ^ 4 * axE4 V W := by
  simp only [axE4]
  ring

theorem axE6_swap (V W s : ℝ) : axE6 (s ^ 2 * W) (s ^ 2 * V) = -(s ^ 6 * axE6 V W) := by
  simp only [axE6]
  ring

theorem axDelta_swap (V W s : ℝ) : axDelta (s ^ 2 * W) (s ^ 2 * V) = s ^ 12 * axDelta V W := by
  simp only [axDelta]
  ring

/-- The quasimodular part vanishes at the inverted second variable, for independent `u`. -/
theorem axLeechPlusNum_anti (E2 V W u s : ℝ) :
    axLeechPlusNum E2 V W u (-s ^ 2 * E2 + 6 * s / π) (s ^ 2 * W) (s ^ 2 * V) s⁻¹ = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axLeechPlusNum, axNu, axE4_swap, axE6_swap, axDelta_swap]
  generalize axE4 V W = e4
  generalize axE6 V W = e6
  generalize axDelta V W = dl
  field_simp
  ring

/-- The logarithmic part vanishes at the inverted second variable. -/
theorem axLeechMinusNum_anti (V W La LS s : ℝ) :
    axLeechMinusNum V W La LS (s ^ 2 * W) (s ^ 2 * V) LS = 0 := by
  simp only [axLeechMinusNum, axNu, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  ring

/-- **The numerator vanishes at the inverted second variable**, for independent `u`. -/
theorem axLeechPhi_anti (E2 V W La LS u s : ℝ) :
    axLeechPhi E2 V W La LS u (-s ^ 2 * E2 + 6 * s / π) (s ^ 2 * W) (s ^ 2 * V) LS s⁻¹ = 0 := by
  rw [axLeechPhi, axLeechPlusNum_anti E2 V W u s, axLeechMinusNum_anti]
  ring

namespace Kron

open E8Leech.Taylor
open scoped Topology

/-! ## The numerator as a bilinear form -/

/-- The `τ`-side factors of the Leech numerator. -/
def leechTauPart (Λ : ℕ) (E2a Va Wa lA lSA : IExpr) : List IExpr :=
  [la1E Λ E2a Va Wa, la2E Λ E2a Va Wa, la3E Λ E2a Va Wa, la4E Va Wa, la5E Λ Va Wa lA lSA,
    la6E Λ Va Wa lA lSA]

/-- The `z`-side factors of the Leech numerator. -/
def leechZPart (Λ : ℕ) (E2b Vb Wb lB : IExpr) : List IExpr :=
  [d256E Vb Wb * (e4E Vb Wb - (E2b - 6 * thE) ^ 2),
    9 * d256E Vb Wb * (E2b - 6 * thE) ^ 2 +
      8 * e4E Vb Wb ^ 3 * ((E2b - 6 * thE) ^ 2 - e4E Vb Wb),
    e4E Vb Wb ^ 2 * (7 * e4E Vb Wb * (E2b - 6 * thE) ^ 2 - 5 * e4E Vb Wb ^ 2 -
      f6E Vb Wb * (E2b - 6 * thE)),
    thE * lz41E Λ Vb Wb lB, thE * lz51E Vb Wb, thE * lz61E Vb Wb]

/-- **The Leech numerator is a bilinear form** of the six `τ`-side and the six `z`-side
factors. -/
theorem neg_bil_leech (fs : List (ℝ → ℝ)) (Λ : ℕ) (E2a Va Wa lA lSA E2b Vb Wb lB : IExpr)
    (e : NEnv) :
    -bil ((leechTauPart Λ E2a Va Wa lA lSA).map fun x => IExpr.evalB fs x e)
        ((leechZPart Λ E2b Vb Wb lB).map fun x => IExpr.evalB fs x e) =
      axE24 Λ (IExpr.evalB fs E2a e) (IExpr.evalB fs Va e) (IExpr.evalB fs Wa e)
        (IExpr.evalB fs lA e) (IExpr.evalB fs lSA e) e.u (IExpr.evalB fs E2b e)
        (IExpr.evalB fs Vb e) (IExpr.evalB fs Wb e) (IExpr.evalB fs lB e) e.t := by
  simp only [leechTauPart, leechZPart, la1E, la2E, la3E, la4E, la5E, la6E, lz41E, lz51E, lz61E,
    t1hE, t2hE, psi2E, psi4E, List.map_cons, List.map_nil, bil, axE24, axE240, axE2412, axLPlus0,
    axLPlus12, axLMinus12, axLA1, axLA2, axLA3, axLA4, axLA5, axLA6, axLZ10, axLZ20, axLZ30,
    axLZ11, axLZ21, axLZ31, axLZ41, axLZ51, axLZ61, axT1h, axT2h, axPsi2h, axPsi4h,
    IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat,
    IExpr.evalB_pow, IExpr.evalB_cst, evalB_e4E, evalB_f6E, evalB_d256E, evalB_uhE, evalB_thE]
  push_cast
  ring

/-- The `τ`-side factors of the kernel. -/
def leechTauE (Λ : ℕ) : List IExpr := leechTauPart Λ (.tat 4) vT wT (l0T Λ) lSE

/-- The `z`-side factors of the kernel. -/
def leechZE (Λ : ℕ) : List IExpr := leechZPart Λ (.zat 4) vZ wZ (l0Z Λ)

/-! ## The function `G_u` and its derivatives -/

section Corner

variable (Λ : ℕ)

/-- The values of the `τ`-side factors at `u`. -/
noncomputable def leechTauVals (u : ℝ) : List ℝ :=
  (leechTauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u u)

/-- The values at `t` of the second-derivative expressions of the `z`-side factors. -/
noncomputable def leechZVals (t : ℝ) : List ℝ :=
  (leechZE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv t t)

/-- `π² s² ·` the Leech numerator, as a function of the second variable. -/
noncomputable def leechCornerG (v s : ℝ) : ℝ :=
  -bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val0 Λ v x s)

/-- **The corner certificate**: the bilinear form of the second derivative is positive on the
box `[1/c₀, c₀]²`. -/
def LeechCornerPos (c₀ : ℝ) : Prop :=
  ∀ u t : ℝ, c₀⁻¹ ≤ u → u ≤ c₀ → c₀⁻¹ ≤ t → t ≤ c₀ → 0 < bil (leechTauVals Λ u) (leechZVals Λ t)

variable {Λ}

/-- `G_u` in terms of the integer numerator. -/
theorem leechCornerG_eq (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) (v s : ℝ) :
    leechCornerG Λ v s = π ^ 2 * s ^ 2 *
      axE24 Λ (nomeE2 (axisNEnv v s).a) (nomeV (axisNEnv v s).a) (nomeW (axisNEnv v s).a)
        (Λ * nomeL0 (axisNEnv v s).l (axisNEnv v s).a) (Λ * nomeLS (axisNEnv v s).a)
        (axisNEnv v s).u (nomeE2 (axisNEnv v s).b) (nomeV (axisNEnv v s).b)
        (nomeW (axisNEnv v s).b) (Λ * nomeL0 (axisNEnv v s).l (axisNEnv v s).b)
        (axisNEnv v s).t := by
  have h : -bil ((leechTauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s))
      ((leechZE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s)) =
      axE24 Λ (nomeE2 (axisNEnv v s).a) (nomeV (axisNEnv v s).a) (nomeW (axisNEnv v s).a)
        (Λ * nomeL0 (axisNEnv v s).l (axisNEnv v s).a) (Λ * nomeLS (axisNEnv v s).a)
        (axisNEnv v s).u (nomeE2 (axisNEnv v s).b) (nomeV (axisNEnv v s).b)
        (nomeW (axisNEnv v s).b) (Λ * nomeL0 (axisNEnv v s).l (axisNEnv v s).b)
        (axisNEnv v s).t := by
    have h0 := neg_bil_leech (kernelAtoms Λ ++ []) Λ (.tat 4) vT wT (l0T Λ) lSE (.zat 4) vZ wZ
      (l0Z Λ) (axisNEnv v s)
    rw [evalB_vT, evalB_vZ, evalB_wT, evalB_wZ, evalB_l0T, evalB_l0Z, evalB_lSE, evalB_tat4,
      evalB_zat4] at h0
    exact h0
  have hmap : ((leechTauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s)) =
      leechTauVals Λ v :=
    List.map_congr_left fun x hx =>
      IExpr.evalB_congr_tau _ (hτ x hx) (e := axisNEnv v s) (e' := axisNEnv v v) rfl rfl rfl
  have hlin := bil_map_mul (π ^ 2 * s ^ 2) (leechTauVals Λ v) (leechZE Λ)
    (fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s))
  show -bil (leechTauVals Λ v) ((leechZE Λ).map fun x =>
      π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s)) = _
  rw [hlin, ← h, hmap]
  ring

/-- `G_u` is a positive multiple of `Φ₂₄` on the axes. -/
theorem leechCornerG_eq_phi (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) {v s : ℝ} (hv : 0 < v)
    (hs : 0 < s) :
    leechCornerG Λ v s = π ^ 2 * s ^ 2 * (24576 * Λ * π * (1 / (π * v)) * (1 / (π * s)) ^ 2 *
      axLeechPhi (axE2 v) (axV v) (axW v) (axL v) (axLS v) v (axE2 s) (axV s) (axW s) (axL s)
        s) := by
  rw [leechCornerG_eq hτ, axE24_axis Λ hv hs]

theorem leechCornerG_hasDerivAt (v : ℝ) {s : ℝ} (hs : 0 < s)
    (hxs : Real.exp (-π * s) < 1 / 3) :
    HasDerivAt (leechCornerG Λ v)
      (-bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val1 Λ v x s)) s :=
  (hasDerivAt_bil_val0 Λ v hs hxs (leechTauVals Λ v) (leechZE Λ)).neg

theorem leechCornerG1_hasDerivAt (v : ℝ) {s : ℝ} (hs : 0 < s)
    (hxs : Real.exp (-π * s) < 1 / 3) :
    HasDerivAt (fun s => -bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val1 Λ v x s))
      (-bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val2 Λ v x s)) s :=
  (hasDerivAt_bil_val1 Λ v hs hxs (leechTauVals Λ v) (leechZE Λ)).neg

/-- The second derivative of `G_u` is negative on the box. -/
theorem leechCornerG2_neg (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true) {c₀ : ℝ}
    (H : LeechCornerPos Λ c₀) {v s : ℝ} (hv : c₀⁻¹ ≤ v) (hv' : v ≤ c₀) (hs : c₀⁻¹ ≤ s)
    (hs' : s ≤ c₀) (hs0 : 0 < s) :
    -bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val2 Λ v x s) < 0 := by
  have hmap : ((leechZE Λ).map fun x => val2 Λ v x s) =
      (leechZE Λ).map fun x => π ^ 4 * s ^ 2 / 144 *
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s) :=
    List.map_congr_left fun x hx => by
      show π ^ 4 * s ^ 2 / 144 *
          IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv v s) =
        π ^ 4 * s ^ 2 / 144 * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s)
      rw [IExpr.evalB_congr_z _ (hz x hx) (e := axisNEnv v s) (e' := axisNEnv s s) rfl rfl rfl]
  have hlin := bil_map_mul (π ^ 4 * s ^ 2 / 144) (leechTauVals Λ v) (leechZE Λ)
    (fun x => IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s))
  have hpos : 0 < bil (leechTauVals Λ v) ((leechZE Λ).map fun x =>
      IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s)) := H v s hv hv' hs hs'
  have hc : 0 < π ^ 4 * s ^ 2 / 144 := by positivity
  rw [hmap, hlin]
  have := mul_pos hc hpos
  linarith

/-- **`G_u` is strictly concave on the box.** -/
theorem leechCornerG_strictConcaveOn (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : LeechCornerPos Λ c₀)
    {v : ℝ} (hv : c₀⁻¹ ≤ v) (hv' : v ≤ c₀) :
    StrictConcaveOn ℝ (Set.Icc c₀⁻¹ c₀) (leechCornerG Λ v) := by
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀
  have hd : ∀ s : ℝ, c₀⁻¹ ≤ s → HasDerivAt (leechCornerG Λ v)
      (-bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val1 Λ v x s)) s := fun s hs =>
    leechCornerG_hasDerivAt v (hc0.trans_le hs) (nome_lt_of_ge hx₀ hs)
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt) (fun s hs => ?_)
  rw [interior_Icc] at hs
  have hev : deriv (leechCornerG Λ v) =ᶠ[𝓝 s]
      fun s => -bil (leechTauVals Λ v) ((leechZE Λ).map fun x => val1 Λ v x s) := by
    filter_upwards [Ioi_mem_nhds hs.1] with s' hs'
    exact (hd s' (le_of_lt hs')).deriv
  show deriv (deriv (leechCornerG Λ v)) s < 0
  rw [hev.deriv_eq,
    (leechCornerG1_hasDerivAt v (hc0.trans hs.1) (nome_lt_of_ge hx₀ hs.1.le)).deriv]
  exact leechCornerG2_neg hz H hv hv' hs.1.le hs.2.le (hc0.trans hs.1)

/-- `G_u(u) = 0`. -/
theorem leechCornerG_self (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) (v : ℝ) :
    leechCornerG Λ v v = 0 := by
  rw [leechCornerG_eq hτ]
  have h := axE24_diag (Λ : ℝ) (nomeE2 (axisNEnv v v).a) (nomeV (axisNEnv v v).a)
    (nomeW (axisNEnv v v).a) (Λ * nomeL0 (axisNEnv v v).l (axisNEnv v v).a)
    (Λ * nomeLS (axisNEnv v v).a) (axisNEnv v v).u (axisNEnv v v).t
  have hab : (axisNEnv v v).b = (axisNEnv v v).a := rfl
  rw [hab, h, mul_zero]

/-- `G_u(1/u) = 0`. -/
theorem leechCornerG_inv (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) {v : ℝ} (hv : 0 < v) :
    leechCornerG Λ v v⁻¹ = 0 := by
  rw [leechCornerG_eq_phi hτ hv (inv_pos.mpr hv), axE2_inv hv, axV_inv hv, axW_inv hv,
    axL_inv hv, axLeechPhi_anti]
  ring

/-- `G_u(t)` is continuous in `u`. -/
theorem continuousAt_leechCornerG_left (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ leechZE Λ, x.zOnly = true) (s : ℝ) {v : ℝ} (hv : 0 < v)
    (hxv : Real.exp (-π * v) < 1 / 3) : ContinuousAt (fun w => leechCornerG Λ w s) v := by
  -- the `z`-side list does not depend on `w`
  have hzc : ∀ w : ℝ, ((leechZE Λ).map fun x => val0 Λ w x s) =
      (leechZE Λ).map fun x => val0 Λ 1 x s := fun w =>
    List.map_congr_left fun x hx => by
      show π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w s) =
        π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv 1 s)
      rw [IExpr.evalB_congr_z _ (hz x hx) (e := axisNEnv w s) (e' := axisNEnv 1 s) rfl rfl rfl]
  have hfun : (fun w => leechCornerG Λ w s) =
      fun w => -bil (leechTauVals Λ w) ((leechZE Λ).map fun x => val0 Λ 1 x s) := by
    funext w
    show -bil (leechTauVals Λ w) ((leechZE Λ).map fun x => val0 Λ w x s) = _
    rw [hzc w]
  rw [hfun]
  -- every `τ`-side value is continuous in `w`
  have hcomp : ∀ x ∈ leechTauE Λ, ContinuousAt
      (fun w => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w w)) v := by
    intro x hx
    have h := hasDerivAt_evalB Λ 1 hv hxv (IExpr.swap x)
    have hfun' : (fun w => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w w)) =
        fun w => IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.swap x) (axisNEnv 1 w) := by
      funext w
      have key : IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.swap x) (axisNEnv 1 w) =
          IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w 1) :=
        IExpr.evalB_swap _ x (Real.exp (-π * 1)) (Real.exp (-π * w)) (1 / (π * 1))
          (1 / (π * w)) (Real.log 2)
      rw [key]
      exact IExpr.evalB_congr_tau _ (hτ x hx) (e := axisNEnv w w) (e' := axisNEnv w 1) rfl rfl
        rfl
    rw [hfun']
    exact h.continuousAt
  have hbil : ∀ (xs : List IExpr) (cs : List ℝ), (∀ x ∈ xs, ContinuousAt
      (fun w => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w w)) v) →
      ContinuousAt (fun w => bil (xs.map fun x =>
        IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv w w)) cs) v := by
    intro xs
    induction xs with
    | nil => intro cs _; simpa [bil] using continuousAt_const
    | cons x xs ih =>
      intro cs hc
      cases cs with
      | nil => simpa [bil] using continuousAt_const
      | cons c cs =>
        have h1 := hc x List.mem_cons_self
        have h2 := ih cs fun y hy => hc y (List.mem_cons_of_mem _ hy)
        have h3 := (h1.mul (continuousAt_const (y := c))).add h2
        simp only [List.map_cons, bil]
        exact h3
  exact (hbil (leechTauE Λ) _ hcomp).neg

end Corner

/-! ## The sign of `G_u` on the box -/

section Sign

variable {Λ : ℕ} {c₀ : ℝ}

/-- The sign of `G_u(t)` for `u ≠ 1` on the box: positive strictly between `u` and `1/u`,
negative strictly outside. -/
theorem leechCornerG_sign (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true) (hc₀ : 0 < c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : LeechCornerPos Λ c₀) {v t : ℝ} (hv : c₀⁻¹ ≤ v)
    (hv' : v ≤ c₀) (hv1 : v ≠ 1) (ht : c₀⁻¹ ≤ t) (ht' : t ≤ c₀) :
    (v < t → t < v⁻¹ → 0 < leechCornerG Λ v t) ∧ (v⁻¹ < t → t < v → 0 < leechCornerG Λ v t) ∧
      (t < v → t < v⁻¹ → leechCornerG Λ v t < 0) ∧
      (v < t → v⁻¹ < t → leechCornerG Λ v t < 0) := by
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀
  have hv0 : 0 < v := hc0.trans_le hv
  have hconc := leechCornerG_strictConcaveOn hz hc₀ hx₀ H hv hv'
  have hvI : v ∈ Set.Icc c₀⁻¹ c₀ := ⟨hv, hv'⟩
  have hiI : v⁻¹ ∈ Set.Icc c₀⁻¹ c₀ := by
    refine ⟨inv_anti₀ hv0 hv', ?_⟩
    have h := inv_anti₀ hc0 hv
    rwa [inv_inv] at h
  have htI : t ∈ Set.Icc c₀⁻¹ c₀ := ⟨ht, ht'⟩
  have hne : v ≠ v⁻¹ := by
    intro h
    have h2 := mul_inv_cancel₀ hv0.ne'
    rw [← h] at h2
    have h3 : (v - 1) * (v + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hv1 (by linarith)
    · linarith
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨s1, s2, s3⟩ := sign_of_two_zeros hconc hvI hiI htI h (leechCornerG_self hτ v)
      (leechCornerG_inv hτ hv0)
    exact ⟨fun a b => s1 a b, fun a b => absurd (a.trans b) (not_lt.mpr h.le),
      fun a _ => s2 a, fun _ b => s3 b⟩
  · obtain ⟨s1, s2, s3⟩ := sign_of_two_zeros hconc hiI hvI htI h (leechCornerG_inv hτ hv0)
      (leechCornerG_self hτ v)
    exact ⟨fun a b => absurd (a.trans b) (not_lt.mpr h.le), fun a b => s1 a b,
      fun _ b => s2 b, fun a _ => s3 a⟩

/-- `G_1(t) < 0` for `t ≠ 1` on the box. -/
theorem leechCornerG_one_neg (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true)
    (hz0 : ∀ x ∈ leechZE Λ, x.zOnly = true)
    (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true) (hc₀ : 1 ≤ c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : LeechCornerPos Λ c₀) {t : ℝ} (ht : c₀⁻¹ ≤ t)
    (ht' : t ≤ c₀) (ht1 : t ≠ 1) : leechCornerG Λ 1 t < 0 := by
  have hc₀0 : 0 < c₀ := one_pos.trans_le hc₀
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀0
  have h1lo : c₀⁻¹ ≤ 1 := inv_le_one_of_le hc₀
  have h1I : (1 : ℝ) ∈ Set.Icc c₀⁻¹ c₀ := ⟨h1lo, hc₀⟩
  have hconc := leechCornerG_strictConcaveOn hz hc₀0 hx₀ H h1lo hc₀
  have hG1 : leechCornerG Λ 1 1 = 0 := leechCornerG_self hτ 1
  have hle : ∀ s : ℝ, c₀⁻¹ ≤ s → s ≤ c₀ → leechCornerG Λ 1 s ≤ 0 := by
    intro s hs hs'
    rcases eq_or_ne s 1 with rfl | hs1
    · exact hG1.le
    · have hs0 : 0 < s := hc0.trans_le hs
      have hcont := continuousAt_leechCornerG_left (Λ := Λ) hτ hz0 s one_pos
        (nome_lt_of_ge hx₀ h1lo)
      obtain ⟨b, hb1, hbc, hb⟩ : ∃ b : ℝ, 1 < b ∧ b ≤ c₀ ∧ ∀ v : ℝ, 1 < v → v < b →
          (v < s ∧ v⁻¹ < s) ∨ (s < v ∧ s < v⁻¹) := by
        rcases lt_or_gt_of_ne hs1 with h | h
        · have hb1 : 1 < s⁻¹ := by
            have := lt_inv_of_mul_lt_one hs0 (by rw [mul_one]; exact h)
            exact this
          have hbc : s⁻¹ ≤ c₀ := by
            have h2 := inv_anti₀ hc0 hs
            rwa [inv_inv] at h2
          refine ⟨s⁻¹, hb1, hbc, fun v hv1 hvb => Or.inr ⟨h.trans hv1, ?_⟩⟩
          have hv0 : 0 < v := one_pos.trans hv1
          have h3 : v * s < 1 := by
            have h4 := mul_lt_mul_of_pos_right hvb hs0
            rw [inv_mul_cancel₀ hs0.ne'] at h4
            exact h4
          exact lt_inv_of_mul_lt_one hv0 h3
        · refine ⟨s, h, hs', fun v hv1 hvb => Or.inl ⟨hvb, ?_⟩⟩
          have hv0 : 0 < v := one_pos.trans hv1
          have h3 : v⁻¹ < 1 := inv_lt_of_one_lt_mul hv0 (by rw [mul_one]; exact hv1)
          exact h3.trans h
      have hev : ∀ᶠ v in 𝓝[>] (1 : ℝ), leechCornerG Λ v s ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hb1).filter_mono nhdsWithin_le_nhds]
          with v hv1 hvb
        have hv1' : (1 : ℝ) < v := hv1
        have hsg := leechCornerG_sign hτ hz hc₀0 hx₀ H (h1lo.trans hv1'.le) (hvb.le.trans hbc)
          hv1'.ne' hs hs'
        rcases hb v hv1' hvb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hsg.2.2.2 h1 h2).le
        · exact (hsg.2.2.1 h1 h2).le
      exact le_of_tendsto (Filter.Tendsto.mono_left hcont nhdsWithin_le_nhds) hev
  have htI : t ∈ Set.Icc c₀⁻¹ c₀ := ⟨ht, ht'⟩
  have h := hconc.2 h1I htI (Ne.symm ht1) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  rw [hG1] at h
  have hm := hle (1 / 2 * 1 + 1 / 2 * t) (by linarith) (by linarith)
  linarith

end Sign

/-! ## The kernel on the box -/

/-- **(6.4)(1) for `d = 24` on the corner box.** If the bilinear form of the second derivative
is positive on `[1/c₀, c₀]²`, then the Leech hat kernel is positive there, off the singular
curves. -/
theorem leechKernel_pos_of_corner {Λ : ℕ} (hΛ : 0 < Λ)
    (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) (hz0 : ∀ x ∈ leechZE Λ, x.zOnly = true)
    (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true) {c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : LeechCornerPos Λ c₀) {q t : ℝ} (hq : c₀⁻¹ ≤ q)
    (hq' : q ≤ c₀) (ht : c₀⁻¹ ≤ t) (ht' : t ≤ c₀)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hc₀0 : 0 < c₀ := one_pos.trans_le hc₀
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀0
  have hq0 : 0 < q := hc0.trans_le hq
  have ht0 : 0 < t := hc0.trans_le ht
  have hqt : q ≠ t := fun h => hJ (by rw [h])
  have hJinv : kleinModularJ (imagPt q⁻¹) = kleinModularJ (imagPt q) := by
    rw [← S_smul_imagPt hq0, kleinModularJ_S]
  have hqt' : q⁻¹ ≠ t := fun h => hJ (by rw [← hJinv, h])
  have hprod : q * t ≠ 1 := by
    intro h
    apply hqt'
    have h2 := mul_inv_cancel₀ hq0.ne'
    have h3 : q * (q⁻¹ - t) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hq0.ne'
    · linarith
  -- the numerator and the denominator
  have hΔ := axDelta_pos ht0
  have hNne : axNu (axV q) (axW q) (axV t) (axW t) ≠ 0 := by
    intro h0
    have h1 := leechDenominator_axis hq0 ht0
    rw [h0, mul_zero, Complex.ofReal_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ModularForm.discriminant_ne_zero _ h3
      · exact ModularForm.discriminant_ne_zero _ ((pow_eq_zero_iff two_ne_zero).mp h3)
    · exact hJ (sub_eq_zero.mp h2)
  have haxis : (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re *
      (3456 * (axDelta (axV t) (axW t) * axNu (axV q) (axW q) (axV t) (axW t))) =
      axLeechPhi (axE2 q) (axV q) (axW q) (axL q) (axLS q) q (axE2 t) (axV t) (axW t) (axL t)
        t := by
    rw [ckmrvLeechHatKernel_axis hq0 ht0 (sub_ne_zero.mpr hJ), Complex.ofReal_re]
    exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) (mul_ne_zero hΔ.ne' hNne))
  have hG : leechCornerG Λ q t = π ^ 2 * t ^ 2 *
      (24576 * Λ * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) * (3456 * axDelta (axV t) (axW t)) *
      ((ckmrvLeechHatKernel (imagPt q) (imagPt t)).re * axNu (axV q) (axW q) (axV t) (axW t)) := by
    rw [leechCornerG_eq_phi hτ hq0 ht0, ← haxis]
    ring
  have hκ : 0 < π ^ 2 * t ^ 2 * (24576 * Λ * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) *
      (3456 * axDelta (axV t) (axW t)) := by positivity
  have hN : ∀ D : ℝ, D ≠ 0 → axNu (axV q) (axW q) (axV t) (axW t) =
      axNu (axV q) (axW q) (axV t) (axW t) / D * D := fun D hD => (div_mul_cancel₀ _ hD).symm
  refine pos_of_mul_mul hκ hG ?_
  rcases lt_or_gt_of_ne hqt with hlt | hlt
  · -- `q < t`: the difference of the nomes is negative
    have hD : Real.exp (-π * t) - Real.exp (-π * q) < 0 :=
      sub_neg.mpr (Real.exp_lt_exp.mpr (by nlinarith))
    rcases lt_or_gt_of_ne hprod with hp | hp
    · -- `q t < 1`: between the zeros
      have hden := ckmrvAxisDividedDenominator_neg hq0 ht0 hqt hp
      have hNpos : 0 < axNu (axV q) (axW q) (axV t) (axW t) := by
        rw [hN _ hD.ne]
        exact mul_pos_of_neg_of_neg hden hD
      have htinv : t < q⁻¹ := lt_inv_of_mul_lt_one hq0 hp
      have hq1 : q ≠ 1 := by
        intro h
        rw [h, inv_one] at htinv
        rw [h] at hlt
        linarith
      exact Or.inl ⟨(leechCornerG_sign hτ hz hc₀0 hx₀ H hq hq' hq1 ht ht').1 hlt htinv, hNpos⟩
    · -- `1 < q t`: above both zeros
      have hden := ckmrvAxisDividedDenominator_pos hq0 ht0 hqt hp
      have hNneg : axNu (axV q) (axW q) (axV t) (axW t) < 0 := by
        rw [hN _ hD.ne]
        exact mul_neg_of_pos_of_neg hden hD
      have htinv : q⁻¹ < t := inv_lt_of_one_lt_mul hq0 hp
      refine Or.inr ⟨?_, hNneg⟩
      rcases eq_or_ne q 1 with h1 | h1
      · rw [h1]
        refine leechCornerG_one_neg hτ hz0 hz hc₀ hx₀ H ht ht' ?_
        rw [h1] at hlt
        exact hlt.ne'
      · exact (leechCornerG_sign hτ hz hc₀0 hx₀ H hq hq' h1 ht ht').2.2.2 hlt htinv
  · -- `t < q`: the difference of the nomes is positive
    have hD : 0 < Real.exp (-π * t) - Real.exp (-π * q) :=
      sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith))
    rcases lt_or_gt_of_ne hprod with hp | hp
    · -- `q t < 1`: below both zeros
      have hden := ckmrvAxisDividedDenominator_neg hq0 ht0 hqt hp
      have hNneg : axNu (axV q) (axW q) (axV t) (axW t) < 0 := by
        rw [hN _ hD.ne']
        exact mul_neg_of_neg_of_pos hden hD
      have htinv : t < q⁻¹ := lt_inv_of_mul_lt_one hq0 hp
      refine Or.inr ⟨?_, hNneg⟩
      rcases eq_or_ne q 1 with h1 | h1
      · rw [h1]
        refine leechCornerG_one_neg hτ hz0 hz hc₀ hx₀ H ht ht' ?_
        rw [h1] at hlt
        exact hlt.ne
      · exact (leechCornerG_sign hτ hz hc₀0 hx₀ H hq hq' h1 ht ht').2.2.1 hlt htinv
    · -- `1 < q t`: between the zeros
      have hden := ckmrvAxisDividedDenominator_pos hq0 ht0 hqt hp
      have hNpos : 0 < axNu (axV q) (axW q) (axV t) (axW t) := by
        rw [hN _ hD.ne']
        exact mul_pos hden hD
      have htinv : q⁻¹ < t := inv_lt_of_one_lt_mul hq0 hp
      have hq1 : q ≠ 1 := by
        intro h
        rw [h, inv_one] at htinv
        rw [h] at hlt
        linarith
      exact Or.inl ⟨(leechCornerG_sign hτ hz hc₀0 hx₀ H hq hq' hq1 ht ht').2.1 htinv hlt, hNpos⟩

end Kron

end E8Leech
