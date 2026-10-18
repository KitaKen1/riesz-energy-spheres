import E8Leech.KronJetN

/-!
# Taylor enclosures of expressions in the second variable

For an expression `y` of the second variable the derivation `dz` computes the derivative along the
imaginary axis: `d/dt = −(π/12) ∂`. In the variable `θ = π (c − t)/12` the derivative is `∂`
itself, so Taylor's formula around `t = c` reads

`y(t) = Σ_{p ≤ N} ∂ᵖy(c) θᵖ/p! + w θᴺ⁺¹/(N+1)!`,

with `w` between the bounds of `∂ᴺ⁺¹y` on the interval. With interval jets of order `N` on a thin
cell around the centre and of order `N + 1` on a cell around the interval, every value of `y` on
the interval is a polynomial in `θ` whose coefficients lie in known intervals (`TayMem`), the first
`N + 1` of them narrow. The corner certificate for `d = 24` pairs such rows.

* `taylor_exists`: Taylor's formula with a remainder between the bounds of the next derivative.
* `evalB_taylor`: the formula for expressions.
* `IExpr.zOnly_swap`: the mirror image (`KronCorner`) of a `τ`-side expression is on the `z`-side.
* `QI.sqr`, `QI.npow`, `tpows`: enclosures of `θᵖ/p!`.
* `jetH`, `jMem_jetH`: the jet of `hOf x` from the jet of `x`.
* `TayMem`, `tayRow`, `tayMem_row`: the row of an expression on an interval.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## Taylor's formula with an enclosure of the remainder -/

/-- A function that vanishes at `c` and whose derivative is a nonnegative multiple of
`(σ − c)ᵏ` has the sign of `(s − c)ᵏ⁺¹`. -/
theorem sign_of_deriv_pow {h h' : ℝ → ℝ} {a b c s : ℝ} {k : ℕ}
    (hd : ∀ σ ∈ Set.Icc a b, HasDerivAt h (h' σ) σ)
    (hv : ∀ σ ∈ Set.Icc a b, ∃ v : ℝ, 0 ≤ v ∧ h' σ = v * (σ - c) ^ k)
    (hc : c ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b) (h0 : h c = 0) :
    0 ≤ h s * (s - c) ^ (k + 1) := by
  rcases le_total c s with hcs | hsc
  · -- on `[c, s]` the derivative is nonnegative
    have hsub : Set.Icc c s ⊆ Set.Icc a b := Set.Icc_subset_Icc hc.1 hs.2
    have hmono : MonotoneOn h (Set.Icc c s) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc c s)
        (fun σ hσ => (hd σ (hsub hσ)).continuousAt.continuousWithinAt)
        (fun σ hσ => (hd σ (hsub (interior_subset hσ))).differentiableAt.differentiableWithinAt)
        (fun σ hσ => ?_)
      have hσ' := interior_subset hσ
      rw [(hd σ (hsub hσ')).deriv]
      obtain ⟨v, hv0, hv1⟩ := hv σ (hsub hσ')
      rw [hv1]
      exact mul_nonneg hv0 (pow_nonneg (sub_nonneg.mpr hσ'.1) k)
    have h1 := hmono (Set.left_mem_Icc.mpr hcs) (Set.right_mem_Icc.mpr hcs) hcs
    rw [h0] at h1
    exact mul_nonneg h1 (pow_nonneg (sub_nonneg.mpr hcs) _)
  · have hsub : Set.Icc s c ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 hc.2
    rcases Nat.even_or_odd k with hk | hk
    · -- even `k`: the derivative is nonnegative on `[s, c]`, and `(s − c)ᵏ⁺¹ ≤ 0`
      have hmono : MonotoneOn h (Set.Icc s c) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc s c)
          (fun σ hσ => (hd σ (hsub hσ)).continuousAt.continuousWithinAt)
          (fun σ hσ => (hd σ (hsub (interior_subset hσ))).differentiableAt.differentiableWithinAt)
          (fun σ hσ => ?_)
        have hσ' := interior_subset hσ
        rw [(hd σ (hsub hσ')).deriv]
        obtain ⟨v, hv0, hv1⟩ := hv σ (hsub hσ')
        rw [hv1]
        exact mul_nonneg hv0 (hk.pow_nonneg _)
      have h1 := hmono (Set.left_mem_Icc.mpr hsc) (Set.right_mem_Icc.mpr hsc) hsc
      rw [h0] at h1
      exact mul_nonneg_of_nonpos_of_nonpos h1
        (hk.add_one.pow_nonpos_iff.mpr (sub_nonpos.mpr hsc))
    · -- odd `k`: the derivative is nonpositive on `[s, c]`, and `(s − c)ᵏ⁺¹ ≥ 0`
      have hanti : AntitoneOn h (Set.Icc s c) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc s c)
          (fun σ hσ => (hd σ (hsub hσ)).continuousAt.continuousWithinAt)
          (fun σ hσ => (hd σ (hsub (interior_subset hσ))).differentiableAt.differentiableWithinAt)
          (fun σ hσ => ?_)
        have hσ' := interior_subset hσ
        rw [(hd σ (hsub hσ')).deriv]
        obtain ⟨v, hv0, hv1⟩ := hv σ (hsub hσ')
        rw [hv1]
        exact mul_nonpos_of_nonneg_of_nonpos hv0 (hk.pow_nonpos_iff.mpr (sub_nonpos.mpr hσ'.2))
      have h1 := hanti (Set.left_mem_Icc.mpr hsc) (Set.right_mem_Icc.mpr hsc) hsc
      rw [h0] at h1
      exact mul_nonneg h1 (hk.add_one.pow_nonneg _)

/-- The derivative of `(σ − c)ⁿ⁺¹/(n+1)!`. -/
theorem hasDerivAt_tpow (c : ℝ) (n : ℕ) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => (σ - c) ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((σ - c) ^ n / (n.factorial : ℝ)) σ := by
  have h := (hasDerivAt_pow (n + 1) (σ - c)).comp σ ((hasDerivAt_id' σ).sub_const c)
  have h' : HasDerivAt (fun σ : ℝ => (σ - c) ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * (σ - c) ^ (n + 1 - 1) * 1) σ := h
  refine (h'.div_const _).congr_deriv ?_
  have hn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- **Taylor's formula with an enclosure of the remainder**: if `g (p+1)` is the derivative of
`g p` for `p < n` on an interval and `m ≤ g n ≤ M` there, then
`g 0 s = Σ_{p<n} g p c (s−c)ᵖ/p! + w (s−c)ⁿ/n!` with `m ≤ w ≤ M`. -/
theorem taylor_exists {m M a b : ℝ} : ∀ (n : ℕ) (g : ℕ → ℝ → ℝ),
    (∀ p, p < n → ∀ σ ∈ Set.Icc a b, HasDerivAt (g p) (g (p + 1) σ) σ) →
    (∀ σ ∈ Set.Icc a b, m ≤ g n σ ∧ g n σ ≤ M) →
    ∀ c ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, ∃ w, m ≤ w ∧ w ≤ M ∧
      g 0 s = (∑ p ∈ Finset.range n, g p c * ((s - c) ^ p / (p.factorial : ℝ))) +
        w * ((s - c) ^ n / (n.factorial : ℝ))
  | 0, g, _, hb, c, _, s, hs => ⟨g 0 s, (hb s hs).1, (hb s hs).2, by simp⟩
  | n + 1, g, hd, hb, c, hc, s, hs => by
    -- the expansion of the derivative
    have ih := taylor_exists n (fun p => g (p + 1))
      (fun p hp σ hσ => hd (p + 1) (Nat.succ_lt_succ hp) σ hσ) hb c hc
    -- the Taylor polynomial and its derivative
    let T : ℝ → ℝ := fun σ =>
      ∑ p ∈ Finset.range (n + 1), g p c * ((σ - c) ^ p / (p.factorial : ℝ))
    let T' : ℝ → ℝ := fun σ =>
      ∑ p ∈ Finset.range n, g (p + 1) c * ((σ - c) ^ p / (p.factorial : ℝ))
    have hTd : ∀ σ, HasDerivAt T (T' σ) σ := by
      intro σ
      have e : T = fun σ => (∑ p ∈ Finset.range n,
          g (p + 1) c * ((σ - c) ^ (p + 1) / ((p + 1).factorial : ℝ))) + g 0 c := by
        funext σ
        show ∑ p ∈ Finset.range (n + 1), g p c * ((σ - c) ^ p / (p.factorial : ℝ)) = _
        rw [Finset.sum_range_succ']
        simp
      rw [e]
      exact (HasDerivAt.fun_sum fun p _ => (hasDerivAt_tpow c p σ).const_mul (g (p + 1) c)).add_const
        (g 0 c)
    have hTc : T c = g 0 c := by
      show ∑ p ∈ Finset.range (n + 1), g p c * ((c - c) ^ p / (p.factorial : ℝ)) = _
      rw [Finset.sum_range_succ']
      simp
    have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hfact' : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    -- the two comparison functions
    have hM : 0 ≤ (M * ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - (g 0 s - T s)) *
        (s - c) ^ (n + 1) := by
      refine sign_of_deriv_pow (a := a) (b := b) (c := c) (k := n)
        (h := fun σ => M * ((σ - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - (g 0 σ - T σ))
        (h' := fun σ => M * ((σ - c) ^ n / (n.factorial : ℝ)) - (g 1 σ - T' σ))
        (fun σ hσ => ((hasDerivAt_tpow c n σ).const_mul M).sub
          ((hd 0 (Nat.succ_pos n) σ hσ).sub (hTd σ)))
        (fun σ hσ => ?_) hc hs ?_
      · obtain ⟨w, -, hwM, hw⟩ := ih σ hσ
        refine ⟨(M - w) / (n.factorial : ℝ), div_nonneg (sub_nonneg.mpr hwM) hfact.le, ?_⟩
        show M * ((σ - c) ^ n / (n.factorial : ℝ)) - (g 1 σ - T' σ) = _
        have hw' : g 1 σ = T' σ + w * ((σ - c) ^ n / (n.factorial : ℝ)) := hw
        rw [hw']
        ring
      · show M * ((c - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - (g 0 c - T c) = 0
        rw [hTc]
        simp
    have hm : 0 ≤ ((g 0 s - T s) - m * ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ))) *
        (s - c) ^ (n + 1) := by
      refine sign_of_deriv_pow (a := a) (b := b) (c := c) (k := n)
        (h := fun σ => (g 0 σ - T σ) - m * ((σ - c) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (h' := fun σ => (g 1 σ - T' σ) - m * ((σ - c) ^ n / (n.factorial : ℝ)))
        (fun σ hσ => ((hd 0 (Nat.succ_pos n) σ hσ).sub (hTd σ)).sub
          ((hasDerivAt_tpow c n σ).const_mul m))
        (fun σ hσ => ?_) hc hs ?_
      · obtain ⟨w, hwm, -, hw⟩ := ih σ hσ
        refine ⟨(w - m) / (n.factorial : ℝ), div_nonneg (sub_nonneg.mpr hwm) hfact.le, ?_⟩
        show (g 1 σ - T' σ) - m * ((σ - c) ^ n / (n.factorial : ℝ)) = _
        have hw' : g 1 σ = T' σ + w * ((σ - c) ^ n / (n.factorial : ℝ)) := hw
        rw [hw']
        ring
      · show (g 0 c - T c) - m * ((c - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) = 0
        rw [hTc]
        simp
    -- the remainder as a multiple of `(s − c)ⁿ⁺¹/(n+1)!`
    show ∃ w, m ≤ w ∧ w ≤ M ∧ g 0 s = T s + w * ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ))
    rcases eq_or_ne s c with hsc | hsc
    · have hmM := hb c hc
      refine ⟨g (n + 1) c, hmM.1, hmM.2, ?_⟩
      rw [hsc, hTc]
      simp
    · have hne : s - c ≠ 0 := sub_ne_zero.mpr hsc
      have hpw : (s - c) ^ (n + 1) ≠ 0 := pow_ne_zero _ hne
      have hQ : 0 < (s - c) ^ (n + 1) * (s - c) ^ (n + 1) := mul_self_pos.mpr hpw
      have hP : (s - c) ^ (n + 1) / ((n + 1).factorial : ℝ) ≠ 0 := div_ne_zero hpw hfact'.ne'
      have hF : ((n + 1).factorial : ℝ) ≠ 0 := hfact'.ne'
      refine ⟨(g 0 s - T s) / ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)), ?_, ?_, ?_⟩
      · have key : (g 0 s - T s) / ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - m =
            ((g 0 s - T s) - m * ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ))) *
              (s - c) ^ (n + 1) * ((n + 1).factorial : ℝ) /
              ((s - c) ^ (n + 1) * (s - c) ^ (n + 1)) := by
          field_simp
        have h1 : 0 ≤ (g 0 s - T s) / ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - m := by
          rw [key]
          exact div_nonneg (mul_nonneg hm hfact'.le) hQ.le
        linarith
      · have key : M - (g 0 s - T s) / ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) =
            (M * ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) - (g 0 s - T s)) *
              (s - c) ^ (n + 1) * ((n + 1).factorial : ℝ) /
              ((s - c) ^ (n + 1) * (s - c) ^ (n + 1)) := by
          field_simp
        have h1 : 0 ≤ M - (g 0 s - T s) / ((s - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [key]
          exact div_nonneg (mul_nonneg hM hfact'.le) hQ.le
        linarith
      · rw [div_mul_cancel₀ _ hP]
        ring

/-! ## Taylor's formula for expressions -/

theorem IExpr.dzn_succ' (Λ k : ℕ) (x : IExpr) :
    IExpr.dzn Λ (k + 1) x = IExpr.dz Λ (IExpr.dzn Λ k x) :=
  Function.iterate_succ_apply' _ _ _

/-- **Taylor's formula for an expression of the second variable**, in the variable
`θ = π (c − t)/12`, with the remainder between the bounds of the next derivation. -/
theorem evalB_taylor (Λ : ℕ) (y : IExpr) (u : ℝ) {c t t0 t1 m M : ℝ} (n : ℕ) (ht0 : 0 < t0)
    (hx : Real.exp (-π * t0) < 1 / 3) (hc : c ∈ Set.Icc t0 t1) (ht : t ∈ Set.Icc t0 t1)
    (hb : ∀ s ∈ Set.Icc t0 t1,
      m ≤ IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ n y) (axisNEnv u s) ∧
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ n y) (axisNEnv u s) ≤ M) :
    ∃ w, m ≤ w ∧ w ≤ M ∧ IExpr.evalB (kernelAtoms Λ ++ []) y (axisNEnv u t) =
      (∑ p ∈ Finset.range n,
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ p y) (axisNEnv u c) *
          ((π * (c - t) / 12) ^ p / (p.factorial : ℝ))) +
        w * ((π * (c - t) / 12) ^ n / (n.factorial : ℝ)) := by
  have hπ := Real.pi_pos
  have hπ0 : π ≠ 0 := hπ.ne'
  -- the functions of `θ`
  let G : ℕ → ℝ → ℝ := fun p θ =>
    IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ p y) (axisNEnv u (c - 12 * θ / π))
  have hmem : ∀ θ ∈ Set.Icc (π * (c - t1) / 12) (π * (c - t0) / 12),
      c - 12 * θ / π ∈ Set.Icc t0 t1 := by
    intro θ hθ
    have e1 : c - 12 * (π * (c - t0) / 12) / π = t0 := by field_simp; ring
    have e2 : c - 12 * (π * (c - t1) / 12) / π = t1 := by field_simp; ring
    have m1 : 12 * θ / π ≤ 12 * (π * (c - t0) / 12) / π :=
      div_le_div_of_nonneg_right (by linarith [hθ.2]) hπ.le
    have m2 : 12 * (π * (c - t1) / 12) / π ≤ 12 * θ / π :=
      div_le_div_of_nonneg_right (by linarith [hθ.1]) hπ.le
    exact ⟨by linarith, by linarith⟩
  have hG : ∀ p, ∀ θ ∈ Set.Icc (π * (c - t1) / 12) (π * (c - t0) / 12),
      HasDerivAt (G p) (G (p + 1) θ) θ := by
    intro p θ hθ
    have hs := hmem θ hθ
    have hs0 : 0 < c - 12 * θ / π := lt_of_lt_of_le ht0 hs.1
    have hxs : Real.exp (-π * (c - 12 * θ / π)) < 1 / 3 := by
      refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hx
      nlinarith [hs.1]
    have h1 := hasDerivAt_evalB Λ u hs0 hxs (IExpr.dzn Λ p y)
    have h2 : HasDerivAt (fun θ : ℝ => c - 12 * θ / π) (-(12 / π)) θ := by
      have h := (((hasDerivAt_id' θ).const_mul (12 : ℝ)).div_const π).const_sub c
      exact h.congr_deriv (by ring)
    have h3 := h1.comp θ h2
    refine h3.congr_deriv ?_
    show -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ (IExpr.dzn Λ p y))
        (axisNEnv u (c - 12 * θ / π)) * -(12 / π) =
      IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ (p + 1) y) (axisNEnv u (c - 12 * θ / π))
    rw [IExpr.dzn_succ']
    field_simp
  have hGb : ∀ θ ∈ Set.Icc (π * (c - t1) / 12) (π * (c - t0) / 12), m ≤ G n θ ∧ G n θ ≤ M :=
    fun θ hθ => hb _ (hmem θ hθ)
  have h0 : (0 : ℝ) ∈ Set.Icc (π * (c - t1) / 12) (π * (c - t0) / 12) := by
    constructor
    · have : π * (c - t1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hπ.le (by linarith [hc.2])
      linarith
    · have : 0 ≤ π * (c - t0) := mul_nonneg hπ.le (by linarith [hc.1])
      linarith
  have hθ : π * (c - t) / 12 ∈ Set.Icc (π * (c - t1) / 12) (π * (c - t0) / 12) := by
    constructor
    · have : π * (c - t1) ≤ π * (c - t) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hπ.le
      linarith
    · have : π * (c - t) ≤ π * (c - t0) := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hπ.le
      linarith
  obtain ⟨w, hwm, hwM, hw⟩ := taylor_exists n G (fun p _ θ hθ => hG p θ hθ) hGb 0 h0 _ hθ
  refine ⟨w, hwm, hwM, ?_⟩
  have e0 : ∀ p, G p 0 = IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ p y) (axisNEnv u c) := by
    intro p
    show IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ p y) (axisNEnv u (c - 12 * 0 / π)) = _
    rw [show c - 12 * 0 / π = c by ring]
  have et : G 0 (π * (c - t) / 12) = IExpr.evalB (kernelAtoms Λ ++ []) y (axisNEnv u t) := by
    show IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ 0 y)
      (axisNEnv u (c - 12 * (π * (c - t) / 12) / π)) = _
    rw [show c - 12 * (π * (c - t) / 12) / π = t by field_simp; ring]
    rfl
  rw [et] at hw
  rw [hw]
  simp only [sub_zero, e0]

/-! ## The mirror image of an expression -/

namespace IExpr

theorem zOnly_swap : ∀ x : IExpr, x.swap.zOnly = x.tauOnly
  | .zat _ => rfl
  | .tat _ => rfl
  | .cst _ => rfl
  | .mono _ => rfl
  | .add x y => by
    show (x.swap.zOnly && y.swap.zOnly) = (x.tauOnly && y.tauOnly)
    rw [zOnly_swap x, zOnly_swap y]
  | .sub x y => by
    show (x.swap.zOnly && y.swap.zOnly) = (x.tauOnly && y.tauOnly)
    rw [zOnly_swap x, zOnly_swap y]
  | .mul x y => by
    show (x.swap.zOnly && y.swap.zOnly) = (x.tauOnly && y.tauOnly)
    rw [zOnly_swap x, zOnly_swap y]

end IExpr

/-! ## Enclosures of the powers of `θ` -/

namespace QI

/-- The square of an interval, as a set of squares. -/
def sqr (I : QI) : QI :=
  ⟨if 0 ≤ I.lo then I.lo ^ 2 else if I.hi ≤ 0 then I.hi ^ 2 else 0, max (I.lo ^ 2) (I.hi ^ 2)⟩

theorem mem_sqr {I : QI} {v : ℝ} (h : I.Mem v) : I.sqr.Mem (v ^ 2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show (((if 0 ≤ I.lo then I.lo ^ 2 else if I.hi ≤ 0 then I.hi ^ 2 else 0 : ℚ)) : ℝ) ≤ v ^ 2
    split_ifs with c1 c2
    · have c1' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast c1
      push_cast
      nlinarith
    · have c2' : (I.hi : ℝ) ≤ 0 := by exact_mod_cast c2
      push_cast
      nlinarith
    · push_cast
      positivity
  · show v ^ 2 ≤ ((max (I.lo ^ 2) (I.hi ^ 2) : ℚ) : ℝ)
    rw [Rat.cast_max]
    push_cast
    rcases le_total 0 v with hv | hv
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)

/-- The `p`-th power of an interval, even powers through the square. -/
def npow (I : QI) (p : ℕ) : QI :=
  if p % 2 = 0 then I.sqr.pow (p / 2) else (I.sqr.pow (p / 2)).mul I

theorem mem_npow {I : QI} {v : ℝ} (h : I.Mem v) (p : ℕ) : (I.npow p).Mem (v ^ p) := by
  have h2 := mem_pow (mem_sqr h) (p / 2)
  rw [← pow_mul] at h2
  unfold npow
  split_ifs with c
  · have e : 2 * (p / 2) = p := by omega
    rwa [e] at h2
  · have e : 2 * (p / 2) + 1 = p := by omega
    have h3 := mem_mul h2 h
    rwa [← pow_succ, e] at h3

end QI

/-- The enclosures of `θᵖ/p!` for `p < n`. -/
def tpows (n : ℕ) (Θ : QI) : List QI :=
  (List.range n).map fun p => (Θ.npow p).scale (1 / (p.factorial : ℚ))

theorem mem_tpows {n : ℕ} {Θ : QI} {θ : ℝ} (h : Θ.Mem θ) {p : ℕ} (hp : p < n) :
    ((tpows n Θ).getD p QI.zero).Mem (θ ^ p / (p.factorial : ℝ)) := by
  rw [tpows, getD_map_range _ _ hp]
  have h1 := QI.mem_scale (c := 1 / (p.factorial : ℚ)) (by positivity) (QI.mem_npow h p)
  have e : ((1 / (p.factorial : ℚ) : ℚ) : ℝ) * θ ^ p = θ ^ p / (p.factorial : ℝ) := by
    push_cast
    ring
  rwa [e] at h1

/-! ## The jet of `hOf` -/

/-- The jet of order `n` of `hOf x = ∂²x − 48 t̂ ∂x + 288 t̂² x` from the jet of order `n + 2`
of `x`. -/
def jetH (n : ℕ) (E : IEnv) (J : List QI) : List QI :=
  jadd n
    (jsub n (J.drop 2)
      (jmul n (jmul n (jconst n (QI.const 48)) (monoJet E n thMono)) (J.drop 1)))
    (jmul n
      (jmul n (jconst n (QI.const 288))
        (jmul n (jmul n (jconst n (QI.const 1)) (monoJet E n thMono)) (monoJet E n thMono)))
      J)

theorem jMem_jetH {Λ : ℕ} {fs : List (ℝ → ℝ)} {e : NEnv} {n : ℕ} {E : IEnv}
    (hE : E.Sound fs e) {J : List QI} {x : IExpr} (h : JMem Λ fs e (n + 2) J x) :
    JMem Λ fs e n (jetH n E J) (IExpr.hOf Λ x) := by
  have hth : JMem Λ fs e n (monoJet E n thMono) (.mono thMono) := jMem_monoJet hE n thMono
  have h2 : JMem Λ fs e n (J.drop 2) (IExpr.dz Λ (IExpr.dz Λ x)) := jMem_drop 2 h
  have h1 : JMem Λ fs e n (J.drop 1) (IExpr.dz Λ x) :=
    jMem_drop 1 (jMem_mono (Nat.le_succ (n + 1)) h)
  have h0 : JMem Λ fs e n J x := jMem_mono (Nat.le_add_right n 2) h
  have c48 : JMem Λ fs e n (jconst n (QI.const 48)) (.cst 48) := jMem_jconst_cst 48
  have c288 : JMem Λ fs e n (jconst n (QI.const 288)) (.cst 288) := jMem_jconst_cst 288
  have c1 : JMem Λ fs e n (jconst n (QI.const 1)) (.cst 1) := jMem_jconst_cst 1
  exact jMem_jadd (jMem_jsub h2 (jMem_jmul (jMem_jmul c48 hth) h1))
    (jMem_jmul (jMem_jmul c288 (jMem_jmul (jMem_jmul c1 hth) hth)) h0)

/-! ## The row of an expression on an interval -/

/-- `v` is a polynomial in `θ` with `n` coefficients in the intervals of `J`. -/
def TayMem (n : ℕ) (θ : ℝ) (J : List QI) (v : ℝ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ p, p < n → (J.getD p QI.zero).Mem (c p)) ∧
    v = ∑ p ∈ Finset.range n, c p * (θ ^ p / (p.factorial : ℝ))

/-- The row of an expression: the entries `≤ N` of the jet at the centre and the entry `N + 1` of
the jet on the interval. -/
def tayRow (N : ℕ) (JC JX : List QI) : List QI :=
  (List.range (N + 2)).map fun p => if p ≤ N then JC.getD p QI.zero else JX.getD p QI.zero

/-- **The row encloses the Taylor coefficients.** `xc` is the reciprocal parameter of the centre,
`[x0, x1]` the interval of reciprocal parameters. -/
theorem tayMem_row {Λ N : ℕ} {y : IExpr} {xc x0 x1 x : ℝ} {JC JX : List QI} (hx0 : 0 < x0)
    (h0c : x0 ≤ xc) (hc1 : xc ≤ x1) (hx : x ∈ Set.Icc x0 x1)
    (hnome : Real.exp (-x1⁻¹) < 1 / 3)
    (hJC : JMem Λ (kernelAtoms Λ ++ []) (recNEnv xc xc) N JC y)
    (hJX : ∀ s ∈ Set.Icc x0 x1, JMem Λ (kernelAtoms Λ ++ []) (recNEnv xc s) (N + 1) JX y) :
    TayMem (N + 2) ((xc⁻¹ - x⁻¹) / 12) (tayRow N JC JX)
      (IExpr.evalB (kernelAtoms Λ ++ []) y (recNEnv xc x)) := by
  have hπ := Real.pi_pos
  have hπ0 : π ≠ 0 := hπ.ne'
  have hxc : 0 < xc := lt_of_lt_of_le hx0 h0c
  have hx1 : 0 < x1 := lt_of_lt_of_le hxc hc1
  have hxp : 0 < x := lt_of_lt_of_le hx0 hx.1
  -- the reciprocal parameter `s` belongs to the point `1/(π s)` of the axis
  have henv : ∀ s : ℝ, 0 < s → axisNEnv (1 / (π * xc)) (1 / (π * s)) = recNEnv xc s := by
    intro s hs
    rw [axisNEnv_eq_recNEnv]
    have e1 : 1 / (π * (1 / (π * xc))) = xc := by field_simp
    have e2 : 1 / (π * (1 / (π * s))) = s := by field_simp
    rw [e1, e2]
  have hrec : ∀ s : ℝ, 0 < s → ∀ r : ℝ, 0 < r → (1 / (π * s) ≤ 1 / (π * r) ↔ r ≤ s) := by
    intro s hs r hr
    rw [one_div_le_one_div (mul_pos hπ hs) (mul_pos hπ hr)]
    exact mul_le_mul_iff_of_pos_left hπ
  have ht0 : (0 : ℝ) < 1 / (π * x1) := by positivity
  have hx' : Real.exp (-π * (1 / (π * x1))) < 1 / 3 := by
    have e : -π * (1 / (π * x1)) = -x1⁻¹ := by field_simp
    rw [e]
    exact hnome
  have hcI : 1 / (π * xc) ∈ Set.Icc (1 / (π * x1)) (1 / (π * x0)) :=
    ⟨(hrec x1 hx1 xc hxc).mpr hc1, (hrec xc hxc x0 hx0).mpr h0c⟩
  have htI : 1 / (π * x) ∈ Set.Icc (1 / (π * x1)) (1 / (π * x0)) :=
    ⟨(hrec x1 hx1 x hxp).mpr hx.2, (hrec x hxp x0 hx0).mpr hx.1⟩
  -- the bounds of the last derivation on the interval
  have hb : ∀ s ∈ Set.Icc (1 / (π * x1)) (1 / (π * x0)),
      ((JX.getD (N + 1) QI.zero).lo : ℝ) ≤ IExpr.evalB (kernelAtoms Λ ++ [])
          (IExpr.dzn Λ (N + 1) y) (axisNEnv (1 / (π * xc)) s) ∧
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ (N + 1) y)
          (axisNEnv (1 / (π * xc)) s) ≤ ((JX.getD (N + 1) QI.zero).hi : ℝ) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht0 hs.1
    have hr0 : 0 < 1 / (π * s) := by positivity
    have e : s = 1 / (π * (1 / (π * s))) := by field_simp
    have hrI : 1 / (π * s) ∈ Set.Icc x0 x1 := by
      constructor
      · have h1 := hs.2
        rw [e] at h1
        exact (hrec _ hr0 x0 hx0).mp h1
      · have h1 := hs.1
        rw [e] at h1
        exact (hrec x1 hx1 _ hr0).mp h1
    have h2 := hJX _ hrI (N + 1) le_rfl
    rw [← henv _ hr0, ← e] at h2
    exact h2
  obtain ⟨w, hwm, hwM, hw⟩ := evalB_taylor Λ y (1 / (π * xc)) (N + 1) ht0 hx' hcI htI hb
  rw [henv x hxp, henv xc hxc] at hw
  have eθ : π * (1 / (π * xc) - 1 / (π * x)) / 12 = (xc⁻¹ - x⁻¹) / 12 := by
    field_simp
  rw [eθ] at hw
  refine ⟨fun p => if p ≤ N then
    IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dzn Λ p y) (recNEnv xc xc) else w, ?_, ?_⟩
  · intro p hp
    rw [tayRow, getD_map_range _ _ hp]
    dsimp only
    split_ifs with hpN
    · exact hJC p hpN
    · have hpe : p = N + 1 := by omega
      rw [hpe]
      exact ⟨hwm, hwM⟩
  · rw [hw, Finset.sum_range_succ (n := N + 1)]
    dsimp only
    have hlast : ¬ (N + 1 ≤ N) := by omega
    rw [if_neg hlast]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpN : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [if_pos hpN]

end E8Leech.Kron
