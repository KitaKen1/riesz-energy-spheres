import E8Leech.KronLeechH2K
import E8Leech.KronLeechH2Sign

/-!
# The truncated Leech kernel inequality (6.4)(2) for `q ≤ 1 ≤ t` from divided-difference models

For `q = 1/v` the numerator of `KronLeechH2K` is `−H₂ᴷ = N₀ + t̂ N₁`. With the third-order jets of
`KronLeechJetH` and the program `ISLP.h2Prog`, `N₁ = b² ρ₁` and `N₀ = b³ ρ₂` exactly as for
`u, t ≥ 1` (`KronLeechH2Sign`), but the `a`-version of `ρ₁` does not vanish: it is
`165888 Λ (K/a²)(t̂ − û)` with `K = (256Δ)² E₄² · 2E₆ ≥ 0` at `iv`, `v ≥ 1`. Hence

`−H₂ᴷ = b² (b − a) (t̂ · ρ₁[a, b] + b · ρ₂[a, b] + t̂ · 165888 Λ (K/a²) q)`,
`q = (t̂ − û)/(b − a) > 0`,

the form of the numerator of `𝒦⁽²⁴⁾` in `KronLeechSignK` with the pivots `a²b`, `a³` for the two
divided differences and `a³b`, `a⁴` for `K`.

* `combination_pos_vertex_add`: positivity of `t̂ f₁ + b f₂ + t̂ κ (g/a²) q` on a cell from three
  models, by the vertex check with a constant term.
* `leechHatTruncK_of_dd`: the inequality at a point from the positivity of the bracket.
* `leechKModel_of_run`: the model of `K` from a checked run of its program.
* `vertexHKCellOK`, `leechHatTruncK_of_cell`, `leechHatTruncK_of_cover`,
  `leechHatTrunc_of_cover_le_one`: the inequality on a cell, on a cover, and for `q ≤ 1 ≤ t`
  outside a corner box.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## A split combination with the vertex check and a constant term -/

/-- **Positivity of `t̂ f₁ + b f₂ + t̂ κ (g/a²) q` on a cell.** `T₁`, `T₂` are models of `f₁`, `f₂`
with the pivots `aⁱb`, `aⁱ⁺¹` (the first one checked at the eight vertices), `TK` is a model of the
function `g ≥ 0` of the first nome with the pivots `aⁱ⁺¹b`, `aⁱ⁺²`, and `q₀` bounds
`q = (t̂ − û)/(b − a)` from below on the cell. -/
theorem combination_pos_vertex_add {Bx : Bounds} {f₁ f₂ g : NEnv → ℝ} {T₁ T₂ TK : MTM} {i : ℕ}
    {κ : ℚ} (h₁ : T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₁)
    (h₂ : T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₂) (hK : TK.Approx Bx (fun _ => True) g)
    (hd₁ : T₁.Divisible i 0) (hd₂ : T₂.Divisible i 0) (hdK : TK.Divisible (i + 1) 0)
    (hPB : (T₁.quots i 0).PB.MultiAffine) (hPA : (T₁.quots i 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w q₀ : ℚ} (hw : WOK C w) (hq : QOK C q₀) (hκ : 0 ≤ κ)
    (hKB : 0 ≤ (TK.quots (i + 1) 0).marginB C)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots i 0).marginBv C p q r + w * min ((T₂.quots i 0).marginB C) 0)
        ((T₁.quots i 0).marginAv C p q r + w * min ((T₂.quots i 0).marginA C) 0)
        (κ * max ((TK.quots (i + 1) 0).marginA C) 0 * q₀))
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t) (hmem : C.Mem (axisNEnv u t))
    (hg0 : 0 ≤ g (axisNEnv u t)) :
    0 < (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) +
      (axisNEnv u t).t * (κ * (g (axisNEnv u t) / (axisNEnv u t).a ^ 2) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) := by
  have hπ := Real.pi_pos
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
  have l₁ := MTM.lower_of_divisible_eval h₁ hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible h₂ hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have lK := MTM.lower_of_divisible hK hdK hC hsub hmem trivial ha.le hb.le
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
  have hκ' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  -- the function `g`
  have hKB' : (0 : ℝ) ≤ ((TK.quots (i + 1) 0).marginB C : ℝ) := by exact_mod_cast hKB
  have hKκ : (axisNEnv u t).a ^ (i + 2) * (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) ≤
      g (axisNEnv u t) := by
    have e : (axisNEnv u t).a ^ (i + 1) * (axisNEnv u t).b ^ 0 *
        ((axisNEnv u t).b * (((TK.quots (i + 1) 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ)) =
        (axisNEnv u t).a ^ (i + 1) * (axisNEnv u t).b * (((TK.quots (i + 1) 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a ^ (i + 2) * (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) := by
      ring
    have hnn := mul_nonneg (mul_nonneg (pow_nonneg ha.le (i + 1)) hb.le) hKB'
    rw [e] at lK
    linarith
  have hKmax : (axisNEnv u t).a ^ (i + 2) * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 ≤
      g (axisNEnv u t) := by
    rcases le_total (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact hg0
    · rw [max_eq_left h]
      exact hKκ
  have hKdiv : (axisNEnv u t).a ^ i * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 ≤
      g (axisNEnv u t) / (axisNEnv u t).a ^ 2 := by
    rw [le_div_iff₀ (pow_pos ha 2)]
    calc (axisNEnv u t).a ^ i * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 *
          (axisNEnv u t).a ^ 2 =
        (axisNEnv u t).a ^ (i + 2) * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 := by ring
      _ ≤ g (axisNEnv u t) := hKmax
  have hKq := mul_le_mul hKdiv hqe hq0' (div_nonneg hg0 (pow_nonneg ha.le 2))
  have hKq' := mul_le_mul_of_nonneg_left hKq hκ'
  -- the weighted margins at the vertices
  have hkey := Cell.pos_of_vertices_add hC hPB hPA hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots i 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots i 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hpos : 0 < f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t) +
      κ * (g (axisNEnv u t) / (axisNEnv u t).a ^ 2 *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) := by
    have hin : 0 < (axisNEnv u t).b * (IPoly.eval (T₁.quots i 0).PB (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RB : ℝ)) +
        (axisNEnv u t).a * (IPoly.eval (T₁.quots i 0).PA (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RA : ℝ)) +
        W * ((axisNEnv u t).b * (((T₂.quots i 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((T₂.quots i 0).marginA C : ℚ) : ℝ)) +
        κ * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 * q₀ := by
      nlinarith [hkey, kB, kA]
    have hmul := mul_pos hc hin
    have hKq'' : (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 *
        (κ * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 * q₀) ≤
        κ * (g (axisNEnv u t) / (axisNEnv u t).a ^ 2 *
          (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) := by
      calc (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 *
            (κ * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 * q₀) =
          κ * ((axisNEnv u t).a ^ i * max (((TK.quots (i + 1) 0).marginA C : ℚ) : ℝ) 0 * q₀) := by
            ring
        _ ≤ _ := hKq'
    generalize (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 = c at hmul l₁ k2 hKq''
    nlinarith [hmul, l₁, k2, hKq'']
  have hlin : (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) +
      (axisNEnv u t).t * (κ * (g (axisNEnv u t) / (axisNEnv u t).a ^ 2) *
        (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a))) =
      (axisNEnv u t).t * (f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t) +
        κ * (g (axisNEnv u t) / (axisNEnv u t).a ^ 2 *
          (((axisNEnv u t).t - (axisNEnv u t).u) / ((axisNEnv u t).b - (axisNEnv u t).a)))) := by
    rw [← hWdef]
    ring
  rw [hlin]
  exact mul_pos hY hpos

/-! ## The sign of the truncated kernel -/

/-- The real-number core at the inverted first variable: `c Δ N w⁻¹ (K − E) = b² δ S` with
`N/δ > 0` and `S > 0`. -/
theorem trunc_lt_of_splitK {c Δ N δ w K E b S : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hN : 0 < N / δ)
    (hw : 0 < w) (hb : 0 < b) (hS : 0 < S) (h : c * Δ * N * w⁻¹ * (K - E) = b ^ 2 * δ * S) :
    E < K := by
  refine trunc_lt_of_split (c := c * w⁻¹) (by positivity) hΔ hN hb hS ?_
  rw [← h]
  ring

/-- The factor `K = (256Δ)² E₄² · 2E₆` at `iv`, `v ≥ 1`, among the fifteen atoms. -/
theorem leechKE_hAtoms_nonneg (Λ : ℕ) {v : ℝ} (hv : 1 ≤ v) (t : ℝ) :
    0 ≤ IExpr.evalA (hAtoms Λ) leechKE (axisNEnv v t) := by
  have h := leechKE_nonneg Λ hv t
  rw [leechKE_evalA] at h
  rw [hAtoms_eq, leechKE_evalA]
  exact h

section SignK

variable {Λ : ℕ} {prog : List IInstr} {k₁ k₀ : ℕ}

/-- **The truncated inequality (6.4)(2) at a point `(1/v, t)`** from the positivity of the split
divided difference with the explicit diagonal term:
`t̂ · ρ₁[a, b] + b · ρ₂[a, b] + t̂ · 165888 Λ (K/a²) q`. -/
theorem leechHatTruncK_of_dd (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechN21KE Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechN20E Λ) {v t : ℝ} (hv : 0 < v)
    (ht : 0 < t) (hvt : v ≠ t) (hprod : 1 < v * t)
    (hJ : kleinModularJ (imagPt v) ≠ kleinModularJ (imagPt t))
    (hsmall : NomeSmallH (axisNEnv v t))
    (hc₁ : ∀ side : Bool, ∀ j, j < 2 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) 0 = 0)
    (hc₀ : ∀ side : Bool, ∀ j, j < 3 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) 0 = 0)
    (hDD : 0 < (axisNEnv v t).t *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0) /
          ((axisNEnv v t).b - (axisNEnv v t).a)) +
      (axisNEnv v t).b *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0) /
          ((axisNEnv v t).b - (axisNEnv v t).a)) +
      (axisNEnv v t).t * (165888 * Λ *
        (IExpr.evalA (hAtoms Λ) leechKE (axisNEnv v t) / (axisNEnv v t).a ^ 2) *
        (((axisNEnv v t).t - (axisNEnv v t).u) / ((axisNEnv v t).b - (axisNEnv v t).a)))) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) v⁻¹ 0).re * t + (leechAxisCusp (-1) v⁻¹ 1).re) <
      (ckmrvLeechHatKernel (imagPt v⁻¹) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  obtain ⟨⟨ha4, hb4, ha3s, ha4s, hb3s, hb4s⟩, haη, hbη⟩ := hsmall
  have ha : 0 < (axisNEnv v t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv v t).b := Real.exp_pos _
  -- the two parts on the two sides
  have hB1 := h2_rho1 (prog := prog) h2 false (axisNEnv v t) hb.le hb4 hb3s hb4s hbη k₁ (hc₁ false)
  have hA1 := h2_rho1 (prog := prog) h2 true (axisNEnv v t) ha.le ha4 ha3s ha4s haη k₁ (hc₁ true)
  have hB0 := h2_rho2 (prog := prog) h2 false (axisNEnv v t) hb.le hb4 hb3s hb4s hbη k₁ k₀
    (hc₀ false)
  have hA0 := h2_rho2 (prog := prog) h2 true (axisNEnv v t) ha.le ha4 ha3s ha4s haη k₁ k₀
    (hc₀ true)
  rw [hp₁] at hB1 hA1
  rw [hp₀] at hB0 hA0
  have z1 : IExpr.evalA (hAtoms Λ) (leechN21KE Λ) (axisNEnv v t) =
      165888 * Λ * IExpr.evalA (hAtoms Λ) leechKE (axisNEnv v t) *
        ((axisNEnv v t).t - (axisNEnv v t).u) := by
    rw [hAtoms_eq]
    exact leechN21KE_evalA Λ _ _
  have z0 : IExpr.evalA (hAtoms Λ) (leechN20E Λ) (axisNEnv v t) = 0 := by
    rw [hAtoms_eq]
    exact leechN20E_evalA Λ _ _
  have ha2 : (axisNEnv v t).a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hA1' : (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 =
      165888 * Λ * (IExpr.evalA (hAtoms Λ) leechKE (axisNEnv v t) / (axisNEnv v t).a ^ 2) *
        ((axisNEnv v t).t - (axisNEnv v t).u) := by
    have h : IExpr.evalA (hAtoms Λ) (leechN21KE Λ) (axisNEnv v t) = (axisNEnv v t).a ^ 2 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hA1
    rw [z1] at h
    field_simp
    linarith
  have hA0' : (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 = 0 := by
    have h : IExpr.evalA (hAtoms Λ) (leechN20E Λ) (axisNEnv v t) = (axisNEnv v t).a ^ 3 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hA0
    rw [z0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 ha.ne')
  rw [hA1', hA0', sub_zero] at hDD
  have hB1' : IExpr.evalB (hAtoms Λ) (leechN21KE Λ) (axisNEnv v t) = (axisNEnv v t).b ^ 2 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hB1
  have hB0' : IExpr.evalB (hAtoms Λ) (leechN20E Λ) (axisNEnv v t) = (axisNEnv v t).b ^ 3 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv v t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hB0
  -- the numerator and the denominator
  have hax := leechH2K_eval_axis Λ (red3Atoms Λ ++ [lam2Eta Λ]) hv ht hJ
  rw [← hAtoms_eq, hB0', hB1'] at hax
  have hden : 0 < axNu (axV v) (axW v) (axV t) (axW t) /
      ((axisNEnv v t).b - (axisNEnv v t).a) := ckmrvAxisDividedDenominator_pos hv ht hvt hprod
  have hδ : (axisNEnv v t).b - (axisNEnv v t).a ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hden
    exact lt_irrefl _ hden
  have hc0 : (0 : ℝ) < 21743271936 * Λ * π * (1 / (π * v)) * (1 / (π * t)) ^ 2 := by positivity
  refine trunc_lt_of_splitK hc0 (axDelta_pos ht) hden (pow_pos hv 12) hb hDD ?_
  rw [← hax]
  field_simp
  ring

/-! ## The models -/

/-- **The model of the factor `K` from a checked run of its program.** -/
theorem leechKModel_of_run {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) {D Dcap N' NE' : ℕ}
    (hR : RedHOK Bx D Dcap N' NE') {n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n + 3 → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (progK : List IInstr) (k : ℕ)
    (h : (ISLP.runExpr progK []).getD k (.cst 0) = leechKE) :
    ((ISLP.runMDD Bx D Dcap (hAtomModels Bx D Dcap Λ n K N NE N' NE') progK []).getD k
      MDD.zero).A.Approx Bx (fun _ => True) (IExpr.evalA (hAtoms Λ) leechKE) :=
  (ISLP.approx_checked (S := fun _ => True) hG.1.1 D Dcap (hAtoms_ok hG hR K N hΛ hL) progK k _
    h).1

/-! ## Cells and covers -/

/-- **The truncated inequality on a cell, first variable inverted.** A cell inside the bounds of
the models that passes the vertex check with the constant term (pivots `a²b`, `a³` for the divided
differences and `a³b`, `a⁴` for `K`) contains no point `(v, t)` with `v ≥ 1`, `vt > 1`, `v ≠ t`
where the truncated inequality at `(1/v, t)` fails. -/
theorem leechHatTruncK_of_cell {Bx : Bounds} {T₁ T₂ TK : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechN21KE Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechN20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂)
    (hK : TK.Approx Bx (fun _ => True) (IExpr.evalA (hAtoms Λ) leechKE))
    (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0) (hdK : TK.Divisible 3 0)
    (hPB : (T₁.quots 2 0).PB.MultiAffine) (hPA : (T₁.quots 2 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w q₀ : ℚ} (hw : WOK C w) (hq : QOK C q₀)
    (hKB : 0 ≤ (TK.quots 3 0).marginB C)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots 2 0).marginBv C p q r + w * min ((T₂.quots 2 0).marginB C) 0)
        ((T₁.quots 2 0).marginAv C p q r + w * min ((T₂.quots 2 0).marginA C) 0)
        (165888 * Λ * max ((TK.quots 3 0).marginA C) 0 * q₀))
    {v t : ℝ} (hv : 1 ≤ v) (ht : 0 < t) (hvt : v ≠ t) (hprod : 1 < v * t)
    (hJ : kleinModularJ (imagPt v) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv v t)) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) v⁻¹ 0).re * t + (leechAxisCusp (-1) v⁻¹ 1).re) <
      (ckmrvLeechHatKernel (imagPt v⁻¹) (imagPt t)).re := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hBx : Bx.Mem (axisNEnv v t) := Bounds.mem_of_le hC.2 hsub hmem.2.2.2.2.2
  have h := combination_pos_vertex_add (κ := 165888 * (Λ : ℚ)) hM.dd₁ hM.dd₀ hK hd₁ hd₂ hdK hPB hPA
    hC hsub hw hq (by positivity) hKB hOK hv0 ht hvt hmem (leechKE_hAtoms_nonneg Λ hv t)
  push_cast at h
  exact leechHatTruncK_of_dd hΛ h2 hp₁ hp₀ hv0 ht hvt hprod hJ (hM.small _ hBx)
    (fun side j hj => hM.zero₁ side j hj _ hBx) (fun side j hj => hM.zero₀ side j hj _ hBx) h

/-- The cell test of the truncated numerator at the inverted first variable: the vertex check
with the constant term; `w` bounds `b / t̂` from above and `q₀` bounds `q` from below. -/
def vertexHKCellOK (Bx : Bounds) (Λ : ℕ) (Q₁ Q₂ QK : Quots) (C : Cell) (w q₀ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧ QOK C q₀ ∧ 0 ≤ QK.marginB C ∧ ∀ p q r : Bool,
    C.PosOK (Q₁.marginBv C p q r + w * min (Q₂.marginB C) 0)
      (Q₁.marginAv C p q r + w * min (Q₂.marginA C) 0) (165888 * Λ * max (QK.marginA C) 0 * q₀))

/-- **The truncated inequality at `(1/v, t)` on a cover**, in the reciprocal coordinates of
`(v, t)`, outside the corner. -/
theorem leechHatTruncK_of_cover {Bx : Bounds} {T₁ T₂ TK : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechN21KE Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechN20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂)
    (hK : TK.Approx Bx (fun _ => True) (IExpr.evalA (hAtoms Λ) leechKE))
    (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0) (hdK : TK.Divisible 3 0)
    {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 2 0 = Q₁) (hQ₂ : T₂.quots 2 0 = Q₂)
    (hQK : TK.quots 3 0 = QK) (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ}
    {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKb k n) (vertexHKCellOK Bx Λ Q₁ Q₂ QK) c r = true) {v t : ℝ}
    (hv : 1 ≤ v) (ht : 0 < t) (hr : r.Mem (1 / (π * v)) (1 / (π * t))) (hvt : v ≠ t)
    (hprod : 1 < v * t) (hJ : kleinModularJ (imagPt v) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * v) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      Real.exp (2 * π * t) *
          ((leechAxisCusp (-1) v⁻¹ 0).re * t + (leechAxisCusp (-1) v⁻¹ 1).re) <
        (ckmrvLeechHatKernel (imagPt v⁻¹) (imagPt t)).re := by
  subst hQ₁ hQ₂ hQK
  have hπ := Real.pi_pos
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hx : 0 < 1 / (π * v) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ v t : ℝ, 1 ≤ v → 0 < t → x = 1 / (π * v) → y = 1 / (π * t) → v ≠ t →
      1 < v * t → kleinModularJ (imagPt v) ≠ kleinModularJ (imagPt t) →
      Real.exp (2 * π * t) *
          ((leechAxisCusp (-1) v⁻¹ 0).re * t + (leechAxisCusp (-1) v⁻¹ 1).re) <
        (ckmrvLeechHatKernel (imagPt v⁻¹) (imagPt t)).re)
    (cellOKb_spec k n)
    (fun C w q₀ hC hok x y _ _ hmem v t hv ht hxv hyt hvt hprod hJ => by
      simp only [vertexHKCellOK, decide_eq_true_eq] at hok
      refine leechHatTruncK_of_cell hΛ h2 hp₁ hp₀ hM hK hd₁ hd₂ hdK hPB hPA hC hok.1 hok.2.1
        hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2 hv ht hvt hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxv, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h v t hv ht rfl rfl hvt hprod hJ)

/-- **The truncated inequality for `q ≤ 1 ≤ t` outside a corner box.** The cover is one of the
reciprocal square `[0, x₁]²` with `1/π ≤ x₁` in the variables `1/q` and `t`; its corner
`x, y ≥ c` lies inside `1/q, t ≤ c₀`. -/
theorem leechHatTrunc_of_cover_le_one {Bx : Bounds} {T₁ T₂ TK : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechN21KE Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechN20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂)
    (hK : TK.Approx Bx (fun _ => True) (IExpr.evalA (hAtoms Λ) leechKE))
    (hd₁ : T₁.Divisible 2 0) (hd₂ : T₂.Divisible 2 0) (hdK : TK.Divisible 3 0)
    {Q₁ Q₂ QK : Quots} (hQ₁ : T₁.quots 2 0 = Q₁) (hQ₂ : T₂.quots 2 0 = Q₂)
    (hQK : TK.quots 3 0 = QK) (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ}
    {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKb k n) (vertexHKCellOK Bx Λ Q₁ Q₂ QK) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1) (ht : 1 ≤ t) (hout : c₀ < q⁻¹ ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) <
      (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hv : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).mpr hq
  have hv0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hJ' : kleinModularJ (imagPt q⁻¹) ≠ kleinModularJ (imagPt t) := by
    rw [← S_smul_imagPt hq0, kleinModularJ_S]
    exact hJ
  have hvt : q⁻¹ ≠ t := fun h => hJ' (by rw [h])
  have hx₁0 : (0 : ℝ) < x₁ := by
    by_contra hcon
    have := mul_nonpos_of_nonneg_of_nonpos hπ.le (not_lt.mp hcon)
    linarith
  have hprod : 1 < q⁻¹ * t := by
    rcases lt_or_gt_of_ne hvt with h | h
    · nlinarith
    · nlinarith
  have hrec : ∀ s : ℝ, 1 ≤ s → (0 : ℝ) ≤ 1 / (π * s) ∧ 1 / (π * s) ≤ x₁ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_pos hπ hx₁0).le]
  have hr : (⟨0, x₁, 0, x₁⟩ : Rect).Mem (1 / (π * q⁻¹)) (1 / (π * t)) := by
    refine ⟨?_, (hrec q⁻¹ hv).2, ?_, (hrec t ht).2⟩
    · simpa using (hrec q⁻¹ hv).1
    · simpa using (hrec t ht).1
  have hcorner : ∀ s : ℝ, 0 < s → (c : ℝ) ≤ 1 / (π * s) → s ≤ c₀ := by
    intro s hs hcs
    rw [le_div_iff₀ (by positivity)] at hcs
    have hπc : 0 < π * c := mul_pos hπ hc
    have h1 : π * c * s ≤ π * c * c₀ := by nlinarith
    exact le_of_mul_le_mul_left h1 hπc
  have key := leechHatTruncK_of_cover hΛ h2 hp₁ hp₀ hM hK hd₁ hd₂ hdK hQ₁ hQ₂ hQK hPB hPA hcov hv
    ht0 hr hvt hprod hJ'
  rw [inv_inv] at key
  rcases key with h | h
  · rcases hout with h' | h'
    · exact absurd (hcorner q⁻¹ hv0 h.1) (not_le.mpr h')
    · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
  · exact h

end SignK

end E8Leech.Kron
