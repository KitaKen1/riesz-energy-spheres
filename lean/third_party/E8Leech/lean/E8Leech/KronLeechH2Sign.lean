import E8Leech.KronLeechH2
import E8Leech.KronLeechJetH
import E8Leech.KronLeechSign
import E8Leech.KronJet3Check

/-!
# The truncated Leech kernel inequality (6.4)(2) from divided-difference models

The numerator of `KronLeechH2` is `H₂ = X₀ + t̂ X₁`, where both parts vanish when the generators
of the second variable equal those of the first, `X₁` vanishes to the second order at the cusp
`b = 0` and `X₀` to the third (in fact to the fourth). With the third-order jets of
`KronLeechJetH`: if the first two components of the jet of `X₁` and the first three of the jet
of `X₀` vanish, then `X₁ = b² ρ₁` and `X₀ = b³ ρ₂`, where `ρ₁ = c₂ + b r` is formed by two more
instructions (`ISLP.h2Prog`) and `ρ₂` is the last component of the jet of `X₀`. Hence

`H₂ = b² (b − a) (t̂ · ρ₁[a, b] + b · ρ₂[a, b])`,

the form of the Leech numerator in `KronLeechSign`, and the truncated inequality holds where the
split divided difference is positive (`leechHatTrunc_of_dd`).

* `combination_pos_vertex`: positivity of `t̂ f₁ + b f₂` on a cell from two models, by the vertex
  check (the statement of `splitDD_combination_pos_vertex` for arbitrary functions).
* `ISLP.h2Prog`, `h2_sq`, `h2_cube`: the program and the two factorizations;
  `tr3_of_take_prefix`, `h2Prog_eq_of`: the claimed program of a certificate is `h2Prog`.
* `LeechH2Models`, `leechH2Models_of_run`: the facts that a certificate provides.
* `leechHatTrunc_of_cell`, `leechHatTrunc_of_cover`, `leechHatTrunc_of_cover_ge_one`: the
  inequality on a cell, on a cover, and for `u, t ≥ 1` outside a corner box.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## A split combination with the vertex check -/

/-- **Positivity of `t̂ f₁ + b f₂` on a cell, vertex check.** The statement of
`splitDD_combination_pos_vertex` for two arbitrary functions with models. -/
theorem combination_pos_vertex {Bx : Bounds} {f₁ f₂ : NEnv → ℝ} {T₁ T₂ : MTM} {i : ℕ}
    (h₁ : T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₁)
    (h₂ : T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₂)
    (hd₁ : T₁.Divisible i 0) (hd₂ : T₂.Divisible i 0)
    (hPB : (T₁.quots i 0).PB.MultiAffine) (hPA : (T₁.quots i 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots i 0).marginBv C p q r + w * min ((T₂.quots i 0).marginB C) 0)
        ((T₁.quots i 0).marginAv C p q r + w * min ((T₂.quots i 0).marginA C) 0) 0)
    {u t : ℝ} (ht : 0 < t) (hut : u ≠ t) (hmem : C.Mem (axisNEnv u t)) :
    0 < (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) := by
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
  have l₁ := MTM.lower_of_divisible_eval h₁ hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible h₂ hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
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
  have hkey := Cell.pos_of_vertices hC hPB hPA hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots i 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots i 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hpos : 0 < f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t) := by
    have hin : 0 < (axisNEnv u t).b * (IPoly.eval (T₁.quots i 0).PB (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RB : ℝ)) +
        (axisNEnv u t).a * (IPoly.eval (T₁.quots i 0).PA (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RA : ℝ)) +
        W * ((axisNEnv u t).b * (((T₂.quots i 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((T₂.quots i 0).marginA C : ℚ) : ℝ)) := by
      nlinarith [hkey, kB, kA]
    have hmul := mul_pos hc hin
    generalize (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 = c at hmul l₁ k2
    nlinarith [hmul, l₁, k2]
  have hlin : (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) =
      (axisNEnv u t).t * (f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t)) := by
    rw [← hWdef]
    ring
  rw [hlin]
  exact mul_pos hY hpos

/-! ## The program and the factorizations -/

namespace ISLP

/-- The transformed program with two more instructions: the register after the last one of the
transformed program is `n · r`, and the next one is `ρ = c₂ + n r`, for the jet `(c₀, c₁, c₂, r)`
of the register `k₁` of `prog`. -/
def h2Prog (Λ : ℕ) (prog : List IInstr) (k₁ : ℕ) : List IInstr :=
  (tr3 (zleafH Λ) prog).1 ++
    [.mul 0 ((tr3 (zleafH Λ) prog).2.getD k₁ 1 + 3),
      .add ((tr3 (zleafH Λ) prog).2.getD k₁ 1 + 2) (tr3 (zleafH Λ) prog).1.length]

end ISLP

section Run

variable (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (Λ : ℕ) (prog : List IInstr) (k₁ : ℕ)

theorem length_runR_tr3 :
    (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).length =
      (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length := by
  rw [ISLP.length_runR, List.length_nil, Nat.zero_add]

/-- The run of `h2Prog`: the run of the transformed program and two more registers. -/
theorem runR_h2Prog :
    ISLP.runR fs side e (ISLP.h2Prog Λ prog k₁) [] =
      (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 [] ++
        [(ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD 0 0 *
          (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 3) 0]) ++
        [(ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 [] ++
            [(ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD 0 0 *
              (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
                ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 3) 0]).getD
              ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 2) 0 +
          (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 [] ++
            [(ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD 0 0 *
              (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
                ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 3) 0]).getD
              (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length 0] := by
  rw [ISLP.h2Prog, ISLP.runR_append]
  rfl

/-- The registers of the transformed program are not changed by the two instructions. -/
theorem runR_h2Prog_getD_lt {q : ℕ} (hq : q < (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length) :
    (ISLP.runR fs side e (ISLP.h2Prog Λ prog k₁) []).getD q 0 =
      (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD q 0 := by
  have hlen := length_runR_tr3 fs side e Λ prog
  rw [runR_h2Prog,
    List.getD_append _ _ _ _ (by rw [List.length_append, hlen]; omega),
    List.getD_append _ _ _ _ (by rw [hlen]; exact hq)]

/-- The last register of `h2Prog` is `c₂ + n r`. -/
theorem runR_h2Prog_getD_rho
    (hp : (ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 3 < (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length) :
    (ISLP.runR fs side e (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 =
      (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 2) 0 +
        (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD 0 0 *
          (ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + 3) 0 := by
  have hlen := length_runR_tr3 fs side e Λ prog
  rw [runR_h2Prog]
  generalize ISLP.runR fs side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 [] = R at hlen ⊢
  generalize (ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 = p at hp ⊢
  generalize (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length = len at hlen hp ⊢
  subst hlen
  have h1 : (R ++ [R.getD 0 0 * R.getD (p + 3) 0]).length = R.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have e1 : (R ++ [R.getD 0 0 * R.getD (p + 3) 0]).getD (p + 2) 0 = R.getD (p + 2) 0 :=
    List.getD_append _ _ _ _ (by omega)
  have e2 : (R ++ [R.getD 0 0 * R.getD (p + 3) 0]).getD R.length 0 =
      R.getD 0 0 * R.getD (p + 3) 0 := by
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    rfl
  rw [List.getD_append_right _ _ _ _ (by rw [h1]), h1, Nat.sub_self, e1, e2]
  rfl

end Run

/-- The transformation from a checked prefix: the statement of `ISLP.tr3_of_take` when the claimed
program has further instructions. -/
theorem tr3_of_take_prefix {zleaf : ℕ → ISLP.Block} {prog0 prog : List IInstr} {outs : List ℕ}
    {c s : ℕ}
    (h : ISLP.tr3Aux zleaf (prog0.take c) [] ISLP.prelude3 = (prog.take s, outs))
    (hc : prog0.length ≤ c) : ISLP.tr3 zleaf prog0 = (prog.take s, outs) := by
  rw [List.take_of_length_le hc] at h
  exact h

/-- **The claimed program is `h2Prog`**: its first `len` instructions are the transformed program
and the last two are the instructions of `ρ₁`. -/
theorem h2Prog_eq_of {Λ : ℕ} {prog0 prog : List IInstr} {outs : List ℕ} {k₁ len : ℕ}
    (htr : ISLP.tr3 (ISLP.zleafH Λ) prog0 = (prog.take len, outs)) (hlen : len ≤ prog.length)
    (hdrop : prog.drop len = [.mul 0 (outs.getD k₁ 1 + 3), .add (outs.getD k₁ 1 + 2) len]) :
    ISLP.h2Prog Λ prog0 k₁ = prog := by
  rw [ISLP.h2Prog, htr]
  simp only
  rw [List.length_take, Nat.min_eq_left hlen, ← hdrop, List.take_append_drop]

/-- The nomes of an environment are small enough for the blocks of the fifteen atoms. -/
def NomeSmallH (e : NEnv) : Prop :=
  NomeSmall e ∧ |e.a * devEta e.a| < 1 ∧ |e.b * devEta e.b| < 1

section Jets

variable {Λ : ℕ} {prog : List IInstr}

/-- The jets of the transformed program end before its last register. -/
theorem h2_jet_lt (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) (k : ℕ) :
    (ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + 3 < (ISLP.tr3 (ISLP.zleafH Λ) prog).1.length := by
  have hf : (hAtoms Λ).getD 0 (fun _ => 0) = id := rfl
  have hz := ISLP.zleafH_ok Λ h2 side e hx0 hx4 hs3 hs4 hsη
  have h := ((ISLP.sim3_tr3Aux hz prog [] ISLP.prelude3 [] (ISLP.sim3_prelude hf)).get k).1
  rw [ISLP.length_runR, List.length_nil, Nat.zero_add] at h
  exact h

/-- **The value of a register is the square of the nome times `c₂ + n r`**, when the first two
components of its jet vanish. -/
theorem h2_sq (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) (k : ℕ)
    (hc : ∀ j, j < 2 → (ISLP.runR (hAtoms Λ) side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + j) 0 = 0) :
    ISLP.eval (hAtoms Λ) side e ((ISLP.runExpr prog []).getD k (.cst 0)) =
      (if side then e.a else e.b) ^ 2 *
        ((ISLP.runR (hAtoms Λ) side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + 2) 0 +
          (if side then e.a else e.b) *
            (ISLP.runR (hAtoms Λ) side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
              ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + 3) 0) := by
  have hf : (hAtoms Λ).getD 0 (fun _ => 0) = id := rfl
  have hz := ISLP.zleafH_ok Λ h2 side e hx0 hx4 hs3 hs4 hsη
  have hjet := ISLP.sim3_tr3 hf hz prog k
  have hn := ISLP.tr3_nome hf hz prog
  rw [ISLP.eval_runExpr_getD, ← hjet, ISLP.jet3Val, hn]
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  rw [Nat.add_zero] at c0
  rw [c0, c1]
  ring

/-- **The value of a register is the cube of the nome times the last component of its jet**, when
the first three components vanish. -/
theorem h2_cube (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) (k : ℕ)
    (hc : ∀ j, j < 3 → (ISLP.runR (hAtoms Λ) side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + j) 0 = 0) :
    ISLP.eval (hAtoms Λ) side e ((ISLP.runExpr prog []).getD k (.cst 0)) =
      (if side then e.a else e.b) ^ 3 *
        (ISLP.runR (hAtoms Λ) side e (ISLP.tr3 (ISLP.zleafH Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k 1 + 3) 0 := by
  have hf : (hAtoms Λ).getD 0 (fun _ => 0) = id := rfl
  have hz := ISLP.zleafH_ok Λ h2 side e hx0 hx4 hs3 hs4 hsη
  have hjet := ISLP.sim3_tr3 hf hz prog k
  have hn := ISLP.tr3_nome hf hz prog
  rw [ISLP.eval_runExpr_getD, ← hjet, ISLP.jet3Val, hn]
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  have c2 := hc 2 (by norm_num)
  rw [Nat.add_zero] at c0
  rw [c0, c1, c2]
  ring

/-- The first part in terms of the last register of `h2Prog`: `X = n² ρ₁`. -/
theorem h2_rho1 (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) (k₁ : ℕ)
    (hc : ∀ j, j < 2 → (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) 0 = 0) :
    ISLP.eval (hAtoms Λ) side e ((ISLP.runExpr prog []).getD k₁ (.cst 0)) =
      (if side then e.a else e.b) ^ 2 *
        (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := by
  have hlt := h2_jet_lt (prog := prog) h2 side e hx0 hx4 hs3 hs4 hsη k₁
  have hf : (hAtoms Λ).getD 0 (fun _ => 0) = id := rfl
  have hn := ISLP.tr3_nome hf (ISLP.zleafH_ok Λ h2 side e hx0 hx4 hs3 hs4 hsη) prog
  rw [runR_h2Prog_getD_rho _ _ _ _ _ _ hlt, hn]
  refine h2_sq h2 side e hx0 hx4 hs3 hs4 hsη k₁ fun j hj => ?_
  rw [← runR_h2Prog_getD_lt (hAtoms Λ) side e Λ prog k₁ (by omega)]
  exact hc j hj

/-- The second part in terms of the registers of `h2Prog`: `X = n³ ρ₂`. -/
theorem h2_rho2 (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) (k₁ k₀ : ℕ)
    (hc : ∀ j, j < 3 → (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) 0 = 0) :
    ISLP.eval (hAtoms Λ) side e ((ISLP.runExpr prog []).getD k₀ (.cst 0)) =
      (if side then e.a else e.b) ^ 3 *
        (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := by
  have hlt := h2_jet_lt (prog := prog) h2 side e hx0 hx4 hs3 hs4 hsη k₀
  rw [runR_h2Prog_getD_lt (hAtoms Λ) side e Λ prog k₁ hlt]
  refine h2_cube h2 side e hx0 hx4 hs3 hs4 hsη k₀ fun j hj => ?_
  rw [← runR_h2Prog_getD_lt (hAtoms Λ) side e Λ prog k₁ (by omega)]
  exact hc j hj

end Jets

/-! ## The sign of the truncated kernel -/

/-- The fifteen atoms as an extension of the atoms of the kernel. -/
theorem hAtoms_eq (Λ : ℕ) : hAtoms Λ = kernelAtoms Λ ++ (red3Atoms Λ ++ [lam2Eta Λ]) :=
  List.append_assoc _ _ _

/-- The real-number core: `c Δ N (K − E) = b² δ S` with `N/δ > 0` and `S > 0`. -/
theorem trunc_lt_of_split {c Δ N δ K E b S : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hN : 0 < N / δ)
    (hb : 0 < b) (hS : 0 < S) (h : c * Δ * N * (K - E) = b ^ 2 * δ * S) : E < K := by
  have hδ : δ ≠ 0 := by
    rintro rfl
    simp at hN
  have e := div_mul_cancel₀ N hδ
  have h2 : (c * Δ * (N / δ) * (K - E) - b ^ 2 * S) * δ = 0 := by
    linear_combination h + (c * Δ * (K - E)) * e
  have h' : c * Δ * (N / δ) * (K - E) = b ^ 2 * S := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hδ
  have hpos : 0 < c * Δ * (N / δ) := by positivity
  have hprod : 0 < c * Δ * (N / δ) * (K - E) := by
    rw [h']
    positivity
  have := (pos_iff_pos_of_mul_pos hprod).mp hpos
  linarith

section Sign

variable {Λ : ℕ} {prog : List IInstr} {k₁ k₀ : ℕ}

/-- **The truncated inequality (6.4)(2) at a point** from the positivity of the split divided
difference `t̂ · ρ₁[a, b] + b · ρ₂[a, b]`. -/
theorem leechHatTrunc_of_dd (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ) {u t : ℝ} (hu : 0 < u)
    (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hsmall : NomeSmallH (axisNEnv u t))
    (hc₁ : ∀ side : Bool, ∀ j, j < 2 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) 0 = 0)
    (hc₀ : ∀ side : Bool, ∀ j, j < 3 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) 0 = 0)
    (hDD : 0 < (axisNEnv u t).t *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0) /
          ((axisNEnv u t).b - (axisNEnv u t).a)) +
      (axisNEnv u t).b *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0) /
          ((axisNEnv u t).b - (axisNEnv u t).a))) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re) <
      (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  obtain ⟨⟨ha4, hb4, ha3s, ha4s, hb3s, hb4s⟩, haη, hbη⟩ := hsmall
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  -- the two parts on the two sides
  have hB1 := h2_rho1 (prog := prog) h2 false (axisNEnv u t) hb.le hb4 hb3s hb4s hbη k₁ (hc₁ false)
  have hA1 := h2_rho1 (prog := prog) h2 true (axisNEnv u t) ha.le ha4 ha3s ha4s haη k₁ (hc₁ true)
  have hB0 := h2_rho2 (prog := prog) h2 false (axisNEnv u t) hb.le hb4 hb3s hb4s hbη k₁ k₀
    (hc₀ false)
  have hA0 := h2_rho2 (prog := prog) h2 true (axisNEnv u t) ha.le ha4 ha3s ha4s haη k₁ k₀
    (hc₀ true)
  rw [hp₁] at hB1 hA1
  rw [hp₀] at hB0 hA0
  have z1 : IExpr.evalA (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = 0 := by
    rw [hAtoms_eq]
    exact leechH21E_evalA Λ _ _
  have z0 : IExpr.evalA (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = 0 := by
    rw [hAtoms_eq]
    exact leechH20E_evalA Λ _ _
  have hA1' : (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 = 0 := by
    have h : IExpr.evalA (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = (axisNEnv u t).a ^ 2 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hA1
    rw [z1] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 ha.ne')
  have hA0' : (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 = 0 := by
    have h : IExpr.evalA (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = (axisNEnv u t).a ^ 3 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hA0
    rw [z0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 ha.ne')
  rw [hA1', hA0', sub_zero, sub_zero] at hDD
  have hB1' : IExpr.evalB (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = (axisNEnv u t).b ^ 2 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hB1
  have hB0' : IExpr.evalB (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = (axisNEnv u t).b ^ 3 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hB0
  -- the numerator and the denominator
  have hax := leechH2_eval_axis Λ (red3Atoms Λ ++ [lam2Eta Λ]) hu ht hJ
  rw [← hAtoms_eq, hB0', hB1'] at hax
  have hden : 0 < axNu (axV u) (axW u) (axV t) (axW t) /
      ((axisNEnv u t).b - (axisNEnv u t).a) := ckmrvAxisDividedDenominator_pos hu ht hut hprod
  have hδ : (axisNEnv u t).b - (axisNEnv u t).a ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hden
    exact lt_irrefl _ hden
  have hc0 : (0 : ℝ) < 21743271936 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 := by positivity
  refine trunc_lt_of_split hc0 (axDelta_pos ht) hden hb hDD ?_
  rw [← hax]
  field_simp
  ring

/-! ## The models -/

/-- What the certificate provides: the first two components of the jet of the register `k₁` and
the first three of the jet of the register `k₀` vanish, `T₁`, `T₂` are models of the divided
differences of `ρ₁`, `ρ₂`, and the nomes are small. -/
structure LeechH2Models (Bx : Bounds) (Λ : ℕ) (prog : List IInstr) (k₁ k₀ : ℕ) (T₁ T₂ : MTM) :
    Prop where
  zero₁ : ∀ (side : Bool) (j : ℕ), j < 2 → ∀ e, Bx.Mem e →
    (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) 0 = 0
  zero₀ : ∀ (side : Bool) (j : ℕ), j < 3 → ∀ e, Bx.Mem e →
    (ISLP.runR (hAtoms Λ) side e (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) 0 = 0
  dd₁ : T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) fun e =>
    ((ISLP.runR (hAtoms Λ) false e (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 -
      (ISLP.runR (hAtoms Λ) true e (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0) / (e.b - e.a)
  dd₀ : T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) fun e =>
    ((ISLP.runR (hAtoms Λ) false e (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 -
      (ISLP.runR (hAtoms Λ) true e (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0) / (e.b - e.a)
  small : ∀ e, Bx.Mem e → NomeSmallH e

/-- **The facts from a checked run of the transformed program.** -/
theorem leechH2Models_of_run {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) {D Dcap N' NE' : ℕ}
    (hR : RedHOK Bx D Dcap N' NE') {Λ n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n + 3 → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k₁ k₀ : ℕ)
    (hz₁ : ∀ j, j < 2 → (ISLP.runMDD Bx D Dcap (hAtomModels Bx D Dcap Λ n K N NE N' NE')
      (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) MDD.zero = MDD.zero)
    (hz₀ : ∀ j, j < 3 → (ISLP.runMDD Bx D Dcap (hAtomModels Bx D Dcap Λ n K N NE N' NE')
      (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) MDD.zero = MDD.zero) :
    LeechH2Models Bx Λ prog k₁ k₀
      ((ISLP.runMDD Bx D Dcap (hAtomModels Bx D Dcap Λ n K N NE N' NE')
        (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) MDD.zero).D
      ((ISLP.runMDD Bx D Dcap (hAtomModels Bx D Dcap Λ n K N NE N' NE')
        (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) MDD.zero).D := by
  have hB : Bx.Valid := hG.1.1
  have hAt : ISLP.AtomsOK Bx (fun _ => True) (hAtomModels Bx D Dcap Λ n K N NE N' NE')
      (hAtoms Λ) := hAtoms_ok hG hR K N hΛ hL
  refine ⟨fun side j hj e he => ?_, fun side j hj e he => ?_, ?_, ?_, fun e he => ?_⟩
  · have h := ISLP.approx_run hB D Dcap hAt (ISLP.h2Prog Λ prog k₁)
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j)
    rw [hz₁ j hj] at h
    cases side
    · exact MTM.eq_zero_of_approx h.2.1 he trivial
    · exact MTM.eq_zero_of_approx h.1 he trivial
  · have h := ISLP.approx_run hB D Dcap hAt (ISLP.h2Prog Λ prog k₁)
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j)
    rw [hz₀ j hj] at h
    cases side
    · exact MTM.eq_zero_of_approx h.2.1 he trivial
    · exact MTM.eq_zero_of_approx h.1 he trivial
  · exact (ISLP.approx_run hB D Dcap hAt (ISLP.h2Prog Λ prog k₁)
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1)).2.2
  · exact (ISLP.approx_run hB D Dcap hAt (ISLP.h2Prog Λ prog k₁)
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3)).2.2
  · obtain ⟨⟨hS, -, h3, h4⟩, hη⟩ := hR
    obtain ⟨-, hsa, hsb, -⟩ := hS
    have hS' : SeriesOK Bx 4 := hG.1
    have had : (0 : ℝ) < Bx.ad := by exact_mod_cast hB.1
    have hbd : (0 : ℝ) < Bx.bd := by exact_mod_cast hB.2.1
    have hsa' : (4 : ℝ) * Bx.an < Bx.ad := by exact_mod_cast hsa
    have hsb' : (4 : ℝ) * Bx.bn < Bx.bd := by exact_mod_cast hsb
    have hea : e.a * Bx.ad ≤ Bx.an := he.2.1
    have heb : e.b * Bx.bd ≤ Bx.bn := he.2.2.2.1
    have small : ∀ {d : MDD} {f : ℝ → ℝ}, d.Approx Bx (fun _ => True) (fun e => f e.a)
        (fun e => f e.b) → MDD.RLogOK Bx D Dcap d → |e.a * f e.a| < 1 ∧ |e.b * f e.b| < 1 := by
      intro d f hd hok
      have hza := MTM.approx_mul hB D Dcap (MDD.approx_nomeA (Bx := Bx) (S := fun _ => True)) hd.1
      have hzb := MTM.approx_mul hB D Dcap (MDD.approx_nomeB (Bx := Bx) (S := fun _ => True))
        hd.2.1
      have h1 := MTM.abs_le_absMaj hB hza he trivial
      have h2 := MTM.absMaj_le_half hB hok.1 he
      have h3 := MTM.abs_le_absMaj hB hzb he trivial
      have h4 := MTM.absMaj_le_half hB hok.2.1 he
      exact ⟨by linarith, by linarith⟩
    obtain ⟨a3, b3⟩ := small (approx_devTheta3MDD hS' N' (S := fun _ => True)) h3
    obtain ⟨a4, b4⟩ := small (approx_devTheta4MDD hS' N' (S := fun _ => True)) h4
    obtain ⟨aη, bη⟩ := small (approx_devEtaMDD hS' D Dcap N' (S := fun _ => True)) hη
    refine ⟨⟨?_, ?_, a3, a4, b3, b4⟩, aη, bη⟩
    · have h : 4 * e.a * Bx.ad < 1 * Bx.ad := by nlinarith
      exact lt_of_mul_lt_mul_right h had.le
    · have h : 4 * e.b * Bx.bd < 1 * Bx.bd := by nlinarith
      exact lt_of_mul_lt_mul_right h hbd.le

/-! ## Cells and covers -/

/-- **The truncated inequality on a cell.** A cell inside the bounds of the models that passes
the vertex check (pivots `a⁴b` and `a⁵`) contains no point `(u, t)` with `ut > 1`, `u ≠ t` where
the truncated inequality fails. -/
theorem leechHatTrunc_of_cell {Bx : Bounds} {T₁ T₂ : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hPB : (T₁.quots 4 0).PB.MultiAffine) (hPA : (T₁.quots 4 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots 4 0).marginBv C p q r + w * min ((T₂.quots 4 0).marginB C) 0)
        ((T₁.quots 4 0).marginAv C p q r + w * min ((T₂.quots 4 0).marginA C) 0) 0)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t) (hprod : 1 < u * t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re) <
      (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  have hBx : Bx.Mem (axisNEnv u t) := Bounds.mem_of_le hC.2 hsub hmem.2.2.2.2.2
  exact leechHatTrunc_of_dd hΛ h2 hp₁ hp₀ hu ht hut hprod hJ (hM.small _ hBx)
    (fun side j hj => hM.zero₁ side j hj _ hBx) (fun side j hj => hM.zero₀ side j hj _ hBx)
    (combination_pos_vertex hM.dd₁ hM.dd₀ hd₁ hd₂ hPB hPA hC hsub hw hOK ht hut hmem)

/-- **The truncated inequality on a cover**, in reciprocal coordinates, outside the corner. -/
theorem leechHatTrunc_of_cover {Bx : Bounds} {T₁ T₂ : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 4 0 = Q₁) (hQ₂ : T₂.quots 4 0 = Q₂)
    (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c : ℚ} {cov : Cover}
    {r : Rect} (hcov : cov.check (cellOKb k n) (vertexCellOK Bx Q₁ Q₂) c r = true) {u t : ℝ}
    (hu : 0 < u) (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t)
    (hprod : 1 < u * t) (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨
      Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re) <
        (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  subst hQ₁ hQ₂
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 0 < u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      1 < u * t → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) →
      Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re) <
        (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re)
    (cellOKb_spec k n)
    (fun C w _ hC hok x y _ _ hmem u t hu ht hxu hyt hut hprod hJ => by
      simp only [vertexCellOK, decide_eq_true_eq] at hok
      refine leechHatTrunc_of_cell hΛ h2 hp₁ hp₀ hM hd₁ hd₂ hPB hPA hC hok.1 hok.2.1 hok.2.2 hu ht
        hut hprod hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hprod hJ)

/-- **The truncated inequality for `u, t ≥ 1` outside a corner box.** The cover is one of the
reciprocal square `[0, x₁]²` with `1/π ≤ x₁`; its corner `x, y ≥ c` lies inside `u, t ≤ c₀`. -/
theorem leechHatTrunc_of_cover_ge_one {Bx : Bounds} {T₁ T₂ : MTM} (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 4 0 = Q₁) (hQ₂ : T₂.quots 4 0 = Q₂)
    (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKb k n) (vertexCellOK Bx Q₁ Q₂) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {u t : ℝ}
    (hu : 1 ≤ u) (ht : 1 ≤ t) (hut : u ≠ t) (hout : c₀ < u ∨ c₀ < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re) <
      (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
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
  rcases leechHatTrunc_of_cover hΛ h2 hp₁ hp₀ hM hd₁ hd₂ hQ₁ hQ₂ hPB hPA hcov hu0 ht0 hr hut hprod
    hJ with h | h
  · rcases hout with h' | h'
    · exact absurd (hcorner u hu0 h.1) (not_le.mpr h')
    · exact absurd (hcorner t ht0 h.2) (not_le.mpr h')
  · exact h

end Sign

end E8Leech.Kron
