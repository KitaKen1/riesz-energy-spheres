import E8Leech.KronJet

/-!
# The corner certificate on a grid of intervals

`CornerPos` is the positivity of a bilinear form `Σ_k A_k(u) H_k(t)` of seven functions of `u` and
seven functions of `t` on a square. Each of the fourteen functions is enclosed on every interval of
a grid: the `A_k` by the interval run of a program (`KronInterval`), the second-derivative
expressions `H_k = hOf B_k` by the jet run of the program of the `B_k` (`KronJet`). The enclosures
are compared once with rounded tables, and the tables are then paired.

* `QI.round`, `IEnv.round`: outward rounding to dyadic endpoints, to keep the numbers short.
* `bilLo`, `bilLo_le`: a lower bound of the pairing of two lists of intervals.
* `GCell`, `intervalOK`, `mem_of_intervalOK`: an interval of the grid and its two tables.
* `coverOK`, `exists_of_coverOK`: the intervals cover a segment.
* `cornerPos_of_grid`: the certificate.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## Rounding -/

namespace QI

/-- The interval rounded outward to multiples of `2⁻ᵖ`. -/
def round (p : ℕ) (I : QI) : QI :=
  ⟨(⌊I.lo * 2 ^ p⌋ : ℤ) / 2 ^ p, (⌈I.hi * 2 ^ p⌉ : ℤ) / 2 ^ p⟩

theorem mem_round (p : ℕ) {I : QI} {v : ℝ} (h : I.Mem v) : (I.round p).Mem v := by
  have h2 : (0 : ℚ) < 2 ^ p := by positivity
  have hlo : ((⌊I.lo * 2 ^ p⌋ : ℤ) : ℚ) / 2 ^ p ≤ I.lo :=
    (div_le_iff₀ h2).mpr (Int.floor_le _)
  have hhi : I.hi ≤ ((⌈I.hi * 2 ^ p⌉ : ℤ) : ℚ) / 2 ^ p :=
    (le_div_iff₀ h2).mpr (Int.le_ceil _)
  exact ⟨(Rat.cast_le.mpr hlo).trans h.1, h.2.trans (Rat.cast_le.mpr hhi)⟩

/-- `I` lies inside `J`. -/
def within (I J : QI) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

theorem mem_of_within {I J : QI} (h : I.within J = true) {v : ℝ} (hv : I.Mem v) : J.Mem v := by
  have h' : J.lo ≤ I.lo ∧ I.hi ≤ J.hi := of_decide_eq_true h
  exact ⟨(Rat.cast_le.mpr h'.1).trans hv.1, hv.2.trans (Rat.cast_le.mpr h'.2)⟩

end QI

/-- The atom enclosures rounded outward. -/
def IEnv.round (p : ℕ) (E : IEnv) : IEnv :=
  ⟨fun i => (E.za i).round p, fun i => (E.ta i).round p, E.va, E.vb, E.vu, E.vt, E.vl⟩

theorem IEnv.sound_round (p : ℕ) {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (h : E.Sound fs e) :
    (E.round p).Sound fs e :=
  ⟨fun i => QI.mem_round p (h.1 i), fun i => QI.mem_round p (h.2.1 i), h.2.2⟩

/-! ## Pairing lists of intervals -/

/-- A lower bound of the pairing of two lists of intervals. -/
def bilLo : List QI → List QI → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | I :: Is, J :: Js => (I.mul J).lo + bilLo Is Js

theorem bilLo_le {Is Js : List QI} {vs ws : List ℝ} (h1 : List.Forall₂ QI.Mem Is vs)
    (h2 : List.Forall₂ QI.Mem Js ws) : ((bilLo Is Js : ℚ) : ℝ) ≤ bil vs ws := by
  induction h1 generalizing Js ws with
  | nil => simp [bilLo, bil]
  | cons hv _ ih =>
    cases h2 with
    | nil => simp [bilLo, bil]
    | cons hw h2' =>
      simp only [bilLo, bil]
      rw [Rat.cast_add]
      exact add_le_add (QI.mem_mul hv hw).1 (ih h2')

/-- Componentwise containment of two lists of intervals of the same length. -/
def withinAll : List QI → List QI → Bool
  | [], [] => true
  | I :: Is, J :: Js => I.within J && withinAll Is Js
  | _, _ => false

theorem forall₂_of_withinAll : ∀ (Is Js : List QI) (vs : List ℝ), withinAll Is Js = true →
    List.Forall₂ QI.Mem Is vs → List.Forall₂ QI.Mem Js vs
  | [], [], _, _, h => by
    cases h
    exact List.Forall₂.nil
  | I :: Is, J :: Js, _, hw, h => by
    cases h with
    | cons hv h' =>
      simp only [withinAll, Bool.and_eq_true] at hw
      exact List.Forall₂.cons (QI.mem_of_within hw.1 hv) (forall₂_of_withinAll Is Js _ hw.2 h')
  | [], _ :: _, _, hw, _ => by simp [withinAll] at hw
  | _ :: _, [], _, hw, _ => by simp [withinAll] at hw

/-- The interval run encloses the values of the expressions at the listed registers. -/
theorem forall₂_mem_run {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e)
    (prog : List IInstr) :
    ∀ ks : List ℕ, List.Forall₂ QI.Mem (ks.map fun k => (ISLP.runI E prog []).getD k QI.zero)
      (ks.map fun k => IExpr.evalB fs ((ISLP.runExpr prog []).getD k (.cst 0)) e)
  | [] => List.Forall₂.nil
  | k :: ks =>
    List.Forall₂.cons (ISLP.mem_runI_expr hE prog k _ rfl) (forall₂_mem_run hE prog ks)

/-- The jet run encloses `hOf` of the expressions at the listed registers. -/
theorem forall₂_mem_runH {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e) (Λ : ℕ)
    (prog : List IInstr) :
    ∀ ks : List ℕ, List.Forall₂ QI.Mem
      (ks.map fun k => ((ISLP.runJ Λ E prog []).getD k QJ.zero).hOf E)
      (ks.map fun k => IExpr.evalB fs (IExpr.hOf Λ ((ISLP.runExpr prog []).getD k (.cst 0))) e)
  | [] => List.Forall₂.nil
  | k :: ks =>
    List.Forall₂.cons (QJ.mem_hOf hE (ISLP.mem_runJ hE prog k)) (forall₂_mem_runH hE Λ prog ks)

/-! ## An interval of the grid -/

/-- An interval `[x0, x1]` of reciprocal parameters and a cell that encloses its diagonal square. -/
structure GCell where
  x0 : ℚ
  x1 : ℚ
  C : Cell

/-- The interval enclosures of the listed registers of a program on an interval of the grid. -/
def gridVals (p : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : GCell) : List QI :=
  ks.map fun k => (ISLP.runI ((IEnv.ofCell At g.C).round p) prog []).getD k QI.zero

/-- The enclosures of `hOf` of the listed registers of a program on an interval of the grid, from
the jet run. -/
def gridValsH (p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : GCell) :
    List QI :=
  ks.map fun k => ((ISLP.runJ Λ ((IEnv.ofCell At g.C).round p) prog []).getD k QJ.zero).hOf
    ((IEnv.ofCell At g.C).round p)

/-- The cell encloses the interval, lies inside the bounds of the models, and the two tables
contain the enclosures of the `τ`-side program and of `hOf` of the `z`-side program. -/
def intervalOK (k n p Λ : ℕ) (Bx : Bounds) (At : List MDD) (progT progZ : List IInstr)
    (kT kZ : List ℕ) (g : GCell) (TA TZ : List QI) : Bool :=
  cellOKb k n ⟨g.x0, g.x1, g.x0, g.x1⟩ g.C && decide (g.C.hi.le Bx) &&
    withinAll (gridVals p At progT kT g) TA && withinAll (gridValsH p Λ At progZ kZ g) TZ

section Interval

variable {Bx : Bounds} {At : List MDD} {Λ : ℕ} {progT progZ : List IInstr} {kT kZ : List ℕ}

/-- The tables of a checked interval contain the values of the fourteen functions. -/
theorem mem_of_intervalOK (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hT : (kT.map fun k => (ISLP.runExpr progT []).getD k (.cst 0)) = tauE Λ)
    (hZ : (kZ.map fun k => (ISLP.runExpr progZ []).getD k (.cst 0)) = zE Λ)
    {k n p : ℕ} {g : GCell} {TA TZ : List QI}
    (h : intervalOK k n p Λ Bx At progT progZ kT kZ g TA TZ = true) {u : ℝ} (hu : 0 < u)
    (h0 : (g.x0 : ℝ) ≤ 1 / (π * u)) (h1 : 1 / (π * u) ≤ g.x1) :
    List.Forall₂ QI.Mem TA (tauVals Λ u) ∧ List.Forall₂ QI.Mem TZ (zVals Λ u) := by
  simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hcell, hsub⟩, hwT⟩, hwZ⟩ := h
  obtain ⟨hC, hmem⟩ := cellOKb_spec k n _ _ hcell
  have hx : 0 < 1 / (π * u) := by
    have hπ := Real.pi_pos
    positivity
  have hr : (⟨g.x0, g.x1, g.x0, g.x1⟩ : Rect).Mem (1 / (π * u)) (1 / (π * u)) := ⟨h0, h1, h0, h1⟩
  have he : g.C.Mem (axisNEnv u u) := by
    rw [axisNEnv_eq_recNEnv]
    exact hmem _ _ hx hx hr
  have hE := IEnv.sound_round p (IEnv.sound_ofCell hAt hC hsub he)
  have eT : tauVals Λ u = kT.map fun k => IExpr.evalB (kernelAtoms Λ ++ [])
      ((ISLP.runExpr progT []).getD k (.cst 0)) (axisNEnv u u) := by
    rw [tauVals, ← hT, List.map_map]
    rfl
  have eZ : zVals Λ u = kZ.map fun k => IExpr.evalB (kernelAtoms Λ ++ [])
      (IExpr.hOf Λ ((ISLP.runExpr progZ []).getD k (.cst 0))) (axisNEnv u u) := by
    rw [zVals, ← hZ, List.map_map]
    rfl
  rw [eT, eZ]
  exact ⟨forall₂_of_withinAll _ _ _ hwT (forall₂_mem_run hE progT kT),
    forall₂_of_withinAll _ _ _ hwZ (forall₂_mem_runH hE Λ progZ kZ)⟩

end Interval

/-! ## Covers of a segment -/

/-- The intervals cover `[lo, hi]`: each starts at or before the end of the previous one, and
the last one ends after `hi`. -/
def coverOK (hi : ℚ) : ℚ → List GCell → Bool
  | lo, [] => decide (hi < lo)
  | lo, g :: gs => decide (g.x0 ≤ lo) && coverOK hi g.x1 gs

theorem exists_of_coverOK {hi : ℚ} : ∀ (lo : ℚ) (gs : List GCell), coverOK hi lo gs = true →
    ∀ x : ℝ, (lo : ℝ) ≤ x → x ≤ hi → ∃ g ∈ gs, (g.x0 : ℝ) ≤ x ∧ x ≤ g.x1
  | lo, [], h, x, h1, h2 => by
    have h' : hi < lo := of_decide_eq_true h
    have h'' : (hi : ℝ) < lo := Rat.cast_lt.mpr h'
    linarith
  | lo, g :: gs, h, x, h1, h2 => by
    simp only [coverOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have h0 : (g.x0 : ℝ) ≤ lo := Rat.cast_le.mpr h.1
    rcases le_total x (g.x1 : ℝ) with hx | hx
    · exact ⟨g, List.mem_cons_self, h0.trans h1, hx⟩
    · obtain ⟨g', hg', hb⟩ := exists_of_coverOK g.x1 gs h.2 x hx h2
      exact ⟨g', List.mem_cons_of_mem _ hg', hb⟩

/-! ## The certificate -/

/-- All pairs of a table of `τ`-side enclosures and a table of `z`-side enclosures have a positive
lower bound. -/
def pairOK (TAs TZs : List (List QI)) : Bool :=
  TAs.all fun a => TZs.all fun z => decide (0 < bilLo a z)

/-- **The corner certificate from a grid.** Every interval carries a cell and two tables; the
intervals cover the reciprocals of `[1/c₀, c₀]`; all pairs of tables are positive. -/
theorem cornerPos_of_grid {Bx : Bounds} {At : List MDD} {Λ : ℕ} {progT progZ : List IInstr}
    {kT kZ : List ℕ} (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hT : (kT.map fun k => (ISLP.runExpr progT []).getD k (.cst 0)) = tauE Λ)
    (hZ : (kZ.map fun k => (ISLP.runExpr progZ []).getD k (.cst 0)) = zE Λ)
    {k n p : ℕ} {gs : List (GCell × List QI × List QI)}
    (hint : ∀ g ∈ gs, intervalOK k n p Λ Bx At progT progZ kT kZ g.1 g.2.1 g.2.2 = true)
    (hpair : pairOK (gs.map fun g => g.2.1) (gs.map fun g => g.2.2) = true) {lo hi : ℚ}
    (hcov : coverOK hi lo (gs.map fun g => g.1) = true) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlo : (lo : ℝ) ≤ 1 / (π * c₀)) (hhi : c₀ / π ≤ hi) : CornerPos Λ c₀ := by
  have hπ := Real.pi_pos
  have key : ∀ v : ℝ, c₀⁻¹ ≤ v → v ≤ c₀ → ∃ g ∈ gs, List.Forall₂ QI.Mem g.2.1 (tauVals Λ v) ∧
      List.Forall₂ QI.Mem g.2.2 (zVals Λ v) := by
    intro v hv hv'
    have hv0 : 0 < v := (inv_pos.mpr hc₀).trans_le hv
    have h1 : (lo : ℝ) ≤ 1 / (π * v) := by
      refine hlo.trans ?_
      exact one_div_le_one_div_of_le (mul_pos hπ hv0) (mul_le_mul_of_nonneg_left hv' hπ.le)
    have h2 : 1 / (π * v) ≤ hi := by
      refine le_trans ?_ hhi
      rw [div_le_div_iff₀ (mul_pos hπ hv0) hπ]
      have h3 : 1 ≤ c₀ * v := by
        have h4 := mul_le_mul_of_nonneg_left hv hc₀.le
        rwa [mul_inv_cancel₀ hc₀.ne'] at h4
      nlinarith [mul_nonneg hπ.le (sub_nonneg.mpr h3)]
    obtain ⟨g0, hg0, hb⟩ := exists_of_coverOK lo _ hcov _ h1 h2
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg0
    exact ⟨g, hg, mem_of_intervalOK hAt hT hZ (hint g hg) hv0 hb.1 hb.2⟩
  intro u t hu hu' ht ht'
  obtain ⟨gu, hgu, hTu, -⟩ := key u hu hu'
  obtain ⟨gt, hgt, -, hZt⟩ := key t ht ht'
  have hp : 0 < bilLo gu.2.1 gt.2.2 := by
    simp only [pairOK, List.all_eq_true, decide_eq_true_eq] at hpair
    exact hpair _ (List.mem_map.mpr ⟨gu, hgu, rfl⟩) _ (List.mem_map.mpr ⟨gt, hgt, rfl⟩)
  have hp' : (0 : ℝ) < ((bilLo gu.2.1 gt.2.2 : ℚ) : ℝ) := by exact_mod_cast hp
  exact lt_of_lt_of_le hp' (bilLo_le hTu hZt)

end E8Leech.Kron
