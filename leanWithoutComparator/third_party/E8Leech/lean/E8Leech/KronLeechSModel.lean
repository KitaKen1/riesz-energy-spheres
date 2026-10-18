import E8Leech.KronLeechSignS
import E8Leech.KronStages

/-!
# The certificates of the Leech kernels with the second variable inverted

The sign theorems of `KronLeechSignS` need three facts about the transformed program of a pairing:
the first three components of its jet vanish, the divided difference of the last component is
positive, and the nomes are small. Here they are obtained from a checked run of the program on the
models of the fourteen atoms: zero models give zero values, the model of the divided difference
with the pivots `a⁴b`, `a⁵` decides its sign on a cell, and the smallness follows from the checks
of the atoms.

* `MTM.logRatioSh_eq_of`, `MTM.logRatioShDD_eq_of`, `MDD.rlogSh_eq_of`, `tAtomModels_eq_of`: the
  atoms from their parts, for staged kernel checks.
* `LeechSModels`, `leechSModels_of_run`: the facts from a checked run.
* `leechHatKernel_pos_of_rs_cell`, `leechKernelK_neg_of_ss_cell`: the signs on a cell.
* `leechKernel_pos_of_coverRS`, `leechKernel_pos_of_coverSS`: positivity of the hat kernel for
  `t ≤ 1 ≤ q` and for `q, t ≤ 1`, outside a corner box.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly
open scoped Real

/-! ## The atoms from their parts -/

namespace MTM

/-- `Λ ℓ_j` from its Horner chain and the powers of its majorant. -/
theorem logRatioSh_eq_of {B : Bounds} {D Dcap Λ n j : ℕ} {T H R : MTM} {cs : List ℤ}
    {G P : IPoly} (hc : logRatioShCoeffs Λ n j = cs) (hH : horner B D Dcap T cs = H)
    (hG : absMaj B T = G) (hP : powMaj B Dcap G n = P)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale ((2 * Λ : ℕ) : ℤ) P)⟩ : MTM) = R) :
    logRatioSh B D Dcap Λ n j T = R := by
  subst hc hH hG hP hR
  rfl

/-- The divided difference of `Λ ℓ_j` from its chain and the powers of its majorant. -/
theorem logRatioShDD_eq_of {B : Bounds} {D Dcap Λ n j : ℕ} {P Q H R : MTM} {cs : List ℤ}
    {G M : IPoly} (hc : logRatioShDDCoeffs Λ n j = cs)
    (hH : hsumAux B D Dcap P Q cs (const 1) (const 1) zero = H)
    (hG : IPoly.add (absMaj B P) (absMaj B Q) = G) (hM : powMaj B Dcap G n = M)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale ((2 * Λ : ℕ) : ℤ) M)⟩ : MTM) = R) :
    logRatioShDD B D Dcap Λ n j P Q = R := by
  subst hc hH hG hM hR
  rfl

end MTM

namespace MDD

/-- The atom `Λ ℓ_j(x d)` from its parts. -/
theorem rlogSh_eq_of {Bx : Bounds} {D Dcap Λ n j : ℕ} {d : MDD} {PA PB A B RD S2 Dd : MTM}
    (hPA : MTM.mul Bx D Dcap nomeA d.A = PA) (hPB : MTM.mul Bx D Dcap nomeB d.B = PB)
    (hA : MTM.logRatioSh Bx D Dcap Λ n j PA = A) (hB : MTM.logRatioSh Bx D Dcap Λ n j PB = B)
    (hRD : MTM.logRatioShDD Bx D Dcap Λ n j PA PB = RD)
    (hS2 : d.B.add (MTM.mul Bx D Dcap nomeA d.D) = S2) (hD : MTM.mul Bx D Dcap S2 RD = Dd) :
    rlogSh Bx D Dcap Λ n j d = ⟨A, B, Dd⟩ := by
  subst hPA hPB hA hB hRD hS2 hD
  rfl

end MDD

/-- The fourteen models of the third-order atoms from their entries. -/
theorem tAtomModels_eq_of {Bx : Bounds} {D Dcap Λ n K N NE N' NE' : ℕ}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : MDD}
    (h : kernelAtomModels Bx D Dcap Λ n K N NE = [a0, a1, a2, a3, a4, a5, a6, a7])
    (h8 : delta3MDD Bx N' = a8) (h9 : delta4MDD Bx N' = a9) (h10 : deltaEtaMDD Bx N' = a10)
    (h11 : etE2MDD Bx NE' = a11)
    (h12 : MDD.rlogSh Bx D Dcap Λ n 2 (devTheta3MDD Bx N') = a12)
    (h13 : MDD.rlogSh Bx D Dcap Λ n 2 (devTheta4MDD Bx N') = a13) :
    tAtomModels Bx D Dcap Λ n K N NE N' NE' =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13] := by
  subst h8 h9 h10 h11 h12 h13
  rw [tAtomModels, h]
  rfl

/-! ## The facts from a checked run -/

/-- What the certificate of a pairing provides: the first three components of the jet of the
register `k` vanish, `T` is a model of the divided difference of the last component, and the
nomes are small. -/
structure LeechSModels (Bx : Bounds) (Λ : ℕ) (prog : List IInstr) (k : ℕ) (T : MTM) : Prop where
  zero : ∀ (side : Bool) (j : ℕ), j < 3 → ∀ e, Bx.Mem e →
    (ISLP.runR (tAtoms Λ) side e (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
      ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j) 0 = 0
  dd : T.Approx Bx (fun e => True ∧ e.a ≠ e.b) fun e =>
    ((ISLP.runR (tAtoms Λ) false e (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 -
      (ISLP.runR (tAtoms Λ) true e (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0) / (e.b - e.a)
  small : ∀ e, Bx.Mem e → NomeSmall e

/-- **The facts from a checked run of the transformed program.** -/
theorem leechSModels_of_run {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) {D Dcap N' NE' : ℕ}
    (hR : Red3OK Bx D Dcap N' NE') {Λ n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n + 3 → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) (prog : List IInstr) (k : ℕ)
    (hz : ∀ j, j < 3 → (ISLP.runMDD Bx D Dcap (tAtomModels Bx D Dcap Λ n K N NE N' NE')
      (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
        ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j) MDD.zero = MDD.zero) :
    LeechSModels Bx Λ prog k
      ((ISLP.runMDD Bx D Dcap (tAtomModels Bx D Dcap Λ n K N NE N' NE')
        (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) MDD.zero).D := by
  have hB : Bx.Valid := hG.1.1
  have hAt : ISLP.AtomsOK Bx (fun _ => True) (tAtomModels Bx D Dcap Λ n K N NE N' NE')
      (tAtoms Λ) := tAtoms_ok hG hR K N hΛ hL
  refine ⟨fun side j hj e he => ?_, ?_, fun e he => ?_⟩
  · have h := ISLP.approx_run hB D Dcap hAt (ISLP.tr3 (ISLP.zleafL Λ) prog).1
      ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + j)
    rw [hz j hj] at h
    cases side
    · exact MTM.eq_zero_of_approx h.2.1 he trivial
    · exact MTM.eq_zero_of_approx h.1 he trivial
  · exact (ISLP.approx_run hB D Dcap hAt (ISLP.tr3 (ISLP.zleafL Λ) prog).1
      ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3)).2.2
  · obtain ⟨hS, -, h3, h4⟩ := hR
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
    refine ⟨?_, ?_, a3, a4, b3, b4⟩
    · have h : 4 * e.a * Bx.ad < 1 * Bx.ad := by nlinarith
      exact lt_of_mul_lt_mul_right h had.le
    · have h : 4 * e.b * Bx.bd < 1 * Bx.bd := by nlinarith
      exact lt_of_mul_lt_mul_right h hbd.le

/-! ## The signs on a cell -/

section Cell

variable {Bx : Bounds} {Λ : ℕ} {prog : List IInstr} {k : ℕ} {T : MTM}

theorem axisNEnvS_ne {u s : ℝ} (hus : u ≠ s) : (axisNEnvS u s).a ≠ (axisNEnvS u s).b := by
  intro h
  have h' : Real.exp (-π * u) = Real.exp (-π * s) := h
  exact hus (mul_left_cancel₀ (neg_ne_zero.mpr Real.pi_pos.ne') (Real.exp_injective h'))

/-- The divided difference of the last component of the jet is positive on a checked cell. -/
theorem leechS_dd_pos (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx)
    (hOK : C.PosOK ((T.quots 4 0).marginB C) ((T.quots 4 0).marginA C) 0) {u s : ℝ}
    (hus : u ≠ s) (hmem : C.Mem (axisNEnvS u s)) :
    0 < ((ISLP.runR (tAtoms Λ) false (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0 -
        (ISLP.runR (tAtoms Λ) true (axisNEnvS u s) (ISLP.tr3 (ISLP.zleafL Λ) prog).1 []).getD
          ((ISLP.tr3 (ISLP.zleafL Λ) prog).2.getD k 1 + 3) 0) /
        ((axisNEnvS u s).b - (axisNEnvS u s).a) := by
  have ha : 0 < (axisNEnvS u s).a := Real.exp_pos _
  have hb : 0 < (axisNEnvS u s).b := Real.exp_pos _
  have l := MTM.lower_of_divisible hM.dd hd hC hsub hmem ⟨trivial, axisNEnvS_ne hus⟩ ha.le hb.le
  have hkey := Cell.pos_of_posOK hC hOK hmem ha hb
  rw [Rat.cast_zero, add_zero] at hkey
  have hc : 0 < (axisNEnvS u s).a ^ 4 * (axisNEnvS u s).b ^ 0 := by positivity
  exact lt_of_lt_of_le (mul_pos hc hkey) l

/-- **Positivity of `𝒦̂⁽²⁴⁾(iu, i/s)` on a cell.** -/
theorem leechHatKernel_pos_of_rs_cell (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechRSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) (hOK : C.PosOK ((T.quots 4 0).marginB C) ((T.quots 4 0).marginA C) 0)
    {u s : ℝ} (hu : 0 < u) (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hmem : C.Mem (axisNEnvS u s)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt s⁻¹)).re := by
  have he : Bx.Mem (axisNEnvS u s) := Bounds.mem_of_le hC.2 hsub hmem.2.2.2.2.2
  exact leechHatKernel_pos_of_rs hΛ h2 hprog hu hs hus hprod hJ (hM.small _ he)
    (fun side j hj => hM.zero side j hj _ he) (leechS_dd_pos hM hd hC hsub hOK hus hmem)

/-- **Negativity of `𝒦⁽²⁴⁾(iu, i/s)` on a cell.** -/
theorem leechKernelK_neg_of_ss_cell (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechSSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) (hOK : C.PosOK ((T.quots 4 0).marginB C) ((T.quots 4 0).marginA C) 0)
    {u s : ℝ} (hu : 0 < u) (hs : 0 < s) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹))
    (hmem : C.Mem (axisNEnvS u s)) :
    (ckmrvLeechKernel (imagPt u) (imagPt s⁻¹)).re < 0 := by
  have he : Bx.Mem (axisNEnvS u s) := Bounds.mem_of_le hC.2 hsub hmem.2.2.2.2.2
  exact leechKernelK_neg_of_ss hΛ h2 hprog hu hs hus hprod hJ (hM.small _ he)
    (fun side j hj => hM.zero side j hj _ he) (leechS_dd_pos hM hd hC hsub hOK hus hmem)

/-! ## Covers -/

/-- **Positivity of `𝒦̂⁽²⁴⁾(iu, i/s)` on a cover**, in the reciprocal coordinates of `u` and `s`,
outside the corner. -/
theorem leechKernel_pos_of_cover_rs (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechRSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {Q : Quots} (hQ : T.quots 4 0 = Q)
    {kc n : ℕ} {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c r = true) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hr : r.Mem (1 / (π * u)) (1 / (π * s))) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * s)) ∨
      0 < (ckmrvLeechHatKernel (imagPt u) (imagPt s⁻¹)).re := by
  subst hQ
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * s) := by positivity
  have h := Cover.sound (env := recNEnvS)
    (P := fun x y => ∀ u s : ℝ, 0 < u → 0 < s → x = 1 / (π * u) → y = 1 / (π * s) → u ≠ s →
      1 < u * s → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹) →
      0 < (ckmrvLeechHatKernel (imagPt u) (imagPt s⁻¹)).re)
    (cellOKSb_spec kc n)
    (fun C _ _ hC hok x y _ _ hmem u s hu hs hxu hys hus hprod hJ => by
      simp only [sCellOK, decide_eq_true_eq] at hok
      refine leechHatKernel_pos_of_rs_cell hΛ h2 hprog hM hd hC hok.1 hok.2 hu hs hus hprod hJ ?_
      rw [axisNEnvS_eq_recNEnvS, ← hxu, ← hys]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u s hu hs rfl rfl hus hprod hJ)

/-- **Negativity of `𝒦⁽²⁴⁾(iu, i/s)` on a cover**, outside the corner. -/
theorem leechKernelK_neg_of_cover_ss (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechSSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {Q : Quots} (hQ : T.quots 4 0 = Q)
    {kc n : ℕ} {c : ℚ} {cov : Cover} {r : Rect}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c r = true) {u s : ℝ} (hu : 0 < u)
    (hs : 0 < s) (hr : r.Mem (1 / (π * u)) (1 / (π * s))) (hus : u ≠ s) (hprod : 1 < u * s)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * s)) ∨
      (ckmrvLeechKernel (imagPt u) (imagPt s⁻¹)).re < 0 := by
  subst hQ
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * s) := by positivity
  have h := Cover.sound (env := recNEnvS)
    (P := fun x y => ∀ u s : ℝ, 0 < u → 0 < s → x = 1 / (π * u) → y = 1 / (π * s) → u ≠ s →
      1 < u * s → kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt s⁻¹) →
      (ckmrvLeechKernel (imagPt u) (imagPt s⁻¹)).re < 0)
    (cellOKSb_spec kc n)
    (fun C _ _ hC hok x y _ _ hmem u s hu hs hxu hys hus hprod hJ => by
      simp only [sCellOK, decide_eq_true_eq] at hok
      refine leechKernelK_neg_of_ss_cell hΛ h2 hprog hM hd hC hok.1 hok.2 hu hs hus hprod hJ ?_
      rw [axisNEnvS_eq_recNEnvS, ← hxu, ← hys]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u s hu hs rfl rfl hus hprod hJ)

/-- **Positivity for `t ≤ 1 ≤ q` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` with `1/π ≤ x₁` in the variables `q` and `1/t`; its corner `x, y ≥ c` lies inside
`q, 1/t ≤ c₀`. -/
theorem leechKernel_pos_of_coverRS (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechRSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {Q : Quots} (hQ : T.quots 4 0 = Q)
    {kc n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq : 1 ≤ q) (ht0 : 0 < t) (ht : t ≤ 1) (hout : c₀ < q ∨ c₀ < t⁻¹)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
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
  have key := leechKernel_pos_of_cover_rs hΛ h2 hprog hM hd hQ hcov hq0 hs0 hr hus hprod hJ'
  rw [inv_inv] at key
  rcases key with h | h
  · rcases hout with h' | h'
    · exact absurd (le_of_rec_ge hc hc₀ hq0 h.1) (not_le.mpr h')
    · exact absurd (le_of_rec_ge hc hc₀ hs0 h.2) (not_le.mpr h')
  · exact h

/-- **Positivity for `q, t ≤ 1` outside a corner box.** The cover is one of the reciprocal
square `[0, x₁]²` in the variables `1/q` and `1/t`. -/
theorem leechKernel_pos_of_coverSS (hΛ : 0 < Λ) (h2 : 2 ∣ Λ)
    (hprog : (ISLP.runExpr prog []).getD k (.cst 0) = leechSSE Λ)
    (hM : LeechSModels Bx Λ prog k T) (hd : T.Divisible 4 0) {Q : Quots} (hQ : T.quots 4 0 = Q)
    {kc n : ℕ} {c x₁ : ℚ} {cov : Cover}
    (hcov : cov.check (cellOKSb kc n) (sCellOK Bx Q) c ⟨0, x₁, 0, x₁⟩ = true)
    (hx₁ : (1 : ℝ) ≤ π * x₁) (hc : (0 : ℝ) < c) {c₀ : ℝ} (hc₀ : 1 ≤ π * c * c₀) {q t : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1) (ht0 : 0 < t) (ht : t ≤ 1) (hout : c₀ < q⁻¹ ∨ c₀ < t⁻¹)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
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
  have key := leechKernelK_neg_of_cover_ss hΛ h2 hprog hM hd hQ hcov hu0 hs0 hr hus hprod hJ'
  rw [inv_inv] at key
  have hneg : (ckmrvLeechKernel (imagPt q⁻¹) (imagPt t)).re < 0 := by
    rcases key with h | h
    · rcases hout with h' | h'
      · exact absurd (le_of_rec_ge hc hc₀ hu0 h.1) (not_le.mpr h')
      · exact absurd (le_of_rec_ge hc hc₀ hs0 h.2) (not_le.mpr h')
    · exact h
  rw [ckmrvLeechHatKernel_imagPt_re hq0]
  have hq12 : 0 < (q ^ 12)⁻¹ := by positivity
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hq12) hneg

end Cell

end E8Leech.Kron
