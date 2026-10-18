import E8Leech.KronLeechJet3

/-!
# The third-order jet of `Λ log η₁`

The jet transformation of `KronLeechJet3` treats the atom `Λ log η₁` of the second variable as an
opaque leaf, which is enough for the kernels with the second variable inverted (they do not contain
it). The numerator of the truncated inequality (6.4)(2) contains the logarithm
`L₀ = 4 log 2 + 4 log η₁ − 4 log θ₃` of the second variable, so this atom needs its jet too:

`Λ log η₁ = Λ x² + x³ · x (Λ δ_η − (Λ/2) u² + x² u³ · Λ ℓ₂(η₁ − 1))`, `u = 1 + x² δ_η`,

with one more atom `Λ ℓ₂(η₁ − 1)` (`lam2Eta`), whose model is the one of `KronRedLog3` for
`(η₁ − 1)/x = x + x³ δ_η`.

* `nomeMDD`, `devEta`, `devEtaMDD`, `approx_devEtaMDD`: the model of `(η₁ − 1)/x`.
* `lam2Eta`, `log_eta1_cube`: the atom and the identity.
* `hAtoms`, `hAtomModels`, `RedHOK`, `hAtoms_ok`: the fifteen atoms and their models.
* `ISLP.logEtaT`, `ISLP.zleafH`, `ISLP.zleafH_ok`: the blocks of the atoms, with the new block for
  the atom `7`.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-! ## The model of `(η₁ − 1)/x` -/

/-- The model of the nome. -/
def nomeMDD : MDD := ⟨MDD.nomeA, MDD.nomeB, MTM.const 1⟩

theorem approx_nomeMDD {Bx : Bounds} {S : NEnv → Prop} :
    nomeMDD.Approx Bx S (fun e => e.a) (fun e => e.b) := by
  refine ⟨MDD.approx_nomeA, MDD.approx_nomeB, ?_⟩
  refine MTM.approx_congr (MTM.approx_const 1) fun e _ hs => ?_
  have h : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  rw [div_self h]
  norm_num

/-- `(η₁(x) − 1)/x = x + x³ δ_η(x)`. -/
def devEta (x : ℝ) : ℝ := x + x ^ 3 * deltaEta x

theorem nomeEta1_eq_one_add_dev {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeEta1 x = 1 + x * devEta x := by
  rw [nomeEta1_eq_cube hx0 hx1, devEta]
  ring

/-- The model of `(η₁ − 1)/x`. -/
def devEtaMDD (Bx : Bounds) (D Dcap N : ℕ) : MDD :=
  nomeMDD.add (MDD.mul Bx D Dcap
    (MDD.mul Bx D Dcap (MDD.mul Bx D Dcap nomeMDD nomeMDD) nomeMDD) (deltaEtaMDD Bx N))

theorem approx_devEtaMDD {Bx : Bounds} (h : SeriesOK Bx 4) (D Dcap N : ℕ) {S : NEnv → Prop} :
    (devEtaMDD Bx D Dcap N).Approx Bx S (fun e => devEta e.a) (fun e => devEta e.b) := by
  have hB := h.1
  have hn := approx_nomeMDD (Bx := Bx) (S := S)
  have h3 := MDD.approx_mul hB D Dcap (MDD.approx_mul hB D Dcap hn hn) hn
  have hd := MDD.approx_mul hB D Dcap h3 (approx_deltaEtaMDD h N (S := S))
  refine MDD.approx_congr (MDD.approx_add hn hd) (fun e _ _ => ?_) (fun e _ _ => ?_)
  · simp only [devEta]
    ring
  · simp only [devEta]
    ring

/-! ## The atom and the identity -/

/-- `Λ ℓ₂(η₁ − 1)`. -/
def lam2Eta (Λ : ℕ) (x : ℝ) : ℝ := (Λ : ℝ) * logRatioSh 2 (x * devEta x)

/-- `Λ log η₁ = Λ x² + x³ (…)`. -/
theorem log_eta1_cube (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hs : |x * devEta x| < 1) :
    (Λ : ℝ) * Real.log (nomeEta1 x) = Λ * x ^ 2 +
      x ^ 3 * (x * (Λ * deltaEta x - Λ / 2 * (1 + x ^ 2 * deltaEta x) ^ 2 +
        x ^ 2 * ((1 + x ^ 2 * deltaEta x) ^ 3 * lam2Eta Λ x))) := by
  rw [nomeEta1_eq_one_add_dev hx0 hx1, log_one_add_cube hs, lam2Eta]
  generalize logRatioSh 2 (x * devEta x) = L
  simp only [devEta]
  ring

/-! ## The fifteen atoms -/

/-- The atoms of `KronLeechJet3` and `Λ ℓ₂(η₁ − 1)`. -/
def hAtoms (Λ : ℕ) : List (ℝ → ℝ) := tAtoms Λ ++ [lam2Eta Λ]

/-- The models of the fifteen atoms. -/
def hAtomModels (Bx : Bounds) (D Dcap Λ n K N NE N' NE' : ℕ) : List MDD :=
  tAtomModels Bx D Dcap Λ n K N NE N' NE' ++
    [MDD.rlogSh Bx D Dcap Λ n 2 (devEtaMDD Bx D Dcap N')]

/-- The checks of the reduced atoms, with the one of the new atom. -/
def RedHOK (Bx : Bounds) (D Dcap N' NE' : ℕ) : Prop :=
  Red3OK Bx D Dcap N' NE' ∧ MDD.RLogOK Bx D Dcap (devEtaMDD Bx D Dcap N')

instance (Bx : Bounds) (D Dcap N' NE' : ℕ) : Decidable (RedHOK Bx D Dcap N' NE') := by
  unfold RedHOK
  infer_instance

theorem hAtoms_ok {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) {D Dcap N' NE' : ℕ}
    (hR : RedHOK Bx D Dcap N' NE') {Λ n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n + 3 → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (hAtomModels Bx D Dcap Λ n K N NE N' NE') (hAtoms Λ) := by
  refine ISLP.AtomsOK.append rfl (tAtoms_ok hG hR.1 K N hΛ hL) ?_
  intro i
  rcases i with _ | i
  · have h := MDD.approx_rlogSh hR.1.1.1 D Dcap (j := 2) (n := n) (Λ := Λ)
      (fun i hi => hΛ (i + 2) (by omega)) (approx_devEtaMDD hR.1.1 D Dcap N' (S := S)) hR.2
    simpa [lam2Eta] using h
  · simpa using MDD.approx_zero (Bx := Bx) (S := S)

namespace ISLP

/-! ## The blocks -/

/-- The block of `Λ log η₁ = Λ n² + n³ · n (Λ δ − (Λ/2) u² + n² u³ L)`, `u = 1 + n² δ`: the atoms
`jd` and `jl` are `δ_η` and `L = Λ ℓ₂(η₁ − 1)`. -/
def logEtaT (Λ : ℕ) (jd jl : ℕ) : List TInstr :=
  [.zat jd, .zat jl, .mul (.abs 0) (.abs 0), .mul (.loc 2) (.loc 0), .cst 1,
    .add (.loc 4) (.loc 3), .mul (.loc 5) (.loc 5), .mul (.loc 6) (.loc 5), .mul (.loc 7) (.loc 1),
    .mul (.loc 2) (.loc 8), .cst Λ, .mul (.loc 10) (.loc 0), .cst ((Λ / 2 : ℕ) : ℤ),
    .mul (.loc 12) (.loc 6), .sub (.loc 11) (.loc 13), .add (.loc 14) (.loc 9), .cst 0, .cst 0,
    .cst Λ, .mul (.abs 0) (.loc 15)]

/-- The blocks of the atoms: those of `zleafL`, and the block of `Λ log η₁` for the atom `7`. -/
def zleafH (Λ : ℕ) : ℕ → Block
  | 0 => ⟨0, [.cst 0, .cst 1, .cst 0, .cst 0]⟩
  | 1 => ⟨1, genT 2 0 8⟩
  | 2 => ⟨1, genT (-2) 0 9⟩
  | 3 => ⟨1, genT 0 1 10⟩
  | 4 => ⟨1, genT 0 (-24) 11⟩
  | 5 => ⟨20, logT Λ 1 8 12⟩
  | 6 => ⟨20, logT Λ (-1) 9 13⟩
  | 7 => ⟨16, logEtaT Λ 10 14⟩
  | i + 8 => ⟨0, leafT (.zat (i + 8))⟩

/-- **The blocks of the fifteen atoms are sound.** -/
theorem zleafH_ok (Λ : ℕ) (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1)
    (hsη : |(if side then e.a else e.b) * devEta (if side then e.a else e.b)| < 1) :
    ZLeafOK (hAtoms Λ) side e (if side then e.a else e.b) (zleafH Λ) := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = (if side then e.a else e.b) := ⟨_, rfl⟩
  rw [← hxdef] at hx0 hx4 hs3 hs4 hsη ⊢
  have hx1 : x < 1 := by linarith
  have hΛ2 : (((Λ / 2 : ℕ) : ℤ) : ℝ) = (Λ : ℝ) / 2 := by
    rw [Int.cast_natCast, Nat.cast_div h2 (by norm_num)]
    norm_num
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · -- the nome
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 0 + 3 < 0 + 4), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, evalT, TInstr.val, List.nil_append, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = x
    push_cast
    ring
  · -- `θ₃`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 1 + 3 < 0 + 5), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = nomeTheta3 x
    rw [nomeTheta3_eq_cube hx0 hx1]
    show _ + x * _ + x ^ 2 * _ + x ^ 3 * (x * delta3 x) = _
    push_cast
    ring
  · -- `θ₄`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 1 + 3 < 0 + 5), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = nomeTheta4 x
    rw [nomeTheta4_eq_cube hx0 hx1]
    show _ + x * _ + x ^ 2 * _ + x ^ 3 * (x * delta4 x) = _
    push_cast
    ring
  · -- `η₁`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 1 + 3 < 0 + 5), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = nomeEta1 x
    rw [nomeEta1_eq_cube hx0 hx1]
    show _ + x * _ + x ^ 2 * _ + x ^ 3 * (x * deltaEta x) = _
    push_cast
    ring
  · -- `E₂`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 1 + 3 < 0 + 5), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = nomeE2 x
    rw [nomeE2_eq_cube hx0 hx4]
    show _ + x * _ + x ^ 2 * _ + x ^ 3 * (x * etE2 x) = _
    push_cast
    ring
  · -- `Λ log θ₃`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 20 + 3 < 0 + 24), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, logT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    have ed : (hAtoms Λ).getD 8 (fun _ => 0) = delta3 := rfl
    have el : (hAtoms Λ).getD 12 (fun _ => 0) = lam2Theta3 Λ := rfl
    rw [ed, el]
    show _ = (Λ : ℝ) * Real.log (nomeTheta3 x)
    rw [log_theta3_cube Λ hx0 hx1 hs3, devTheta3_eq hx0 hx1, hΛ2]
    push_cast
    ring
  · -- `Λ log θ₄`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 20 + 3 < 0 + 24), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, logT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    have ed : (hAtoms Λ).getD 9 (fun _ => 0) = delta4 := rfl
    have el : (hAtoms Λ).getD 13 (fun _ => 0) = lam2Theta4 Λ := rfl
    rw [ed, el]
    show _ = (Λ : ℝ) * Real.log (nomeTheta4 x)
    rw [log_theta4_cube Λ hx0 hx1 hs4, devTheta4_eq hx0 hx1, hΛ2]
    push_cast
    ring
  · -- `Λ log η₁`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 16 + 3 < 0 + 20), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafH, logEtaT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    have ed : (hAtoms Λ).getD 10 (fun _ => 0) = deltaEta := rfl
    have el : (hAtoms Λ).getD 14 (fun _ => 0) = lam2Eta Λ := rfl
    rw [ed, el]
    show _ = (Λ : ℝ) * Real.log (nomeEta1 x)
    rw [log_eta1_cube Λ hx0 hx1 hsη, hΛ2]
    push_cast
    ring
  · -- the other atoms
    refine ⟨OK_of_all_okB rfl, fun rs h0 _ =>
      ⟨by rw [length_evalT]; exact (by decide : 0 + 3 < 0 + 4), ?_⟩⟩
    show jet3Val (rs ++ evalT (hAtoms Λ) side e rs (leafT (.zat (i + 8))) []) (rs.length + 0) = _
    rw [jet3Val_leafT _ _ _ _ _ h0]
    rfl

end ISLP

end E8Leech.Kron
