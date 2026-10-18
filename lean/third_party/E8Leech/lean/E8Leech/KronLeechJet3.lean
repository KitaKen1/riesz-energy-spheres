import E8Leech.KronJet3
import E8Leech.KronRedAtoms3

/-!
# The third-order jets of the atoms

The blocks of the atoms of the second variable for the transformation of `KronJet3`, over the
fourteen atoms `tAtoms Λ = kernelAtoms Λ ++ red3Atoms Λ`:

* the nome: `(0, 1, 0, 0)`;
* `θ₃ = 1 + 2n + n³ (n δ₃)`, `θ₄ = 1 − 2n + n³ (n δ₄)`, `η₁ = 1 + n² + n³ (n δ_η)`,
  `E₂ = 1 − 24n² + n³ (n ε)`;
* `Λ log θ₃ = 2Λ n − 2Λ n² + n³ (Λ n δ₃ − 2Λ n² δ₃ − (Λ/2) n⁵ δ₃² + d³ Λℓ₂)`, `d = 2 + n³ δ₃`, and
  the same for `θ₄` with `d = −2 + n³ δ₄`;
* every other atom is its own jet.

`zleafL_ok` is the soundness of these blocks on nomes below `1/4` at which `θ₃ − 1` and `θ₄ − 1`
are below `1` in absolute value.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

/-- The fourteen atoms of the third-order forms. -/
noncomputable def tAtoms (Λ : ℕ) : List (ℝ → ℝ) := kernelAtoms Λ ++ red3Atoms Λ

/-- The models of the fourteen atoms. -/
def tAtomModels (Bx : Bounds) (D Dcap Λ n K N NE N' NE' : ℕ) : List MDD :=
  kernelAtomModels Bx D Dcap Λ n K N NE ++ red3AtomModels Bx D Dcap Λ n N' NE'

theorem tAtoms_ok {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) {D Dcap N' NE' : ℕ}
    (hR : Red3OK Bx D Dcap N' NE') {Λ n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n + 3 → (i + 1) ∣ Λ)
    (hL : LogsOK Bx D Dcap K N NE) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (tAtomModels Bx D Dcap Λ n K N NE N' NE') (tAtoms Λ) :=
  ISLP.AtomsOK.append rfl
    (kernelAtoms_ok hG D Dcap K N (fun i hi => hΛ i (by omega)) hL)
    (red3Atoms_ok hR fun i hi => hΛ (i + 2) (by omega))

namespace ISLP

/-- The block of a generator `1 + c₁ n + c₂ n² + n⁴ δ`; `δ` is the atom `i`. -/
def genT (c1 c2 : ℤ) (i : ℕ) : List TInstr :=
  [.zat i, .cst 1, .cst c1, .cst c2, .mul (.abs 0) (.loc 0)]

/-- The block of `Λ log θ` for `θ = 1 + n d`, `d = 2σ + n³ δ`, `σ = ±1`: the atoms `jd` and `jl`
are `δ` and `Λ ℓ₂(θ − 1)`. -/
def logT (Λ : ℕ) (σ : ℤ) (jd jl : ℕ) : List TInstr :=
  [.zat jd, .zat jl, .mul (.abs 0) (.loc 0), .mul (.abs 0) (.loc 2), .mul (.abs 0) (.loc 3),
    .cst Λ, .mul (.loc 5) (.loc 2), .cst (σ * (2 * Λ)), .mul (.loc 7) (.loc 3),
    .sub (.loc 6) (.loc 8), .mul (.loc 2) (.loc 4), .mul (.abs 0) (.loc 10),
    .cst ((Λ / 2 : ℕ) : ℤ), .mul (.loc 12) (.loc 11), .sub (.loc 9) (.loc 13), .cst (σ * 2),
    .add (.loc 15) (.loc 4), .mul (.loc 16) (.loc 16), .mul (.loc 17) (.loc 16),
    .mul (.loc 18) (.loc 1), .cst 0, .cst (σ * (2 * Λ)), .cst (-(2 * Λ)),
    .add (.loc 14) (.loc 19)]

/-- The blocks of the atoms. -/
def zleafL (Λ : ℕ) : ℕ → Block
  | 0 => ⟨0, [.cst 0, .cst 1, .cst 0, .cst 0]⟩
  | 1 => ⟨1, genT 2 0 8⟩
  | 2 => ⟨1, genT (-2) 0 9⟩
  | 3 => ⟨1, genT 0 1 10⟩
  | 4 => ⟨1, genT 0 (-24) 11⟩
  | 5 => ⟨20, logT Λ 1 8 12⟩
  | 6 => ⟨20, logT Λ (-1) 9 13⟩
  | i + 7 => ⟨0, leafT (.zat (i + 7))⟩

/-- **The blocks of the atoms are sound.** -/
theorem zleafL_ok (Λ : ℕ) (h2 : 2 ∣ Λ) (side : Bool) (e : NEnv)
    (hx0 : 0 ≤ (if side then e.a else e.b)) (hx4 : 4 * (if side then e.a else e.b) < 1)
    (hs3 : |(if side then e.a else e.b) * devTheta3 (if side then e.a else e.b)| < 1)
    (hs4 : |(if side then e.a else e.b) * devTheta4 (if side then e.a else e.b)| < 1) :
    ZLeafOK (tAtoms Λ) side e (if side then e.a else e.b) (zleafL Λ) := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = (if side then e.a else e.b) := ⟨_, rfl⟩
  rw [← hxdef] at hx0 hx4 hs3 hs4 ⊢
  have hx1 : x < 1 := by linarith
  have hΛ2 : (((Λ / 2 : ℕ) : ℤ) : ℝ) = (Λ : ℝ) / 2 := by
    rw [Int.cast_natCast, Nat.cast_div h2 (by norm_num)]
    norm_num
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · -- the nome
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 0 + 3 < 0 + 4), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafL, evalT, TInstr.val, List.nil_append, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [hx, ← hxdef]
    show _ = x
    push_cast
    ring
  · -- `θ₃`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 1 + 3 < 0 + 5), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafL, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
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
    simp only [zleafL, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
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
    simp only [zleafL, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
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
    simp only [zleafL, genT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
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
    simp only [zleafL, logT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    have ed : (tAtoms Λ).getD 8 (fun _ => 0) = delta3 := rfl
    have el : (tAtoms Λ).getD 12 (fun _ => 0) = lam2Theta3 Λ := rfl
    rw [ed, el]
    show _ = (Λ : ℝ) * Real.log (nomeTheta3 x)
    rw [log_theta3_cube Λ hx0 hx1 hs3, devTheta3_eq hx0 hx1, hΛ2]
    push_cast
    ring
  · -- `Λ log θ₄`
    refine ⟨OK_of_all_okB rfl, fun rs h0 hx =>
      ⟨by rw [length_evalT]; exact (by decide : 20 + 3 < 0 + 24), ?_⟩⟩
    rw [jet3Val_block _ _ _ h0]
    simp only [zleafL, logT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx, ← hxdef]
    have ed : (tAtoms Λ).getD 9 (fun _ => 0) = delta4 := rfl
    have el : (tAtoms Λ).getD 13 (fun _ => 0) = lam2Theta4 Λ := rfl
    rw [ed, el]
    show _ = (Λ : ℝ) * Real.log (nomeTheta4 x)
    rw [log_theta4_cube Λ hx0 hx1 hs4, devTheta4_eq hx0 hx1, hΛ2]
    push_cast
    ring
  · -- the other atoms
    refine ⟨OK_of_all_okB rfl, fun rs h0 _ =>
      ⟨by rw [length_evalT]; exact (by decide : 0 + 3 < 0 + 4), ?_⟩⟩
    show jet3Val (rs ++ evalT (tAtoms Λ) side e rs (leafT (.zat (i + 7))) []) (rs.length + 0) = _
    rw [jet3Val_leafT _ _ _ _ _ h0]
    rfl

end ISLP

end E8Leech.Kron
