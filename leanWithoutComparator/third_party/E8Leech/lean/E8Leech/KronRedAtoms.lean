import E8Leech.KronRedLog
import E8Leech.KronKernelSplit

/-!
# The logarithms of `θ₃, θ₄` divided by the nome

For `θ = 1 + x d(x)` the quotient `Λ log θ(x) / x` is the atom `Λ d ℓ(x d)` of `KronRedLog`.
With these two atoms a numerator that vanishes at the cusp of the second variable, logarithmic
terms included, is the nome times an expression in the atoms.

* `devTheta3`, `nomeTheta3_eq_one_add`, `devTheta3MDD`: the quotient `(θ₃ − 1)/x`.
* `rlogTheta3`, `rlogTheta4`: the two atoms; `log_theta3_eq`, `log_theta4_eq`.
* `redAtoms`, `redAtomModels`, `redAtoms_ok`: the atoms with the indices `10, 11` after the ten
  atoms of `KronKernelSplit`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-- `(θ₃(x) − 1)/x = 2 + 2x³ + 2x⁸ + …` as a series. -/
noncomputable def devTheta3 (x : ℝ) : ℝ :=
  ((2 : ℤ) : ℝ) + ∑' k, ((th3w (k + 1) : ℚ) : ℝ) * x ^ dsqE k

theorem nomeTheta3_eq_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeTheta3 x = 1 + x * devTheta3 x := by
  have hsum : Summable fun k => ((th3w k : ℚ) : ℝ) * x ^ sqE k :=
    summable_series_geom sqE_strictMono (w := fun k => ((th3w k : ℚ) : ℝ)) (W := 2) (ρ := 1)
      (fun k => by
        have h : ((|th3w k| : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_th3w k)
        rw [Rat.cast_abs] at h
        simpa using h)
      le_rfl hx0 (by simpa using hx1)
  have e : ∑' k, ((th3w k : ℚ) : ℝ) * x ^ sqE k =
      ((th3w 0 : ℚ) : ℝ) * x ^ sqE 0 + ∑' k, ((th3w (k + 1) : ℚ) : ℝ) * x ^ sqE (k + 1) :=
    hsum.tsum_eq_zero_add
  have h : ∑' k, ((th3w (k + 1) : ℚ) : ℝ) * x ^ sqE (k + 1) =
      x * ∑' k, ((th3w (k + 1) : ℚ) : ℝ) * x ^ dsqE k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← dsqE_add_one, pow_succ]
      ring
  have h0 : ((th3w 0 : ℚ) : ℝ) * x ^ sqE 0 = 2 * x := by
    norm_num [th3w, sqE]
  rw [nomeTheta3_eq_series, e, h, h0, devTheta3]
  push_cast
  ring

/-- The model of `(θ₃ − 1)/x`, truncated after `N` terms. -/
def devTheta3MDD (Bx : Bounds) (N : ℕ) : MDD :=
  seriesMDD Bx 2 (fun _ => 2) dsqE 2 1 N

theorem approx_devTheta3MDD {Bx : Bounds} (h : SeriesOK Bx 4) (N : ℕ) {S : NEnv → Prop} :
    (devTheta3MDD Bx N).Approx Bx S (fun e => devTheta3 e.a) (fun e => devTheta3 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) dsqE_strictMono dsqE_zero (w := fun k => th3w (k + 1))
    (W := 2) (ρ := 1) (fun k => by simpa using abs_th3w (k + 1)) le_rfl h.one 2 N
    (fun _ => 2) (fun k _ => by simp [th3w])

/-- `Λ log θ₃(x) / x`. -/
noncomputable def rlogTheta3 (Λ : ℕ) (x : ℝ) : ℝ :=
  (Λ : ℝ) * (devTheta3 x * TM.logRatio (x * devTheta3 x))

/-- `Λ log θ₄(x) / x`. -/
noncomputable def rlogTheta4 (Λ : ℕ) (x : ℝ) : ℝ :=
  (Λ : ℝ) * (devTheta4 x * TM.logRatio (x * devTheta4 x))

theorem log_one_add_eq (z : ℝ) : Real.log (1 + z) = z * TM.logRatio z := by
  by_cases h : z = 0
  · subst h
    simp
  · rw [TM.logRatio, if_neg h]
    field_simp

theorem log_theta3_eq (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (Λ : ℝ) * Real.log (nomeTheta3 x) = x * rlogTheta3 Λ x := by
  rw [nomeTheta3_eq_one_add hx0 hx1, log_one_add_eq, rlogTheta3]
  ring

theorem log_theta4_eq (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (Λ : ℝ) * Real.log (nomeTheta4 x) = x * rlogTheta4 Λ x := by
  rw [nomeTheta4_eq_one_add hx0 hx1, log_one_add_eq, rlogTheta4]
  ring

/-! ## The two atoms and their models -/

/-- The atoms `Λ log θ₃ / x` and `Λ log θ₄ / x`, with the indices `10` and `11`. -/
noncomputable def redAtoms (Λ : ℕ) : List (ℝ → ℝ) := [rlogTheta3 Λ, rlogTheta4 Λ]

/-- The models of the two atoms. -/
def redAtomModels (Bx : Bounds) (D Dcap Λ n N' : ℕ) : List MDD :=
  [MDD.rlog Bx D Dcap Λ n (devTheta3MDD Bx N'), MDD.rlog Bx D Dcap Λ n (devTheta4MDD Bx N')]

/-- The smallness checks of the two reduced logarithms. -/
def RedOK (Bx : Bounds) (D Dcap N' : ℕ) : Prop :=
  SeriesOK Bx 4 ∧ MDD.RLogOK Bx D Dcap (devTheta3MDD Bx N') ∧
    MDD.RLogOK Bx D Dcap (devTheta4MDD Bx N')

instance (Bx : Bounds) (D Dcap N' : ℕ) : Decidable (RedOK Bx D Dcap N') := by
  unfold RedOK
  infer_instance

theorem redAtoms_ok {Bx : Bounds} {D Dcap N' : ℕ} (h : RedOK Bx D Dcap N') {Λ n : ℕ}
    (hΛ : ∀ i, i < n + 1 → (i + 1) ∣ Λ) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (redAtomModels Bx D Dcap Λ n N') (redAtoms Λ) := by
  obtain ⟨hS, h3, h4⟩ := h
  intro i
  rcases i with _ | _ | i
  · simpa [redAtomModels, redAtoms, rlogTheta3] using
      MDD.approx_rlog hS.1 D Dcap hΛ (approx_devTheta3MDD hS N' (S := S)) h3
  · simpa [redAtomModels, redAtoms, rlogTheta4] using
      MDD.approx_rlog hS.1 D Dcap hΛ (approx_devTheta4MDD hS N' (S := S)) h4
  · simpa [redAtomModels, redAtoms] using MDD.approx_zero (Bx := Bx) (S := S)

/-- The twelve atoms of the forms with the second variable inverted. -/
noncomputable def sAtoms (Λ : ℕ) : List (ℝ → ℝ) := kernelAtoms Λ ++ (devAtoms ++ redAtoms Λ)

/-- The models of the twelve atoms. -/
def sAtomModels (Bx : Bounds) (D Dcap Λ n K N NE N' NE' : ℕ) : List MDD :=
  kernelAtomModels Bx D Dcap Λ n K N NE ++
    (devAtomModels Bx N' NE' ++ redAtomModels Bx D Dcap Λ n N')

theorem sAtoms_ok {Bx : Bounds} {NE NE' : ℕ} (hG : GenOK Bx NE) (hG' : GenOK Bx NE')
    {D Dcap N' : ℕ} (hR : RedOK Bx D Dcap N') {Λ n : ℕ} (K N : ℕ)
    (hΛ : ∀ i, i < n + 1 → (i + 1) ∣ Λ) (hL : LogsOK Bx D Dcap K N NE) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (sAtomModels Bx D Dcap Λ n K N NE N' NE') (sAtoms Λ) :=
  ISLP.AtomsOK.append rfl
    (kernelAtoms_ok hG D Dcap K N (fun i hi => hΛ i (by omega)) hL)
    (ISLP.AtomsOK.append rfl (devAtoms_ok hG' N') (redAtoms_ok hR hΛ))

end E8Leech.Kron
