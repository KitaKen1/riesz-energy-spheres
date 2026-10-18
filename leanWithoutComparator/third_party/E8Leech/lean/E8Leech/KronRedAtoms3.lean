import E8Leech.KronRedLog3
import E8Leech.KronRedAtoms

/-!
# Third-order reductions of the generators and of the logarithms of `θ₃, θ₄`

With the second variable inverted, the factors of the Leech numerator vanish to the third order at
the cusp of the second variable. To write them as the cube of the nome times an expression, the
generators and the logarithms are expanded to the third order:

`θ₃ = 1 + 2x + x⁴ δ₃`,  `θ₄ = 1 − 2x + x⁴ δ₄`,  `η₁ = 1 + x² + x⁴ δ_η`,  `E₂ = 1 − 24x² + x⁴ ε`,

`Λ log θ = Λ x d − (Λ/2) x² d² + x³ d³ · Λ ℓ₂(x d)`,  `d = (θ − 1)/x = ±2 + x³ δ`.

The four functions `δ₃, δ₄, δ_η, ε` are series of the same kind as the generators, and
`Λ ℓ₂(x d)` has the models of `KronRedLog3`.

* `delta3`, `delta4`, `deltaEta`, `etE2` and the four expansions.
* `lam2Theta3`, `lam2Theta4`, `log_theta3_cube`, `log_theta4_cube`.
* `red3Atoms`, `red3AtomModels`, `red3Atoms_ok`: the six atoms and their models.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-! ## The series -/

/-- The exponents `(k + 3)² − 4` of `(θ − 1 ∓ 2x)/x⁴` after its constant term. -/
def q4E (k : ℕ) : ℕ := (k + 3) ^ 2 - 4

/-- The exponents `(k + 2)(k + 3) − 4` of `(η₁ − 1 − x²)/x⁴`. -/
def t4E (k : ℕ) : ℕ := (k + 2) * (k + 3) - 4

theorem q4E_strictMono : StrictMono q4E := fun i j h => by
  unfold q4E
  have h1 : (i + 3) ^ 2 < (j + 3) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : 2 ^ 2 ≤ (i + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem t4E_strictMono : StrictMono t4E := fun i j h => by
  unfold t4E
  have h1 : (i + 2) * (i + 3) < (j + 2) * (j + 3) := Nat.mul_lt_mul'' (by omega) (by omega)
  have h2 : 2 * 2 ≤ (i + 2) * (i + 3) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem q4E_zero : 1 ≤ q4E 0 := by decide

theorem t4E_zero : 1 ≤ t4E 0 := by decide

theorem q4E_add_three (k : ℕ) : q4E k + 3 = dsqE (k + 1) := by
  unfold q4E dsqE
  have h2 : 2 ^ 2 ≤ (k + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e : k + 1 + 2 = k + 3 := by omega
  rw [e]
  omega

theorem t4E_add_four (k : ℕ) : t4E k + 4 = triE (k + 1) := by
  unfold t4E triE
  have h2 : 2 * 2 ≤ (k + 2) * (k + 3) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : k + 1 + 1 = k + 2 := by omega
  have e2 : k + 1 + 2 = k + 3 := by omega
  rw [e1, e2]
  omega

/-- `(θ₃(x) − 1 − 2x)/x⁴ = 2 + 2x⁵ + 2x¹² + …`. -/
noncomputable def delta3 (x : ℝ) : ℝ :=
  ((2 : ℤ) : ℝ) + ∑' k, ((th3w (k + 1 + 1) : ℚ) : ℝ) * x ^ q4E k

/-- `(θ₄(x) − 1 + 2x)/x⁴ = 2 − 2x⁵ + 2x¹² − …`. -/
noncomputable def delta4 (x : ℝ) : ℝ :=
  ((2 : ℤ) : ℝ) + ∑' k, ((th4w (k + 1 + 1) : ℚ) : ℝ) * x ^ q4E k

/-- `(η₁(x) − 1 − x²)/x⁴ = x² + x⁸ + x¹⁶ + …`. -/
noncomputable def deltaEta (x : ℝ) : ℝ :=
  ((0 : ℤ) : ℝ) + ∑' k, ((eta1w (k + 1) : ℚ) : ℝ) * x ^ t4E k

/-- `(E₂(x) − 1 + 24x²)/x⁴ = −72 − 96x² − …`. -/
noncomputable def etE2 (x : ℝ) : ℝ :=
  ((-72 : ℤ) : ℝ) + ∑' k, ((e2w (k + 1 + 1) : ℚ) : ℝ) * x ^ evenE k

theorem devTheta3_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    devTheta3 x = 2 + x ^ 3 * delta3 x := by
  have hsum : Summable fun k => ((th3w (k + 1) : ℚ) : ℝ) * x ^ dsqE k :=
    summable_series_geom dsqE_strictMono (w := fun k => ((th3w (k + 1) : ℚ) : ℝ)) (W := 2)
      (ρ := 1)
      (fun k => by
        have h : ((|th3w (k + 1)| : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_th3w (k + 1))
        rw [Rat.cast_abs] at h
        simpa using h)
      le_rfl hx0 (by simpa using hx1)
  have e : ∑' k, ((th3w (k + 1) : ℚ) : ℝ) * x ^ dsqE k =
      ((th3w (0 + 1) : ℚ) : ℝ) * x ^ dsqE 0 +
        ∑' k, ((th3w (k + 1 + 1) : ℚ) : ℝ) * x ^ dsqE (k + 1) :=
    hsum.tsum_eq_zero_add
  have h : ∑' k, ((th3w (k + 1 + 1) : ℚ) : ℝ) * x ^ dsqE (k + 1) =
      x ^ 3 * ∑' k, ((th3w (k + 1 + 1) : ℚ) : ℝ) * x ^ q4E k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← q4E_add_three, pow_add]
      ring
  have h0 : ((th3w (0 + 1) : ℚ) : ℝ) * x ^ dsqE 0 = 2 * x ^ 3 := by
    norm_num [th3w, dsqE]
  rw [devTheta3, e, h, h0, delta3]
  push_cast
  ring

theorem devTheta4_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    devTheta4 x = -2 + x ^ 3 * delta4 x := by
  have hsum : Summable fun k => ((th4w (k + 1) : ℚ) : ℝ) * x ^ dsqE k :=
    summable_series_geom dsqE_strictMono (w := fun k => ((th4w (k + 1) : ℚ) : ℝ)) (W := 2)
      (ρ := 1)
      (fun k => by
        have h : ((|th4w (k + 1)| : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_th4w (k + 1))
        rw [Rat.cast_abs] at h
        simpa using h)
      le_rfl hx0 (by simpa using hx1)
  have e : ∑' k, ((th4w (k + 1) : ℚ) : ℝ) * x ^ dsqE k =
      ((th4w (0 + 1) : ℚ) : ℝ) * x ^ dsqE 0 +
        ∑' k, ((th4w (k + 1 + 1) : ℚ) : ℝ) * x ^ dsqE (k + 1) :=
    hsum.tsum_eq_zero_add
  have h : ∑' k, ((th4w (k + 1 + 1) : ℚ) : ℝ) * x ^ dsqE (k + 1) =
      x ^ 3 * ∑' k, ((th4w (k + 1 + 1) : ℚ) : ℝ) * x ^ q4E k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← q4E_add_three, pow_add]
      ring
  have h0 : ((th4w (0 + 1) : ℚ) : ℝ) * x ^ dsqE 0 = 2 * x ^ 3 := by
    norm_num [th4w, dsqE]
  rw [devTheta4, e, h, h0, delta4]
  push_cast
  ring

/-- `θ₃ = 1 + 2x + x⁴ δ₃`. -/
theorem nomeTheta3_eq_cube {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeTheta3 x = 1 + 2 * x + x ^ 4 * delta3 x := by
  rw [nomeTheta3_eq_one_add hx0 hx1, devTheta3_eq hx0 hx1]
  ring

/-- `θ₄ = 1 − 2x + x⁴ δ₄`. -/
theorem nomeTheta4_eq_cube {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeTheta4 x = 1 - 2 * x + x ^ 4 * delta4 x := by
  rw [nomeTheta4_eq_one_add hx0 hx1, devTheta4_eq hx0 hx1]
  ring

/-- `η₁ = 1 + x² + x⁴ δ_η`. -/
theorem nomeEta1_eq_cube {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeEta1 x = 1 + x ^ 2 + x ^ 4 * deltaEta x := by
  have hsum : Summable fun k => ((eta1w k : ℚ) : ℝ) * x ^ triE k :=
    summable_series_geom triE_strictMono (w := fun k => ((eta1w k : ℚ) : ℝ)) (W := 1) (ρ := 1)
      (fun k => by
        have h : ((|eta1w k| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_eta1w k)
        rw [Rat.cast_abs] at h
        simpa using h)
      le_rfl hx0 (by simpa using hx1)
  have e : ∑' k, ((eta1w k : ℚ) : ℝ) * x ^ triE k =
      ((eta1w 0 : ℚ) : ℝ) * x ^ triE 0 + ∑' k, ((eta1w (k + 1) : ℚ) : ℝ) * x ^ triE (k + 1) :=
    hsum.tsum_eq_zero_add
  have h : ∑' k, ((eta1w (k + 1) : ℚ) : ℝ) * x ^ triE (k + 1) =
      x ^ 4 * ∑' k, ((eta1w (k + 1) : ℚ) : ℝ) * x ^ t4E k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← t4E_add_four, pow_add]
      ring
  have h0 : ((eta1w 0 : ℚ) : ℝ) * x ^ triE 0 = x ^ 2 := by
    norm_num [eta1w, triE]
  rw [nomeEta1_eq_series hx0 hx1, e, h, h0, deltaEta]
  push_cast
  ring

/-- `E₂ = 1 − 24x² + x⁴ ε`. -/
theorem nomeE2_eq_cube {x : ℝ} (hx0 : 0 ≤ x) (hx4 : 4 * x < 1) :
    nomeE2 x = 1 - 24 * x ^ 2 + x ^ 4 * etE2 x := by
  have hsum : Summable fun k => ((e2w k : ℚ) : ℝ) * x ^ evenE k :=
    summable_series_geom evenE_strictMono (w := fun k => ((e2w k : ℚ) : ℝ)) (W := 24) (ρ := 4)
      (fun k => by
        have h : ((|e2w k| : ℚ) : ℝ) ≤ ((24 * 4 ^ k : ℚ) : ℝ) := Rat.cast_le.mpr (abs_e2w k)
        rw [Rat.cast_abs] at h
        simpa using h)
      (by norm_num) hx0 hx4
  have hsum1 : Summable fun k => ((e2w (k + 1) : ℚ) : ℝ) * x ^ evenE (k + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have e : ∑' k, ((e2w k : ℚ) : ℝ) * x ^ evenE k =
      ((e2w 0 : ℚ) : ℝ) * x ^ evenE 0 + ∑' k, ((e2w (k + 1) : ℚ) : ℝ) * x ^ evenE (k + 1) :=
    hsum.tsum_eq_zero_add
  have e1 : ∑' k, ((e2w (k + 1) : ℚ) : ℝ) * x ^ evenE (k + 1) =
      ((e2w (0 + 1) : ℚ) : ℝ) * x ^ evenE (0 + 1) +
        ∑' k, ((e2w (k + 1 + 1) : ℚ) : ℝ) * x ^ evenE (k + 1 + 1) :=
    hsum1.tsum_eq_zero_add
  have h : ∑' k, ((e2w (k + 1 + 1) : ℚ) : ℝ) * x ^ evenE (k + 1 + 1) =
      x ^ 4 * ∑' k, ((e2w (k + 1 + 1) : ℚ) : ℝ) * x ^ evenE k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      have hE : evenE (k + 1 + 1) = evenE k + 4 := by
        unfold evenE
        omega
      rw [hE, pow_add]
      ring
  have w0 : e2w 0 = -24 := by
    rw [← e2wList_spec 0 (by norm_num)]
    norm_num [e2wList]
  have w1 : e2w (0 + 1) = -72 := by
    rw [← e2wList_spec 1 (by norm_num)]
    norm_num [e2wList]
  have h0 : ((e2w 0 : ℚ) : ℝ) * x ^ evenE 0 = -24 * x ^ 2 := by
    rw [w0]
    norm_num [evenE]
  have h1 : ((e2w (0 + 1) : ℚ) : ℝ) * x ^ evenE (0 + 1) = -72 * x ^ 4 := by
    rw [w1]
    norm_num [evenE]
  rw [nomeE2_eq_series, e, e1, h, h0, h1, etE2]
  push_cast
  ring

/-! ## The models of the four series -/

/-- The model of `δ₃`, truncated after `N` terms. -/
def delta3MDD (Bx : Bounds) (N : ℕ) : MDD := seriesMDD Bx 2 (fun _ => 2) q4E 2 1 N

/-- The model of `δ₄`, truncated after `N` terms. -/
def delta4MDD (Bx : Bounds) (N : ℕ) : MDD :=
  seriesMDD Bx 2 (fun k => 2 * (-1) ^ (k + 1 + 1 + 1)) q4E 2 1 N

/-- The model of `δ_η`, truncated after `N` terms. -/
def deltaEtaMDD (Bx : Bounds) (N : ℕ) : MDD := seriesMDD Bx 0 (fun _ => 1) t4E 1 1 N

/-- The model of `ε`, truncated after `NE` terms. -/
def etE2MDD (Bx : Bounds) (NE : ℕ) : MDD :=
  seriesMDD Bx (-72) (fun k => e2wList.getD (k + 1 + 1) 0) evenE 384 4 NE

theorem approx_delta3MDD {Bx : Bounds} (h : SeriesOK Bx 4) (N : ℕ) {S : NEnv → Prop} :
    (delta3MDD Bx N).Approx Bx S (fun e => delta3 e.a) (fun e => delta3 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) q4E_strictMono q4E_zero (w := fun k => th3w (k + 1 + 1))
    (W := 2) (ρ := 1) (fun k => by simpa using abs_th3w (k + 1 + 1)) le_rfl h.one 2 N
    (fun _ => 2) (fun k _ => by simp [th3w])

theorem approx_delta4MDD {Bx : Bounds} (h : SeriesOK Bx 4) (N : ℕ) {S : NEnv → Prop} :
    (delta4MDD Bx N).Approx Bx S (fun e => delta4 e.a) (fun e => delta4 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) q4E_strictMono q4E_zero (w := fun k => th4w (k + 1 + 1))
    (W := 2) (ρ := 1) (fun k => by simpa using abs_th4w (k + 1 + 1)) le_rfl h.one 2 N
    (fun k => 2 * (-1) ^ (k + 1 + 1 + 1)) (fun k _ => by simp [th4w])

theorem approx_deltaEtaMDD {Bx : Bounds} (h : SeriesOK Bx 4) (N : ℕ) {S : NEnv → Prop} :
    (deltaEtaMDD Bx N).Approx Bx S (fun e => deltaEta e.a) (fun e => deltaEta e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) t4E_strictMono t4E_zero (w := fun k => eta1w (k + 1))
    (W := 1) (ρ := 1) (fun k => by simpa using abs_eta1w (k + 1)) le_rfl h.one 0 N
    (fun _ => 1) (fun k _ => by simp [eta1w])

theorem approx_etE2MDD {Bx : Bounds} (h : SeriesOK Bx 4) {NE : ℕ} (hNE : NE + 2 ≤ 12)
    {S : NEnv → Prop} :
    (etE2MDD Bx NE).Approx Bx S (fun e => etE2 e.a) (fun e => etE2 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) evenE_strictMono (by decide)
    (w := fun k => e2w (k + 1 + 1)) (W := 384) (ρ := 4)
    (fun k => by
      have h := abs_e2w (k + 1 + 1)
      have e : (24 : ℚ) * 4 ^ (k + 1 + 1) = ((384 : ℕ) : ℚ) * ((4 : ℕ) : ℚ) ^ k := by
        push_cast
        ring
      rwa [e] at h)
    (by norm_num) h (-72) NE (fun k => e2wList.getD (k + 1 + 1) 0)
    (fun k hk => e2wList_spec (k + 1 + 1) (by omega))

/-! ## The logarithms to the third order -/

/-- `Λ ℓ₂(θ₃ − 1)`. -/
noncomputable def lam2Theta3 (Λ : ℕ) (x : ℝ) : ℝ := (Λ : ℝ) * logRatioSh 2 (x * devTheta3 x)

/-- `Λ ℓ₂(θ₄ − 1)`. -/
noncomputable def lam2Theta4 (Λ : ℕ) (x : ℝ) : ℝ := (Λ : ℝ) * logRatioSh 2 (x * devTheta4 x)

/-- `Λ log θ₃ = 2Λ x − 2Λ x² + x³ (…)`. -/
theorem log_theta3_cube (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hs : |x * devTheta3 x| < 1) :
    (Λ : ℝ) * Real.log (nomeTheta3 x) = 2 * Λ * x - 2 * Λ * x ^ 2 +
      x ^ 3 * (Λ * x * delta3 x - 2 * Λ * x ^ 2 * delta3 x - Λ / 2 * x ^ 5 * delta3 x ^ 2 +
        devTheta3 x ^ 3 * lam2Theta3 Λ x) := by
  have hd := devTheta3_eq hx0 hx1
  rw [nomeTheta3_eq_one_add hx0 hx1, log_one_add_cube hs, lam2Theta3]
  generalize logRatioSh 2 (x * devTheta3 x) = L
  rw [hd]
  ring

/-- `Λ log θ₄ = −2Λ x − 2Λ x² + x³ (…)`. -/
theorem log_theta4_cube (Λ : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hs : |x * devTheta4 x| < 1) :
    (Λ : ℝ) * Real.log (nomeTheta4 x) = -(2 * Λ * x) - 2 * Λ * x ^ 2 +
      x ^ 3 * (Λ * x * delta4 x + 2 * Λ * x ^ 2 * delta4 x - Λ / 2 * x ^ 5 * delta4 x ^ 2 +
        devTheta4 x ^ 3 * lam2Theta4 Λ x) := by
  have hd := devTheta4_eq hx0 hx1
  rw [nomeTheta4_eq_one_add hx0 hx1, log_one_add_cube hs, lam2Theta4]
  generalize logRatioSh 2 (x * devTheta4 x) = L
  rw [hd]
  ring

/-! ## The six atoms and their models -/

/-- The atoms `δ₃, δ₄, δ_η, ε, Λ ℓ₂(θ₃ − 1), Λ ℓ₂(θ₄ − 1)`. -/
noncomputable def red3Atoms (Λ : ℕ) : List (ℝ → ℝ) :=
  [delta3, delta4, deltaEta, etE2, lam2Theta3 Λ, lam2Theta4 Λ]

/-- The models of the six atoms. -/
def red3AtomModels (Bx : Bounds) (D Dcap Λ n N' NE' : ℕ) : List MDD :=
  [delta3MDD Bx N', delta4MDD Bx N', deltaEtaMDD Bx N', etE2MDD Bx NE',
    MDD.rlogSh Bx D Dcap Λ n 2 (devTheta3MDD Bx N'),
    MDD.rlogSh Bx D Dcap Λ n 2 (devTheta4MDD Bx N')]

/-- The checks of the six atoms. -/
def Red3OK (Bx : Bounds) (D Dcap N' NE' : ℕ) : Prop :=
  SeriesOK Bx 4 ∧ NE' + 2 ≤ 12 ∧ MDD.RLogOK Bx D Dcap (devTheta3MDD Bx N') ∧
    MDD.RLogOK Bx D Dcap (devTheta4MDD Bx N')

instance (Bx : Bounds) (D Dcap N' NE' : ℕ) : Decidable (Red3OK Bx D Dcap N' NE') := by
  unfold Red3OK
  infer_instance

theorem red3Atoms_ok {Bx : Bounds} {D Dcap N' NE' : ℕ} (h : Red3OK Bx D Dcap N' NE') {Λ n : ℕ}
    (hΛ : ∀ i, i < n + 1 → (i + 2 + 1) ∣ Λ) {S : NEnv → Prop} :
    ISLP.AtomsOK Bx S (red3AtomModels Bx D Dcap Λ n N' NE') (red3Atoms Λ) := by
  obtain ⟨hS, hNE, h3, h4⟩ := h
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simpa [red3AtomModels, red3Atoms] using approx_delta3MDD hS N' (S := S)
  · simpa [red3AtomModels, red3Atoms] using approx_delta4MDD hS N' (S := S)
  · simpa [red3AtomModels, red3Atoms] using approx_deltaEtaMDD hS N' (S := S)
  · simpa [red3AtomModels, red3Atoms] using approx_etE2MDD hS hNE (S := S)
  · simpa [red3AtomModels, red3Atoms, lam2Theta3] using
      MDD.approx_rlogSh hS.1 D Dcap hΛ (approx_devTheta3MDD hS N' (S := S)) h3
  · simpa [red3AtomModels, red3Atoms, lam2Theta4] using
      MDD.approx_rlogSh hS.1 D Dcap hΛ (approx_devTheta4MDD hS N' (S := S)) h4
  · simpa [red3AtomModels, red3Atoms] using MDD.approx_zero (Bx := Bx) (S := S)

end E8Leech.Kron
