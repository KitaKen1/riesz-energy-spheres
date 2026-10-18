import E8Leech.KronGenerators

/-!
# Generators divided by the nome

At the cusp `x = 0` the generators `θ₄` and `E₂` equal `1`. The quotients

`(θ₄(x) − 1)/x = −2 + 2x³ − 2x⁸ + …`,  `(E₂(x) − 1)/x = −24x − 72x³ − …`

are series of the same kind, so they have models with divided differences. A numerator that
vanishes at the cusp of the second variable can then be written as the nome times an expression
in these quotients, and its divided difference inherits the factor: the majorants do not have to
see a cancellation.

* `devTheta4`, `devE2`: the quotients; `nomeTheta4_eq_one_add`, `nomeE2_eq_one_add`.
* `devTheta4MDD`, `devE2MDD`: their models; `approx_devTheta4MDD`, `approx_devE2MDD`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-- The exponents `(k + 2)² − 1` of `(θ₄ − 1)/x` after its constant term. -/
def dsqE (k : ℕ) : ℕ := (k + 2) ^ 2 - 1

/-- The exponents `2k + 1` of `(E₂ − 1)/x`. -/
def oddE (k : ℕ) : ℕ := 2 * k + 1

theorem dsqE_strictMono : StrictMono dsqE := fun i j h => by
  unfold dsqE
  have h1 : (i + 2) ^ 2 < (j + 2) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : 1 ≤ (i + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem oddE_strictMono : StrictMono oddE := fun i j h => by
  unfold oddE
  omega

theorem dsqE_zero : 1 ≤ dsqE 0 := by decide

theorem oddE_zero : 1 ≤ oddE 0 := by decide

theorem dsqE_add_one (k : ℕ) : dsqE k + 1 = sqE (k + 1) := by
  have h2 : 1 ≤ (k + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  show (k + 2) ^ 2 - 1 + 1 = (k + 2) ^ 2
  exact Nat.sub_add_cancel h2

theorem oddE_add_one (k : ℕ) : oddE k + 1 = evenE k := by
  unfold oddE evenE
  omega

/-- `(θ₄(x) − 1)/x` as a series. -/
noncomputable def devTheta4 (x : ℝ) : ℝ :=
  ((-2 : ℤ) : ℝ) + ∑' k, ((th4w (k + 1) : ℚ) : ℝ) * x ^ dsqE k

/-- `(E₂(x) − 1)/x` as a series. -/
noncomputable def devE2 (x : ℝ) : ℝ :=
  ((0 : ℤ) : ℝ) + ∑' k, ((e2w k : ℚ) : ℝ) * x ^ oddE k

theorem nomeE2_eq_one_add (x : ℝ) : nomeE2 x = 1 + x * devE2 x := by
  have h : ∑' k, ((e2w k : ℚ) : ℝ) * x ^ evenE k = x * ∑' k, ((e2w k : ℚ) : ℝ) * x ^ oddE k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← oddE_add_one, pow_succ]
      ring
  rw [nomeE2_eq_series, h, devE2]
  push_cast
  ring

theorem nomeTheta4_eq_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeTheta4 x = 1 + x * devTheta4 x := by
  have hsum : Summable fun k => ((th4w k : ℚ) : ℝ) * x ^ sqE k :=
    summable_series_geom sqE_strictMono (w := fun k => ((th4w k : ℚ) : ℝ)) (W := 2) (ρ := 1)
      (fun k => by
        have h : ((|th4w k| : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_th4w k)
        rw [Rat.cast_abs] at h
        simpa using h)
      le_rfl hx0 (by simpa using hx1)
  have e : ∑' k, ((th4w k : ℚ) : ℝ) * x ^ sqE k =
      ((th4w 0 : ℚ) : ℝ) * x ^ sqE 0 + ∑' k, ((th4w (k + 1) : ℚ) : ℝ) * x ^ sqE (k + 1) :=
    hsum.tsum_eq_zero_add
  have h : ∑' k, ((th4w (k + 1) : ℚ) : ℝ) * x ^ sqE (k + 1) =
      x * ∑' k, ((th4w (k + 1) : ℚ) : ℝ) * x ^ dsqE k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by
      rw [← dsqE_add_one, pow_succ]
      ring
  have h0 : ((th4w 0 : ℚ) : ℝ) * x ^ sqE 0 = -2 * x := by
    norm_num [th4w, sqE]
  rw [nomeTheta4_eq_series, e, h, h0, devTheta4]
  push_cast
  ring

/-- The model of `(θ₄ − 1)/x`, truncated after `N` terms. -/
def devTheta4MDD (Bx : Bounds) (N : ℕ) : MDD :=
  seriesMDD Bx (-2) (fun k => 2 * (-1) ^ (k + 1 + 1)) dsqE 2 1 N

/-- The model of `(E₂ − 1)/x`, truncated after `NE` terms. -/
def devE2MDD (Bx : Bounds) (NE : ℕ) : MDD :=
  seriesMDD Bx 0 (fun k => e2wList.getD k 0) oddE 24 4 NE

theorem approx_devTheta4MDD {Bx : Bounds} (h : SeriesOK Bx 4) (N : ℕ) {S : NEnv → Prop} :
    (devTheta4MDD Bx N).Approx Bx S (fun e => devTheta4 e.a) (fun e => devTheta4 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) dsqE_strictMono dsqE_zero (w := fun k => th4w (k + 1))
    (W := 2) (ρ := 1) (fun k => by simpa using abs_th4w (k + 1)) le_rfl h.one (-2) N
    (fun k => 2 * (-1) ^ (k + 1 + 1)) (fun k _ => by simp [th4w])

theorem approx_devE2MDD {Bx : Bounds} {NE : ℕ} (h : GenOK Bx NE) {S : NEnv → Prop} :
    (devE2MDD Bx NE).Approx Bx S (fun e => devE2 e.a) (fun e => devE2 e.b) :=
  approx_seriesMDD (Bx := Bx) (S := S) oddE_strictMono oddE_zero (w := e2w) (W := 24) (ρ := 4)
    (fun k => by simpa using abs_e2w k) (by norm_num) h.1 0 NE (fun k => e2wList.getD k 0)
    (fun k hk => e2wList_spec k (lt_of_lt_of_le hk h.2))

end E8Leech.Kron
