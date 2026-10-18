import E8Leech.CKMRVSeriesTMGeom
import E8Leech.TaylorModelLogDD
import E8Leech.CKMRVNomeSeries

/-!
# Divided-difference Taylor models of the nome generators

Triples (value at `a`, value at `b`, divided difference) for the generators of the axis numerator:
the nome `x` itself, `θ₃`, `θ₄`, `η₁` (bounded weights) and `E₂` (weights `24 σ₁(k+1) ≤ 24·4ᵏ`).
The remainders depend only on the box bounds `ahi, bhi` and on a common bound `M ≥ ahi, bhi`.
-/

namespace E8Leech.Taylor

open scoped Real

/-! ## Exponents and weights -/

def sqE (k : ℕ) : ℕ := (k + 1) ^ 2
def triE (k : ℕ) : ℕ := (k + 1) * (k + 2)
def evenE (k : ℕ) : ℕ := 2 * (k + 1)

theorem sqE_strictMono : StrictMono sqE := fun i j h => by
  unfold sqE
  exact Nat.pow_lt_pow_left (by omega) (by norm_num)

theorem triE_strictMono : StrictMono triE := fun i j h => by
  unfold triE
  exact Nat.mul_lt_mul'' (by omega) (by omega)

theorem evenE_strictMono : StrictMono evenE := fun i j h => by
  unfold evenE
  omega

theorem sqE_zero : 1 ≤ sqE 0 := by decide
theorem triE_zero : 1 ≤ triE 0 := by decide
theorem evenE_zero : 1 ≤ evenE 0 := by decide

def th3w (_ : ℕ) : ℚ := 2
def th4w (k : ℕ) : ℚ := 2 * (-1) ^ (k + 1)
def eta1w (_ : ℕ) : ℚ := 1
def e2w (k : ℕ) : ℚ := -24 * (ArithmeticFunction.sigma 1 (k + 1) : ℚ)

theorem abs_th3w (k : ℕ) : |th3w k| ≤ 2 := by simp [th3w]
theorem abs_th4w (k : ℕ) : |th4w k| ≤ 2 := by
  simp [th4w, abs_mul, abs_pow]
theorem abs_eta1w (k : ℕ) : |eta1w k| ≤ 1 := by simp [eta1w]
theorem abs_e2w (k : ℕ) : |e2w k| ≤ 24 * 4 ^ k := by
  have h := sigma_one_succ_le_four_pow k
  simp only [e2w, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℚ) ≤ 24)]
  rw [abs_of_nonneg (by positivity)]
  have : (ArithmeticFunction.sigma 1 (k + 1) : ℚ) ≤ 4 ^ k := by exact_mod_cast h
  linarith

/-! ## The nome series in sparse form -/

theorem nomeTheta3_eq_series (x : ℝ) :
    nomeTheta3 x = (1 : ℚ) + ∑' k, (th3w k : ℝ) * x ^ sqE k := by
  simp only [nomeTheta3, th3w, sqE, tsum_mul_left]
  push_cast
  ring

theorem nomeTheta4_eq_series (x : ℝ) :
    nomeTheta4 x = (1 : ℚ) + ∑' k, (th4w k : ℝ) * x ^ sqE k := by
  simp only [nomeTheta4, th4w, sqE]
  push_cast
  rw [← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by ring

theorem nomeEta1_eq_series {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    nomeEta1 x = (1 : ℚ) + ∑' k, (eta1w k : ℝ) * x ^ triE k := by
  rw [nomeEta1, (summable_pow_triangular hx0 hx1).tsum_eq_zero_add]
  simp only [eta1w, triE]
  push_cast
  congr 1
  exact tsum_congr fun k => by ring_nf

theorem nomeE2_eq_series (x : ℝ) :
    nomeE2 x = (1 : ℚ) + ∑' k, (e2w k : ℝ) * x ^ evenE k := by
  simp only [nomeE2, eisensteinTwoQ, e2w, evenE]
  push_cast
  rw [sub_eq_add_neg, ← neg_mul, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by rw [pow_mul]; ring

/-! ## Generator triples -/

/-- The triple of a sparse series with given remainders. -/
def seriesGenDD (c0 : ℚ) (w : ℕ → ℚ) (E : ℕ → ℕ) (N : ℕ) (rA rB rD : ℚ) : DD :=
  ⟨⟨seriesPoly true c0 w E N, rA⟩, ⟨seriesPoly false c0 w E N, rB⟩, ⟨seriesDDPoly w E N, rD⟩⟩

/-- Remainders for bounded weights `|wₖ| ≤ W`. -/
def boundedGenDD (B : Box) (c0 : ℚ) (w : ℕ → ℚ) (E : ℕ → ℕ) (W M : ℚ) (N : ℕ) : DD :=
  seriesGenDD c0 w E N (W * B.ahi ^ E N / (1 - B.ahi)) (W * B.bhi ^ E N / (1 - B.bhi))
    (W * E N * M ^ (E N - 1) / (1 - M) ^ 2)

/-- Remainders for weights `|wₖ| ≤ W ρᵏ`. -/
def geomGenDD (B : Box) (c0 : ℚ) (w : ℕ → ℚ) (E : ℕ → ℕ) (W ρ M : ℚ) (N : ℕ) : DD :=
  seriesGenDD c0 w E N (W * ρ ^ N * B.ahi ^ E N / (1 - ρ * B.ahi))
    (W * ρ ^ N * B.bhi ^ E N / (1 - ρ * B.bhi)) (W * ρ ^ N * E N * M ^ (E N - 1) / (1 - ρ * M) ^ 2)

/-- The nome bounds of a box used by the generator lemmas. -/
structure NomeOK (B : Box) (M : ℚ) : Prop where
  valid : B.Valid
  ahi_le : B.ahi ≤ M
  bhi_le : B.bhi ≤ M
  M_le : M ≤ 1 / 2

theorem NomeOK.mem {B : Box} {M : ℚ} (h : NomeOK B M) {e : Env} (he : B.Mem e) :
    0 ≤ e.a ∧ e.a ≤ M ∧ 0 ≤ e.b ∧ e.b ≤ M := by
  obtain ⟨ha0, hb0, -, -, -, -⟩ := h.valid
  obtain ⟨ha1, ha2, hb1, hb2, -⟩ := he
  refine ⟨le_trans (by exact_mod_cast ha0) ha1, le_trans ha2 (by exact_mod_cast h.ahi_le),
    le_trans (by exact_mod_cast hb0) hb1, le_trans hb2 (by exact_mod_cast h.bhi_le)⟩

theorem approx_boundedGenDD {B : Box} {M : ℚ} (h : NomeOK B M) {S : Env → Prop} {E : ℕ → ℕ}
    (hE : StrictMono E) (hE0 : 1 ≤ E 0) {w : ℕ → ℚ} {W : ℚ} (hw : ∀ k, |w k| ≤ W) (c0 : ℚ)
    (N : ℕ) :
    (boundedGenDD B c0 w E W M N).Approx B S
      (fun e => c0 + ∑' k, (w k : ℝ) * e.a ^ E k) (fun e => c0 + ∑' k, (w k : ℝ) * e.b ^ E k) := by
  have hM1 : M < 1 := by linarith [h.M_le]
  refine ⟨?_, ?_, ?_⟩
  · exact seriesTM_approx true hE hw c0 N (lt_of_le_of_lt h.ahi_le hM1) fun e he => by
      obtain ⟨h1, h2, -, -⟩ := h.mem he
      exact ⟨h1, by
        obtain ⟨-, ha2, -⟩ := he
        simpa [Env.nome] using ha2⟩
  · exact seriesTM_approx false hE hw c0 N (lt_of_le_of_lt h.bhi_le hM1) fun e he => by
      obtain ⟨-, -, h3, -⟩ := h.mem he
      exact ⟨h3, by
        obtain ⟨-, -, -, hb2, -⟩ := he
        simpa [Env.nome] using hb2⟩
  · exact seriesDD_approx hE hE0 hw c0 N h.M_le fun e he => h.mem he

theorem approx_geomGenDD {B : Box} {M : ℚ} (h : NomeOK B M) {S : Env → Prop} {E : ℕ → ℕ}
    (hE : StrictMono E) (hE0 : 1 ≤ E 0) {w : ℕ → ℚ} {W ρ : ℚ} (hw : ∀ k, |w k| ≤ W * ρ ^ k)
    (hρ : 1 ≤ ρ) (hρM : ρ * M < 1) (c0 : ℚ) (N : ℕ) :
    (geomGenDD B c0 w E W ρ M N).Approx B S
      (fun e => c0 + ∑' k, (w k : ℝ) * e.a ^ E k) (fun e => c0 + ∑' k, (w k : ℝ) * e.b ^ E k) := by
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
  refine ⟨?_, ?_, ?_⟩
  · exact seriesTM_approx_geom true hE hw hρ c0 N
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h.ahi_le hρ0) hρM) fun e he => by
      obtain ⟨h1, -, -, -⟩ := h.mem he
      exact ⟨h1, by
        obtain ⟨-, ha2, -⟩ := he
        simpa [Env.nome] using ha2⟩
  · exact seriesTM_approx_geom false hE hw hρ c0 N
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h.bhi_le hρ0) hρM) fun e he => by
      obtain ⟨-, -, h3, -⟩ := h.mem he
      exact ⟨h3, by
        obtain ⟨-, -, -, hb2, -⟩ := he
        simpa [Env.nome] using hb2⟩
  · exact seriesDD_approx_geom hE hE0 hw hρ c0 N h.M_le hρM fun e he => h.mem he

/-- The nome itself: `(a, b, 1)`. -/
def xDD : DD :=
  ⟨⟨[(⟨1, 0, 0, 0, 0, 0⟩, 1)], 0⟩, ⟨[(⟨0, 1, 0, 0, 0, 0⟩, 1)], 0⟩, ⟨[(Mono.one, 1)], 0⟩⟩

theorem approx_xDD {B : Box} {S : Env → Prop} : xDD.Approx B S (fun e => e.a) (fun e => e.b) := by
  refine ⟨fun e _ _ => ?_, fun e _ _ => ?_, fun e _ hs => ?_⟩
  · simp [xDD, Mono.eval]
  · simp [xDD, Mono.eval]
  · have hba : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
    simp [xDD, Mono.eval_one, div_self hba]

end E8Leech.Taylor
