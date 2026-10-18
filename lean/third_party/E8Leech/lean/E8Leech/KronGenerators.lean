import E8Leech.KronSeries

/-!
# The five generators and three logarithms as models with majorants

`generatorMDD` gives the nome and the series `θ₃, θ₄, η₁, E₂` with the generator functions of
`CKMRVKExpr` as their meaning; `logarithmMDD` gives `Λ` times the logarithms of `θ₃, θ₄, η₁`.
The Eisenstein series has its own truncation order `NE`. Its integer weights `−24 σ₁(k+1)` are
tabulated for `k < 12` and compared with the arithmetic function by the kernel.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

/-- The nome itself: `(a, b, 1)`. -/
def xMDD : MDD :=
  ⟨⟨[(⟨1, 0, 0, 0, 0⟩, 1)], []⟩, ⟨[(⟨0, 1, 0, 0, 0⟩, 1)], []⟩, ⟨[(NMono.one, 1)], []⟩⟩

theorem approx_xMDD {Bx : Bounds} {S : NEnv → Prop} :
    xMDD.Approx Bx S (fun e => e.a) (fun e => e.b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e _ _
    simp [xMDD, NMono.eval]
  · intro e _ _
    simp [xMDD, NMono.eval]
  · intro e _ hs
    have h : e.b - e.a ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
    simp [xMDD, NMono.eval_one, div_self h]

/-- `−24 σ₁(k + 1)` for `k < 12`. -/
def e2wList : List ℤ := [-24, -72, -96, -168, -144, -288, -192, -360, -312, -432, -288, -672]

theorem e2wList_spec : ∀ k, k < 12 → ((e2wList.getD k 0 : ℤ) : ℚ) = e2w k := by
  decide +kernel

/-- Models of `x, θ₃, θ₄, η₁, E₂`, in the order of `genFun`. -/
def generatorMDD (Bx : Bounds) (N NE : ℕ) : Fin 5 → MDD
  | 0 => xMDD
  | 1 => seriesMDD Bx 1 (fun _ => 2) sqE 2 1 N
  | 2 => seriesMDD Bx 1 (fun k => 2 * (-1) ^ (k + 1)) sqE 2 1 N
  | 3 => seriesMDD Bx 1 (fun _ => 1) triE 1 1 N
  | 4 => seriesMDD Bx 1 (fun k => e2wList.getD k 0) evenE 24 4 NE

/-- The nome bounds leave room for the tails, and the `E₂` table is long enough. -/
def GenOK (Bx : Bounds) (NE : ℕ) : Prop := SeriesOK Bx 4 ∧ NE ≤ 12

instance (Bx : Bounds) (NE : ℕ) : Decidable (GenOK Bx NE) := by
  unfold GenOK
  infer_instance

theorem SeriesOK.one {Bx : Bounds} (h : SeriesOK Bx 4) : SeriesOK Bx 1 := by
  obtain ⟨hB, h1, h2, h3⟩ := h
  exact ⟨hB, by omega, by omega, by omega⟩

theorem nome_lt_one {Bx : Bounds} (h : SeriesOK Bx 4) {e : NEnv} (he : Bx.Mem e) :
    e.a < 1 ∧ e.b < 1 := by
  obtain ⟨hB, h1, h2, -⟩ := h
  obtain ⟨-, ha', -, hb', -⟩ := he
  have hda : (0 : ℝ) < Bx.ad := by exact_mod_cast hB.1
  have hdb : (0 : ℝ) < Bx.bd := by exact_mod_cast hB.2.1
  have k1 : ((4 * Bx.an : ℕ) : ℝ) < Bx.ad := by exact_mod_cast h1
  have k2 : ((4 * Bx.bn : ℕ) : ℝ) < Bx.bd := by exact_mod_cast h2
  push_cast at k1 k2
  constructor
  · by_contra hcon
    have := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hda.le
    have hn : (0 : ℝ) ≤ Bx.an := Nat.cast_nonneg _
    linarith
  · by_contra hcon
    have := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hdb.le
    have hn : (0 : ℝ) ≤ Bx.bn := Nat.cast_nonneg _
    linarith

theorem approx_generatorMDD {Bx : Bounds} {NE : ℕ} (h : GenOK Bx NE) (N : ℕ)
    {S : NEnv → Prop} (i : Fin 5) :
    (generatorMDD Bx N NE i).Approx Bx S (fun e => genFun i e.a) (fun e => genFun i e.b) := by
  obtain ⟨hOK, hNE⟩ := h
  have hOK1 := hOK.one
  fin_cases i
  · simpa [generatorMDD, genFun] using approx_xMDD (Bx := Bx) (S := S)
  · have h1 := approx_seriesMDD (Bx := Bx) (S := S) sqE_strictMono sqE_zero (w := th3w)
      (W := 2) (ρ := 1) (fun k => by simpa using abs_th3w k) le_rfl hOK1 1 N (fun _ => 2)
      (fun k _ => by simp [th3w])
    refine MDD.approx_congr h1 (fun e _ _ => ?_) (fun e _ _ => ?_)
    · simp [genFun, nomeTheta3_eq_series]
    · simp [genFun, nomeTheta3_eq_series]
  · have h1 := approx_seriesMDD (Bx := Bx) (S := S) sqE_strictMono sqE_zero (w := th4w)
      (W := 2) (ρ := 1) (fun k => by simpa using abs_th4w k) le_rfl hOK1 1 N
      (fun k => 2 * (-1) ^ (k + 1)) (fun k _ => by simp [th4w])
    refine MDD.approx_congr h1 (fun e _ _ => ?_) (fun e _ _ => ?_)
    · simp [genFun, nomeTheta4_eq_series]
    · simp [genFun, nomeTheta4_eq_series]
  · have h1 := approx_seriesMDD (Bx := Bx) (S := S) triE_strictMono triE_zero (w := eta1w)
      (W := 1) (ρ := 1) (fun k => by simpa using abs_eta1w k) le_rfl hOK1 1 N (fun _ => 1)
      (fun k _ => by simp [eta1w])
    refine MDD.approx_congr h1 (fun e he _ => ?_) (fun e he _ => ?_)
    · have hlt := (nome_lt_one hOK he).1
      simp [genFun, nomeEta1_eq_series he.1 hlt]
    · have hlt := (nome_lt_one hOK he).2
      simp [genFun, nomeEta1_eq_series he.2.2.1 hlt]
  · have h1 := approx_seriesMDD (Bx := Bx) (S := S) evenE_strictMono evenE_zero (w := e2w)
      (W := 24) (ρ := 4) (fun k => by simpa using abs_e2w k) (by norm_num) hOK 1 NE
      (fun k => e2wList.getD k 0) (fun k hk => e2wList_spec k (lt_of_lt_of_le hk hNE))
    refine MDD.approx_congr h1 (fun e _ _ => ?_) (fun e _ _ => ?_)
    · simp [genFun, nomeE2_eq_series]
    · simp [genFun, nomeE2_eq_series]

/-- `Λ` times the logarithms of `θ₃, θ₄, η₁`. -/
def logarithmMDD (Bx : Bounds) (D Dcap Λ n K N NE : ℕ) (j : Fin 3) : MDD :=
  MDD.log Bx D Dcap Λ n K (generatorMDD Bx N NE (logarithmIndex j))

/-- The smallness checks of the three logarithms. -/
def LogsOK (Bx : Bounds) (D Dcap K N NE : ℕ) : Prop :=
  ∀ j : Fin 3, MDD.LogOK Bx D Dcap K (generatorMDD Bx N NE (logarithmIndex j))

instance (Bx : Bounds) (D Dcap K N NE : ℕ) : Decidable (LogsOK Bx D Dcap K N NE) := by
  unfold LogsOK
  infer_instance

theorem approx_logarithmMDD {Bx : Bounds} {NE : ℕ} (hG : GenOK Bx NE) (D Dcap : ℕ)
    {Λ n : ℕ} (K N : ℕ) (hΛ : ∀ i, i < n → (i + 1) ∣ Λ) (hL : LogsOK Bx D Dcap K N NE)
    {S : NEnv → Prop} (j : Fin 3) :
    (logarithmMDD Bx D Dcap Λ n K N NE j).Approx Bx S (fun e => Λ * logFun j e.a)
      (fun e => Λ * logFun j e.b) := by
  have h := MDD.approx_log hG.1.1 D Dcap K hΛ
    (approx_generatorMDD hG N (S := S) (logarithmIndex j)) (hL j)
  refine MDD.approx_congr h (fun e _ _ => ?_) (fun e _ _ => ?_)
  · rw [logFun_eq_log_generator]
  · rw [logFun_eq_log_generator]

end E8Leech.Kron
