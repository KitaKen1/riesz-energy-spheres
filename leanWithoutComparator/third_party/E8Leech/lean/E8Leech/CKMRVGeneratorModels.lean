import E8Leech.CKMRVKExpr
import E8Leech.CKMRVNomeSeries

/-!
# Complete generator models for the kernel certificate

`generatorDD` supplies the five nome generators, including their divided differences.
`logarithmDD` supplies the three logarithms. Their computable side conditions are collected in
`LogarithmOK`; in particular positivity of the logarithm arguments follows from the certified
bound `|f - 1| < 1`, rather than being an extra analytic premise.
-/

namespace E8Leech.Taylor

/-- Models of `x`, `θ₃`, `θ₄`, `η₁`, and `E₂`, in the order used by `KExpr`. -/
def generatorDD (B : Box) (M : ℚ) (N : ℕ) : Fin 5 → DD
  | 0 => xDD
  | 1 => boundedGenDD B 1 th3w sqE 2 M N
  | 2 => boundedGenDD B 1 th4w sqE 2 M N
  | 3 => boundedGenDD B 1 eta1w triE 1 M N
  | 4 => geomGenDD B 1 e2w evenE 24 4 M N

theorem approx_generatorDD {B : Box} {M : ℚ} (hB : NomeOK B M) (hM : 4 * M < 1)
    (N : ℕ) {S : Env → Prop} (i : Fin 5) :
    (generatorDD B M N i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b) := by
  fin_cases i
  · exact approx_xDD
  · simpa only [generatorDD, genFun, nomeTheta3_eq_series, Rat.cast_one] using
      approx_boundedGenDD hB sqE_strictMono sqE_zero abs_th3w 1 N (S := S)
  · simpa only [generatorDD, genFun, nomeTheta4_eq_series, Rat.cast_one] using
      approx_boundedGenDD hB sqE_strictMono sqE_zero abs_th4w 1 N (S := S)
  · have h := approx_boundedGenDD hB triE_strictMono triE_zero abs_eta1w 1 N (S := S)
    refine ⟨TM.approx_congr h.1 ?_, TM.approx_congr h.2.1 ?_, TM.approx_congr h.2.2 ?_⟩
    · intro e he _
      obtain ⟨ha0, haM, -, -⟩ := hB.mem he
      simpa only [genFun, Rat.cast_one] using (nomeEta1_eq_series ha0
        (lt_of_le_of_lt haM (by exact_mod_cast (show M < 1 by linarith [hB.M_le])))).symm
    · intro e he _
      obtain ⟨-, -, hb0, hbM⟩ := hB.mem he
      simpa only [genFun, Rat.cast_one] using (nomeEta1_eq_series hb0
        (lt_of_le_of_lt hbM (by exact_mod_cast (show M < 1 by linarith [hB.M_le])))).symm
    · intro e he _
      obtain ⟨ha0, haM, hb0, hbM⟩ := hB.mem he
      have hM1 : (M : ℝ) < 1 := by exact_mod_cast (show M < 1 by linarith [hB.M_le])
      simp only [genFun, Rat.cast_one, nomeEta1_eq_series ha0 (lt_of_le_of_lt haM hM1),
        nomeEta1_eq_series hb0 (lt_of_le_of_lt hbM hM1)]
  · simpa only [generatorDD, genFun, nomeE2_eq_series, Rat.cast_one] using
      approx_geomGenDD hB evenE_strictMono evenE_zero abs_e2w (by norm_num) hM 1 N (S := S)

/-- The index of each logarithm argument in the generator vector. -/
def logarithmIndex : Fin 3 → Fin 5
  | 0 => 1
  | 1 => 2
  | 2 => 3

theorem logFun_eq_log_generator (j : Fin 3) (x : ℝ) :
    logFun j x = Real.log (genFun (logarithmIndex j) x) := by
  fin_cases j <;> rfl

/-- Apply the verified logarithm construction to the three generator triples. -/
def logarithmDD (B : Box) (M : ℚ) (N D n K : ℕ) (j : Fin 3) : DD :=
  DD.log B D n K (generatorDD B M N (logarithmIndex j))

/-- Rational inequalities required by the logarithm construction; all are computable. -/
structure LogarithmOK (B : Box) (M : ℚ) (N D K : ℕ) : Prop where
  left : ∀ j, TM.absBound B ((generatorDD B M N (logarithmIndex j)).A.sub (TM.const 1)) < 1
  right : ∀ j, TM.absBound B ((generatorDD B M N (logarithmIndex j)).B.sub (TM.const 1)) < 1
  difference : ∀ j, TM.absBound B (DD.logZ B D K (generatorDD B M N (logarithmIndex j))) < 1

theorem approx_logarithmDD {B : Box} {M : ℚ} (hB : NomeOK B M) (hM : 4 * M < 1)
    (N D n K : ℕ) (hL : LogarithmOK B M N D K) {S : Env → Prop} (j : Fin 3) :
    (logarithmDD B M N D n K j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b) := by
  have hG := approx_generatorDD hB hM N (S := S) (logarithmIndex j)
  have hpos : ∀ (T : TM) (f : Env → ℝ), T.Approx B S f →
      TM.absBound B (T.sub (TM.const 1)) < 1 → ∀ e, B.Mem e → S e → 0 < f e := by
    intro T f hf hbound e he hs
    have h := TM.abs_le_absBound hB.valid (TM.approx_sub hf (TM.approx_const 1)) he hs
    have hb : (TM.absBound B (T.sub (TM.const 1)) : ℝ) < 1 := by exact_mod_cast hbound
    have hn := neg_abs_le (f e - ((1 : ℚ) : ℝ))
    norm_num at h hn
    linarith
  have h := DD.approx_log hB.valid D n K hG
    (hpos _ _ hG.1 (hL.left j)) (hpos _ _ hG.2.1 (hL.right j))
    (hL.left j) (hL.right j) (hL.difference j)
  simpa only [logarithmDD, logFun_eq_log_generator] using h

end E8Leech.Taylor
