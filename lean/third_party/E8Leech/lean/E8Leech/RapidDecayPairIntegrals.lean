import E8Leech.PolynomialCellDecay

/-!
# Rapid-decay values suffice for full-space point-pair integrals

Only two value estimates, at orders zero and d+1, are needed. No derivative,
Fourier inversion, or additional moment assumption on the point process is
used here. `HasRapidDecay` is the order-zero value profile, not a definition
of smooth Schwartz functions. The actual CKMRV function must still be built
and proved to have this profile.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def HasRapidDecay {d : ℕ} (h : Ambient d → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ^ n * |h x| ≤ C

theorem padded_weight_bound_of_two_bounds {d : ℕ}
    (h : Ambient d → ℝ) (n : ℕ) (C₀ Cₙ : ℝ)
    (hC₀ : 0 ≤ C₀) (hCₙ : 0 ≤ Cₙ)
    (hzero : ∀ x, |h x| ≤ C₀) (hweighted : ∀ x, ‖x‖ ^ n * |h x| ≤ Cₙ)
    (x : Ambient d) :
    (1 + ‖x‖) ^ n * |h x| ≤ (2 : ℝ) ^ n * (C₀ + Cₙ) := by
  by_cases hx : ‖x‖ ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ n * C₀ := by gcongr; linarith; exact hzero x
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hlarge : 1 ≤ ‖x‖ := (not_le.mp hx).le
    calc
      _ ≤ (2 * ‖x‖) ^ n * |h x| := by gcongr; linarith
      _ = (2 : ℝ) ^ n * (‖x‖ ^ n * |h x|) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ n * Cₙ := mul_le_mul_of_nonneg_left (hweighted x) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Two known weighted bounds give an explicit nonsingular decay constant. -/
theorem polynomial_decay_of_two_bounds {d : ℕ}
    (h : Ambient d → ℝ) (n : ℕ) (C₀ Cₙ : ℝ)
    (hC₀ : 0 ≤ C₀) (hCₙ : 0 ≤ Cₙ)
    (hzero : ∀ x, |h x| ≤ C₀) (hweighted : ∀ x, ‖x‖ ^ n * |h x| ≤ Cₙ)
    (x : Ambient d) :
    |h x| ≤ ((2 : ℝ) ^ n * (C₀ + Cₙ)) * (1 + ‖x‖) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (show 0 < (1 + ‖x‖) ^ n by positivity)).mpr
  simpa only [mul_comm] using padded_weight_bound_of_two_bounds h n C₀ Cₙ hC₀ hCₙ
    hzero hweighted x

theorem exists_polynomial_decay_of_rapidDecay {d : ℕ}
    (h : Ambient d → ℝ) (hdecay : HasRapidDecay h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |h x| ≤ C * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
  obtain ⟨C₀, hC₀, hzero⟩ := hdecay 0
  simp only [pow_zero, one_mul] at hzero
  obtain ⟨Cₙ, hCₙ, hweighted⟩ := hdecay (d + 1)
  refine ⟨(2 : ℝ) ^ (d + 1) * (C₀ + Cₙ), by positivity, ?_⟩
  exact polynomial_decay_of_two_bounds h (d + 1) C₀ Cₙ hC₀ hCₙ hzero hweighted

theorem exists_summable_difference_cell_envelope_of_rapidDecay {d : ℕ}
    (h : Ambient d → ℝ) (hdecay : HasRapidDecay h) (a : Ambient d) :
    ∃ M : IntegerCellIndex d → ℝ, (∑' z, ENNReal.ofReal (M z)) ≠ ∞ ∧
      ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
        ∀ y ∈ integerCell z, |h (x - y)| ≤ M z := by
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_decay_of_rapidDecay h hdecay
  exact exists_summable_difference_cell_envelope h C hC
    (by exact_mod_cast Nat.lt_succ_self d) hbound a

theorem measurable_ofReal_abs_difference {d : ℕ}
    (h : Ambient d → ℝ) (hh : Measurable h) :
    Measurable (Function.uncurry (fun x y => ENNReal.ofReal |h (x - y)|)) := by
  change Measurable (fun q : Ambient d × Ambient d => ENNReal.ofReal |h (q.1 - q.2)|)
  have hpair : Measurable (fun q : Ambient d × Ambient d => h (q.1 - q.2)) :=
    hh.comp (measurable_fst.sub measurable_snd)
  simpa only [Real.norm_eq_abs] using hpair.norm.ennreal_ofReal

theorem expected_abs_difference_pair_univ_ne_top_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ) ≠ ∞ := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_difference_cell_envelope_of_rapidDecay h hdecay a
  have hm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal |h (x - y)|)) :=
    measurable_ofReal_abs_difference h hh
  exact expected_pair_univ_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy _ hm a
    (fun z => ENNReal.ofReal (M z)) hM
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal (hbound z x hx y hy))

theorem integrable_signed_difference_pair_univ_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    Integrable (fun c => signedLocalizedPairIntegral (fun x y => h (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ) μ := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_difference_cell_envelope_of_rapidDecay h hdecay a
  exact integrable_signed_pair_univ_of_riesz hs μ hμ ρ hρ hρtop henergy
    (fun x y => h (x - y)) (hh.comp (measurable_fst.sub measurable_snd)) a M hM hbound

theorem tendsto_expected_abs_difference_pair_tail_zero_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    Filter.Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
        ((fun x => a + x) ⁻¹' unitWindow d) (integerCellTail F) ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_difference_cell_envelope_of_rapidDecay h hdecay a
  have hm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal |h (x - y)|)) :=
    measurable_ofReal_abs_difference h hh
  exact tendsto_expected_pair_tail_zero_of_riesz hs μ hμ ρ hρ hρtop henergy _ hm a
    (fun z => ENNReal.ofReal (M z)) hM
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal (hbound z x hx y hy))

theorem exists_uniform_abs_difference_pair_tail_cutoff_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h)
    (a : Ambient d) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F₀ : Finset (IntegerCellIndex d),
      ∀ F : Finset (IntegerCellIndex d), F₀ ⊆ F →
      ∀ μ : Measure (Configuration (Ambient d)), IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
        ((fun x => a + x) ⁻¹' unitWindow d) (integerCellTail F) ∂μ) < ε := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_difference_cell_envelope_of_rapidDecay h hdecay a
  have hm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal |h (x - y)|)) :=
    measurable_ofReal_abs_difference h hh
  exact exists_uniform_pair_tail_cutoff hs L Δ hLtop hΔtop _ hm a
    (fun z => ENNReal.ofReal (M z)) hM
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal (hbound z x hx y hy)) ε hε

end E8Leech
