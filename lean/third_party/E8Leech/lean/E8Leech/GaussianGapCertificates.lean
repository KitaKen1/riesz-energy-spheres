import E8Leech.RieszGaussianIntegral

/-!
# Unweighted Gaussian family gaps supply the actual Riesz gap

The Euler weight is explicit and positive. Scaling actual ordered/lattice
energies first lets the checked Riesz mixture bridge use unweighted Gaussian
certificates. The existence of those certificates is still a proof obligation.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem orderedWindowEnergy_mul_left {d : ℕ} (a : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) :
    orderedWindowEnergy (fun x y => a * V x y) c W = a * orderedWindowEnergy V c W := by
  unfold orderedWindowEnergy
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) = (x : Ambient d) <;> simp [hy]
  · simp [hx]

theorem latticePotentialEnergy_mul_left {d : ℕ} (a : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (Λ : Set (Ambient d)) :
    latticePotentialEnergy Λ (fun x y => a * V x y) = a * latticePotentialEnergy Λ V := by
  unfold latticePotentialEnergy
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  by_cases hy : (y : Ambient d) = 0 <;> simp [hy]

theorem expected_orderedWindowEnergy_mul_left {d : ℕ} (a : ℝ≥0∞) (ha : a ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (μ : Measure (Configuration (Ambient d)))
    (W : Set (Ambient d)) :
    (∫⁻ c, orderedWindowEnergy (fun x y => a * V x y) c W ∂μ) =
      a * ∫⁻ c, orderedWindowEnergy V c W ∂μ := by
  simp_rw [orderedWindowEnergy_mul_left]
  exact lintegral_const_mul' a _ ha

def rieszGaussianWeight (s α : ℝ) : ℝ := α ^ (s / 2 - 1) / Real.Gamma (s / 2)

theorem rieszGaussianWeight_pos {s α : ℝ} (hs : 0 < s) (hα : 0 < α) :
    0 < rieszGaussianWeight s α := by
  exact div_pos (Real.rpow_pos_of_pos hα _) (Real.Gamma_pos_of_pos (by positivity))

theorem measurable_rieszGaussianWeight (s : ℝ) : Measurable (rieszGaussianWeight s) := by
  unfold rieszGaussianWeight
  fun_prop

theorem rieszGaussianFamily_eq_weighted_gaussian {d : ℕ} {s α : ℝ}
    (hs : 0 < s) (hα : 0 < α) (x y : Ambient d) :
    rieszGaussianFamily s α x y = ENNReal.ofReal (rieszGaussianWeight s α) *
      gaussianPotential α x y := by
  unfold gaussianPotential
  rw [← ENNReal.ofReal_mul (rieszGaussianWeight_pos hs hα).le]
  unfold rieszGaussianFamily rieszGaussianWeight gaussianKernel
  rw [dist_eq_norm]
  congr 1
  rw [show -(‖x - y‖ ^ 2 * α) = -α * ‖x - y‖ ^ 2 by ring]
  ring

theorem measurable_weighted_riesz_slack {d : ℕ} (s : ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2)) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      ENNReal.ofReal (rieszGaussianWeight s p.1) * V p.1 p.2.1 p.2.2) :=
  ((measurable_rieszGaussianWeight s).comp measurable_fst).ennreal_ofReal.mul hV

theorem expected_riesz_gap_of_unweighted_gaussian_gap {d : ℕ} {s : ℝ} (hs : 0 < s)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hgap : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      latticePotentialEnergy Λ (gaussianPotential α) +
        (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
        ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    latticeRieszEnergy Λ s +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (volume.restrict (Ioi (0 : ℝ)))
        (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y)) c
        (unitWindow d) ∂μ) ≤ rieszEnergy s μ := by
  apply expected_riesz_gap_of_gaussianFamily_gap hs μ _
    (measurable_weighted_riesz_slack s V hV) Λ hΛ
  filter_upwards [hgap, ae_restrict_mem measurableSet_Ioi] with α hgap hα
  have heq : rieszGaussianFamily (d := d) s α =
      fun x y => ENNReal.ofReal (rieszGaussianWeight s α) * gaussianPotential α x y := by
    funext x y
    exact rieszGaussianFamily_eq_weighted_gaussian hs hα x y
  rw [heq, latticePotentialEnergy_mul_left,
    expected_orderedWindowEnergy_mul_left _ ENNReal.ofReal_ne_top,
    expected_orderedWindowEnergy_mul_left _ ENNReal.ofReal_ne_top, ← mul_add]
  exact mul_le_mul_of_nonneg_left hgap zero_le

theorem stationarySlackGapInput_of_unweighted_gaussian_gap {d : ℕ} {s : ℝ} (hs : 0 < s)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    StationarySlackGapInput Λ s
      (potentialMixture (volume.restrict (Ioi (0 : ℝ)))
        (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y)) := by
  constructor
  intro μ hprob hμ hρ
  let := hprob
  by_cases henergy : rieszEnergy s μ = ∞
  · rw [henergy]
    exact le_top
  exact expected_riesz_gap_of_unweighted_gaussian_gap hs μ V hV Λ hΛ
    (hgap μ hprob hμ hρ henergy)

end E8Leech
