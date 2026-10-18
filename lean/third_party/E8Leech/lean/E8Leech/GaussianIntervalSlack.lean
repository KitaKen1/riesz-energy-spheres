import E8Leech.GaussianGapCertificates

/-!
# A positive Gaussian parameter interval supplies the Riesz quadratic cost

The Euler weight has an explicit positive lower bound on a positive compact
interval. Integrating a Gaussian slack lower bound there supplies the exact
law-independent coefficient required by the existing transfer theorem.
The actual Gaussian gaps and common interval slack remain hypotheses to prove.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def rieszIntervalWeightLower (s a b : ℝ) : ℝ :=
  min (a ^ (s / 2 - 1)) (b ^ (s / 2 - 1)) / Real.Gamma (s / 2)

def rieszIntervalGapCoefficient (s a b k : ℝ) : ℝ :=
  rieszIntervalWeightLower s a b * k * (b - a)

theorem rieszIntervalWeightLower_pos {s a b : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hab : a < b) : 0 < rieszIntervalWeightLower s a b := by
  apply div_pos
  · exact lt_min (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos (ha.trans hab) _)
  · exact Real.Gamma_pos_of_pos (by positivity)

theorem rieszIntervalWeightLower_le {s a b α : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hα : α ∈ Icc a b) :
    rieszIntervalWeightLower s a b ≤ rieszGaussianWeight s α := by
  unfold rieszIntervalWeightLower rieszGaussianWeight
  apply div_le_div_of_nonneg_right _ (Real.Gamma_pos_of_pos (by positivity)).le
  by_cases hp : 0 ≤ s / 2 - 1
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow ha.le hα.1 hp)
  · exact (min_le_right _ _).trans
      (Real.rpow_le_rpow_of_nonpos (ha.trans_le hα.1) hα.2 (not_le.mp hp).le)

theorem rieszIntervalGapCoefficient_pos {s a b k : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hab : a < b) (hk : 0 < k) :
    0 < rieszIntervalGapCoefficient s a b k :=
  mul_pos (mul_pos (rieszIntervalWeightLower_pos hs ha hab) hk) (sub_pos.mpr hab)

theorem volume_positive_parameter_interval {a b : ℝ} (ha : 0 < a) :
    volume.restrict (Ioi (0 : ℝ)) (Icc a b) = ENNReal.ofReal (b - a) := by
  rw [Measure.restrict_apply measurableSet_Icc]
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun α hα => ha.trans_le hα.1
  rw [inter_eq_left.mpr hsub, Real.volume_Icc]

theorem riesz_weighted_slack_interval_lower {d : ℕ} {s a b k : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b) (hk : 0 < k)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) (t : ℝ) (x y : Ambient d)
    (hlower : ∀ α ∈ Icc a b, ENNReal.ofReal (k * t ^ 2) ≤ V α x y) :
    ENNReal.ofReal (rieszIntervalGapCoefficient s a b k * t ^ 2) ≤
      potentialMixture (volume.restrict (Ioi (0 : ℝ)))
        (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y) x y := by
  have hlow := (rieszIntervalWeightLower_pos hs ha hab).le
  have hp := potentialMixture_lower_on_parameter_set
    (volume.restrict (Ioi (0 : ℝ)))
    (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y)
    (A := Icc a b) measurableSet_Icc
    (ENNReal.ofReal (rieszIntervalWeightLower s a b * (k * t ^ 2))) x y ?_
  · have heq : ENNReal.ofReal (rieszIntervalGapCoefficient s a b k * t ^ 2) =
        ENNReal.ofReal (rieszIntervalWeightLower s a b * (k * t ^ 2)) *
          volume.restrict (Ioi (0 : ℝ)) (Icc a b) := by
      rw [volume_positive_parameter_interval ha,
        ← ENNReal.ofReal_mul (mul_nonneg hlow (mul_nonneg hk.le (sq_nonneg t)))]
      congr 1
      unfold rieszIntervalGapCoefficient
      ring
    rw [heq]
    exact hp
  · intro α hα
    rw [ENNReal.ofReal_mul hlow]
    calc
      _ ≤ ENNReal.ofReal (rieszGaussianWeight s α) * ENNReal.ofReal (k * t ^ 2) :=
        mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (rieszIntervalWeightLower_le hs ha hα)) zero_le
      _ ≤ ENNReal.ofReal (rieszGaussianWeight s α) * V α x y :=
        mul_le_mul_of_nonneg_left (hlower α hα) zero_le

theorem analyticUnitCostInput_of_gaussian_gap_interval {d : ℕ} {s a b k : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b) (hk : 0 < k)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) (r : ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ)
    (hlower : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ α ∈ Icc a b,
      ∀ x y : Ambient d, x ≠ y → dist x y < r * (1 - t) →
        ENNReal.ofReal (k * t ^ 2) ≤ V α x y) :
    AnalyticUnitCostInput Λ s r (rieszIntervalGapCoefficient s a b k)⁻¹ (1 / 8) := by
  apply analyticUnitCostInput_of_quadratic_slack Λ s r _
    (rieszIntervalGapCoefficient_pos hs ha hab hk) _
    (stationarySlackGapInput_of_unweighted_gaussian_gap hs V hV Λ hΛ hgap)
  intro t ht hhalf x y hne hclose
  exact riesz_weighted_slack_interval_lower hs ha hab hk V t x y
    (fun α hα => hlower t ht hhalf α hα x y hne hclose)

end E8Leech
