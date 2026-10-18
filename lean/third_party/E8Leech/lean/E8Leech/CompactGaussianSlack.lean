import E8Leech.CompactQuadraticSlack
import E8Leech.GaussianIntervalSlack

/-!
# Retain the full Gaussian baseline and extract slack on one compact interval

No CKMRV slack is needed outside the chosen parameter interval. The ordinary
Gaussian lattice lower bound is still required almost everywhere on all positive
parameters: discarding its complement would lose the actual Riesz baseline.
Every analytic certificate below remains an explicit input to construct.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical

def cutoffGaussianSlack {d : ℕ} (A : Set ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) (α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  if α ∈ A then V α x y else 0

def compactRieszSlackPotential {d : ℕ} (s a b : ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) : Ambient d → Ambient d → ℝ≥0∞ :=
  potentialMixture (volume.restrict (Icc a b))
    (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y)

/-- Full positive-parameter baseline, and the stronger gap only on [a,b]. -/
structure CompactGaussianGapInput {d : ℕ} (Λ : Set (Ambient d)) (s a b : ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) : Prop where
  baseline : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
    IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
    ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      latticePotentialEnergy Λ (gaussianPotential α) ≤
        ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ
  localGap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
    IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ → ∀ α ∈ Icc a b,
      latticePotentialEnergy Λ (gaussianPotential α) +
        (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
        ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ

theorem measurable_cutoffGaussianSlack {d : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2)) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      cutoffGaussianSlack A V p.1 p.2.1 p.2.2) :=
  Measurable.ite (hA.preimage measurable_fst) hV measurable_const

theorem orderedWindowEnergy_cutoffGaussianSlack {d : ℕ} (A : Set ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) (α : ℝ)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy (cutoffGaussianSlack A V α) c W =
      if α ∈ A then orderedWindowEnergy (V α) c W else 0 := by
  by_cases hα : α ∈ A <;> simp [cutoffGaussianSlack, hα, orderedWindowEnergy]

theorem weighted_cutoff_mixture_eq_compact {d : ℕ} (s : ℝ) {a b : ℝ} (ha : 0 < a)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) :
    potentialMixture (volume.restrict (Ioi (0 : ℝ)))
      (fun α x y => ENNReal.ofReal (rieszGaussianWeight s α) *
        cutoffGaussianSlack (Icc a b) V α x y) = compactRieszSlackPotential s a b V := by
  funext x y
  unfold compactRieszSlackPotential potentialMixture
  have heq : (fun α => ENNReal.ofReal (rieszGaussianWeight s α) *
      cutoffGaussianSlack (Icc a b) V α x y) =
      (Icc a b).indicator (fun α => ENNReal.ofReal (rieszGaussianWeight s α) * V α x y) := by
    funext α
    by_cases hα : α ∈ Icc a b <;> simp [cutoffGaussianSlack, hα]
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun α hα => ha.trans_le hα.1
  rw [heq, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict_of_subset hsub]

theorem measurable_compactRieszSlackPotential {d : ℕ} (s a b : ℝ)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2)) :
    Measurable (Function.uncurry (compactRieszSlackPotential s a b V)) :=
  measurable_potentialMixture _ _ (measurable_weighted_riesz_slack s V hV)

theorem expected_riesz_gap_of_compact_gaussian_slack {d : ℕ} {s a b : ℝ}
    (hs : 0 < s) (ha : 0 < a) (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hbase : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      latticePotentialEnergy Λ (gaussianPotential α) ≤
        ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ)
    (hlocal : ∀ α ∈ Icc a b, latticePotentialEnergy Λ (gaussianPotential α) +
      (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
        ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    latticeRieszEnergy Λ s +
      (∫⁻ c, orderedWindowEnergy (compactRieszSlackPotential s a b V) c
        (unitWindow d) ∂μ) ≤ rieszEnergy s μ := by
  have h := expected_riesz_gap_of_unweighted_gaussian_gap hs μ
    (cutoffGaussianSlack (Icc a b) V) (measurable_cutoffGaussianSlack measurableSet_Icc V hV)
    Λ hΛ ?_
  · rwa [weighted_cutoff_mixture_eq_compact s ha V] at h
  · filter_upwards [hbase] with α hb
    simp_rw [orderedWindowEnergy_cutoffGaussianSlack]
    by_cases hα : α ∈ Icc a b
    · simpa only [if_pos hα] using hlocal α hα
    · simpa only [if_neg hα, lintegral_zero, add_zero] using hb

theorem stationarySlackGapInput_of_compact_gaussian_slack {d : ℕ} {s a b : ℝ}
    (hs : 0 < s) (ha : 0 < a) (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (hgap : CompactGaussianGapInput Λ s a b V) :
    StationarySlackGapInput Λ s (compactRieszSlackPotential s a b V) := by
  constructor
  intro μ hprob hμ hρ
  let := hprob
  by_cases henergy : rieszEnergy s μ = ∞
  · rw [henergy]
    exact le_top
  exact expected_riesz_gap_of_compact_gaussian_slack hs ha μ V hV Λ hΛ
    (hgap.baseline μ hprob hμ hρ henergy) (hgap.localGap μ hprob hμ hρ henergy)

theorem compact_riesz_slack_quadratic_lower {d : ℕ} {s a b k r : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b) (hk : 0 < k)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) (x y : Ambient d)
    (hlower : ∀ α ∈ Icc a b, ENNReal.ofReal (k * (r - dist x y) ^ 2) ≤ V α x y) :
    ENNReal.ofReal (rieszIntervalGapCoefficient s a b k * (r - dist x y) ^ 2) ≤
      compactRieszSlackPotential s a b V x y := by
  have h := riesz_weighted_slack_interval_lower hs ha hab hk
    (cutoffGaussianSlack (Icc a b) V) (r - dist x y) x y
    (fun α hα => by simpa [cutoffGaussianSlack, hα] using hlower α hα)
  rwa [weighted_cutoff_mixture_eq_compact s ha V] at h

theorem analyticUnitCostInput_of_compact_gaussian_slack {d : ℕ} {s a b k r : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b) (hk : 0 < k) (hr : 0 < r)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (hgap : CompactGaussianGapInput Λ s a b V)
    (hlower : ∀ α ∈ Icc a b, ∀ x y : Ambient d, dist x y ≤ r →
      ENNReal.ofReal (k * (r - dist x y) ^ 2) ≤ V α x y) :
    AnalyticUnitCostInput Λ s r (rieszIntervalGapCoefficient s a b k * r ^ 2)⁻¹
      (1 / 8) := by
  have hC := rieszIntervalGapCoefficient_pos hs ha hab hk
  apply analyticUnitCostInput_of_quadratic_slack Λ s r _ (mul_pos hC (pow_pos hr 2)) _
    (stationarySlackGapInput_of_compact_gaussian_slack hs ha Λ hΛ V hV hgap)
  intro t ht _hhalf x y _hne hclose
  have hur : dist x y ≤ r := by nlinarith only [hclose, mul_pos hr ht]
  exact (ENNReal.ofReal_le_ofReal
    (full_quadratic_slack_close_pair_cost hr hC.le ht hclose le_rfl)).trans
    (compact_riesz_slack_quadratic_lower hs ha hab hk V x y
      (fun α hα => hlower α hα x y hur))

theorem analyticUnitCostInput_of_origin_inclusive_normalized_kernel {d : ℕ} {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) (m : ℕ) (φ K : ℝ × ℝ → ℝ)
    (hmφ : Measurable φ)
    (hφ : ContinuousOn φ (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r)))
    (horigin : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), 0 < φ (α, 0))
    (hinterior : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u))
    (hK : ContinuousOn K (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v)))
    (hgap : CompactGaussianGapInput Λ s (Real.pi / 4) (Real.pi / 3)
      (fun α x y => ENNReal.ofReal (φ (α, dist x y)))) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput Λ s r C (1 / 8) := by
  obtain ⟨k, hk, hl⟩ := uniform_full_quadratic_slack_of_normalized_laplace_kernel
    m hr hroot φ K hφ horigin hinterior hK hKpos hKnonneg hint hfactor
  have ha : 0 < Real.pi / 4 := by positivity
  have hab : Real.pi / 4 < Real.pi / 3 := by linarith only [Real.pi_pos]
  refine ⟨(rieszIntervalGapCoefficient s (Real.pi / 4) (Real.pi / 3) k * r ^ 2)⁻¹,
    inv_pos.mpr (mul_pos (rieszIntervalGapCoefficient_pos hs ha hab hk) (pow_pos hr 2)), ?_⟩
  have hdist : Measurable (fun p : ℝ × (Ambient d × Ambient d) => dist p.2.1 p.2.2) :=
    measurable_snd.fst.dist measurable_snd.snd
  have hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      ENNReal.ofReal (φ (p.1, dist p.2.1 p.2.2))) :=
    (hmφ.comp (measurable_fst.prodMk hdist)).ennreal_ofReal
  apply analyticUnitCostInput_of_compact_gaussian_slack hs ha hab hk hr Λ hΛ
    (fun α x y => ENNReal.ofReal (φ (α, dist x y))) hV hgap
  intro α hα x y hur
  exact ENNReal.ofReal_le_ofReal (hl α hα (dist x y) ⟨dist_nonneg, hur⟩)

end E8Leech
