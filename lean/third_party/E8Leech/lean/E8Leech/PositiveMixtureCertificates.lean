import E8Leech.SecondMomentSchwartzLP
import E8Leech.GaussianSchwartzCertificates

/-!
# Positive Gaussian mixture gaps without a process Riesz-energy hypothesis

Finite mixture energy supplies the local second moment. Finite lattice mixture
energy supplies sigma-finiteness on positive parameters. Actual function-level
Gaussian certificates then yield the full baseline, while only a chosen compact
parameter block of slack is retained. Actual CKMRV certificates and their uniform
quadratic lower bounds still have to be constructed.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap FourierTransform

theorem GaussianSchwartzCertificate.expected_gap_of_second_moment {d : ℕ} {α : ℝ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞)
    {Λ : Set (Ambient d)}
    (hfinite : latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    {f : 𝓢(Ambient d, ℂ)} (hcert : GaussianSchwartzCertificate Λ α f) :
    latticePotentialEnergy Λ (gaussianPotential α) +
      (∫⁻ c, orderedWindowEnergy (gaussianSchwartzSlackPotential α f) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ :=
  expected_potential_gap_of_schwartzMap_minorant_of_second_moment μ hμ hρ hsecond
    (gaussianPotential α) (gaussianSchwartzSlackPotential α f)
    ((measurable_gaussianPotential_joint d).comp (measurable_const.prodMk measurable_id))
    (measurable_gaussianSchwartzSlackPotential α f) _ hfinite f
    hcert.fourierReal hcert.fourierNonneg
    (gaussian_schwartz_slack_minorant_balance α f hcert.minorant) hcert.calibration

theorem expected_positiveGaussianMixture_gap_of_schwartz_family {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c
      (unitWindow d) ∂μ) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α)) :
    latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (ν.restrict (Ioi 0))
        (fun α => gaussianSchwartzSlackPotential α (f α))) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow d) ∂μ := by
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hbase
  have hsecond := expected_unit_count_sq_ne_top_of_positiveGaussianMixture ν hν hz hne hbase
    μ 1 hρ (by simp) henergy
  apply expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential
    (fun α => gaussianSchwartzSlackPotential α (f α)) (measurable_gaussianPotential_joint d)
    (measurable_gaussianSchwartzSlackPotential_family f hf) Λ hΛ
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  exact (hcert α hα).expected_gap_of_second_moment μ hμ hρ hsecond (hgaussian α hα)

theorem positive_cutoff_mixture_eq_interval {d : ℕ} (ν : Measure ℝ)
    {a b : ℝ} (ha : 0 < a) (V : ℝ → Ambient d → Ambient d → ℝ≥0∞) :
    potentialMixture (ν.restrict (Ioi 0)) (cutoffGaussianSlack (Icc a b) V) =
      potentialMixture (ν.restrict (Icc a b)) V := by
  funext x y
  unfold potentialMixture
  have heq : (fun α => cutoffGaussianSlack (Icc a b) V α x y) =
      (Icc a b).indicator (fun α => V α x y) := by
    funext α
    by_cases hα : α ∈ Icc a b <;> simp [cutoffGaussianSlack, hα]
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun _ h => ha.trans_le h.1
  rw [heq, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict_of_subset hsub]

theorem expected_compact_positiveGaussianMixture_gap_of_schwartz_family {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c
      (unitWindow d) ∂μ) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    {a b : ℝ} (ha : 0 < a) :
    latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (ν.restrict (Icc a b))
        (fun α => gaussianSchwartzSlackPotential α (f α))) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow d) ∂μ := by
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hbase
  have hsecond := expected_unit_count_sq_ne_top_of_positiveGaussianMixture ν hν hz hne hbase
    μ 1 hρ (by simp) henergy
  rw [← positive_cutoff_mixture_eq_interval ν ha]
  apply expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential
    (cutoffGaussianSlack (Icc a b) (fun α => gaussianSchwartzSlackPotential α (f α)))
    (measurable_gaussianPotential_joint d)
    (measurable_cutoffGaussianSlack measurableSet_Icc _
      (measurable_gaussianSchwartzSlackPotential_family f hf)) Λ hΛ
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  have hgap := (hcert α hα).expected_gap_of_second_moment μ hμ hρ hsecond (hgaussian α hα)
  by_cases hin : α ∈ Icc a b
  · simpa only [orderedWindowEnergy_cutoffGaussianSlack, if_pos hin] using hgap
  · simp only [orderedWindowEnergy_cutoffGaussianSlack, if_neg hin, lintegral_zero, add_zero]
    exact (le_add_right le_rfl).trans hgap

theorem compact_positiveGaussianMixture_slack_quadratic_lower {d : ℕ}
    (ν : Measure ℝ) (a b k r : ℝ) (hk : 0 ≤ k)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hquad : ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
      k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re)
    (x y : Ambient d) (hxy : dist x y ≤ r) :
    (ENNReal.ofReal k * ν (Icc a b)) * ENNReal.ofReal ((r - dist x y) ^ 2) ≤
      potentialMixture (ν.restrict (Icc a b))
        (fun α => gaussianSchwartzSlackPotential α (f α)) x y := by
  have h := potentialMixture_lower_on_parameter_set (ν.restrict (Icc a b))
    (fun α => gaussianSchwartzSlackPotential α (f α)) (A := Icc a b) measurableSet_Icc
    (ENNReal.ofReal (k * (r - dist x y) ^ 2)) x y (fun α hα => by
      apply ENNReal.ofReal_le_ofReal
      simpa only [gaussianSchwartzSlackPotential, dist_eq_norm] using
        hquad α hα (x - y) (by simpa only [dist_eq_norm] using hxy))
  rw [Measure.restrict_apply measurableSet_Icc, inter_self, ENNReal.ofReal_mul hk] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h


theorem countable_e8Set : e8Set.Countable :=
  Set.Countable.image (Set.to_countable e8Numerators) halfCoordinates

theorem countable_leechSet : leechSet.Countable :=
  Set.Countable.image (Set.to_countable leechNumerators) leechCoordinates

theorem e8_expected_compact_positiveGaussianMixture_gap
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c
      (unitWindow 8) ∂μ) ≠ ∞)
    (f : ℝ → 𝓢(Ambient 8, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient 8 => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate e8Set α (f α))
    {a b : ℝ} (ha : 0 < a) :
    latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (ν.restrict (Icc a b))
        (fun α => gaussianSchwartzSlackPotential α (f α))) c (unitWindow 8) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow 8) ∂μ := by
  obtain ⟨z, hz, hne, _⟩ := e8Set_minimum_attained
  exact expected_compact_positiveGaussianMixture_gap_of_schwartz_family ν hν μ hμ hρ
    e8Set countable_e8Set hz hne hbase henergy
    (fun _ hα => e8_gaussian_lattice_energy_ne_top hα) f hf hcert ha

theorem leech_expected_compact_positiveGaussianMixture_gap
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c
      (unitWindow 24) ∂μ) ≠ ∞)
    (f : ℝ → 𝓢(Ambient 24, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient 24 => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate leechSet α (f α))
    {a b : ℝ} (ha : 0 < a) :
    latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (ν.restrict (Icc a b))
        (fun α => gaussianSchwartzSlackPotential α (f α))) c (unitWindow 24) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow 24) ∂μ := by
  obtain ⟨z, hz, hne, _⟩ := leechSet_minimum_attained
  exact expected_compact_positiveGaussianMixture_gap_of_schwartz_family ν hν μ hμ hρ
    leechSet countable_leechSet hz hne hbase henergy
    (fun _ hα => leech_gaussian_lattice_energy_ne_top hα) f hf hcert ha

end E8Leech
