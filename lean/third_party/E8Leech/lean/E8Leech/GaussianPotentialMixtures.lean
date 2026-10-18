import E8Leech.PotentialMixtures

/-!
# Concrete positive Gaussian potential mixtures

The mixing measure is restricted to positive parameters. Tonelli identifies
both the process and lattice energies with the Gaussian energy mixtures.
This is the checked closure step, not the missing CKMRV Gaussian gap family.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def gaussianPotential {d : ℕ} (α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianKernel α (x - y))

def positiveGaussianMixturePotential {d : ℕ} (ν : Measure ℝ)
    (x y : Ambient d) : ℝ≥0∞ :=
  potentialMixture (ν.restrict (Ioi 0)) (gaussianPotential (d := d)) x y

theorem measurable_gaussianPotential_joint (d : ℕ) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) => gaussianPotential p.1 p.2.1 p.2.2) := by
  unfold gaussianPotential gaussianKernel
  fun_prop

theorem positiveGaussianMixturePotential_eq_integral {d : ℕ}
    (ν : Measure ℝ) (x y : Ambient d) :
    positiveGaussianMixturePotential ν x y =
      ∫⁻ α in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-α * dist x y ^ 2)) ∂ν := by
  simp only [positiveGaussianMixturePotential, potentialMixture, gaussianPotential,
    gaussianKernel, dist_eq_norm]

theorem measurable_positiveGaussianMixturePotential {d : ℕ}
    (ν : Measure ℝ) [SFinite ν] :
    Measurable (Function.uncurry (positiveGaussianMixturePotential (d := d) ν)) :=
  measurable_potentialMixture (ν.restrict (Ioi 0)) gaussianPotential
    (measurable_gaussianPotential_joint d)

theorem expected_positiveGaussianMixture_energy
    {d : ℕ} (ν : Measure ℝ) [SFinite ν]
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] :
    (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow d) ∂μ) =
      ∫⁻ α in Ioi (0 : ℝ), ∫⁻ c,
        orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ ∂ν :=
  expected_orderedWindowEnergy_potentialMixture (ν.restrict (Ioi 0)) μ gaussianPotential
    (measurable_gaussianPotential_joint d) (measurable_unitWindow d)

theorem lattice_positiveGaussianMixture_energy
    {d : ℕ} (ν : Measure ℝ) (Λ : Set (Ambient d)) (hΛ : Λ.Countable) :
    latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) =
      ∫⁻ α in Ioi (0 : ℝ), latticePotentialEnergy Λ (gaussianPotential α) ∂ν := by
  apply latticePotentialEnergy_potentialMixture (ν.restrict (Ioi 0)) gaussianPotential _ Λ hΛ
  intro x y
  exact (measurable_gaussianPotential_joint d).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

theorem expected_positiveGaussianMixture_gap
    {d : ℕ} (ν : Measure ℝ) [SFinite ν]
    (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hgap : ∀ᵐ α ∂ν.restrict (Ioi 0), latticePotentialEnergy Λ (gaussianPotential α) +
      (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (ν.restrict (Ioi 0)) V) c
        (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow d) ∂μ :=
  expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential V
    (measurable_gaussianPotential_joint d) hV Λ hΛ hgap

end E8Leech
