import E8Leech.GaussianSchwartzCertificates

/-!
# Certificates are needed only for almost every Gaussian parameter

The Riesz assembly (`analyticUnitCostInput_of_normalized_gaussian_laplace_kernel`) uses the
Gaussian gap only for almost every `α > 0`, plus the local interval `α ∈ [π/4, π/3]`. So a
certificate family may omit a null set of parameters. In particular `α = π`, i.e. the CKMRV
parameter `τ = i` where the kernel has a double pole, is not needed for the main theorem.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal SchwartzMap

/-- Certificates for every `α > 0` except one value hold almost everywhere on `(0, ∞)`. -/
theorem ae_certificate_of_forall_ne {d : ℕ} {Λ : Set (Ambient d)} {f : ℝ → 𝓢(Ambient d, ℂ)}
    (a : ℝ) (hcert : ∀ α : ℝ, 0 < α → α ≠ a → GaussianSchwartzCertificate Λ α (f α)) :
    ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)), GaussianSchwartzCertificate Λ α (f α) := by
  have hne : ∀ᵐ α ∂(volume : Measure ℝ), α ∉ ({a} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton a)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hne] with α hα hαa
  exact hcert α hα fun h => hαa (mem_singleton_iff.mpr h)

/-- **The almost-everywhere Gaussian gap** (the `hgap` input of the Riesz assembly) from
certificates for almost every parameter and a radial profile `φ` of the slack. -/
theorem gaussian_gap_ae_of_certificates {d : ℕ} {s : ℝ} (hs : 0 ≤ s) {Λ : Set (Ambient d)}
    (n : ℕ) (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) (f : ℝ → 𝓢(Ambient d, ℂ))
    (hcert : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)), GaussianSchwartzCertificate Λ α (f α))
    (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ α : ℝ, ∀ v : Ambient d, φ (α, ‖v‖) = gaussianKernel α v - (f α v).re) :
    ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (fun x y => ENNReal.ofReal (φ (α, dist x y)))
            c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ := by
  intro μ hprob hμ hρ henergy
  filter_upwards [hcert, ae_restrict_mem measurableSet_Ioi] with α hα hpos
  have heq : (fun x y : Ambient d => ENNReal.ofReal (φ (α, dist x y))) =
      gaussianSchwartzSlackPotential α (f α) := by
    funext x y
    simp only [gaussianSchwartzSlackPotential, dist_eq_norm, hφ α]
  rw [heq]
  exact hα.expected_gap hs μ hμ hρ henergy n hfinite hpos

end E8Leech
