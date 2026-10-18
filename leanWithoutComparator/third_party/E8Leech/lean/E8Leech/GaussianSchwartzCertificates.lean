import E8Leech.SchwartzPotentialGap
import E8Leech.GaussianLatticeFiniteness
import E8Leech.CompactGaussianSlack

/-!
# Function-level Gaussian certificates discharge the law-level gap interface

All certificate fields concern an actual Schwartz function, its actual Fourier
transform and actual Gaussian lattice energy. No extra process-law premise is
introduced. Certificates for actual CKMRV families remain to be constructed.
Parameter measurability is needed only for the nonnegative slack mixture; no
uniform Schwartz seminorms or signed auxiliary-family integral are required.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap FourierTransform

structure GaussianSchwartzCertificate {d : ℕ} (Λ : Set (Ambient d)) (α : ℝ)
    (f : 𝓢(Ambient d, ℂ)) : Prop where
  fourierReal : ∀ ξ, (𝓕 f ξ).im = 0
  fourierNonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re
  minorant : ∀ v : Ambient d, v ≠ 0 → (f v).re ≤ gaussianKernel α v
  calibration : (latticePotentialEnergy Λ (gaussianPotential α)).toReal =
    (𝓕 f (0 : Ambient d)).re - (f 0).re

theorem GaussianSchwartzCertificate.expected_gap {d : ℕ} {s α : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (henergy : rieszEnergy s μ ≠ ∞)
    {Λ : Set (Ambient d)} (n : ℕ) (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞)
    (hα : 0 < α) {f : 𝓢(Ambient d, ℂ)} (hcert : GaussianSchwartzCertificate Λ α f) :
    latticePotentialEnergy Λ (gaussianPotential α) +
      (∫⁻ c, orderedWindowEnergy (gaussianSchwartzSlackPotential α f) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ :=
  expected_gaussian_slack_gap_of_schwartzMap hs μ hμ hρ henergy Λ α
    (gaussian_lattice_energy_ne_top_of_riesz hα Λ n hfinite) f
    hcert.fourierReal hcert.fourierNonneg hcert.minorant hcert.calibration

theorem GaussianSchwartzCertificate.expected_baseline {d : ℕ} {s α : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (henergy : rieszEnergy s μ ≠ ∞)
    {Λ : Set (Ambient d)} (n : ℕ) (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞)
    (hα : 0 < α) {f : 𝓢(Ambient d, ℂ)} (hcert : GaussianSchwartzCertificate Λ α f) :
    latticePotentialEnergy Λ (gaussianPotential α) ≤
      ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ :=
  (le_add_right le_rfl).trans (hcert.expected_gap hs μ hμ hρ henergy n hfinite hα)

theorem measurable_gaussianSchwartzSlackPotential_family {d : ℕ}
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re)) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      gaussianSchwartzSlackPotential p.1 (f p.1) p.2.1 p.2.2) := by
  have hK : Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      gaussianKernel p.1 (p.2.1 - p.2.2)) := by
    unfold gaussianKernel
    fun_prop
  have haux : Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      (f p.1 (p.2.1 - p.2.2)).re) :=
    hf.comp (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))
  exact (hK.sub haux).ennreal_ofReal

theorem compactGaussianGapInput_of_schwartz_family {d : ℕ} {s a b : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (Λ : Set (Ambient d)) (n : ℕ)
    (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) (f : ℝ → 𝓢(Ambient d, ℂ))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α)) :
    CompactGaussianGapInput Λ s a b (fun α => gaussianSchwartzSlackPotential α (f α)) := by
  constructor
  · intro μ hprob hμ hρ henergy
    let := hprob
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact (hcert α hα).expected_baseline hs μ hμ hρ henergy n hfinite hα
  · intro μ hprob hμ hρ henergy α hα
    let := hprob
    have hpos := ha.trans_le hα.1
    exact (hcert α hpos).expected_gap hs μ hμ hρ henergy n hfinite hpos

theorem compactGaussianGapInput_of_schwartz_family_radial {d : ℕ} {s a b : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (Λ : Set (Ambient d)) (n : ℕ)
    (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) (f : ℝ → 𝓢(Ambient d, ℂ))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ v : Ambient d,
      φ (α, ‖v‖) = gaussianKernel α v - (f α v).re) :
    CompactGaussianGapInput Λ s a b (fun α x y => ENNReal.ofReal (φ (α, dist x y))) := by
  have hgap := compactGaussianGapInput_of_schwartz_family (b := b) hs ha Λ n hfinite f hcert
  refine ⟨hgap.baseline, ?_⟩
  intro μ hprob hμ hρ henergy α hα
  have heq : (fun x y : Ambient d => ENNReal.ofReal (φ (α, dist x y))) =
      gaussianSchwartzSlackPotential α (f α) := by
    funext x y
    simp only [gaussianSchwartzSlackPotential, dist_eq_norm, hφ α hα]
  rw [heq]
  exact hgap.localGap μ hprob hμ hρ henergy α hα

theorem gaussianSchwartzCertificate_of_real_even_auxiliary {d : ℕ}
    (Λ : Set (Ambient d)) (α : ℝ) (f : 𝓢(Ambient d, ℝ))
    (heven : ∀ v, f (-v) = f v)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (fun v => (f v : ℂ)) ξ).re)
    (hminor : ∀ v : Ambient d, v ≠ 0 → f v ≤ gaussianKernel α v)
    (hcalib : (latticePotentialEnergy Λ (gaussianPotential α)).toReal =
      (𝓕 (fun v => (f v : ℂ)) (0 : Ambient d)).re - f 0) :
    GaussianSchwartzCertificate Λ α (complexSchwartzMap f) := by
  refine ⟨fourier_complexSchwartzMap_im_zero_of_even f heven, ?_, ?_, ?_⟩
  · simpa only [fourier_complexSchwartzMap_apply] using hnonneg
  · simpa only [complexSchwartzMap_apply, Complex.ofReal_re] using hminor
  · simpa only [fourier_complexSchwartzMap_apply, complexSchwartzMap_apply,
      Complex.ofReal_re] using hcalib

theorem analyticUnitCostInput_of_schwartz_gaussian_family {d : ℕ} {s a b k r : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b) (hk : 0 < k) (hr : 0 < r)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) (n : ℕ)
    (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    (hquad : ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
      k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re) :
    AnalyticUnitCostInput Λ s r (rieszIntervalGapCoefficient s a b k * r ^ 2)⁻¹
      (1 / 8) := by
  apply analyticUnitCostInput_of_compact_gaussian_slack hs ha hab hk hr Λ hΛ
    (fun α => gaussianSchwartzSlackPotential α (f α))
    (measurable_gaussianSchwartzSlackPotential_family f hf)
    (compactGaussianGapInput_of_schwartz_family hs.le ha Λ n hfinite f hcert)
  intro α hα x y hur
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [dist_eq_norm] using hquad α hα (x - y) (by simpa only [dist_eq_norm] using hur))

theorem e8_compactGaussianGapInput_of_schwartz_family {s a b : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (f : ℝ → 𝓢(Ambient 8, ℂ))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate e8Set α (f α)) :
    CompactGaussianGapInput e8Set s a b (fun α => gaussianSchwartzSlackPotential α (f α)) :=
  compactGaussianGapInput_of_schwartz_family hs ha e8Set 9
    (e8_latticeRieszEnergy_ne_top (by norm_num)) f hcert

theorem leech_compactGaussianGapInput_of_schwartz_family {s a b : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (f : ℝ → 𝓢(Ambient 24, ℂ))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate leechSet α (f α)) :
    CompactGaussianGapInput leechSet s a b (fun α => gaussianSchwartzSlackPotential α (f α)) :=
  compactGaussianGapInput_of_schwartz_family hs ha leechSet 25
    (leech_latticeRieszEnergy_ne_top (by norm_num)) f hcert

end E8Leech
