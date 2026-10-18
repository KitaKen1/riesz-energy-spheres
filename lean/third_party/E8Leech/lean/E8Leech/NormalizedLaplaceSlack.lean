import E8Leech.GaussianParameterNormalization
import E8Leech.PositiveLaplaceSlack

/-!
# The actual dual Gaussian prefactor in a Laplace slack representation

Normalize a real dual-parameter kernel K(q,v) by q = pi/alpha and q^m,
where m = 4 or 12. The compact dual rectangle is [3,4] x [1,2].
Its positive lower bound transfers to the real Gaussian interval
[pi/4,pi/3], including the exact Fourier prefactor.

The CKMRV kernel formula, signs and representation remain explicit inputs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def gaussianDualLaplaceKernel (m : ℕ) (K : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.pi / p.1) ^ m * K (Real.pi / p.1, p.2)

theorem continuousOn_gaussianDualLaplaceKernel (m : ℕ) (K : ℝ × ℝ → ℝ)
    (hK : ContinuousOn K (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2)) :
    ContinuousOn (gaussianDualLaplaceKernel m K)
      (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc (1 : ℝ) 2) := by
  have hq : ContinuousOn (fun p : ℝ × ℝ => Real.pi / p.1)
      (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc (1 : ℝ) 2) :=
    continuousOn_const.div continuousOn_fst
      (fun p hp => ne_of_gt (gaussian_compact_interval_pos hp.1))
  exact (hq.pow m).mul (hK.comp (hq.prodMk continuousOn_snd)
    (fun p hp => ⟨gaussian_dual_compact_interval hp.1, hp.2⟩))

theorem gaussianDualLaplaceKernel_pos (m : ℕ) (K : ℝ × ℝ → ℝ)
    (hK : ∀ p ∈ Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    {p : ℝ × ℝ} (hp : p ∈ Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc (1 : ℝ) 2) :
    0 < gaussianDualLaplaceKernel m K p := by
  exact mul_pos (pow_pos (div_pos Real.pi_pos (gaussian_compact_interval_pos hp.1)) m)
    (hK _ ⟨gaussian_dual_compact_interval hp.1, hp.2⟩)

theorem gaussianDualLaplaceKernel_nonneg (m : ℕ) (K : ℝ × ℝ → ℝ)
    (hK : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    {α v : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : 0 < v) :
    0 ≤ gaussianDualLaplaceKernel m K (α, v) := by
  exact mul_nonneg (pow_nonneg (div_pos Real.pi_pos (gaussian_compact_interval_pos hα)).le m)
    (hK _ (gaussian_dual_compact_interval hα) v hv)

theorem integrableOn_gaussianDualLaplaceKernel (m : ℕ) (K : ℝ × ℝ → ℝ) (α u : ℝ)
    (hint : IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun v => gaussianDualLaplaceKernel m K (α, v) *
      Real.exp (-Real.pi * u ^ 2 * v)) (Ioi (0 : ℝ)) volume := by
  simpa only [IntegrableOn, gaussianDualLaplaceKernel, mul_assoc] using
    hint.const_mul ((Real.pi / α) ^ m)

theorem integral_gaussianDualLaplaceKernel (m : ℕ) (K : ℝ × ℝ → ℝ) (α u : ℝ) :
    (∫ v in Ioi (0 : ℝ), gaussianDualLaplaceKernel m K (α, v) *
      Real.exp (-Real.pi * u ^ 2 * v)) =
      (Real.pi / α) ^ m *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v) := by
  simp only [gaussianDualLaplaceKernel, mul_assoc, integral_const_mul]

theorem gaussian_normalized_laplace_block_lower (m : ℕ) (K : ℝ × ℝ → ℝ)
    {B α u : ℝ} (hB : 0 ≤ B) (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hu : u ^ 2 ≤ 4)
    (hnonneg : ∀ v : ℝ, 0 < v → 0 ≤ K (Real.pi / α, v))
    (hblock : ∀ v ∈ Icc (1 : ℝ) 2, B ≤ K (Real.pi / α, v))
    (hint : IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
      (Ioi (0 : ℝ)) volume) :
    (3 : ℝ) ^ m * B * Real.exp (-8 * Real.pi) ≤
      (Real.pi / α) ^ m *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v) := by
  have hq := gaussian_dual_compact_interval hα
  have hpow : (3 : ℝ) ^ m ≤ (Real.pi / α) ^ m :=
    pow_le_pow_left₀ (by norm_num) hq.1 m
  rw [← integral_gaussianDualLaplaceKernel]
  apply laplace_factor_lower_from_unit_block hu ?_ ?_
    (integrableOn_gaussianDualLaplaceKernel m K α u hint)
  · intro v hv
    exact mul_nonneg (pow_nonneg (by linarith [hq.1]) m) (hnonneg v hv)
  · intro v hv
    exact mul_le_mul hpow (hblock v hv) hB
      (pow_nonneg (by linarith [hq.1]) m)

theorem uniform_quadratic_slack_of_normalized_laplace_kernel (m : ℕ) {r : ℝ}
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4) (φ K : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hK : ContinuousOn K (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u : ℝ, 0 ≤ u →
        u < r * (1 - t) → k * t ^ 2 ≤ φ (α, u) := by
  apply uniform_quadratic_slack_of_positive_laplace_kernel hr hroot φ
    (gaussianDualLaplaceKernel m K) hφ hφpos
    (continuousOn_gaussianDualLaplaceKernel m K hK)
    (fun p hp => gaussianDualLaplaceKernel_pos m K hKpos hp)
    (fun α hα v hv => gaussianDualLaplaceKernel_nonneg m K hKnonneg hα hv)
    (fun α hα u hu => integrableOn_gaussianDualLaplaceKernel m K α u (hint α hα u hu))
  intro α hα u hu
  rw [hfactor α hα u hu, integral_gaussianDualLaplaceKernel]
  ring

theorem analyticUnitCostInput_of_normalized_gaussian_laplace_kernel
    {d : ℕ} {s r : ℝ} (m : ℕ) (hs : 0 < s)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) (φ K : ℝ × ℝ → ℝ) (hm : Measurable φ)
    (hφ : ContinuousOn φ (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hK : ContinuousOn K (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v)))
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (fun x y => ENNReal.ofReal (φ (α, dist x y)))
            c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput Λ s r C⁻¹ (1 / 8) := by
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_normalized_laplace_kernel
    m hr hroot φ K hφ hφpos hK hKpos hKnonneg hint hfactor
  have ha : 0 < Real.pi / 4 := div_pos Real.pi_pos (by norm_num)
  have hab : Real.pi / 4 < Real.pi / 3 := by linarith [Real.pi_pos]
  refine ⟨rieszIntervalGapCoefficient s (Real.pi / 4) (Real.pi / 3) k,
    rieszIntervalGapCoefficient_pos hs ha hab hk, ?_⟩
  have hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      ENNReal.ofReal (φ (p.1, dist p.2.1 p.2.2))) :=
    (hm.comp (measurable_fst.prodMk
      (measurable_snd.fst.dist measurable_snd.snd))).ennreal_ofReal
  apply analyticUnitCostInput_of_gaussian_gap_interval hs ha hab hk Λ hΛ r
    (fun α x y => ENNReal.ofReal (φ (α, dist x y))) hV hgap
  intro t ht hhalf α hα x y _ hclose
  exact ENNReal.ofReal_le_ofReal (hlower t ht hhalf α hα (dist x y) dist_nonneg hclose)

end E8Leech
