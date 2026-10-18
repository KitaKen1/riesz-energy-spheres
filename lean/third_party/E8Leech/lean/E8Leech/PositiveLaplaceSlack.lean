import E8Leech.SineSquaredSlack
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A finite positive kernel block gives uniform quadratic slack

For a nonnegative Laplace kernel, keep only the fixed interval [1,2].
If r^2 <= 4, its exponential factor is at least exp(-8*pi) there.
A positive continuous kernel on the parameter rectangle therefore supplies
a common positive lower bound. This avoids differentiating or proving joint
continuity of the entire improper integral.

The actual CKMRV kernel, its sign, integral representation and integrability
are still proof inputs; the lemmas below prove the transfer from those inputs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem laplace_factor_lower_from_unit_block {K : ℝ → ℝ} {B u : ℝ}
    (hu : u ^ 2 ≤ 4)
    (hK : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (hblock : ∀ t ∈ Icc (1 : ℝ) 2, B ≤ K t)
    (hint : IntegrableOn (fun t => K t * Real.exp (-Real.pi * u ^ 2 * t))
      (Ioi (0 : ℝ)) volume) :
    B * Real.exp (-8 * Real.pi) ≤
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * u ^ 2 * t) := by
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := by intro t ht; exact lt_of_lt_of_le (by norm_num) ht.1
  have hlow : ∀ t ∈ Icc (1 : ℝ) 2,
      B * Real.exp (-8 * Real.pi) ≤ K t * Real.exp (-Real.pi * u ^ 2 * t) := by
    intro t ht
    have hproduct : u ^ 2 * t ≤ 8 := by
      calc
        u ^ 2 * t ≤ 4 * t := mul_le_mul_of_nonneg_right hu (by linarith [ht.1])
        _ ≤ 8 := by linarith [ht.2]
    have hexp : Real.exp (-8 * Real.pi) ≤ Real.exp (-Real.pi * u ^ 2 * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hproduct)]
    exact mul_le_mul (hblock t ht) hexp (Real.exp_pos _).le (hK t (hsub ht))
  have hlower := setIntegral_ge_of_const_le_real (μ := volume)
    measurableSet_Icc (by simp : volume (Icc (1 : ℝ) 2) ≠ ∞) hlow (hint.mono_set hsub)
  have hmass : volume.real (Icc (1 : ℝ) 2) = 1 := by
    norm_num [Measure.real, Real.volume_Icc]
  rw [hmass, mul_one] at hlower
  refine hlower.trans (setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (hK t ht) (Real.exp_pos _).le

theorem uniform_laplace_factor_lower {a b : ℝ} (K : ℝ × ℝ → ℝ)
    (hK : ContinuousOn K (Icc a b ×ˢ Icc (1 : ℝ) 2))
    (hpos : ∀ p ∈ Icc a b ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hnonneg : ∀ α ∈ Icc a b, ∀ t : ℝ, 0 < t → 0 ≤ K (α, t)) :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Icc a b, ∀ u : ℝ, u ^ 2 ≤ 4 →
      IntegrableOn (fun t => K (α, t) * Real.exp (-Real.pi * u ^ 2 * t))
        (Ioi (0 : ℝ)) volume →
      B ≤ ∫ t in Ioi (0 : ℝ), K (α, t) * Real.exp (-Real.pi * u ^ 2 * t) := by
  obtain ⟨C, hC, hlower⟩ := compact_rectangle_positive_lower hK hpos
  refine ⟨C * Real.exp (-8 * Real.pi), mul_pos hC (Real.exp_pos _), ?_⟩
  intro α hα u hu hint
  exact laplace_factor_lower_from_unit_block hu (hnonneg α hα) (hlower α hα) hint

theorem uniform_quadratic_slack_of_positive_laplace_kernel {a b r : ℝ}
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (φ K : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc a b ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hK : ContinuousOn K (Icc a b ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc a b ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ α ∈ Icc a b, ∀ t : ℝ, 0 < t → 0 ≤ K (α, t))
    (hint : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun t => K (α, t) * Real.exp (-Real.pi * u ^ 2 * t))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), K (α, t) * Real.exp (-Real.pi * u ^ 2 * t)) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ α ∈ Icc a b, ∀ u : ℝ, 0 ≤ u → u < r * (1 - t) →
        k * t ^ 2 ≤ φ (α, u) := by
  obtain ⟨A, hA, hAlower⟩ := compact_rectangle_positive_lower hφ hφpos
  obtain ⟨B, hB, hBlower⟩ := uniform_laplace_factor_lower K hK hKpos hKnonneg
  refine ⟨min (4 * A) (4 * B * r ^ 4), lt_min (by positivity) (by positivity), ?_⟩
  intro t ht hhalf α hα u hu hclose
  apply quadratic_slack_of_sine_factor_bounds hA hB hr hroot
    (fun u => φ (α, u))
    (fun u => ∫ v in Ioi (0 : ℝ), K (α, v) * Real.exp (-Real.pi * u ^ 2 * v))
    (hAlower α hα) ?_ (hfactor α hα) ht hhalf hu hclose
  intro v hv
  apply hBlower α hα v ?_ (hint α hα v hv)
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hvsq : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv0 hv.2 2
  rcases hroot with h | h <;> nlinarith

theorem analyticUnitCostInput_of_gaussian_laplace_kernel {d : ℕ} {s a b r : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (φ K : ℝ × ℝ → ℝ) (hm : Measurable φ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc a b ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hK : ContinuousOn K (Icc a b ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc a b ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ α ∈ Icc a b, ∀ t : ℝ, 0 < t → 0 ≤ K (α, t))
    (hint : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun t => K (α, t) * Real.exp (-Real.pi * u ^ 2 * t))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), K (α, t) * Real.exp (-Real.pi * u ^ 2 * t))
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (fun x y => ENNReal.ofReal (φ (α, dist x y)))
            c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput Λ s r C⁻¹ (1 / 8) := by
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_positive_laplace_kernel
    hr hroot φ K hφ hφpos hK hKpos hKnonneg hint hfactor
  refine ⟨rieszIntervalGapCoefficient s a b k,
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
