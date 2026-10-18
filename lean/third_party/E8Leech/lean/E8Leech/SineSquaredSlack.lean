import E8Leech.GaussianIntervalSlack
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.Compact

/-!
# Quadratic slack from the actual sine-squared factor

CKMRV (6.2) factors the Fourier auxiliary function as a sine squared times
a positive integral. Near the first radius (sqrt 2 or 2), the elementary
sine chord bound supplies a quantitative quadratic lower bound without
computing a second derivative. Compactness makes positive continuous factors
uniform in a Gaussian parameter interval.

The factor identity, continuity and positivity for the actual CKMRV kernels
remain premises. No CKMRV witness or existence axiom is introduced here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem sine_squared_even_root_lower {r u : ℝ} (hr : 0 < r)
    (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (hu : 7 / 8 * r ≤ u) (hur : u ≤ r) :
    r ^ 2 * (r - u) ^ 2 ≤ Real.sin (Real.pi * u ^ 2 / 2) ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have hdiff0 : 0 ≤ r ^ 2 - u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hur) (add_nonneg hr.le hu0)]
  have hrootle : r ^ 2 ≤ 4 := by rcases hroot with h | h <;> linarith
  have husq : (7 / 8 * r) ^ 2 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by positivity : 0 ≤ u + 7 / 8 * r)]
  have hdiff1 : r ^ 2 - u ^ 2 ≤ 1 := by nlinarith
  have hphase0 : 0 ≤ Real.pi * (r ^ 2 - u ^ 2) / 2 := by positivity
  have hphase1 : Real.pi * (r ^ 2 - u ^ 2) / 2 ≤ Real.pi / 2 := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hdiff1)]
  have hs := Real.mul_le_sin hphase0 hphase1
  have hcancel : 2 / Real.pi * (Real.pi * (r ^ 2 - u ^ 2) / 2) =
      r ^ 2 - u ^ 2 := by field_simp
  rw [hcancel] at hs
  have hlinear : r * (r - u) ≤ r ^ 2 - u ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hur)]
  have hsq : (r * (r - u)) ^ 2 ≤
      Real.sin (Real.pi * (r ^ 2 - u ^ 2) / 2) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) (hlinear.trans hs)
  have hshift : Real.sin (Real.pi * (r ^ 2 - u ^ 2) / 2) ^ 2 =
      Real.sin (Real.pi * u ^ 2 / 2) ^ 2 := by
    rcases hroot with h | h
    · rw [h, show Real.pi * (2 - u ^ 2) / 2 =
        Real.pi - Real.pi * u ^ 2 / 2 by ring, Real.sin_pi_sub]
    · rw [h, show Real.pi * (4 - u ^ 2) / 2 =
        2 * Real.pi - Real.pi * u ^ 2 / 2 by ring]
      simp [Real.sin_sub]
  rw [hshift] at hsq
  nlinarith [hsq]

theorem sine_squared_sqrtTwo_lower {u : ℝ}
    (hu : 7 / 8 * Real.sqrt 2 ≤ u) (hur : u ≤ Real.sqrt 2) :
    2 * (Real.sqrt 2 - u) ^ 2 ≤ Real.sin (Real.pi * u ^ 2 / 2) ^ 2 := by
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs := sine_squared_even_root_lower hr
    (Or.inl (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))) hu hur
  simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hs

theorem sine_squared_two_lower {u : ℝ} (hu : 7 / 4 ≤ u) (hur : u ≤ 2) :
    4 * (2 - u) ^ 2 ≤ Real.sin (Real.pi * u ^ 2 / 2) ^ 2 := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
    sine_squared_even_root_lower (r := 2) (by norm_num)
    (Or.inr (by norm_num)) (by linarith) hur

theorem compact_rectangle_positive_lower {a b c e : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc a b ×ˢ Icc c e))
    (hpos : ∀ p ∈ Icc a b ×ˢ Icc c e, 0 < F p) :
    ∃ k : ℝ, 0 < k ∧ ∀ α ∈ Icc a b, ∀ u ∈ Icc c e, k ≤ F (α, u) := by
  obtain ⟨k, hk, hlower⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le' hF hpos
  exact ⟨k, hk, fun α hα u hu => hlower (α, u) ⟨hα, hu⟩⟩

theorem quadratic_slack_of_sine_factor_bounds {A B r t u : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (φ J : ℝ → ℝ)
    (hAlower : ∀ u ∈ Icc 0 (7 / 8 * r), A ≤ φ u)
    (hBlower : ∀ u ∈ Icc (7 / 8 * r) r, B ≤ J u)
    (hfactor : ∀ u ∈ Icc (7 / 8 * r) r,
      φ u = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 * J u)
    (ht : 0 < t) (hhalf : t ≤ 1 / 2) (hu0 : 0 ≤ u) (hclose : u < r * (1 - t)) :
    min (4 * A) (4 * B * r ^ 4) * t ^ 2 ≤ φ u := by
  have hur : u < r := by nlinarith [mul_pos hr ht]
  by_cases hfar : u ≤ 7 / 8 * r
  · have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
    calc
      min (4 * A) (4 * B * r ^ 4) * t ^ 2 ≤ (4 * A) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg t)
      _ ≤ A := by nlinarith [mul_le_mul_of_nonneg_left ht2 hA.le]
      _ ≤ φ u := hAlower u ⟨hu0, hfar⟩
  · have hnear : u ∈ Icc (7 / 8 * r) r := ⟨(not_le.mp hfar).le, hur.le⟩
    have hs := sine_squared_even_root_lower hr hroot hnear.1 hnear.2
    have hdist : r * t ≤ r - u := by nlinarith
    have hsqt : (r * t) ^ 2 ≤ (r - u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdist 2
    rw [hfactor u hnear]
    calc
      min (4 * A) (4 * B * r ^ 4) * t ^ 2 ≤ (4 * B * r ^ 4) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
      _ = 4 * (r ^ 2 * (r * t) ^ 2) * B := by ring
      _ ≤ 4 * (r ^ 2 * (r - u) ^ 2) * B := by gcongr
      _ ≤ 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 * B := by gcongr
      _ ≤ 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 * J u :=
        mul_le_mul_of_nonneg_left (hBlower u hnear) (by positivity)

/-- Construct a common quadratic coefficient from continuous positive far-zone
slack and the positive factor in the near-zone sine-squared identity. -/
theorem uniform_quadratic_slack_of_sine_factor {a b r : ℝ}
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (φ J : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc a b ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hJ : ContinuousOn J (Icc a b ×ˢ Icc (7 / 8 * r) r))
    (hJpos : ∀ p ∈ Icc a b ×ˢ Icc (7 / 8 * r) r, 0 < J p)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 * J (α, u)) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ α ∈ Icc a b, ∀ u : ℝ, 0 ≤ u → u < r * (1 - t) →
        k * t ^ 2 ≤ φ (α, u) := by
  obtain ⟨A, hA, hAlower⟩ := compact_rectangle_positive_lower hφ hφpos
  obtain ⟨B, hB, hBlower⟩ := compact_rectangle_positive_lower hJ hJpos
  refine ⟨min (4 * A) (4 * B * r ^ 4), lt_min (by positivity) (by positivity), ?_⟩
  intro t ht hhalf α hα u hu0 hclose
  exact quadratic_slack_of_sine_factor_bounds hA hB hr hroot
    (fun u => φ (α, u)) (fun u => J (α, u))
    (hAlower α hα) (hBlower α hα) (hfactor α hα) ht hhalf hu0 hclose

theorem analyticUnitCostInput_of_gaussian_sine_factor {d : ℕ} {s a b r : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (φ J : ℝ × ℝ → ℝ)
    (hm : Measurable φ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (hφpos : ∀ p ∈ Icc a b ×ˢ Icc 0 (7 / 8 * r), 0 < φ p)
    (hJ : ContinuousOn J (Icc a b ×ˢ Icc (7 / 8 * r) r))
    (hJpos : ∀ p ∈ Icc a b ×ˢ Icc (7 / 8 * r) r, 0 < J p)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 * J (α, u))
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy Λ (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (fun x y => ENNReal.ofReal (φ (α, dist x y)))
            c (unitWindow d) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ) :
    ∃ K : ℝ, 0 < K ∧ AnalyticUnitCostInput Λ s r K⁻¹ (1 / 8) := by
  obtain ⟨k, hk, hlower⟩ :=
    uniform_quadratic_slack_of_sine_factor hr hroot φ J hφ hφpos hJ hJpos hfactor
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
