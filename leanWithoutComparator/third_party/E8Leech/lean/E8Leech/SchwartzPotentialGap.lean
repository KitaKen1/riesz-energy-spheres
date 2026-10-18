import E8Leech.SchwartzFourierLP
import E8Leech.GaussianPotentialMixtures

/-!
# Actual Schwartz minorants for an arbitrary nonnegative target potential

Finite original Riesz energy supplies the signed auxiliary-function moments.
The target potential can be Gaussian or any other measurable nonnegative
potential; its calibrated baseline is kept separate from the Riesz baseline.
An infinite target expectation is handled before any real-value conversion.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap FourierTransform

theorem signed_minorant_ofReal_balance {p h : ℝ} (hp : 0 ≤ p) (hm : h ≤ p) :
    ENNReal.ofReal p + ENNReal.ofReal (-h) =
      ENNReal.ofReal (p - h) + ENNReal.ofReal h := by
  by_cases hh : 0 ≤ h
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hh), add_zero,
      ← ENNReal.ofReal_add (sub_nonneg.mpr hm) hh]
    congr 1
    ring
  · have hn : h ≤ 0 := (not_le.mp hh).le
    rw [ENNReal.ofReal_of_nonpos hn, add_zero,
      ← ENNReal.ofReal_add hp (neg_nonneg.mpr hn)]
    congr 1

theorem expected_potential_gap_of_schwartzMap_minorant {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (henergy : rieszEnergy s μ ≠ ∞)
    (P V : Ambient d → Ambient d → ℝ≥0∞)
    (hP : Measurable (Function.uncurry P)) (hV : Measurable (Function.uncurry V))
    (L : ℝ≥0∞) (hL : L ≠ ∞) (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re)
    (hminor : ∀ x y, x ≠ y → P x y + ENNReal.ofReal (-(f (x - y)).re) =
      V x y + ENNReal.ofReal (f (x - y)).re)
    (hcalib : L.toReal = (𝓕 f (0 : Ambient d)).re - (f 0).re) :
    L + (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy P c (unitWindow d) ∂μ := by
  let E := ∫⁻ c, orderedWindowEnergy P c (unitWindow d) ∂μ
  by_cases hE : E = ∞
  · change L + _ ≤ E
    rw [hE]
    exact le_top
  let H : Ambient d → Ambient d → ℝ := fun x y => if y = x then 0 else (f (x - y)).re
  have hH : Measurable (Function.uncurry H) := by
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst) measurable_const
      ((Complex.continuous_re.comp f.continuous).measurable.comp
        (measurable_fst.sub measurable_snd))
  have hunit := expected_abs_schwartzMap_re_pair_unit_ne_top hs μ hμ 1 hρ
    (by simp) henergy f
  have hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c
      (unitWindow d) univ ∂μ) ≠ ∞ := by
    simpa only [differenceOffDiagonal_sub] using
      expected_abs_differenceOffDiagonal_unit_ne_top μ (fun v => (f v).re) hunit
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ H (unitWindow d) univ hfinite
  let A := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c
    (unitWindow d) univ ∂μ
  let B := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c
    (unitWindow d) univ ∂μ
  let S := ∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ
  have hbal : E + B = S + A := expected_signed_minorant_balance μ P V hP hV
    (fun v => (f v).re) hminor (measurable_unitWindow d)
  have hS : S ≠ ∞ :=
    (ENNReal.add_ne_top.mp (hbal ▸ (ENNReal.add_ne_top.mpr ⟨hE, hn⟩))).1
  have hreal := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add hE hn, ENNReal.toReal_add hS hp] at hreal
  have hlower := stationary_schwartzMap_offDiagonal_lower hs μ hμ 1 hρ
    (by simp) henergy f him hnonneg
  simp only [ENNReal.toReal_one, one_pow, one_mul, mul_one] at hlower
  rw [← hcalib, integral_real_pair_eq_pos_sub_neg_of_expected_abs μ H hH
    (measurable_unitWindow d) (isBounded_unitWindow d) MeasurableSet.univ hfinite] at hlower
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hL, hS⟩) hE).mp
  rw [ENNReal.toReal_add hL hS]
  change L.toReal ≤ A.toReal - B.toReal at hlower
  linarith

theorem expected_potential_gap_of_real_even_schwartzMap_minorant {d : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (henergy : rieszEnergy s μ ≠ ∞)
    (P V : Ambient d → Ambient d → ℝ≥0∞)
    (hP : Measurable (Function.uncurry P)) (hV : Measurable (Function.uncurry V))
    (L : ℝ≥0∞) (hL : L ≠ ∞) (f : 𝓢(Ambient d, ℝ)) (heven : ∀ x, f (-x) = f x)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (fun v => (f v : ℂ)) ξ).re)
    (hminor : ∀ x y, x ≠ y → P x y + ENNReal.ofReal (-f (x - y)) =
      V x y + ENNReal.ofReal (f (x - y)))
    (hcalib : L.toReal = (𝓕 (fun v => (f v : ℂ)) (0 : Ambient d)).re - f 0) :
    L + (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy P c (unitWindow d) ∂μ := by
  apply expected_potential_gap_of_schwartzMap_minorant hs μ hμ hρ henergy P V hP hV L hL
    (complexSchwartzMap f) (fourier_complexSchwartzMap_im_zero_of_even f heven) hnonneg
  · simpa only [complexSchwartzMap_apply, Complex.ofReal_re] using hminor
  · simpa only [fourier_complexSchwartzMap_apply, complexSchwartzMap_apply,
      Complex.ofReal_re] using hcalib

def gaussianSchwartzSlackPotential {d : ℕ} (α : ℝ) (f : 𝓢(Ambient d, ℂ))
    (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianKernel α (x - y) - (f (x - y)).re)

theorem measurable_gaussianSchwartzSlackPotential {d : ℕ} (α : ℝ)
    (f : 𝓢(Ambient d, ℂ)) :
    Measurable (Function.uncurry (gaussianSchwartzSlackPotential α f)) := by
  exact (((continuous_gaussianKernel α).sub (Complex.continuous_re.comp f.continuous)).measurable.comp
    (measurable_fst.sub measurable_snd)).ennreal_ofReal

theorem gaussian_schwartz_slack_minorant_balance {d : ℕ} (α : ℝ) (f : 𝓢(Ambient d, ℂ))
    (hminor : ∀ v : Ambient d, v ≠ 0 → (f v).re ≤ gaussianKernel α v)
    (x y : Ambient d) (hne : x ≠ y) :
    gaussianPotential α x y + ENNReal.ofReal (-(f (x - y)).re) =
      gaussianSchwartzSlackPotential α f x y + ENNReal.ofReal (f (x - y)).re :=
  signed_minorant_ofReal_balance (gaussianKernel_pos α (x - y)).le
    (hminor (x - y) (sub_ne_zero.mpr hne))

theorem expected_gaussian_slack_gap_of_schwartzMap {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (henergy : rieszEnergy s μ ≠ ∞)
    (Λ : Set (Ambient d)) (α : ℝ)
    (hL : latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞) (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re)
    (hminor : ∀ v : Ambient d, v ≠ 0 → (f v).re ≤ gaussianKernel α v)
    (hcalib : (latticePotentialEnergy Λ (gaussianPotential α)).toReal =
      (𝓕 f (0 : Ambient d)).re - (f 0).re) :
    latticePotentialEnergy Λ (gaussianPotential α) +
      (∫⁻ c, orderedWindowEnergy (gaussianSchwartzSlackPotential α f) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow d) ∂μ := by
  exact expected_potential_gap_of_schwartzMap_minorant hs μ hμ hρ henergy
    (gaussianPotential α) (gaussianSchwartzSlackPotential α f)
    ((measurable_gaussianPotential_joint d).comp
      (measurable_const.prodMk measurable_id))
    (measurable_gaussianSchwartzSlackPotential α f) _ hL f him hnonneg
    (gaussian_schwartz_slack_minorant_balance α f hminor) hcalib

end E8Leech
