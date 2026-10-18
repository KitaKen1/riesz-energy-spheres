import E8Leech.StationaryRealBoxLimits
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Actual SchwartzMap values discharge the local rapid-decay interface

Use derivative order zero in the existing Mathlib Schwartz definition. No
new differentiability or decay premise is imposed on the process law.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology SchwartzMap

def complexSchwartzMap {d : ℕ} (f : 𝓢(Ambient d, ℝ)) : 𝓢(Ambient d, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM f

@[simp] theorem complexSchwartzMap_apply {d : ℕ} (f : 𝓢(Ambient d, ℝ)) (x : Ambient d) :
    complexSchwartzMap f x = (f x : ℂ) := rfl

theorem hasRapidDecay_schwartzMap {d : ℕ} (f : 𝓢(Ambient d, ℝ)) :
    HasRapidDecay (f : Ambient d → ℝ) := by
  intro n
  obtain ⟨C, hC, hb⟩ := f.decay n 0
  refine ⟨C, hC.le, ?_⟩
  intro x
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb x

theorem hasRapidDecay_schwartzMap_re {d : ℕ} (f : 𝓢(Ambient d, ℂ)) :
    HasRapidDecay (fun x => (f x).re) :=
  hasRapidDecay_schwartzMap (SchwartzMap.postcompCLM Complex.reCLM f)

theorem integrable_schwartzMap_re {d : ℕ} (f : 𝓢(Ambient d, ℂ)) :
    Integrable (fun x => (f x).re) volume :=
  f.integrable.re

theorem expected_abs_schwartzMap_re_pair_unit_ne_top
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (f : 𝓢(Ambient d, ℂ)) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |(f (x - y)).re|) c
      (unitWindow d) univ ∂μ) ≠ ∞ :=
  expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (fun x => (f x).re) (Complex.continuous_re.comp f.continuous).measurable
    (hasRapidDecay_schwartzMap_re f)

theorem tendsto_normalized_expected_schwartzMap_re_pair_box
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (f : 𝓢(Ambient d, ℂ)) :
    Tendsto (fun n : ℕ => (∫ c, realLocalizedPairIntegral
      (fun x y => (f (x - y)).re) c
      (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop
      (𝓝 (∫ c, realLocalizedPairIntegral (fun x y => (f (x - y)).re) c
        (unitWindow d) univ ∂μ)) :=
  tendsto_normalized_expected_real_difference_pair_box_of_rapidDecay hs μ hμ ρ hρ hρtop
    henergy (fun x => (f x).re) (Complex.continuous_re.comp f.continuous).measurable
    (hasRapidDecay_schwartzMap_re f)

end E8Leech
