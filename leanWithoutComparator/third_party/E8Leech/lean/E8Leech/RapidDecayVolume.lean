import E8Leech.DeterministicWindowLimits
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Rapid value decay supplies volume L1 for the deterministic LP limit

The previously certified value profile is enough: only its orders zero and d+1
are used. Mathlib's integrable nonsingular polynomial weight avoids a fresh
shell decomposition or a smooth-Schwartz assumption. No new law moment is added.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

theorem integrable_of_hasRapidDecay {d : ℕ}
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) :
    Integrable h volume := by
  obtain ⟨C, hC, hb⟩ := exists_polynomial_decay_of_rapidDecay h hdecay
  have hi : Integrable (fun x : Ambient d => (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) volume := by
    apply integrable_one_add_norm
    simp
  apply (hi.const_mul C).mono' hh.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hb x

theorem tendsto_normalized_box_pair_of_rapidDecay {d : ℕ}
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) :
    Tendsto (fun n : ℕ => (∫ x in periodCell d ((n : ℝ) + 1),
      ∫ y in periodCell d ((n : ℝ) + 1), h (x - y)) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal) atTop (𝓝 (∫ v, h v)) :=
  tendsto_normalized_box_pair_integral h (integrable_of_hasRapidDecay h hh hdecay)

theorem tendsto_normalized_spectral_window_square_of_rapidDecay {d : ℕ}
    (ν : Measure (Ambient d)) [SFinite ν] (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hdecay : HasRapidDecay (realSpectralKernel ν g)) :
    Tendsto (fun n : ℕ => (∫ ξ, g ξ * Complex.normSq
      (∫ x, (periodCell d ((n : ℝ) + 1)).indicator (spectralPhase ξ) x) ∂ν) /
      (volume (periodCell d ((n : ℝ) + 1))).toReal)
      atTop (𝓝 (∫ v, realSpectralKernel ν g v)) :=
  tendsto_normalized_spectral_window_square ν g hg
    (integrable_of_hasRapidDecay _ (continuous_realSpectralKernel ν g hg).measurable hdecay)

end E8Leech
