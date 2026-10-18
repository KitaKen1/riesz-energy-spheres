import E8Leech.Measurability
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The unit observation window has Euclidean volume one

The coordinate forgetful map from EuclideanSpace to the product space preserves volume.
Thus the half-open coordinate cube really gives energy per unit volume.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem volume_unitWindow (d : ℕ) : volume (unitWindow d) = 1 := by
  let Q : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)
  have hQ : MeasurableSet Q := MeasurableSet.pi (Set.to_countable Set.univ)
    (fun _ _ => measurableSet_Ico)
  have heq : unitWindow d = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' Q := by
    ext x
    simp [unitWindow, Q, Set.mem_pi]
  rw [heq, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hQ.nullMeasurableSet]
  simp [Q, Real.volume_pi_Ico]

theorem expected_count_unitWindow {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) :
    (∫⁻ c, c.count (unitWindow d) ∂μ) = ρ := by
  rw [hρ _ (measurable_unitWindow d), volume_unitWindow, mul_one]

end E8Leech
