import E8Leech.GuardedPeriodization
import E8Leech.JointTranslation

/-!
# A uniform observation centre in a finite period cell

Normalize the Lebesgue measure of the half-open cell. The bad-centre probability
is an explicit boundary-volume ratio. An independent centre translation preserves
every Borel event of the original stationary configuration law.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

def uniformPeriodCell (d : ℕ) (L : ℝ) : Measure (Ambient d) :=
  (volume (periodCell d L))⁻¹ • volume.restrict (periodCell d L)

theorem uniformPeriodCell_apply (d : ℕ) (L : ℝ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    uniformPeriodCell d L W = volume (W ∩ periodCell d L) / volume (periodCell d L) := by
  rw [uniformPeriodCell, Measure.smul_apply, Measure.restrict_apply hW]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem uniformPeriodCell_probability (d : ℕ) (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (uniformPeriodCell d L) := by
  constructor
  rw [uniformPeriodCell_apply d L MeasurableSet.univ, Set.univ_inter, volume_periodCell]
  exact ENNReal.div_self
    (ENNReal.pow_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hL)) _)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem uniformPeriodCell_boundary_probability_le {d : ℕ} (L r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hL : 0 < L) (hw : r + 2 * R ≤ L) :
    uniformPeriodCell d L (guardObservationCenters d L r R)ᶜ ≤
      ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L) := by
  rw [uniformPeriodCell_apply d L (measurable_guardObservationCenters d L r R).compl]
  have he : (guardObservationCenters d L r R)ᶜ ∩ periodCell d L =
      periodCell d L \ guardObservationCenters d L r R := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    exact and_comm
  rw [he]
  exact guard_boundary_fraction_le L r R hr hR hL hw

theorem stationary_uniform_center_event {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) [SFinite μ]
    (L : ℝ) (hL : 0 < L)
    {G : Set (Configuration (Ambient d))} (hG : MeasurableSet G) :
    (μ.prod (uniformPeriodCell d L)) {p | translate (-p.2) p.1 ∈ G} = μ G := by
  let _ := uniformPeriodCell_probability d L hL
  rw [stationary_random_center_event μ hμ _ hG, measure_univ, mul_one]

end E8Leech
