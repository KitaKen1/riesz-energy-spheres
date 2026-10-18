import E8Leech.StationaryOffDiagonalLP
import E8Leech.QuadraticSlack

/-!
# A checked spectral minorant certificate supplies the stationary slack gap

The certificate is about a function and its calibrated lattice value, not an
additional assumption on the point-process law. Keep the minorant relation
additive in ENNReal. Only finite expectations are converted to real values;
infinite original energy makes the desired inequality immediate.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem orderedWindowEnergy_add {d : ℕ}
    (V Z : Ambient d → Ambient d → ℝ≥0∞)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy (fun x y => V x y + Z x y) c W =
      orderedWindowEnergy V c W + orderedWindowEnergy Z c W := by
  unfold orderedWindowEnergy
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx]
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) = (x : Ambient d) <;> simp [hy]
  · simp [hx]

theorem orderedWindowEnergy_congr_offDiagonal {d : ℕ}
    (V Z : Ambient d → Ambient d → ℝ≥0∞)
    (h : ∀ x y, x ≠ y → V x y = Z x y)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy V c W = orderedWindowEnergy Z c W := by
  unfold orderedWindowEnergy
  apply tsum_congr
  intro x
  split_ifs
  · apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) = (x : Ambient d)
    · simp [hy]
    · simp only [if_neg hy]
      exact h x y (Ne.symm hy)
  · rfl

theorem orderedWindowEnergy_ofReal_eq_offDiagonal_pair {d : ℕ}
    (h : Ambient d → ℝ) (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy (fun x y => ENNReal.ofReal (h (x - y))) c W =
      localizedPairIntegral (fun x y => ENNReal.ofReal
        (if y = x then 0 else h (x - y))) c W univ := by
  rw [orderedWindowEnergy_eq_kernel]
  simp only [localizedPairIntegral, mem_univ, ite_true]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ W
  · simp only [if_pos hx]
    apply lintegral_congr
    intro y
    split_ifs <;> simp
  · simp [hx]

theorem orderedWindowEnergy_signed_minorant_balance {d : ℕ}
    (P V : Ambient d → Ambient d → ℝ≥0∞) (h : Ambient d → ℝ)
    (hminor : ∀ x y, x ≠ y →
      P x y + ENNReal.ofReal (-h (x - y)) = V x y + ENNReal.ofReal (h (x - y)))
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy P c W +
      localizedPairIntegral (fun x y => ENNReal.ofReal
        (-(if y = x then 0 else h (x - y)))) c W univ =
    orderedWindowEnergy V c W +
      localizedPairIntegral (fun x y => ENNReal.ofReal
        (if y = x then 0 else h (x - y))) c W univ := by
  have he := orderedWindowEnergy_congr_offDiagonal
    (fun x y => P x y + ENNReal.ofReal (-h (x - y)))
    (fun x y => V x y + ENNReal.ofReal (h (x - y))) hminor c W
  rw [orderedWindowEnergy_add, orderedWindowEnergy_add,
    orderedWindowEnergy_ofReal_eq_offDiagonal_pair (fun v => -h v) c W,
    orderedWindowEnergy_ofReal_eq_offDiagonal_pair h c W] at he
  simpa only [neg_ite, neg_zero] using he

theorem expected_signed_minorant_balance {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (P V : Ambient d → Ambient d → ℝ≥0∞)
    (hP : Measurable (Function.uncurry P)) (hV : Measurable (Function.uncurry V))
    (h : Ambient d → ℝ)
    (hminor : ∀ x y, x ≠ y →
      P x y + ENNReal.ofReal (-h (x - y)) = V x y + ENNReal.ofReal (h (x - y)))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, orderedWindowEnergy P c W ∂μ) +
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal
        (-(if y = x then 0 else h (x - y)))) c W univ ∂μ) =
    (∫⁻ c, orderedWindowEnergy V c W ∂μ) +
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal
        (if y = x then 0 else h (x - y))) c W univ ∂μ) := by
  rw [← lintegral_add_left (measurable_orderedWindowEnergy hP hW),
    ← lintegral_add_left (measurable_orderedWindowEnergy hV hW)]
  apply lintegral_congr
  intro c
  exact orderedWindowEnergy_signed_minorant_balance P V h hminor c W

theorem stationarySlackGapInput_of_spectral_minorant {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (Λ : Set (Ambient d)) (hbase : latticeRieszEnergy Λ s ≠ ∞)
    (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g))
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (hminor : ∀ x y, x ≠ y →
      rieszPotential s x y + ENNReal.ofReal (-realSpectralKernel ν g (x - y)) =
        V x y + ENNReal.ofReal (realSpectralKernel ν g (x - y)))
    (hcalib : (latticeRieszEnergy Λ s).toReal =
      (∫ v, realSpectralKernel ν g v) - realSpectralKernel ν g 0) :
    StationarySlackGapInput Λ s V := by
  constructor
  intro μ hprob hμ hρ
  let _ := hprob
  by_cases henergy : rieszEnergy s μ = ∞
  · simp [henergy]
  have hm := (continuous_realSpectralKernel ν g hg).measurable
  let H : Ambient d → Ambient d → ℝ := fun x y =>
    if y = x then 0 else realSpectralKernel ν g (x - y)
  have hH : Measurable (Function.uncurry H) := by
    have ht : Measurable (fun xy : Ambient d × Ambient d =>
        differenceOffDiagonal (realSpectralKernel ν g) (xy.1 - xy.2)) :=
      (measurable_differenceOffDiagonal (realSpectralKernel ν g) hm).comp
        (measurable_fst.sub measurable_snd)
    change Measurable (fun xy : Ambient d × Ambient d =>
      if xy.2 = xy.1 then 0 else realSpectralKernel ν g (xy.1 - xy.2))
    simpa only [differenceOffDiagonal_sub] using ht
  have hunit := expected_abs_difference_pair_unit_ne_top_of_rapidDecay hs μ hμ 1 hρ
    (by simp) henergy (realSpectralKernel ν g) hm hdecay
  have hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c
      (unitWindow d) univ ∂μ) ≠ ∞ := by
    simpa only [differenceOffDiagonal_sub] using
      expected_abs_differenceOffDiagonal_unit_ne_top μ (realSpectralKernel ν g) hunit
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ H (unitWindow d) univ hfinite
  let A := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c
    (unitWindow d) univ ∂μ
  let B := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c
    (unitWindow d) univ ∂μ
  let S := ∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ
  have hbal : rieszEnergy s μ + B = S + A :=
    expected_signed_minorant_balance μ (rieszPotential s) V (measurable_rieszPotential s)
      hV (realSpectralKernel ν g) hminor (measurable_unitWindow d)
  have hS : S ≠ ∞ := by
    exact (ENNReal.add_ne_top.mp (hbal ▸ (ENNReal.add_ne_top.mpr ⟨henergy, hn⟩))).1
  have hreal := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add henergy hn, ENNReal.toReal_add hS hp] at hreal
  have hlower := stationary_spectral_offDiagonal_anchor_lower_of_rapidDecay hs μ hμ 1 hρ
    (by simp) henergy ν g hg hgnonneg hdecay
  simp only [ENNReal.toReal_one, one_pow, one_mul, mul_one] at hlower
  rw [← hcalib, integral_real_pair_eq_pos_sub_neg_of_expected_abs μ H hH
    (measurable_unitWindow d) (isBounded_unitWindow d) MeasurableSet.univ hfinite] at hlower
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hbase, hS⟩) henergy).mp
  rw [ENNReal.toReal_add hbase hS]
  change (latticeRieszEnergy Λ s).toReal ≤ A.toReal - B.toReal at hlower
  linarith

/-- The analytic witness alone supplies the gap field of the two-zone input.
The existence of such a witness for each actual E8/Leech potential is still open. -/
theorem twoZoneSlackCertificate_of_spectral_minorant {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (Λ : Set (Ambient d)) (hbase : latticeRieszEnergy Λ s ≠ ∞)
    (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hdecay : HasRapidDecay (realSpectralKernel ν g))
    (r a b : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hminor : ∀ x y, x ≠ y →
      rieszPotential s x y + ENNReal.ofReal (-realSpectralKernel ν g (x - y)) =
        radialSlackPotential φ x y + ENNReal.ofReal (realSpectralKernel ν g (x - y)))
    (hcalib : (latticeRieszEnergy Λ s).toReal =
      (∫ v, realSpectralKernel ν g v) - realSpectralKernel ν g 0)
    (hfar : ∀ u : ℝ, 0 < u → u ≤ r / 2 → a ≤ φ u)
    (hnear : ∀ u : ℝ, r / 2 ≤ u → u < r → b * (r - u) ^ 2 ≤ φ u) :
    TwoZoneSlackCertificate Λ s r a b φ := by
  exact ⟨hφ, stationarySlackGapInput_of_spectral_minorant hs Λ hbase ν g hg hgnonneg
    hdecay (radialSlackPotential φ) (measurable_radialSlackPotential hφ) hminor hcalib,
    hfar, hnear⟩

end E8Leech
