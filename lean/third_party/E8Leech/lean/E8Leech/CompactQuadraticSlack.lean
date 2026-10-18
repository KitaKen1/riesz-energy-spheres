import E8Leech.NormalizedLaplaceSlack
import E8Leech.OriginSlack

/-!
# Origin-inclusive uniform quadratic slack on the full shortest-radius interval

Combine an independently certified origin value, strict interior positivity,
compactness and the normalized finite positive Laplace block. The resulting
bound is c (r-u)^2 for every u in [0,r], not just a close-pair threshold.
This implements Section 2.3 of the supplied paper without theta derivatives
or differentiating the improper integral. Actual CKMRV inputs remain premises.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform

theorem compact_far_positive_of_origin_and_interior {a b r : ℝ}
    (hr : 0 < r) (φ : ℝ × ℝ → ℝ)
    (horigin : ∀ α ∈ Icc a b, 0 < φ (α, 0))
    (hinterior : ∀ α ∈ Icc a b, ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u)) :
    ∀ p ∈ Icc a b ×ˢ Icc 0 (7 / 8 * r), 0 < φ p := by
  rintro ⟨α, u⟩ ⟨hα, hu⟩
  by_cases hz : u = 0
  · simpa only [hz] using horigin α hα
  · exact hinterior α hα u (lt_of_le_of_ne hu.1 (Ne.symm hz)) (by linarith only [hu.2, hr])

/-- The origin proof uses the actual Fourier transform and actual lattice energy. -/
theorem compact_far_positive_of_schwartz_gaussian_duality
    {d : ℕ} {Λ : Set (Ambient d)} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (f : ℝ → 𝓢(Ambient d, ℂ)) (φ : ℝ × ℝ → ℝ)
    {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (him : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ ξ, (𝓕 (f (Real.pi ^ 2 / α)) ξ).im = 0)
    (hnonneg : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (f (Real.pi ^ 2 / α)) ξ).re)
    (hfinite : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      latticePotentialEnergy Λ (gaussianPotential (Real.pi ^ 2 / α)) ≠ ∞)
    (hcalib : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      (𝓕 (f (Real.pi ^ 2 / α)) (0 : Ambient d)).re - (f (Real.pi ^ 2 / α) 0).re =
        (latticePotentialEnergy Λ (gaussianPotential (Real.pi ^ 2 / α))).toReal)
    (hdual : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      gaussianKernel α (0 : Ambient d) - (f α 0).re =
        (Real.pi / α) ^ m * (𝓕 (f (Real.pi ^ 2 / α)) (0 : Ambient d)).re)
    (hφzero : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      φ (α, 0) = gaussianKernel α (0 : Ambient d) - (f α 0).re)
    (hinterior : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u)) :
    ∀ p ∈ Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r), 0 < φ p := by
  apply compact_far_positive_of_origin_and_interior hr φ _ hinterior
  intro α hα
  rw [hφzero α hα]
  exact (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 3) m) (Real.exp_pos _)).trans_le
    (origin_slack_compact_lower f m hα hz hne hnorm (him α hα)
      (hnonneg α hα) (hfinite α hα) (hcalib α hα) (hdual α hα))

/-- Explicit pasting of the two radius regions, including both endpoints. -/
theorem full_quadratic_slack_of_two_regions {A c r u : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hu : u ∈ Icc 0 r)
    {φ : ℝ → ℝ}
    (hfar : ∀ v ∈ Icc 0 (7 / 8 * r), A ≤ φ v)
    (hnear : ∀ v ∈ Icc (7 / 8 * r) r, c * (r - v) ^ 2 ≤ φ v) :
    min (A / r ^ 2) c * (r - u) ^ 2 ≤ φ u := by
  by_cases hf : u ≤ 7 / 8 * r
  · have hs : (r - u) ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hu.2) (by linarith only [hu.1]) 2
    have hd : 0 < r ^ 2 := pow_pos hr 2
    calc
      _ ≤ (A / r ^ 2) * (r - u) ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ ≤ (A / r ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hs (div_pos hA hd).le
      _ = A := div_mul_cancel₀ _ (ne_of_gt hd)
      _ ≤ φ u := hfar u ⟨hu.1, hf⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (hnear u ⟨(not_le.mp hf).le, hu.2⟩)

theorem uniform_full_quadratic_slack_of_normalized_laplace_kernel
    (m : ℕ) {r : ℝ} (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (φ K : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc (Real.pi / 4) (Real.pi / 3) ×ˢ Icc 0 (7 / 8 * r)))
    (horigin : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), 0 < φ (α, 0))
    (hinterior : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u))
    (hK : ContinuousOn K (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2))
    (hKpos : ∀ p ∈ Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2, 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3), ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))) :
    ∃ c : ℝ, 0 < c ∧ ∀ α ∈ Icc (Real.pi / 4) (Real.pi / 3),
      ∀ u ∈ Icc (0 : ℝ) r, c * (r - u) ^ 2 ≤ φ (α, u) := by
  obtain ⟨A, hA, hlA⟩ := compact_rectangle_positive_lower hφ
    (compact_far_positive_of_origin_and_interior hr φ horigin hinterior)
  obtain ⟨B, hB, hlB⟩ := compact_rectangle_positive_lower hK hKpos
  let c := 4 * (3 : ℝ) ^ m * B * Real.exp (-8 * Real.pi) * r ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨min (A / r ^ 2) c, lt_min (div_pos hA (pow_pos hr 2)) hc, ?_⟩
  intro α hα u hu
  apply full_quadratic_slack_of_two_regions hA hr hu (hlA α hα)
  intro v hv
  have hv0 : 0 ≤ v := by linarith only [hv.1, hr]
  have hvsq := pow_le_pow_left₀ hv0 hv.2 2
  have hfour : v ^ 2 ≤ 4 := by rcases hroot with h | h <;> linarith only [hvsq, h]
  have hJ := gaussian_normalized_laplace_block_lower m K hB.le hα hfour
    (hKnonneg _ (gaussian_dual_compact_interval hα)) (hlB _ (gaussian_dual_compact_interval hα))
    (hint α hα v hv)
  have hsin := sine_squared_even_root_lower hr hroot hv.1 hv.2
  rw [hfactor α hα v hv]
  calc
    c * (r - v) ^ 2 = 4 * (r ^ 2 * (r - v) ^ 2) *
        ((3 : ℝ) ^ m * B * Real.exp (-8 * Real.pi)) := by dsimp [c]; ring
    _ ≤ 4 * Real.sin (Real.pi * v ^ 2 / 2) ^ 2 *
        ((3 : ℝ) ^ m * B * Real.exp (-8 * Real.pi)) := by gcongr
    _ ≤ 4 * Real.sin (Real.pi * v ^ 2 / 2) ^ 2 *
        ((Real.pi / α) ^ m * ∫ w in Ioi (0 : ℝ),
          K (Real.pi / α, w) * Real.exp (-Real.pi * v ^ 2 * w)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

theorem full_quadratic_slack_close_pair_cost {r c t u v : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (ht : 0 < t)
    (hclose : u < r * (1 - t)) (hlower : c * (r - u) ^ 2 ≤ v) :
    (c * r ^ 2) * t ^ 2 ≤ v := by
  have hgap : r * t ≤ r - u := by nlinarith only [hclose]
  have hs := pow_le_pow_left₀ (mul_pos hr ht).le hgap 2
  calc
    _ = c * (r * t) ^ 2 := by ring
    _ ≤ c * (r - u) ^ 2 := mul_le_mul_of_nonneg_left hs hc
    _ ≤ v := hlower

end E8Leech
