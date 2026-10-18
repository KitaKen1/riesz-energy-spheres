import E8Leech.KronLeechUpper
import E8Leech.KronLTRS
import E8Leech.KronLTSS
import E8Leech.CKMRVLaplaceAxisClean

/-!
# The Leech kernel inequality (6.4)(1) on the whole regular locus

The quadrant `u, t > 0` is the union of four pieces, each with its own kernel-checked
certificate:

* the half plane `t ≥ 1` (`ckmrvLeechHatKernel_pos_of_one_le`, itself the union of the regions
  `u, t ≥ 1`, `u ≤ 1 ≤ t` and of the corner box);
* the corner box `50/59 ≤ u, t ≤ 59/50` around the crossing `(1, 1)` of the two singular curves
  `t = u` and `ut = 1` (`ckmrvLeechHatKernel_pos_corner`, by joint Taylor expansions);
* `t ≤ 1 ≤ u` (`ckmrvLeechHatKernel_pos_ge_one_le_one`) and `u, t ≤ 1`
  (`ckmrvLeechHatKernel_pos_le_one`), each outside the corner box, by the third-order jets of the
  pairings with the second variable inverted.

* `ckmrvLeechHatKernel_pos`: `Re 𝒦̂⁽²⁴⁾(iu, it) > 0` for all `u, t > 0` with `j(iu) ≠ j(it)`.
* `ckmrvLeechHatKernel_nonneg`: the weak inequality off the singular points `t = u`, `t = u⁻¹`,
  which is the first field of `LeechKernelInequalities`.

On the singular curves the Lean kernel has a junk value (a division by zero in the plus kernel
only), about which nothing is claimed.
-/

noncomputable section

namespace E8Leech

open scoped Real

/-- **(6.4)(1) for the Leech lattice.** The real part of the kernel `𝒦̂⁽²⁴⁾(iu, it)` is strictly
positive for all `u, t > 0` off the singular curves `j(iu) = j(it)`. -/
theorem ckmrvLeechHatKernel_pos {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  rcases le_total 1 t with ht1 | ht1
  · exact ckmrvLeechHatKernel_pos_of_one_le hu ht1 hJ
  have hinv : ∀ x : ℝ, 0 < x → ¬ (50 / 59 : ℝ) ≤ x → (59 / 50 : ℝ) < x⁻¹ := fun x hx h => by
    rw [inv_eq_one_div, lt_div_iff₀ hx]
    linarith [not_le.mp h]
  by_cases hbox : ((50 / 59 : ℝ) ≤ u ∧ u ≤ 59 / 50) ∧ (50 / 59 : ℝ) ≤ t
  · exact ckmrvLeechHatKernel_pos_corner hbox.1.1 hbox.1.2 hbox.2 (by linarith) hJ
  rcases le_total 1 u with hu1 | hu1
  · have hout : (59 / 50 : ℝ) < u ∨ (59 / 50 : ℝ) < t⁻¹ := by
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      refine hbox ⟨⟨by linarith, h.1⟩, ?_⟩
      by_contra h'
      exact absurd (hinv t ht h') (not_lt.mpr h.2)
    exact ckmrvLeechHatKernel_pos_ge_one_le_one hu1 ht ht1 hout hJ
  · have hout : (59 / 50 : ℝ) < u⁻¹ ∨ (59 / 50 : ℝ) < t⁻¹ := by
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      refine hbox ⟨⟨?_, by linarith⟩, ?_⟩
      · by_contra h'
        exact absurd (hinv u hu h') (not_lt.mpr h.1)
      · by_contra h'
        exact absurd (hinv t ht h') (not_lt.mpr h.2)
    exact ckmrvLeechHatKernel_pos_le_one hu hu1 ht ht1 hout hJ

/-- The weak (6.4)(1) for the Leech lattice off the singular points `t = q`, `t = q⁻¹`: the
first field of `LeechKernelInequalities`. -/
theorem ckmrvLeechHatKernel_nonneg {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (h1 : t ≠ q)
    (h2 : t ≠ q⁻¹) : 0 ≤ (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re :=
  (ckmrvLeechHatKernel_pos hq ht (kleinModularJ_imagPt_ne hq ht h1 h2)).le

end E8Leech
