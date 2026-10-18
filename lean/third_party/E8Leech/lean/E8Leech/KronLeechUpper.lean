import E8Leech.KronLR
import E8Leech.KronLS
import E8Leech.KronLC

/-!
# The Leech kernel inequality (6.4)(1) for `t ≥ 1`

The three certificates of the half-plane `t ≥ 1` cover it completely:

* `ckmrvLeechHatKernel_pos_ge_one` (`KronLR`): `u, t ≥ 1` outside the corner box `[1, 59/50]²`;
* `ckmrvLeechHatKernel_pos_le_one_ge_one` (`KronLS`): `u ≤ 1 ≤ t` outside the corner box
  `1/u, t ≤ 59/50`;
* `ckmrvLeechHatKernel_pos_corner` (`KronLC`): the box `[50/59, 59/50]²`.

`ckmrvLeechHatKernel_pos_of_one_le` is the inequality for all `u > 0`, `t ≥ 1` off the singular
curves. The half-plane `t < 1` is not covered here.
-/

namespace E8Leech

/-- **(6.4)(1) for `d = 24` and `t ≥ 1`**: the Leech hat kernel is positive at `(iu, it)` for
every `u > 0` and `t ≥ 1`, off the singular curves `j(iu) = j(it)`. -/
theorem ckmrvLeechHatKernel_pos_of_one_le {u t : ℝ} (hu : 0 < u) (ht : 1 ≤ t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvLeechHatKernel (imagPt u) (imagPt t)).re := by
  rcases le_total 1 u with hu1 | hu1
  · by_cases hout : (59 / 50 : ℝ) < u ∨ (59 / 50 : ℝ) < t
    · exact ckmrvLeechHatKernel_pos_ge_one hu1 ht (fun h => hJ (by rw [h])) hout hJ
    · have hu2 : u ≤ 59 / 50 := not_lt.mp fun h => hout (Or.inl h)
      have ht2 : t ≤ 59 / 50 := not_lt.mp fun h => hout (Or.inr h)
      exact ckmrvLeechHatKernel_pos_corner (by linarith) hu2 (by linarith) ht2 hJ
  · by_cases hout : (59 / 50 : ℝ) < u⁻¹ ∨ (59 / 50 : ℝ) < t
    · exact ckmrvLeechHatKernel_pos_le_one_ge_one hu hu1 ht hout hJ
    · have hu2 : u⁻¹ ≤ 59 / 50 := not_lt.mp fun h => hout (Or.inl h)
      have ht2 : t ≤ 59 / 50 := not_lt.mp fun h => hout (Or.inr h)
      have h1 : (50 / 59 : ℝ) ≤ u := by
        have h2 := (inv_le_comm₀ hu (by norm_num : (0 : ℝ) < 59 / 50)).mp hu2
        norm_num at h2
        linarith
      exact ckmrvLeechHatKernel_pos_corner h1 (by linarith) (by linarith) ht2 hJ

end E8Leech
