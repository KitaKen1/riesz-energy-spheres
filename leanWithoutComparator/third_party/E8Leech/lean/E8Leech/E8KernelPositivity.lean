import E8Leech.KronRR
import E8Leech.KronSR
import E8Leech.KronRS
import E8Leech.KronSS
import E8Leech.KronCornerCert
import E8Leech.E8UnitCostFinal

/-!
# The `E8` kernel inequality (6.4)(1) on the whole regular locus

The quadrant `q, t > 0` is the union of five pieces, each with its own kernel-checked certificate:

* the corner box `10/11 ≤ q, t ≤ 11/10` around the crossing `(1, 1)` of the two singular curves
  `t = q` and `qt = 1` (`ckmrvEightHatKernel_pos_corner`, by concavity in `t`);
* `q, t ≥ 1` (`ckmrvEightHatKernel_pos_ge_one`), `q ≤ 1 ≤ t`
  (`ckmrvEightHatKernel_pos_le_one_ge_one`), `t ≤ 1 ≤ q` (`ckmrvEightHatKernel_pos_ge_one_le_one`)
  and `q, t ≤ 1` (`ckmrvEightHatKernel_pos_le_one`), each outside the corner box.

* `ckmrvEightHatKernel_pos`: `Re 𝒦̂(iq, it) > 0` for all `q, t > 0` with `j(iq) ≠ j(it)`.
* `e8KernelNonneg`: the weak inequality everywhere on the quadrant.
* `e8_analyticUnitCostInput`: the analytic unit-cost input of `E8` for every `s > 0`, without
  hypotheses.
* `e8_analyticUnitCostInput_gt`: the same in the form asked by `CertifiedCrystallizationInputs`.
* `e8_stationaryCrystallization_of_periodic`: the `E8` target from the periodic stability input
  alone.
-/

noncomputable section

namespace E8Leech

open scoped Real

/-- **(6.4)(1) for `E8`.** The real part of the kernel `𝒦̂(iq, it)` is strictly positive for all
`q, t > 0` off the singular curves `j(iq) = j(it)`. -/
theorem ckmrvEightHatKernel_pos {q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re := by
  have hinv : ∀ x : ℝ, 0 < x → ¬ (10 / 11 : ℝ) ≤ x → (11 / 10 : ℝ) < x⁻¹ := fun x hx h => by
    rw [inv_eq_one_div, lt_div_iff₀ hx]
    linarith [not_le.mp h]
  by_cases hbox : ((10 / 11 : ℝ) ≤ q ∧ q ≤ 11 / 10) ∧ (10 / 11 : ℝ) ≤ t ∧ t ≤ 11 / 10
  · exact ckmrvEightHatKernel_pos_corner hbox.1.1 hbox.1.2 hbox.2.1 hbox.2.2 hJ
  · rcases le_total 1 q with hq1 | hq1 <;> rcases le_total 1 t with ht1 | ht1
    · have hout : (11 / 10 : ℝ) < q ∨ (11 / 10 : ℝ) < t := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        exact hbox ⟨⟨by linarith, h.1⟩, by linarith, h.2⟩
      exact ckmrvEightHatKernel_pos_ge_one hq1 ht1 (fun h => hJ (by rw [h])) hout hJ
    · have hout : (11 / 10 : ℝ) < q ∨ (11 / 10 : ℝ) < t⁻¹ := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        refine hbox ⟨⟨by linarith, h.1⟩, ?_, by linarith⟩
        by_contra h'
        exact absurd (hinv t ht h') (not_lt.mpr h.2)
      exact ckmrvEightHatKernel_pos_ge_one_le_one hq1 ht ht1 hout hJ
    · have hout : (11 / 10 : ℝ) < q⁻¹ ∨ (11 / 10 : ℝ) < t := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        refine hbox ⟨⟨?_, by linarith⟩, by linarith, h.2⟩
        by_contra h'
        exact absurd (hinv q hq h') (not_lt.mpr h.1)
      exact ckmrvEightHatKernel_pos_le_one_ge_one hq hq1 ht1 hout hJ
    · have hout : (11 / 10 : ℝ) < q⁻¹ ∨ (11 / 10 : ℝ) < t⁻¹ := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        refine hbox ⟨⟨?_, by linarith⟩, ?_, by linarith⟩
        · by_contra h'
          exact absurd (hinv q hq h') (not_lt.mpr h.1)
        · by_contra h'
          exact absurd (hinv t ht h') (not_lt.mpr h.2)
      exact ckmrvEightHatKernel_pos_le_one hq hq1 ht ht1 hout hJ

/-- The weak (6.4)(1) for `E8` on the whole quadrant (the kernel is `0` on the singular curves). -/
theorem e8KernelNonneg : E8KernelNonneg :=
  e8KernelNonneg_of_pos_regular fun _ _ hq ht hJ => ckmrvEightHatKernel_pos hq ht hJ

/-- **The `E8` analytic unit-cost input**, for every exponent `s > 0`, without hypotheses. -/
theorem e8_analyticUnitCostInput {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput e8Set s (Real.sqrt 2) C⁻¹ (1 / 8) :=
  e8_analyticUnitCostInput_of_kernel_pos hs fun _ _ hq ht hJ => ckmrvEightHatKernel_pos hq ht hJ

/-- The `E8` analytic input in the form asked by `CertifiedCrystallizationInputs`. -/
theorem e8_analyticUnitCostInput_gt (s : ℝ) (hs : ((8 : ℕ) : ℝ) < s) :
    ∃ A δA : ℝ, 0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput e8Set s (Real.sqrt 2) A δA := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  obtain ⟨C, hC, h⟩ := e8_analyticUnitCostInput hs0
  exact ⟨C⁻¹, 1 / 8, (inv_pos.mpr hC).le, by norm_num, h⟩

/-- The `E8` crystallization target from the periodic stability input alone: the analytic input is
now a theorem. -/
theorem e8_stationaryCrystallization_of_periodic {E B c η₀ : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : PeriodicStabilityInput e8Set (Real.sqrt 2) E B c η₀) :
    StationaryCrystallizationFor e8Set :=
  stationaryCrystallizationFor_of_inputs e8Set (fun _ hx _ hy => e8Set_sub hx hy)
    (Real.sqrt 2) E B c η₀ (Real.sqrt_pos.mpr (by norm_num)) hE hB hc hη₀ hperiodic
    e8_analyticUnitCostInput_gt

end E8Leech
