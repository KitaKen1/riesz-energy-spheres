import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RieszSphereFC

/-- Split the regular Mellin integral at one and use inversion on the lower half. -/
theorem weakFEPair_lambdaZero_integral (P : WeakFEPair ℂ)
    (hfg : P.f = P.g) (hε : P.ε = 1) (hf₀ : P.f₀ = 1) (hg₀ : P.g₀ = 1) (u : ℂ) :
    P.Λ₀ u = ∫ t in Ioi (1 : ℝ), (P.f t - 1) *
      ((t : ℂ) ^ (u - 1) + (t : ℂ) ^ ((P.k : ℂ) - u - 1)) := by
  let H : ℝ → ℂ := (Ioi 1).indicator (fun t => P.f t - 1)
  have hmod (v : ℂ) : MellinConvergent P.f_modif v :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin v).1
  have hH (v : ℂ) : MellinConvergent H v := by
    have hi := (hmod v).indicator (t := Ioi (1 : ℝ)) measurableSet_Ioi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases h1 : 1 < t
    · have hn : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_gt h1) h.2
      simp [H, h1, WeakFEPair.f_modif, hf₀, hn]
    · simp [H, h1]
  have hsplit (t : ℝ) (ht : 0 < t) :
      P.f_modif t = H t + (t : ℂ) ^ (-(P.k : ℂ)) * H t⁻¹ := by
    have hfe : P.f t = (t : ℂ) ^ (-(P.k : ℂ)) * P.f t⁻¹ := by
      have h := P.h_feq t⁻¹ (inv_pos.mpr ht)
      rw [← hfg, hε] at h
      simpa only [one_div, inv_inv, one_mul, smul_eq_mul, Real.inv_rpow ht.le,
        ← Real.rpow_neg ht.le, Complex.ofReal_cpow ht.le, Complex.ofReal_neg] using h
    rcases lt_trichotomy t 1 with h1 | rfl | h1
    · have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h1
      have hn : t ∉ Ioi (1 : ℝ) := not_lt_of_gt h1
      have hm : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, h1⟩
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem hn,
        indicator_of_mem hm, hε, hg₀, one_mul, smul_eq_mul, mul_one, zero_add]
      simp only [H, indicator_of_notMem hn, zero_add]
      rw [indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi)]
      rw [Complex.ofReal_cpow ht.le, Complex.ofReal_neg, hfe]
      ring
    · simp [WeakFEPair.f_modif, H]
    · have hi : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr h1
      have hm : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_gt h1) h.2
      have hin : t⁻¹ ∉ Ioi (1 : ℝ) := not_lt_of_gt hi
      simp [WeakFEPair.f_modif, H, h1, hm, hin, hf₀]
  have hG : MellinConvergent (fun t => (t : ℂ) ^ (-(P.k : ℂ)) * H t⁻¹) u := by
    have hi := (hmod u).sub (hH u)
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Pi.sub_apply, smul_eq_mul]
    rw [hsplit t ht]
    ring
  have he : P.Λ₀ u = mellin H u + mellin H ((P.k : ℂ) - u) := by
    calc
      P.Λ₀ u = mellin (fun t => H t + (t : ℂ) ^ (-(P.k : ℂ)) * H t⁻¹) u := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [hsplit t ht]
      _ = mellin H u + mellin (fun t => (t : ℂ) ^ (-(P.k : ℂ)) * H t⁻¹) u :=
        (hasMellin_add (hH u) hG).2
      _ = mellin H u + mellin H ((P.k : ℂ) - u) := by
        simp only [← smul_eq_mul, mellin_cpow_smul, mellin_comp_inv]
        congr 2
        ring
  have hweight (v : ℂ) : (fun t : ℝ => (t : ℂ) ^ (v - 1) • H t) =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (v - 1) * (P.f t - 1)) := by
    funext t
    by_cases ht : 1 < t <;> simp [H, ht, smul_eq_mul]
  have htail (v : ℂ) : mellin H v =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (v - 1) * (P.f t - 1) := by
    unfold mellin
    rw [hweight v, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
  have htail_int (v : ℂ) : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (v - 1) * (P.f t - 1)) (Ioi 1) := by
    have hi := hH v
    rw [MellinConvergent, hweight v] at hi
    change Integrable ((Ioi 1).indicator (fun t : ℝ =>
      (t : ℂ) ^ (v - 1) * (P.f t - 1))) (volume.restrict (Ioi 0)) at hi
    rw [integrable_indicator_iff measurableSet_Ioi] at hi
    change Integrable _ ((volume.restrict (Ioi 0)).restrict (Ioi 1)) at hi
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))] at hi
    exact hi
  rw [he, htail, htail, ← integral_add (htail_int u) (htail_int ((P.k : ℂ) - u))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

end RieszSphereFC
