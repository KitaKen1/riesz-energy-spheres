import E8Leech.GaussianPotentialMixtures
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Actual off-diagonal Riesz kernels as nonnegative Gaussian integrals

Scale the existing Euler integral, prove integrability, and only then identify
the real integral with the nonnegative integral. The diagonal is excluded from
both energy definitions and is not part of this pointwise identification.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem integrableOn_power_exponential {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun α : ℝ => α ^ (a - 1) * Real.exp (-(r * α))) (Ioi 0) := by
  have hscale : IntegrableOn
      (fun α : ℝ => Real.exp (-(r * α)) * (r * α) ^ (a - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) 0 hr).mpr
    simpa only [mul_zero] using Real.GammaIntegral_convergent ha
  have hpow : r ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  refine (hscale.div_const (r ^ (a - 1))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  rw [Real.mul_rpow hr.le hα.le]
  field_simp

theorem integral_normalized_power_exponential {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ α : ℝ in Ioi 0, (α ^ (a - 1) * Real.exp (-(r * α))) / Real.Gamma a) =
      (1 / r) ^ a := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  rw [← div_eq_mul_inv]
  exact mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos ha).ne'

def rieszGaussianFamily {d : ℕ} (s α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (α ^ (s / 2 - 1) * Real.exp (-(dist x y ^ 2 * α)) / Real.Gamma (s / 2))

theorem measurable_rieszGaussianFamily_joint (d : ℕ) (s : ℝ) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      rieszGaussianFamily s p.1 p.2.1 p.2.2) := by
  unfold rieszGaussianFamily
  fun_prop

theorem rieszPotential_eq_gaussian_integral_offDiagonal {d : ℕ} {s : ℝ} (hs : 0 < s)
    (x y : Ambient d) (hxy : x ≠ y) :
    rieszPotential s x y = potentialMixture (volume.restrict (Ioi (0 : ℝ)))
      (rieszGaussianFamily s) x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have ha : 0 < s / 2 := by positivity
  have hr : 0 < dist x y ^ 2 := sq_pos_of_pos hd
  have hi := (integrableOn_power_exponential ha hr).div_const (Real.Gamma (s / 2))
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun α : ℝ => α ^ (s / 2 - 1) * Real.exp (-(dist x y ^ 2 * α)) /
        Real.Gamma (s / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.exp_pos _).le)
      (Real.Gamma_pos_of_pos ha).le
  unfold potentialMixture rieszGaussianFamily rieszPotential
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_normalized_power_exponential ha hr, ENNReal.ofReal_rpow_of_pos hd]
  congr 1
  rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  congr 1
  ring

theorem orderedWindowEnergy_riesz_eq_gaussian_integral {d : ℕ} {s : ℝ} (hs : 0 < s)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy (rieszPotential s) c W =
      ∫⁻ α in Ioi (0 : ℝ), orderedWindowEnergy (rieszGaussianFamily s α) c W := by
  rw [orderedWindowEnergy_congr_offDiagonal (rieszPotential s)
    (potentialMixture (volume.restrict (Ioi (0 : ℝ))) (rieszGaussianFamily s))
    (fun x y hxy => rieszPotential_eq_gaussian_integral_offDiagonal hs x y hxy) c W]
  apply orderedWindowEnergy_potentialMixture
  intro x y
  exact (measurable_rieszGaussianFamily_joint d s).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

private theorem latticeRieszEnergy_eq_rieszGaussianMixture {d : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Set (Ambient d)) :
    latticeRieszEnergy Λ s = latticePotentialEnergy Λ
      (potentialMixture (volume.restrict (Ioi (0 : ℝ))) (rieszGaussianFamily s)) := by
  unfold latticeRieszEnergy latticePotentialEnergy
  apply tsum_congr
  intro y
  by_cases hy : (y : Ambient d) = 0
  · simp [hy]
  · simp only [if_neg hy]
    exact rieszPotential_eq_gaussian_integral_offDiagonal (d := d) hs
      (0 : Ambient d) (y : Ambient d) (Ne.symm hy)

theorem latticeRieszEnergy_eq_gaussian_integral {d : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) :
    latticeRieszEnergy Λ s = ∫⁻ α in Ioi (0 : ℝ),
      latticePotentialEnergy Λ (rieszGaussianFamily s α) := by
  rw [latticeRieszEnergy_eq_rieszGaussianMixture hs Λ]
  apply latticePotentialEnergy_potentialMixture (volume.restrict (Ioi (0 : ℝ)))
    (rieszGaussianFamily s) _ Λ hΛ
  intro x y
  exact (measurable_rieszGaussianFamily_joint d s).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

theorem rieszEnergy_eq_gaussian_integral {d : ℕ} {s : ℝ} (hs : 0 < s)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] :
    rieszEnergy s μ = ∫⁻ α in Ioi (0 : ℝ), ∫⁻ c,
      orderedWindowEnergy (rieszGaussianFamily s α) c (unitWindow d) ∂μ := by
  unfold rieszEnergy
  have heq : (∫⁻ c, orderedWindowEnergy (rieszPotential s) c (unitWindow d) ∂μ) =
      ∫⁻ c, orderedWindowEnergy
        (potentialMixture (volume.restrict (Ioi (0 : ℝ))) (rieszGaussianFamily s)) c
        (unitWindow d) ∂μ := by
    apply lintegral_congr
    intro c
    exact orderedWindowEnergy_congr_offDiagonal _ _
      (fun x y hxy => rieszPotential_eq_gaussian_integral_offDiagonal hs x y hxy) c _
  rw [heq]
  exact expected_orderedWindowEnergy_potentialMixture _ μ _
    (measurable_rieszGaussianFamily_joint d s) (measurable_unitWindow d)

theorem expected_riesz_gap_of_gaussianFamily_gap {d : ℕ} {s : ℝ} (hs : 0 < s)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : ℝ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hgap : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      latticePotentialEnergy Λ (rieszGaussianFamily s α) +
        (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow d) ∂μ) ≤
        ∫⁻ c, orderedWindowEnergy (rieszGaussianFamily s α) c (unitWindow d) ∂μ) :
    latticeRieszEnergy Λ s +
      (∫⁻ c, orderedWindowEnergy (potentialMixture (volume.restrict (Ioi (0 : ℝ))) V) c
        (unitWindow d) ∂μ) ≤ rieszEnergy s μ := by
  have hp := expected_potentialMixture_gap (volume.restrict (Ioi (0 : ℝ))) μ
    (rieszGaussianFamily s) V (measurable_rieszGaussianFamily_joint d s) hV Λ hΛ hgap
  rw [← latticeRieszEnergy_eq_rieszGaussianMixture hs Λ] at hp
  have heq := rieszEnergy_eq_gaussian_integral hs μ
  rw [expected_orderedWindowEnergy_potentialMixture _ μ _
    (measurable_rieszGaussianFamily_joint d s) (measurable_unitWindow d), ← heq] at hp
  exact hp

end E8Leech
