import Riesz.PeanoInterior
import Riesz.NodeSeparation

/-!
# Endpoint factors for the unchanged corrected Peano kernel

Before the first node and after the last node the exact kernel is a
negative sixth power divided by 720. Combining this certificate with
the checked global mesh bound gives a uniform minimum of the mesh
scale and both endpoint factors. This does not assume regularity of
the singular background potential.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

theorem node_gt_quarter (i : Fin 4) : (1:ℝ)/4 < node i := by
  have hi := abs_lt.mp (node_close_to_midpoint i)
  have hi0 : (0:ℝ) ≤ i := by positivity
  linarith

theorem unscaledPeanoKernel_left_endpoint {m : ℕ} (hm : 8 ≤ m)
    {z : ℝ} (hz : z ≤ 1/4) : unscaledPeanoKernel m z = -z^6/720 := by
  rw [unscaledPeanoKernel_left_formula hm (by linarith)]
  have hs : (∑ i : Fin 4, positiveFifth (node i-z)) =
      -(∑ i : Fin 4, (z-node i)^5) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold positiveFifth
    rw [max_eq_left (by linarith [node_gt_quarter i])]
    ring
  rw [hs, right_fifth_sum]
  norm_num [midpointPrimitive, fifthMomentDefect]
  ring

theorem unscaledPeanoKernel_right_endpoint {m : ℕ} (hm : 8 ≤ m)
    {z : ℝ} (hz : z ≤ 1/4) :
    unscaledPeanoKernel m ((m:ℝ)-z) = -z^6/720 := by
  rw [unscaledPeanoKernel_right_formula hm (by linarith)]
  have hs : (∑ i : Fin 4, positiveFifth (z-node i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [positiveFifth, max_eq_right (by linarith [node_gt_quarter i] : z-node i ≤ 0)]
  rw [hs]
  ring

theorem unitPeanoKernel_left_endpoint {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ≤ 1/(4*(m:ℝ))) : unitPeanoKernel m t = -t^6/720 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m:ℝ)*t ≤ 1/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*(m:ℝ))).mp ht
    nlinarith
  have h := unitPeanoKernel_scale hm ((m:ℝ)*t)
  rw [mul_div_cancel_left₀ _ hm0.ne', unscaledPeanoKernel_left_endpoint hm hz] at h
  rw [h]
  field_simp

theorem unitPeanoKernel_right_endpoint {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : 1-1/(4*(m:ℝ)) ≤ t) : unitPeanoKernel m t = -(1-t)^6/720 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m:ℝ)*(1-t) ≤ 1/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*(m:ℝ))).mp
      (show 1-t ≤ 1/(4*(m:ℝ)) by linarith)
    nlinarith
  have h := unitPeanoKernel_scale hm ((m:ℝ)-(m:ℝ)*(1-t))
  have harg : ((m:ℝ)-(m:ℝ)*(1-t))/(m:ℝ) = t := by field_simp; ring
  rw [harg, unscaledPeanoKernel_right_endpoint hm hz] at h
  rw [h]
  field_simp

theorem unitPeanoKernel_left_factor {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : |unitPeanoKernel m t| ≤ 262144*t^6 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  by_cases hs : t ≤ 1/(4*(m:ℝ))
  · rw [unitPeanoKernel_left_endpoint hm hs]
    rw [abs_div, abs_neg, abs_pow, abs_of_nonneg ht.1]
    norm_num
    nlinarith [pow_nonneg ht.1 6]
  · have hbase : 1/(m:ℝ) ≤ 4*t := by
      apply (div_le_iff₀ hm0).mpr
      have h := (div_le_iff₀ (by positivity : 0 < 4*(m:ℝ))).mp (not_le.mp hs).le
      nlinarith
    calc
      _ ≤ 64/(m:ℝ)^6 := unitPeanoKernel_bound hm ht
      _ = 64*(1/(m:ℝ))^6 := by rw [div_pow, one_pow]; ring
      _ ≤ 64*(4*t)^6 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase 6) (by norm_num)
      _ = _ := by ring

theorem unitPeanoKernel_right_factor {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : |unitPeanoKernel m t| ≤ 262144*(1-t)^6 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  by_cases hs : 1-1/(4*(m:ℝ)) ≤ t
  · rw [unitPeanoKernel_right_endpoint hm hs]
    rw [abs_div, abs_neg, abs_pow, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    norm_num
    nlinarith [pow_nonneg (sub_nonneg.mpr ht.2) 6]
  · have hbase : 1/(m:ℝ) ≤ 4*(1-t) := by
      apply (div_le_iff₀ hm0).mpr
      have h := (div_le_iff₀ (by positivity : 0 < 4*(m:ℝ))).mp
        (show 1/(4*(m:ℝ)) ≤ 1-t by linarith [not_le.mp hs])
      nlinarith
    calc
      _ ≤ 64/(m:ℝ)^6 := unitPeanoKernel_bound hm ht
      _ = 64*(1/(m:ℝ))^6 := by rw [div_pow, one_pow]; ring
      _ ≤ 64*(4*(1-t))^6 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase 6) (by norm_num)
      _ = _ := by ring

theorem unitPeanoKernel_endpoint_min {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |unitPeanoKernel m t| ≤ 262144*min ((m:ℝ)⁻¹^6) (min (t^6) ((1-t)^6)) := by
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 262144),
    mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 262144)]
  apply le_min
  · have h := unitPeanoKernel_bound hm ht
    have hpow : 0 ≤ (m:ℝ)⁻¹^6 := by positivity
    calc
      _ ≤ 64*((m:ℝ)⁻¹)^6 := by simpa only [div_eq_mul_inv, inv_pow] using h
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hpow
  · exact le_min (unitPeanoKernel_left_factor hm ht) (unitPeanoKernel_right_factor hm ht)

#print axioms node_gt_quarter
#print axioms unscaledPeanoKernel_left_endpoint
#print axioms unscaledPeanoKernel_right_endpoint
#print axioms unitPeanoKernel_left_endpoint
#print axioms unitPeanoKernel_right_endpoint
#print axioms unitPeanoKernel_left_factor
#print axioms unitPeanoKernel_right_factor
#print axioms unitPeanoKernel_endpoint_min

end SphericalRiesz.Boundary
