import Riesz.PeanoEndpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A rational majorant for singular endpoint derivatives

The continuous majorant h^6/(t+h)^2 replaces a piecewise minimum.
Its integral is at most h^5. The actual original Peano kernel times
any measurable derivative bounded by A*(t^-2+(1-t)^-2) is integrable
and has integral bounded by C*A*m^-5. The actual E8 potential must
still be shown to have this derivative bound and a valid remainder.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def peanoEndpointWeight (h t : ℝ) : ℝ := h^6/(t+h)^2

theorem endpoint_inv_sq_majorant (h t M u : ℝ) (hh : 0 < h) (ht : 0 ≤ t)
    (hM : 0 ≤ M) (hmesh : u ≤ M*h^6) (hend : u ≤ M*t^6) :
    u*t⁻¹^2 ≤ 4*M*peanoEndpointWeight h t := by
  by_cases ht0 : t = 0
  · subst t
    simp only [inv_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
    unfold peanoEndpointWeight
    positivity
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hden : 0 < (t+h)^2 := sq_pos_of_pos (by positivity)
  rw [peanoEndpointWeight, ← mul_div_assoc, le_div_iff₀ hden]
  by_cases hsmall : t ≤ h
  · have hp : (t+h)^2 ≤ (2*h)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc
      _ ≤ (M*t^6*t⁻¹^2)*(2*h)^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hend (sq_nonneg _)) hp
          (sq_nonneg _) (by positivity)
      _ = 4*M*t^4*h^2 := by field_simp; ring
      _ ≤ 4*M*h^4*h^2 := by gcongr
      _ = _ := by ring
  · have hp : (t+h)^2 ≤ (2*t)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [not_le.mp hsmall]) 2
    calc
      _ ≤ (M*h^6*t⁻¹^2)*(2*t)^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hmesh (sq_nonneg _)) hp
          (sq_nonneg _) (by positivity)
      _ = _ := by field_simp; norm_num

theorem peanoEndpointWeight_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (peanoEndpointWeight h) (Set.Icc (0:ℝ) 1) := by
  intro t ht
  have hz : t+h ≠ 0 := ne_of_gt (by linarith [ht.1])
  exact (continuousAt_const.div ((continuousAt_id.add continuousAt_const).pow 2)
    (pow_ne_zero 2 hz)).continuousWithinAt

theorem peanoEndpointWeight_integral {h : ℝ} (hh : 0 < h) :
    (∫ t in (0:ℝ)..1, peanoEndpointWeight h t) = h^6*(h⁻¹-(1+h)⁻¹) := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => -(h^6)*(t+h)⁻¹) (peanoEndpointWeight h t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hz : t+h ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hd := (((hasDerivAt_id t).add_const h).inv hz).const_mul (-(h^6))
    convert hd using 1
    · rfl
    · dsimp only [peanoEndpointWeight, id_eq]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((peanoEndpointWeight_continuousOn hh).intervalIntegrable_of_Icc (by norm_num))
  rw [hi]
  simp only [zero_add]
  ring

theorem peanoEndpointWeight_integral_le {h : ℝ} (hh : 0 < h) :
    (∫ t in (0:ℝ)..1, peanoEndpointWeight h t) ≤ h^5 := by
  rw [peanoEndpointWeight_integral hh]
  calc
    _ ≤ h^6*h⁻¹ := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem unitPeanoKernel_singular_left {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |unitPeanoKernel m t| *t⁻¹^2 ≤ 4*262144*peanoEndpointWeight ((m:ℝ)⁻¹) t := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : |unitPeanoKernel m t| ≤ 262144*((m:ℝ)⁻¹)^6 :=
    (le_min_iff.mp (by
      simpa only [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 262144)] using
        unitPeanoKernel_endpoint_min hm ht)).1
  exact endpoint_inv_sq_majorant _ _ _ _ (inv_pos.mpr hm0) ht.1 (by norm_num)
    hmesh (unitPeanoKernel_left_factor hm ht)

theorem unitPeanoKernel_singular_right {m : ℕ} (hm : 8 ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |unitPeanoKernel m t| *(1-t)⁻¹^2 ≤
      4*262144*peanoEndpointWeight ((m:ℝ)⁻¹) (1-t) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : |unitPeanoKernel m t| ≤ 262144*((m:ℝ)⁻¹)^6 :=
    (le_min_iff.mp (by
      simpa only [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 262144)] using
        unitPeanoKernel_endpoint_min hm ht)).1
  exact endpoint_inv_sq_majorant _ _ _ _ (inv_pos.mpr hm0) (sub_nonneg.mpr ht.2)
    (by norm_num) hmesh (unitPeanoKernel_right_factor hm ht)

private theorem reflected_weight_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (fun t : ℝ => peanoEndpointWeight h (1-t)) (Set.Icc (0:ℝ) 1) :=
  (peanoEndpointWeight_continuousOn hh).comp (by fun_prop)
    (fun _ ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)

private theorem singular_product_majorant {m : ℕ} (hm : 8 ≤ m)
    (g : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ t ∈ Set.Ioo (0:ℝ) 1, |g t| ≤ A*(t⁻¹^2+(1-t)⁻¹^2))
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |unitPeanoKernel m t*g t| ≤ 4*262144*A*
      (peanoEndpointWeight ((m:ℝ)⁻¹) t+peanoEndpointWeight ((m:ℝ)⁻¹) (1-t)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  by_cases h0 : t = 0
  · subst t
    rw [unitPeanoKernel_left_endpoint hm (by positivity)]
    norm_num
    unfold peanoEndpointWeight
    positivity
  by_cases h1 : t = 1
  · subst t
    rw [unitPeanoKernel_right_endpoint hm (sub_le_self _ (by positivity))]
    norm_num
    unfold peanoEndpointWeight
    positivity
  have hti : t ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  rw [abs_mul]
  calc
    _ ≤ |unitPeanoKernel m t| *(A*(t⁻¹^2+(1-t)⁻¹^2)) :=
      mul_le_mul_of_nonneg_left (hg t hti) (abs_nonneg _)
    _ = A*(|unitPeanoKernel m t| *t⁻¹^2+|unitPeanoKernel m t| *(1-t)⁻¹^2) := by ring
    _ ≤ A*(4*262144*peanoEndpointWeight ((m:ℝ)⁻¹) t+
        4*262144*peanoEndpointWeight ((m:ℝ)⁻¹) (1-t)) :=
      mul_le_mul_of_nonneg_left (add_le_add (unitPeanoKernel_singular_left hm ht)
        (unitPeanoKernel_singular_right hm ht)) hA
    _ = _ := by ring

theorem unitPeanoKernel_singular_integrable {m : ℕ} (hm : 8 ≤ m)
    (g : ℝ → ℝ) (hgm : Measurable g) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ t ∈ Set.Ioo (0:ℝ) 1, |g t| ≤ A*(t⁻¹^2+(1-t)⁻¹^2)) :
    IntegrableOn (fun t => unitPeanoKernel m t*g t) (Set.Icc (0:ℝ) 1) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hc := ((peanoEndpointWeight_continuousOn (inv_pos.mpr hm0)).add
    (reflected_weight_continuousOn (inv_pos.mpr hm0))).const_mul (4*262144*A)
  apply hc.integrableOn_Icc.mono'
    ((unitPeanoKernel_continuous m).measurable.mul hgm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  exact singular_product_majorant hm g A hA hg t ht

theorem unitPeanoKernel_singular_integral_bound {m : ℕ} (hm : 8 ≤ m)
    (g : ℝ → ℝ) (hgm : Measurable g) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ t ∈ Set.Ioo (0:ℝ) 1, |g t| ≤ A*(t⁻¹^2+(1-t)⁻¹^2)) :
    |∫ t in (0:ℝ)..1, unitPeanoKernel m t*g t| ≤ 2097152*A/(m:ℝ)^5 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hc := ((peanoEndpointWeight_continuousOn (inv_pos.mpr hm0)).add
    (reflected_weight_continuousOn (inv_pos.mpr hm0))).const_mul (4*262144*A)
  have hi : IntervalIntegrable (fun t => unitPeanoKernel m t*g t) volume 0 1 :=
    IntegrableOn.intervalIntegrable (by
      simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
        unitPeanoKernel_singular_integrable hm g hgm A hA hg)
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => unitPeanoKernel m t*g t)
    (by norm_num : (0:ℝ) ≤ 1)
  rw [Real.norm_eq_abs] at hn
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    hi.norm (hc.intervalIntegrable_of_Icc (by norm_num)) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact singular_product_majorant hm g A hA hg t ht)
  have href : (∫ t in (0:ℝ)..1, peanoEndpointWeight ((m:ℝ)⁻¹) (1-t)) =
      ∫ t in (0:ℝ)..1, peanoEndpointWeight ((m:ℝ)⁻¹) t := by
    simp only [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  calc
    _ ≤ ∫ t in (0:ℝ)..1, 4*262144*A*
        (peanoEndpointWeight ((m:ℝ)⁻¹) t+peanoEndpointWeight ((m:ℝ)⁻¹) (1-t)) := hn.trans hbound
    _ = 4*262144*A*((∫ t in (0:ℝ)..1, peanoEndpointWeight ((m:ℝ)⁻¹) t)+
        ∫ t in (0:ℝ)..1, peanoEndpointWeight ((m:ℝ)⁻¹) (1-t)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        ((peanoEndpointWeight_continuousOn (inv_pos.mpr hm0)).intervalIntegrable_of_Icc (by norm_num))
        ((reflected_weight_continuousOn (inv_pos.mpr hm0)).intervalIntegrable_of_Icc (by norm_num))]
    _ ≤ 4*262144*A*(((m:ℝ)⁻¹)^5+((m:ℝ)⁻¹)^5) := by
      rw [href]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (peanoEndpointWeight_integral_le (inv_pos.mpr hm0))
        (peanoEndpointWeight_integral_le (inv_pos.mpr hm0))) (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

#print axioms endpoint_inv_sq_majorant
#print axioms peanoEndpointWeight_continuousOn
#print axioms peanoEndpointWeight_integral
#print axioms peanoEndpointWeight_integral_le
#print axioms unitPeanoKernel_singular_left
#print axioms unitPeanoKernel_singular_right
#print axioms unitPeanoKernel_singular_integrable
#print axioms unitPeanoKernel_singular_integral_bound

end SphericalRiesz.Boundary
