import Riesz.QuadratureError

/-!
# A direct finite spline certificate for the boundary Peano kernel

The sixth-order kernel is examined first on the left four mesh cells.
This avoids a general Euler–Maclaurin development. The right edge has an
even shorter direct formula. Interior cells and Taylor/Fubini are connected
in PeanoInterior, PeanoRemainder, and SmoothQuadrature.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

def positiveFifth (x : ℝ) : ℝ := (max x 0)^5

/-- Unscaled coordinates z ∈ [0,m]; multiply by m⁻⁶ for the unit interval kernel. -/
def unscaledPeanoKernel (m : ℕ) (z : ℝ) : ℝ :=
  ((∑ i : Fin 4, positiveFifth (node i-z)) +
    (∑ j ∈ Finset.range (m-8), positiveFifth ((j : ℝ)+4+1/2-z)) +
    (∑ i : Fin 4, positiveFifth ((m : ℝ)-node i-z)) - ((m : ℝ)-z)^6/6)/120

def fifthMomentDefect : ℝ := 194112481/191102976

theorem right_fifth_sum (u : ℝ) :
    (∑ i : Fin 4, (u-node i)^5) =
      4*u^5 - (955/24)*u^4 + 210*u^3 - (59527/96)*u^2 +
        (3885/4)*u - 120684538849/191102976 := by
  obtain ⟨h1, h2, h3, h4⟩ := node_power_moments
  have h (x : ℝ) : (u-x)^5 =
      u^5 - 5*u^4*x + 10*u^3*x^2 - 10*u^2*x^3 + 5*u*x^4-x^5 := by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3, h4, node_power_fifth]
  norm_num
  ring

/-- Exact boundary formula: m drops out entirely. -/
theorem unscaledPeanoKernel_left_formula {m : ℕ} (hm : 8 ≤ m) {z : ℝ} (hz : z ≤ 4) :
    unscaledPeanoKernel m z =
      (-fifthMomentDefect - midpointPrimitive 5 (4-z) +
        ∑ i : Fin 4, positiveFifth (node i-z))/120 := by
  have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hmiddle (j : ℕ) : positiveFifth ((j : ℝ)+4+1/2-z) =
      ((j : ℝ)+4+1/2-z)^5 := by
    unfold positiveFifth
    have hj : (0 : ℝ) ≤ j := by positivity
    rw [max_eq_left (by linarith)]
  have hright (i : Fin 4) : positiveFifth ((m : ℝ)-node i-z) =
      ((m : ℝ)-node i-z)^5 := by
    unfold positiveFifth
    have hi := (node_between_zero_four i).2
    rw [max_eq_left (by linarith)]
  have hmid : (∑ j ∈ Finset.range (m-8), ((j : ℝ)+4+1/2-z)^5) =
      midpointPrimitive 5 (((m-8 : ℕ) : ℝ)+4-z) - midpointPrimitive 5 (4-z) := by
    calc
      _ = ∑ j ∈ Finset.range (m-8), ((j : ℝ)+(4-z)+1/2)^5 := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      _ = midpointPrimitive 5 (((m-8 : ℕ) : ℝ)+(4-z)) - midpointPrimitive 5 (4-z) :=
        shifted_midpoint_sum (5 : Fin 6) (4-z) (m-8)
      _ = _ := by congr 2; ring
  have hn : ((m-8 : ℕ) : ℝ) = (m : ℝ)-8 := by
    rw [Nat.cast_sub hm]; norm_num
  unfold unscaledPeanoKernel
  simp_rw [hmiddle, hright]
  rw [hmid]
  have hr : (∑ i : Fin 4, ((m : ℝ)-node i-z)^5) =
      ∑ i : Fin 4, (((m : ℝ)-z)-node i)^5 := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hr, right_fifth_sum, hn]
  norm_num [midpointPrimitive, fifthMomentDefect]
  ring

/-- A coarse constant is enough: precision of the kernel maximum is unnecessary. -/
theorem unscaledPeanoKernel_left_bound {m : ℕ} (hm : 8 ≤ m)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 4) : |unscaledPeanoKernel m z| ≤ 64 := by
  have hnode (i : Fin 4) : 0 ≤ positiveFifth (node i-z) ∧ positiveFifth (node i-z) ≤ 1024 := by
    have hi := node_between_zero_four i
    have hmax : max (node i-z) 0 ≤ 4 := max_le (by linarith [hz.1]) (by norm_num)
    constructor
    · unfold positiveFifth; positivity
    · unfold positiveFifth
      calc (max (node i-z) 0)^5 ≤ (4 : ℝ)^5 := by gcongr
           _ = 1024 := by norm_num
  have hs0 : 0 ≤ ∑ i : Fin 4, positiveFifth (node i-z) :=
    Finset.sum_nonneg (fun i _ => (hnode i).1)
  have hs : (∑ i : Fin 4, positiveFifth (node i-z)) ≤ 4096 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hnode i).2)
    norm_num at h
    exact h
  have hx0 : 0 ≤ 4-z := by linarith [hz.2]
  have hx4 : 4-z ≤ 4 := by linarith [hz.1]
  have h2 : (4-z)^2 ≤ (4 : ℝ)^2 := by gcongr
  have h4 : (4-z)^4 ≤ (4 : ℝ)^4 := by gcongr
  have h6 : (4-z)^6 ≤ (4 : ℝ)^6 := by gcongr
  have hp : |midpointPrimitive 5 (4-z)| ≤ 800 := by
    norm_num [midpointPrimitive]
    have h := abs_sub ((4-z)^6/6) (5*(4-z)^4/24)
    have h' := abs_add_le ((4-z)^6/6 - 5*(4-z)^4/24) (7*(4-z)^2/96)
    have ha : 0 ≤ (4-z)^6/6 := by positivity
    have hb : 0 ≤ 5*(4-z)^4/24 := by positivity
    rw [abs_of_nonneg ha, abs_of_nonneg hb] at h
    rw [abs_of_nonneg (by positivity : 0 ≤ 7*(4-z)^2/96)] at h'
    nlinarith
  rw [unscaledPeanoKernel_left_formula hm hz.2]
  rw [abs_div]
  norm_num
  have h := abs_sub (-fifthMomentDefect) (midpointPrimitive 5 (4-z))
  have h' := abs_add_le (-fifthMomentDefect - midpointPrimitive 5 (4-z))
    (∑ i : Fin 4, positiveFifth (node i-z))
  rw [abs_of_nonneg hs0] at h'
  unfold fifthMomentDefect at h h' ⊢
  norm_num at h
  linarith

/-- On the right edge all left and middle terms vanish, so reflection is unnecessary. -/
theorem unscaledPeanoKernel_right_formula {m : ℕ} (hm : 8 ≤ m)
    {z : ℝ} (hz : z ≤ 4) : unscaledPeanoKernel m ((m : ℝ)-z) =
      ((∑ i : Fin 4, positiveFifth (z-node i))-z^6/6)/120 := by
  have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : (∑ i : Fin 4, positiveFifth (node i-((m : ℝ)-z))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi := (node_between_zero_four i).2
    simp [positiveFifth, max_eq_right (by linarith : node i-((m : ℝ)-z) ≤ 0)]
  have hmid : (∑ j ∈ Finset.range (m-8),
      positiveFifth ((j : ℝ)+4+1/2-((m : ℝ)-z))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : (j : ℝ)+1 ≤ ((m-8 : ℕ) : ℝ) := by
      have hjn : j < m-8 := Finset.mem_range.mp hj
      exact_mod_cast (by omega : j+1 ≤ m-8)
    rw [Nat.cast_sub hm] at hj'
    norm_num at hj'
    unfold positiveFifth
    rw [max_eq_right (by linarith : (j : ℝ)+4+1/2-((m : ℝ)-z) ≤ 0)]
    norm_num
  have hr (i : Fin 4) : positiveFifth ((m : ℝ)-node i-((m : ℝ)-z)) =
      positiveFifth (z-node i) := by congr 1; ring
  unfold unscaledPeanoKernel
  rw [hl, hmid]
  simp_rw [hr]
  ring

theorem unscaledPeanoKernel_right_bound {m : ℕ} (hm : 8 ≤ m)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 4) :
    |unscaledPeanoKernel m ((m : ℝ)-z)| ≤ 64 := by
  have hnode (i : Fin 4) : 0 ≤ positiveFifth (z-node i) ∧
      positiveFifth (z-node i) ≤ 1024 := by
    have hi := (node_between_zero_four i).1
    have hmax : max (z-node i) 0 ≤ 4 := max_le (by linarith [hz.2]) (by norm_num)
    constructor
    · unfold positiveFifth; positivity
    · unfold positiveFifth
      calc (max (z-node i) 0)^5 ≤ (4 : ℝ)^5 := by gcongr
           _ = 1024 := by norm_num
  have hs0 : 0 ≤ ∑ i : Fin 4, positiveFifth (z-node i) :=
    Finset.sum_nonneg (fun i _ => (hnode i).1)
  have hs : (∑ i : Fin 4, positiveFifth (z-node i)) ≤ 4096 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hnode i).2)
    norm_num at h
    exact h
  have h6 : z^6 ≤ (4 : ℝ)^6 := by
    gcongr
    · exact hz.1
    · exact hz.2
  rw [unscaledPeanoKernel_right_formula hm hz.2, abs_div]
  norm_num
  have h := abs_sub (∑ i : Fin 4, positiveFifth (z-node i)) (z^6/6)
  rw [abs_of_nonneg hs0, abs_of_nonneg (by positivity : 0 ≤ z^6/6)] at h
  nlinarith

def unitPeanoKernel (m : ℕ) (t : ℝ) : ℝ :=
  (quadrature m (fun x => positiveFifth (x-t)) - (1-t)^6/6)/120

theorem unitPeanoKernel_scale {m : ℕ} (hm : 8 ≤ m) (z : ℝ) :
    unitPeanoKernel m (z/m) = unscaledPeanoKernel m z / (m : ℝ)^6 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hf (x : ℝ) : positiveFifth (x/m-z/m) = positiveFifth (x-z)/(m : ℝ)^5 := by
    unfold positiveFifth
    have hmax : max ((x-z)/m) 0 = max (x-z) 0 / m := by
      simpa using max_div_div_right hm0.le (x-z) 0
    rw [← sub_div, hmax, div_pow]
  have h1 : (1 : ℝ)-z/m = ((m : ℝ)-z)/m := by field_simp
  unfold unitPeanoKernel quadrature unscaledPeanoKernel
  simp_rw [hf, ← Finset.sum_div]
  rw [h1, div_pow]
  simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  field_simp [hm0.ne']
  ring

/-- On the left four mesh cells the genuine kernel has the required m⁻⁶ scale. -/
theorem unitPeanoKernel_left_bound {m : ℕ} (hm : 8 ≤ m) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (4/(m : ℝ))) :
    |unitPeanoKernel m t| ≤ 64/(m : ℝ)^6 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m : ℝ)*t ∈ Set.Icc (0 : ℝ) 4 := by
    constructor
    · exact mul_nonneg hm0.le ht.1
    · have h := (le_div_iff₀ hm0).mp ht.2
      linarith
  have hscale : unitPeanoKernel m t = unscaledPeanoKernel m ((m : ℝ)*t)/(m : ℝ)^6 := by
    have h := unitPeanoKernel_scale hm ((m : ℝ)*t)
    rw [mul_div_cancel_left₀ _ hm0.ne'] at h
    exact h
  have hden : 0 ≤ (m : ℝ)^6 := by positivity
  rw [hscale, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (unscaledPeanoKernel_left_bound hm hz) hden

theorem unitPeanoKernel_right_bound {m : ℕ} (hm : 8 ≤ m) {t : ℝ}
    (ht : t ∈ Set.Icc (1-4/(m : ℝ)) 1) :
    |unitPeanoKernel m t| ≤ 64/(m : ℝ)^6 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m : ℝ)*(1-t) ∈ Set.Icc (0 : ℝ) 4 := by
    constructor
    · exact mul_nonneg hm0.le (sub_nonneg.mpr ht.2)
    · have h : (1-t)*(m : ℝ) ≤ 4 := (le_div_iff₀ hm0).mp (by linarith [ht.1])
      nlinarith
  have hscale : unitPeanoKernel m t =
      unscaledPeanoKernel m ((m : ℝ)-(m : ℝ)*(1-t))/(m : ℝ)^6 := by
    have harg : (m : ℝ)-(m : ℝ)*(1-t) = (m : ℝ)*t := by ring
    rw [harg]
    have h := unitPeanoKernel_scale hm ((m : ℝ)*t)
    rw [mul_div_cancel_left₀ _ hm0.ne'] at h
    exact h
  have hden : 0 ≤ (m : ℝ)^6 := by positivity
  rw [hscale, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (unscaledPeanoKernel_right_bound hm hz) hden

theorem integral_positiveFifth {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, positiveFifth (x-t)) = (1-t)^6/6 := by
  have hf : Continuous (fun x : ℝ => positiveFifth (x-t)) := by unfold positiveFifth; fun_prop
  have hleft : (∫ x in (0 : ℝ)..t, positiveFifth (x-t)) = 0 := by
    calc
      _ = ∫ _x in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ht.1] at hx
        simp [positiveFifth, max_eq_right (sub_nonpos.mpr hx.2)]
      _ = 0 := by simp
  have hright : (∫ x in t..(1 : ℝ), positiveFifth (x-t)) = (1-t)^6/6 := by
    calc
      _ = ∫ x in t..(1 : ℝ), (x-t)^5 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ht.2] at hx
        simp only [positiveFifth, max_eq_left (sub_nonneg.mpr hx.1)]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^5) t, integral_pow]
        norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t 1), hleft, hright, zero_add]

theorem unitPeanoKernel_eq_error {m : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    unitPeanoKernel m t =
      (quadrature m (fun x => positiveFifth (x-t)) -
        (∫ x in (0 : ℝ)..1, positiveFifth (x-t)))/120 := by
  rw [integral_positiveFifth ht]
  rfl

#print axioms unscaledPeanoKernel_left_formula
#print axioms unscaledPeanoKernel_left_bound
#print axioms unitPeanoKernel_left_bound
#print axioms unscaledPeanoKernel_right_formula
#print axioms unscaledPeanoKernel_right_bound
#print axioms unitPeanoKernel_right_bound
#print axioms unitPeanoKernel_eq_error

end SphericalRiesz.Boundary
