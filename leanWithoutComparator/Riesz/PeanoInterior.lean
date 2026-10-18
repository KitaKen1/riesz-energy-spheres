import Riesz.PeanoKernel

/-!
# Interior certificate and global Peano-kernel bound

In a mesh cell write z = 4 + a + u, with 0 ≤ u ≤ 1. The zero terms
are discarded and the remaining midpoint powers telescope. The result
depends only on u, without Euler–Maclaurin or an infinite Fourier series.
The general C⁶ remainder is connected in PeanoRemainder and SmoothQuadrature.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

/-- Known-answer certificate: all mesh-size dependence cancels in an interior cell. -/
theorem unscaledPeanoKernel_interior_formula (a b : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    unscaledPeanoKernel (9+a+b) (4+(a : ℝ)+u) =
      (-fifthMomentDefect - midpointPrimitive 5 (1-u) + positiveFifth (1/2-u))/120 := by
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hl : (∑ i : Fin 4, positiveFifth (node i-(4+(a : ℝ)+u))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi := (node_between_zero_four i).2
    unfold positiveFifth
    rw [max_eq_right (by linarith [hu.1])]
    norm_num
  have hn : (9+a+b : ℕ)-8 = a+(b+1) := by omega
  have hprefix : (∑ j ∈ Finset.range a,
      positiveFifth ((j : ℝ)+4+1/2-(4+(a : ℝ)+u))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : (j : ℝ)+1 ≤ a := by
      have hjn := Finset.mem_range.mp hj
      exact_mod_cast (by omega : j+1 ≤ a)
    unfold positiveFifth
    rw [max_eq_right (by linarith [hu.1])]
    norm_num
  have htail (j : ℕ) : positiveFifth (((a+j+1 : ℕ) : ℝ)+4+1/2-(4+(a : ℝ)+u)) =
      ((j : ℝ)+(1-u)+1/2)^5 := by
    push_cast
    have heq : (a : ℝ)+j+1+4+1/2-(4+(a : ℝ)+u) = (j : ℝ)+(1-u)+1/2 := by ring
    rw [heq]
    unfold positiveFifth
    have hj0 : (0 : ℝ) ≤ j := by positivity
    rw [max_eq_left (by linarith [hu.2])]
  have hfirst : positiveFifth (((a+0 : ℕ) : ℝ)+4+1/2-(4+(a : ℝ)+u)) =
      positiveFifth (1/2-u) := by congr 1; push_cast; ring
  have hmid : (∑ j ∈ Finset.range ((9+a+b : ℕ)-8),
      positiveFifth ((j : ℝ)+4+1/2-(4+(a : ℝ)+u))) =
      positiveFifth (1/2-u) + midpointPrimitive 5 ((b : ℝ)+1-u) -
        midpointPrimitive 5 (1-u) := by
    rw [hn, Finset.sum_range_add, hprefix, zero_add, Finset.sum_range_succ']
    simp_rw [show ∀ j : ℕ, a+(j+1) = a+j+1 from fun j => by omega, htail]
    have hsum : (∑ j ∈ Finset.range b, ((j : ℝ)+(1-u)+1/2)^5) =
        midpointPrimitive 5 ((b : ℝ)+(1-u)) - midpointPrimitive 5 (1-u) :=
      shifted_midpoint_sum (5 : Fin 6) (1-u) b
    rw [hfirst, hsum, show (b : ℝ)+(1-u) = (b : ℝ)+1-u by ring]
    ring
  have hr (i : Fin 4) :
      positiveFifth (((9+a+b : ℕ) : ℝ)-node i-(4+(a : ℝ)+u)) =
        ((5+(b : ℝ)-u)-node i)^5 := by
    have hi := (node_between_zero_four i).2
    have heq : ((9+a+b : ℕ) : ℝ)-node i-(4+(a : ℝ)+u) =
        (5+(b : ℝ)-u)-node i := by push_cast; ring
    rw [heq]
    unfold positiveFifth
    rw [max_eq_left (by linarith [hu.2])]
  unfold unscaledPeanoKernel
  rw [hl, hmid]
  simp_rw [hr]
  rw [right_fifth_sum]
  push_cast
  norm_num [midpointPrimitive, fifthMomentDefect]
  ring

theorem unscaledPeanoKernel_interior_bound (a b : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |unscaledPeanoKernel (9+a+b) (4+(a : ℝ)+u)| ≤ 1 := by
  have hx0 : 0 ≤ 1-u := by linarith [hu.2]
  have hx1 : 1-u ≤ 1 := by linarith [hu.1]
  have h2 : (1-u)^2 ≤ (1 : ℝ)^2 := by gcongr
  have h4 : (1-u)^4 ≤ (1 : ℝ)^4 := by gcongr
  have h6 : (1-u)^6 ≤ (1 : ℝ)^6 := by gcongr
  have hp : |midpointPrimitive 5 (1-u)| ≤ 1 := by
    norm_num [midpointPrimitive]
    have h := abs_sub ((1-u)^6/6) (5*(1-u)^4/24)
    have h' := abs_add_le ((1-u)^6/6 - 5*(1-u)^4/24) (7*(1-u)^2/96)
    rw [abs_of_nonneg (by positivity : 0 ≤ (1-u)^6/6),
      abs_of_nonneg (by positivity : 0 ≤ 5*(1-u)^4/24)] at h
    rw [abs_of_nonneg (by positivity : 0 ≤ 7*(1-u)^2/96)] at h'
    nlinarith
  have hpos : 0 ≤ positiveFifth (1/2-u) := by unfold positiveFifth; positivity
  have hmax : max (1/2-u) 0 ≤ 1 := max_le (by linarith [hu.1]) (by norm_num)
  have hpos1 : positiveFifth (1/2-u) ≤ 1 := by
    unfold positiveFifth
    calc (max (1/2-u) 0)^5 ≤ (1 : ℝ)^5 := by gcongr
         _ = 1 := by norm_num
  rw [unscaledPeanoKernel_interior_formula a b hu, abs_div]
  norm_num
  have h := abs_sub (-fifthMomentDefect) (midpointPrimitive 5 (1-u))
  have h' := abs_add_le (-fifthMomentDefect-midpointPrimitive 5 (1-u))
    (positiveFifth (1/2-u))
  rw [abs_of_nonneg hpos] at h'
  unfold fifthMomentDefect at h h' ⊢
  norm_num at h
  linarith

#print axioms unscaledPeanoKernel_interior_formula
#print axioms unscaledPeanoKernel_interior_bound

/-- The two boundary certificates and one translated interior certificate cover every cell. -/
theorem unscaledPeanoKernel_bound {m : ℕ} (hm : 8 ≤ m) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) m) : |unscaledPeanoKernel m z| ≤ 64 := by
  by_cases hleft : z ≤ 4
  · exact unscaledPeanoKernel_left_bound hm ⟨hz.1, hleft⟩
  by_cases hright : (m : ℝ)-4 ≤ z
  · have h := unscaledPeanoKernel_right_bound hm
      (z := (m : ℝ)-z) ⟨by linarith [hz.2], by linarith⟩
    rw [show (m : ℝ)-((m : ℝ)-z) = z by ring] at h
    exact h
  let k : ℕ := Nat.floor z
  have hk0 : (k : ℝ) ≤ z := Nat.floor_le hz.1
  have hk1 : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hk4 : 4 ≤ k := (Nat.le_floor_iff hz.1).mpr (by norm_num; linarith)
  have hklt : k < m-4 := by
    apply (Nat.floor_lt hz.1).mpr
    rw [Nat.cast_sub (by omega : 4 ≤ m)]
    norm_num
    linarith
  have hu : z-(k : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmrepr : 9+(k-4)+(m-k-5) = m := by omega
  have hzrepr : 4+((k-4 : ℕ) : ℝ)+(z-(k : ℝ)) = z := by
    rw [Nat.cast_sub hk4]
    norm_num
  have h := unscaledPeanoKernel_interior_bound (k-4) (m-k-5) hu
  rw [hmrepr, hzrepr] at h
  exact h.trans (by norm_num)

/-- Uniform sixth-order scale on the entire unit interval, for every m ≥ 8. -/
theorem unitPeanoKernel_bound {m : ℕ} (hm : 8 ≤ m) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : |unitPeanoKernel m t| ≤ 64/(m : ℝ)^6 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m : ℝ)*t ∈ Set.Icc (0 : ℝ) m := by
    constructor
    · exact mul_nonneg hm0.le ht.1
    · nlinarith [ht.2]
  have hscale : unitPeanoKernel m t = unscaledPeanoKernel m ((m : ℝ)*t)/(m : ℝ)^6 := by
    have h := unitPeanoKernel_scale hm ((m : ℝ)*t)
    rw [mul_div_cancel_left₀ _ hm0.ne'] at h
    exact h
  have hden : 0 ≤ (m : ℝ)^6 := by positivity
  rw [hscale, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (unscaledPeanoKernel_bound hm hz) hden

theorem unitPeanoKernel_continuous (m : ℕ) : Continuous (unitPeanoKernel m) := by
  unfold unitPeanoKernel quadrature positiveFifth
  fun_prop

/-- This estimates an actual kernel integral. Identifying it with a C⁶ quadrature error is separate. -/
theorem unitPeanoKernel_weighted_integral_bound {m : ℕ} (hm : 8 ≤ m)
    (g : ℝ → ℝ) (M : ℝ) (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M) :
    |∫ t in (0 : ℝ)..1, unitPeanoKernel m t*g t| ≤ (64/(m : ℝ)^6)*M := by
  have h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |unitPeanoKernel m t*g t| ≤ (64/(m : ℝ)^6)*M := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul (unitPeanoKernel_bound hm ht) (hg t ht) (abs_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => unitPeanoKernel m t*g t)
    (C := (64/(m : ℝ)^6)*M) (by
      intro t ht
      rw [Real.norm_eq_abs]
      exact h t ⟨by simpa using ht.1.le, by simpa using ht.2⟩)
  simpa using hi

#print axioms unscaledPeanoKernel_bound
#print axioms unitPeanoKernel_bound
#print axioms unitPeanoKernel_continuous
#print axioms unitPeanoKernel_weighted_integral_bound

end SphericalRiesz.Boundary
