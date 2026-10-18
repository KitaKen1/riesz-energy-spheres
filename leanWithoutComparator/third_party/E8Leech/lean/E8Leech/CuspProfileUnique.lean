import E8Leech.CKMRVLaplaceFull

/-!
# The cusp profile of a function is unique

If `A t e^{ct} + B e^{ct} + C t + D = O(t e^{at})` as `t → ∞` with `a < 0 < c`, then
`A = B = C = D = 0`: the four functions `t e^{ct}`, `e^{ct}`, `t`, `1` have strictly decreasing
growth, and `t e^{at} → 0`. Hence two cusp profiles that approximate the same function to
`O(t e^{at})` have the same coefficients (`cuspProfile_unique`). This is how the cusp coefficients
of `𝒦(iy, ·)` and of `𝒦̂(i/y, ·)` are compared without their formulas.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics Set
open scoped Real

/-- A complex multiple of a positive real function that is `o` of that function is zero. -/
theorem eq_zero_of_const_mul_isLittleO {A : ℂ} {f : ℝ → ℝ} (hf : ∀ᶠ t in atTop, f t ≠ 0)
    (h : (fun t => A * (f t : ℂ)) =o[atTop] f) : A = 0 := by
  by_contra hA
  have h1 : (fun t => (f t : ℂ)) =o[atTop] f := (isLittleO_const_mul_left_iff hA).mp h
  have h2 : f =o[atTop] f := by
    have h3 : (fun t => ‖f t‖) =o[atTop] f :=
      h1.norm_left.congr_left fun t => Complex.norm_real (f t)
    exact h3.of_norm_left
  exact isLittleO_irrefl' (hf.frequently.mono fun t ht => by simpa using ht) h2

theorem isBigO_ofReal_self (f : ℝ → ℝ) : (fun t => (f t : ℂ)) =O[atTop] f :=
  IsBigO.of_bound 1 (Eventually.of_forall fun t => by rw [one_mul, Complex.norm_real])

private theorem exp_decay_isLittleO_one {a : ℝ} (ha : a < 0) :
    (fun t : ℝ => t * Real.exp (a * t)) =o[atTop] fun _ : ℝ => (1 : ℝ) := by
  rw [isLittleO_one_iff]
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop (neg_pos.mpr ha))
  have h' : Tendsto (fun t : ℝ => (-a)⁻¹ * ((-a * t) ^ 1 * Real.exp (-(-a * t)))) atTop (𝓝 0) := by
    simpa using h.const_mul (-a)⁻¹
  refine h'.congr fun t => ?_
  have ha0 : a ≠ 0 := ha.ne
  rw [show -(-a * t) = a * t by ring]
  field_simp

/-- **A cusp profile that is `O(t e^{at})` with `a < 0 < c` vanishes.** -/
theorem cuspProfile_eq_zero_of_isBigO {A B C D : ℂ} {a c : ℝ} (ha : a < 0) (hc : 0 < c)
    (h : (fun t => cuspProfile A B C D c t) =O[atTop] fun t => t * Real.exp (a * t)) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  -- the four comparison functions
  have h1t : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun t : ℝ => t := isLittleO_const_id_atTop 1
  have hte : (fun t : ℝ => t) =o[atTop] fun t : ℝ => Real.exp (c * t) := by
    simpa using isLittleO_pow_exp_pos_mul_atTop 1 hc
  have hete : (fun t : ℝ => Real.exp (c * t)) =o[atTop] fun t : ℝ => t * Real.exp (c * t) := by
    simpa using h1t.mul_isBigO (isBigO_refl (fun t : ℝ => Real.exp (c * t)) atTop)
  have hu1 : (fun t => cuspProfile A B C D c t) =o[atTop] fun _ : ℝ => (1 : ℝ) :=
    h.trans_isLittleO (exp_decay_isLittleO_one ha)
  -- norms of the four terms
  have hnD : (fun _ : ℝ => D) =O[atTop] fun _ : ℝ => (1 : ℝ) := isBigO_const_const D one_ne_zero _
  have hnC : (fun t : ℝ => C * (t : ℂ)) =O[atTop] fun t : ℝ => t :=
    (isBigO_ofReal_self fun t : ℝ => t).const_mul_left C
  have hnB : (fun t : ℝ => B * (Real.exp (c * t) : ℂ)) =O[atTop] fun t : ℝ => Real.exp (c * t) :=
    (isBigO_ofReal_self fun t : ℝ => Real.exp (c * t)).const_mul_left B
  -- step 1: `A = 0`
  have hA : A = 0 := by
    refine eq_zero_of_const_mul_isLittleO (f := fun t => t * Real.exp (c * t)) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact (mul_pos ht (Real.exp_pos _)).ne'
    · have e : (fun t : ℝ => A * ((t * Real.exp (c * t) : ℝ) : ℂ)) =
          fun t => cuspProfile A B C D c t - B * (Real.exp (c * t) : ℂ) - C * (t : ℂ) - D := by
        funext t
        simp only [cuspProfile]
        push_cast
        ring
      rw [e]
      exact (((hu1.trans (h1t.trans (hte.trans hete))).sub (hnB.trans_isLittleO hete)).sub
        (hnC.trans_isLittleO (hte.trans hete))).sub
        (hnD.trans_isLittleO (h1t.trans (hte.trans hete)))
  subst hA
  -- step 2: `B = 0`
  have hB : B = 0 := by
    refine eq_zero_of_const_mul_isLittleO (f := fun t => Real.exp (c * t)) ?_ ?_
    · exact Eventually.of_forall fun t => (Real.exp_pos _).ne'
    · have e : (fun t : ℝ => B * ((Real.exp (c * t) : ℝ) : ℂ)) =
          fun t => cuspProfile 0 B C D c t - C * (t : ℂ) - D := by
        funext t
        simp only [cuspProfile]
        ring
      rw [e]
      exact ((hu1.trans (h1t.trans hte)).sub (hnC.trans_isLittleO hte)).sub
        (hnD.trans_isLittleO (h1t.trans hte))
  subst hB
  -- step 3: `C = 0`
  have hC : C = 0 := by
    refine eq_zero_of_const_mul_isLittleO (f := fun t => t) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact ht.ne'
    · have e : (fun t : ℝ => C * ((t : ℝ) : ℂ)) = fun t => cuspProfile 0 0 C D c t - D := by
        funext t
        simp only [cuspProfile]
        ring
      rw [e]
      exact (hu1.trans h1t).sub (hnD.trans_isLittleO h1t)
  subst hC
  -- step 4: `D = 0`
  have hD : D = 0 := by
    refine eq_zero_of_const_mul_isLittleO (f := fun _ => (1 : ℝ)) ?_ ?_
    · exact Eventually.of_forall fun _ => one_ne_zero
    · have e : (fun _ : ℝ => D * (((1 : ℝ) : ℝ) : ℂ)) = fun t => cuspProfile 0 0 0 D c t := by
        funext t
        simp only [cuspProfile]
        push_cast
        ring
      rw [e]
      exact hu1
  exact ⟨rfl, rfl, rfl, hD⟩

/-- **Uniqueness of the cusp profile.** -/
theorem cuspProfile_unique {k : ℝ → ℂ} {A B C D A' B' C' D' : ℂ} {a c : ℝ} (ha : a < 0)
    (hc : 0 < c)
    (h : (fun t => k t - cuspProfile A B C D c t) =O[atTop] fun t => t * Real.exp (a * t))
    (h' : (fun t => k t - cuspProfile A' B' C' D' c t) =O[atTop] fun t => t * Real.exp (a * t)) :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have hd : (fun t => cuspProfile (A - A') (B - B') (C - C') (D - D') c t) =O[atTop]
      fun t => t * Real.exp (a * t) := by
    refine (h'.sub h).congr_left fun t => ?_
    simp only [cuspProfile]
    ring
  obtain ⟨h1, h2, h3, h4⟩ := cuspProfile_eq_zero_of_isBigO ha hc hd
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3, sub_eq_zero.mp h4⟩

end E8Leech
