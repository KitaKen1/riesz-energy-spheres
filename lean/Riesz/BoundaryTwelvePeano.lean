import Riesz.BoundaryTwelveQuadrature
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Taylor

/-! A finite Peano certificate for the actual twelfth-order rule.
The coarse constant is intentional: only independence of the mesh size matters. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SphericalRiesz.Boundary

def positiveEleventh (x : ℝ) : ℝ := (max x 0)^11

def twelveUnscaledPeanoKernel (m : ℕ) (z : ℝ) : ℝ :=
  ((∑ i : Fin 37, positiveEleventh (twelveStripNode i-z)) +
    (∑ j ∈ Finset.range (m-74), positiveEleventh ((j:ℝ)+37+1/2-z)) +
    (∑ i : Fin 37, positiveEleventh ((m:ℝ)-twelveStripNode i-z)) - ((m:ℝ)-z)^12/12)/39916800

def twelveMomentDefect : ℝ := twelveStripPowerSum 11-twelveMidpointPrimitive 11 37

theorem twelve_right_eleventh_sum (u : ℝ) :
    (∑ i : Fin 37,(u-twelveStripNode i)^11) =
      u^12/12-twelveMidpointPrimitive 11 (u-37)-twelveMomentDefect := by
  have heq (x : ℝ) : (u-x)^11 =
    (1:ℝ)*u^11*x^0 + (-11:ℝ)*u^10*x^1 + (55:ℝ)*u^9*x^2 + (-165:ℝ)*u^8*x^3 + (330:ℝ)*u^7*x^4 + (-462:ℝ)*u^6*x^5 + (462:ℝ)*u^5*x^6 + (-330:ℝ)*u^4*x^7 + (165:ℝ)*u^3*x^8 + (-55:ℝ)*u^2*x^9 + (11:ℝ)*u^1*x^10 + (-1:ℝ)*u^0*x^11 := by ring
  simp only [heq,Finset.sum_add_distrib,← Finset.mul_sum,← twelveStripPowerSum_eq]
  norm_num [twelveMomentDefect,twelveMidpointPrimitive,
    twelveStripPowerSum_0, twelveStripPowerSum_1, twelveStripPowerSum_2, twelveStripPowerSum_3, twelveStripPowerSum_4, twelveStripPowerSum_5, twelveStripPowerSum_6, twelveStripPowerSum_7, twelveStripPowerSum_8, twelveStripPowerSum_9, twelveStripPowerSum_10]
  ring
theorem twelveUnscaledPeanoKernel_left_formula {m : ℕ} (hm : 74 ≤ m) {z : ℝ} (hz : z ≤ 37) :
    twelveUnscaledPeanoKernel m z =
      (-twelveMomentDefect - twelveMidpointPrimitive 11 (37-z) +
        ∑ i : Fin 37, positiveEleventh (twelveStripNode i-z))/39916800 := by
  have hm' : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hmiddle (j : ℕ) : positiveEleventh ((j : ℝ)+37+1/2-z) =
      ((j : ℝ)+37+1/2-z)^11 := by
    unfold positiveEleventh
    have hj : (0 : ℝ) ≤ j := by positivity
    rw [max_eq_left (by linarith)]
  have hright (i : Fin 37) : positiveEleventh ((m : ℝ)-twelveStripNode i-z) =
      ((m : ℝ)-twelveStripNode i-z)^11 := by
    unfold positiveEleventh
    have hi := (twelveStripNode_between i).2
    rw [max_eq_left (by linarith)]
  have hmid : (∑ j ∈ Finset.range (m-74), ((j : ℝ)+37+1/2-z)^11) =
      twelveMidpointPrimitive 11 (((m-74 : ℕ) : ℝ)+37-z) - twelveMidpointPrimitive 11 (37-z) := by
    calc
      _ = ∑ j ∈ Finset.range (m-74), ((j : ℝ)+(37-z)+1/2)^11 := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      _ = twelveMidpointPrimitive 11 (((m-74 : ℕ) : ℝ)+(37-z)) - twelveMidpointPrimitive 11 (37-z) :=
        twelve_shifted_midpoint_sum (11 : Fin 12) (37-z) (m-74)
      _ = _ := by congr 2; ring
  have hn : ((m-74 : ℕ) : ℝ) = (m : ℝ)-74 := by
    rw [Nat.cast_sub hm]; norm_num
  unfold twelveUnscaledPeanoKernel
  simp_rw [hmiddle, hright]
  rw [hmid]
  have hr : (∑ i : Fin 37, ((m : ℝ)-twelveStripNode i-z)^11) =
      ∑ i : Fin 37, (((m : ℝ)-z)-twelveStripNode i)^11 := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hr, twelve_right_eleventh_sum, hn]
  norm_num [twelveMidpointPrimitive, twelveMomentDefect]
  ring

theorem twelveUnscaledPeanoKernel_right_formula {m : ℕ} (hm : 74 ≤ m)
    {z : ℝ} (hz : z ≤ 37) : twelveUnscaledPeanoKernel m ((m : ℝ)-z) =
      ((∑ i : Fin 37, positiveEleventh (z-twelveStripNode i))-z^12/12)/39916800 := by
  have hm' : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : (∑ i : Fin 37, positiveEleventh (twelveStripNode i-((m : ℝ)-z))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi := (twelveStripNode_between i).2
    simp [positiveEleventh, max_eq_right (by linarith : twelveStripNode i-((m : ℝ)-z) ≤ 0)]
  have hmid : (∑ j ∈ Finset.range (m-74),
      positiveEleventh ((j : ℝ)+37+1/2-((m : ℝ)-z))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : (j : ℝ)+1 ≤ ((m-74 : ℕ) : ℝ) := by
      have hjn : j < m-74 := Finset.mem_range.mp hj
      exact_mod_cast (by omega : j+1 ≤ m-74)
    rw [Nat.cast_sub hm] at hj'
    norm_num at hj'
    unfold positiveEleventh
    rw [max_eq_right (by linarith : (j : ℝ)+37+1/2-((m : ℝ)-z) ≤ 0)]
    norm_num
  have hr (i : Fin 37) : positiveEleventh ((m : ℝ)-twelveStripNode i-((m : ℝ)-z)) =
      positiveEleventh (z-twelveStripNode i) := by congr 1; ring
  unfold twelveUnscaledPeanoKernel
  rw [hl, hmid]
  simp_rw [hr]
  ring

theorem twelveUnscaledPeanoKernel_interior_formula (a b : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    twelveUnscaledPeanoKernel (75+a+b) (37+(a : ℝ)+u) =
      (-twelveMomentDefect - twelveMidpointPrimitive 11 (1-u) + positiveEleventh (1/2-u))/39916800 := by
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hl : (∑ i : Fin 37, positiveEleventh (twelveStripNode i-(37+(a : ℝ)+u))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi := (twelveStripNode_between i).2
    unfold positiveEleventh
    rw [max_eq_right (by linarith [hu.1])]
    norm_num
  have hn : (75+a+b : ℕ)-74 = a+(b+1) := by omega
  have hprefix : (∑ j ∈ Finset.range a,
      positiveEleventh ((j : ℝ)+37+1/2-(37+(a : ℝ)+u))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : (j : ℝ)+1 ≤ a := by
      have hjn := Finset.mem_range.mp hj
      exact_mod_cast (by omega : j+1 ≤ a)
    unfold positiveEleventh
    rw [max_eq_right (by linarith [hu.1])]
    norm_num
  have htail (j : ℕ) : positiveEleventh (((a+j+1 : ℕ) : ℝ)+37+1/2-(37+(a : ℝ)+u)) =
      ((j : ℝ)+(1-u)+1/2)^11 := by
    push_cast
    have heq : (a : ℝ)+j+1+37+1/2-(37+(a : ℝ)+u) = (j : ℝ)+(1-u)+1/2 := by ring
    rw [heq]
    unfold positiveEleventh
    have hj0 : (0 : ℝ) ≤ j := by positivity
    rw [max_eq_left (by linarith [hu.2])]
  have hfirst : positiveEleventh (((a+0 : ℕ) : ℝ)+37+1/2-(37+(a : ℝ)+u)) =
      positiveEleventh (1/2-u) := by congr 1; push_cast; ring
  have hmid : (∑ j ∈ Finset.range ((75+a+b : ℕ)-74),
      positiveEleventh ((j : ℝ)+37+1/2-(37+(a : ℝ)+u))) =
      positiveEleventh (1/2-u) + twelveMidpointPrimitive 11 ((b : ℝ)+1-u) -
        twelveMidpointPrimitive 11 (1-u) := by
    rw [hn, Finset.sum_range_add, hprefix, zero_add, Finset.sum_range_succ']
    simp_rw [show ∀ j : ℕ, a+(j+1) = a+j+1 from fun j => by omega, htail]
    have hsum : (∑ j ∈ Finset.range b, ((j : ℝ)+(1-u)+1/2)^11) =
        twelveMidpointPrimitive 11 ((b : ℝ)+(1-u)) - twelveMidpointPrimitive 11 (1-u) :=
      twelve_shifted_midpoint_sum (11 : Fin 12) (1-u) b
    rw [hfirst, hsum, show (b : ℝ)+(1-u) = (b : ℝ)+1-u by ring]
    ring
  have hr (i : Fin 37) :
      positiveEleventh (((75+a+b : ℕ) : ℝ)-twelveStripNode i-(37+(a : ℝ)+u)) =
        ((38+(b : ℝ)-u)-twelveStripNode i)^11 := by
    have hi := (twelveStripNode_between i).2
    have heq : ((75+a+b : ℕ) : ℝ)-twelveStripNode i-(37+(a : ℝ)+u) =
        (38+(b : ℝ)-u)-twelveStripNode i := by push_cast; ring
    rw [heq]
    unfold positiveEleventh
    rw [max_eq_left (by linarith [hu.2])]
  unfold twelveUnscaledPeanoKernel
  rw [hl, hmid]
  simp_rw [hr]
  rw [twelve_right_eleventh_sum]
  push_cast
  norm_num [twelveMidpointPrimitive, twelveMomentDefect]
  ring


private theorem twelve_power_bound {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 37) {k : ℕ} (hk : k ≤ 12) :
    |x^k| ≤ (37:ℝ)^12 := by
  rw [abs_of_nonneg (pow_nonneg hx.1 _)]
  calc
    x^k ≤ (37:ℝ)^k := pow_le_pow_left₀ hx.1 hx.2 k
    _ ≤ (37:ℝ)^12 := pow_le_pow_right₀ (by norm_num) hk

private def twelvePrimitiveCoefficients : Fin 6 → ℝ :=
  ![-2555/6144,1397/1024,-341/192,77/64,-11/24,1/12]

theorem twelveMidpointPrimitive_eleven_bound {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 37) :
    |twelveMidpointPrimitive 11 x| ≤ (10:ℝ)^22 := by
  have heq : twelveMidpointPrimitive 11 x =
      ∑ i : Fin 6,twelvePrimitiveCoefficients i*x^(2*(i.val+1)) := by
    norm_num [twelveMidpointPrimitive,twelvePrimitiveCoefficients,Fin.sum_univ_succ]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 6, |twelvePrimitiveCoefficients i*x^(2*(i.val+1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 6, (2:ℝ)*37^12 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul
      · fin_cases i <;> norm_num [twelvePrimitiveCoefficients]
      · exact twelve_power_bound hx (by have := i.isLt; omega)
      · exact abs_nonneg _
      · norm_num
    _ ≤ _ := by norm_num

theorem twelveMomentDefect_bound : |twelveMomentDefect| ≤ (10:ℝ)^23 := by
  have hs : |twelveStripPowerSum 11| ≤ (37:ℝ)^12 := by
    unfold twelveStripPowerSum
    calc
      _ ≤ ∑ i : Fin 37,|twelveStripNode i^11| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 37,(37:ℝ)^11 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := twelveStripNode_between i
        rw [abs_of_nonneg (pow_nonneg hi.1.le _)]
        exact pow_le_pow_left₀ hi.1.le hi.2.le 11
      _ = _ := by norm_num
  have hp := twelveMidpointPrimitive_eleven_bound (x:=37) (by constructor <;> norm_num)
  unfold twelveMomentDefect
  exact (abs_sub _ _).trans (by norm_num at hs hp ⊢; linarith)

theorem twelveUnscaledPeanoKernel_left_bound {m : ℕ} (hm : 74 ≤ m)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 37) : |twelveUnscaledPeanoKernel m z| ≤ (10:ℝ)^24 := by
  have hs : |∑ i : Fin 37,positiveEleventh (twelveStripNode i-z)| ≤ (37:ℝ)^12 := by
    calc
      _ ≤ ∑ i : Fin 37,|positiveEleventh (twelveStripNode i-z)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 37,(37:ℝ)^11 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := twelveStripNode_between i
        rw [abs_of_nonneg (by unfold positiveEleventh; positivity)]
        unfold positiveEleventh
        gcongr
        exact max_le (by linarith [hz.1]) (by norm_num)
      _ = _ := by norm_num
  have hp := twelveMidpointPrimitive_eleven_bound (x:=37-z) ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hd := twelveMomentDefect_bound
  rw [twelveUnscaledPeanoKernel_left_formula hm hz.2,abs_div]
  norm_num
  have h1 := abs_sub (-twelveMomentDefect) (twelveMidpointPrimitive 11 (37-z))
  have h2 := abs_add_le (-twelveMomentDefect-twelveMidpointPrimitive 11 (37-z))
    (∑ i : Fin 37,positiveEleventh (twelveStripNode i-z))
  rw [abs_neg] at h1
  norm_num at hs hp hd ⊢
  linarith

theorem twelveUnscaledPeanoKernel_right_bound {m : ℕ} (hm : 74 ≤ m)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 37) :
    |twelveUnscaledPeanoKernel m ((m:ℝ)-z)| ≤ (10:ℝ)^24 := by
  have hs : |∑ i : Fin 37,positiveEleventh (z-twelveStripNode i)| ≤ (37:ℝ)^12 := by
    calc
      _ ≤ ∑ i : Fin 37,|positiveEleventh (z-twelveStripNode i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 37,(37:ℝ)^11 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := twelveStripNode_between i
        rw [abs_of_nonneg (by unfold positiveEleventh; positivity)]
        unfold positiveEleventh
        gcongr
        exact max_le (by linarith [hz.2]) (by norm_num)
      _ = _ := by norm_num
  have hp := twelve_power_bound hz (k:=12) (by omega)
  rw [twelveUnscaledPeanoKernel_right_formula hm hz.2,abs_div]
  norm_num
  have h := abs_sub (∑ i : Fin 37,positiveEleventh (z-twelveStripNode i)) (z^12/12)
  rw [abs_div] at h
  norm_num at hs hp h ⊢
  linarith

theorem twelveUnscaledPeanoKernel_interior_bound (a b : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |twelveUnscaledPeanoKernel (75+a+b) (37+(a:ℝ)+u)| ≤ (10:ℝ)^24 := by
  have hp := twelveMidpointPrimitive_eleven_bound (x:=1-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hd := twelveMomentDefect_bound
  have hs : |positiveEleventh (1/2-u)| ≤ (37:ℝ)^11 := by
    rw [abs_of_nonneg (by unfold positiveEleventh; positivity)]
    unfold positiveEleventh
    gcongr
    exact max_le (by linarith [hu.1]) (by norm_num)
  rw [twelveUnscaledPeanoKernel_interior_formula a b hu,abs_div]
  norm_num
  have h1 := abs_sub (-twelveMomentDefect) (twelveMidpointPrimitive 11 (1-u))
  have h2 := abs_add_le (-twelveMomentDefect-twelveMidpointPrimitive 11 (1-u)) (positiveEleventh (1/2-u))
  rw [abs_neg] at h1
  norm_num at hs hp hd ⊢
  linarith
theorem twelveUnscaledPeanoKernel_bound {m : ℕ} (hm : 74 ≤ m) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) m) : |twelveUnscaledPeanoKernel m z| ≤ (10^24) := by
  by_cases hleft : z ≤ 37
  · exact twelveUnscaledPeanoKernel_left_bound hm ⟨hz.1, hleft⟩
  by_cases hright : (m : ℝ)-37 ≤ z
  · have h := twelveUnscaledPeanoKernel_right_bound hm
      (z := (m : ℝ)-z) ⟨by linarith [hz.2], by linarith⟩
    rw [show (m : ℝ)-((m : ℝ)-z) = z by ring] at h
    exact h
  let k : ℕ := Nat.floor z
  have hk0 : (k : ℝ) ≤ z := Nat.floor_le hz.1
  have hk1 : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hk4 : 37 ≤ k := (Nat.le_floor_iff hz.1).mpr (by norm_num; linarith)
  have hklt : k < m-37 := by
    apply (Nat.floor_lt hz.1).mpr
    rw [Nat.cast_sub (by omega : 37 ≤ m)]
    norm_num
    linarith
  have hu : z-(k : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmrepr : 75+(k-37)+(m-k-38) = m := by omega
  have hzrepr : 37+((k-37 : ℕ) : ℝ)+(z-(k : ℝ)) = z := by
    rw [Nat.cast_sub hk4]
    norm_num
  have h := twelveUnscaledPeanoKernel_interior_bound (k-37) (m-k-38) hu
  rw [hmrepr, hzrepr] at h
  exact h

def twelveUnitPeanoKernel (m : ℕ) (t : ℝ) : ℝ :=
  (twelveQuadrature m (fun x => positiveEleventh (x-t)) - (1-t)^12/12)/39916800

theorem twelveUnitPeanoKernel_scale {m : ℕ} (hm : 74 ≤ m) (z : ℝ) :
    twelveUnitPeanoKernel m (z/m) = twelveUnscaledPeanoKernel m z / (m : ℝ)^12 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hf (x : ℝ) : positiveEleventh (x/m-z/m) = positiveEleventh (x-z)/(m : ℝ)^11 := by
    unfold positiveEleventh
    have hmax : max ((x-z)/m) 0 = max (x-z) 0 / m := by
      simpa using max_div_div_right hm0.le (x-z) 0
    rw [← sub_div, hmax, div_pow]
  have h1 : (1 : ℝ)-z/m = ((m : ℝ)-z)/m := by field_simp
  unfold twelveUnitPeanoKernel twelveQuadrature twelveUnscaledPeanoKernel
  simp_rw [hf, ← Finset.sum_div]
  rw [h1, div_pow]
  simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  field_simp [hm0.ne']
  ring

theorem twelveUnitPeanoKernel_bound {m : ℕ} (hm : 74 ≤ m) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : |twelveUnitPeanoKernel m t| ≤ (10^24)/(m : ℝ)^12 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hz : (m : ℝ)*t ∈ Set.Icc (0 : ℝ) m := by
    constructor
    · exact mul_nonneg hm0.le ht.1
    · nlinarith [ht.2]
  have hscale : twelveUnitPeanoKernel m t = twelveUnscaledPeanoKernel m ((m : ℝ)*t)/(m : ℝ)^12 := by
    have h := twelveUnitPeanoKernel_scale hm ((m : ℝ)*t)
    rw [mul_div_cancel_left₀ _ hm0.ne'] at h
    exact h
  have hden : 0 ≤ (m : ℝ)^12 := by positivity
  rw [hscale, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (twelveUnscaledPeanoKernel_bound hm hz) hden

theorem twelveUnitPeanoKernel_continuous (m : ℕ) : Continuous (twelveUnitPeanoKernel m) := by
  unfold twelveUnitPeanoKernel twelveQuadrature positiveEleventh
  fun_prop

/-- This estimates an actual kernel integral. Identifying it with a C⁶ twelveQuadrature error is separate. -/
theorem twelveUnitPeanoKernel_weighted_integral_bound {m : ℕ} (hm : 74 ≤ m)
    (g : ℝ → ℝ) (M : ℝ) (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M) :
    |∫ t in (0 : ℝ)..1, twelveUnitPeanoKernel m t*g t| ≤ ((10^24)/(m : ℝ)^12)*M := by
  have h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |twelveUnitPeanoKernel m t*g t| ≤ ((10^24)/(m : ℝ)^12)*M := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul (twelveUnitPeanoKernel_bound hm ht) (hg t ht) (abs_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => twelveUnitPeanoKernel m t*g t)
    (C := ((10^24)/(m : ℝ)^12)*M) (by
      intro t ht
      rw [Real.norm_eq_abs]
      exact h t ⟨by simpa using ht.1.le, by simpa using ht.2⟩)
  simpa using hi


theorem integral_positiveEleventh {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, positiveEleventh (x-t)) = (1-t)^12/12 := by
  have hf : Continuous (fun x : ℝ => positiveEleventh (x-t)) := by unfold positiveEleventh; fun_prop
  have hleft : (∫ x in (0 : ℝ)..t, positiveEleventh (x-t)) = 0 := by
    calc
      _ = ∫ _x in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ht.1] at hx
        simp [positiveEleventh, max_eq_right (sub_nonpos.mpr hx.2)]
      _ = 0 := by simp
  have hright : (∫ x in t..(1 : ℝ), positiveEleventh (x-t)) = (1-t)^12/12 := by
    calc
      _ = ∫ x in t..(1 : ℝ), (x-t)^11 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ht.2] at hx
        simp only [positiveEleventh, max_eq_left (sub_nonneg.mpr hx.1)]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^11) t, integral_pow]
        norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t 1), hleft, hright, zero_add]

theorem twelveUnitPeanoKernel_eq_error {m : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    twelveUnitPeanoKernel m t =
      (twelveQuadrature m (fun x => positiveEleventh (x-t)) -
        (∫ x in (0 : ℝ)..1, positiveEleventh (x-t)))/39916800 := by
  rw [integral_positiveEleventh ht]
  rfl


end SphericalRiesz.Boundary
