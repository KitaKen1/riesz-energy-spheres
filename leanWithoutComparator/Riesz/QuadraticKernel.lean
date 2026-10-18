import Riesz.LocalCellQuadrature

/-!
# Coordinate derivatives of the inverse-fourth kernel

Along one coordinate, the squared distance is (t-c)^2+b. Six explicit
rational functions form a derivative certificate. Each consecutive
identity is checked with the first-derivative rules and polynomial
normalization. This avoids a general high-order chain rule.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz

def quadraticKernel (b c t : ℝ) : ℝ := 1/((t-c)^2+b)^2

def quadraticKernelDerivative (n : ℕ) (b c t : ℝ) : ℝ :=
  match n with
  | 0 => 1/((t-c)^2+b)^2
  | 1 => (-4*(t-c))/((t-c)^2+b)^3
  | 2 => (20*(t-c)^2-4*b)/((t-c)^2+b)^4
  | 3 => (-120*(t-c)^3+72*b*(t-c))/((t-c)^2+b)^5
  | 4 => (840*(t-c)^4-1008*b*(t-c)^2+72*b^2)/((t-c)^2+b)^6
  | 5 => (-6720*(t-c)^5+13440*b*(t-c)^3-2880*b^2*(t-c))/((t-c)^2+b)^7
  | 6 => (60480*(t-c)^6-181440*b*(t-c)^4+77760*b^2*(t-c)^2-2880*b^3)/((t-c)^2+b)^8
  | _ => 0

theorem quadraticKernelDerivative_step (n : Fin 6) (b c x : ℝ)
    (hq : (x-c)^2+b ≠ 0) :
    HasDerivAt (quadraticKernelDerivative n.val b c)
      (quadraticKernelDerivative (n.val+1) b c x) x := by
  have ht : HasDerivAt (fun t : ℝ => t-c) 1 x := (hasDerivAt_id x).sub_const c
  have hq' : HasDerivAt (fun t : ℝ => (t-c)^2+b) (2*(x-c)) x := by
    convert (ht.pow 2).add_const b using 1
    ring
  fin_cases n
  · dsimp only [quadraticKernelDerivative]
    convert (hasDerivAt_const x (1 : ℝ)).div (hq'.pow 2) (pow_ne_zero 2 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring
  · dsimp only [quadraticKernelDerivative]
    have hp : HasDerivAt (fun t : ℝ => -4*(t-c)) (-4) x := by
      convert ht.const_mul (-4) using 1
      ring
    convert hp.div (hq'.pow 3) (pow_ne_zero 3 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring
  · dsimp only [quadraticKernelDerivative]
    have hp : HasDerivAt (fun t : ℝ => 20*(t-c)^2-4*b) (40*(x-c)) x := by
      convert ((ht.pow 2).const_mul 20).sub_const (4*b) using 1
      ring
    convert hp.div (hq'.pow 4) (pow_ne_zero 4 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring
  · dsimp only [quadraticKernelDerivative]
    have hp : HasDerivAt (fun t : ℝ => -120*(t-c)^3+72*b*(t-c))
        (-360*(x-c)^2+72*b) x := by
      convert ((ht.pow 3).const_mul (-120)).add (ht.const_mul (72*b)) using 1
      ring
    convert hp.div (hq'.pow 5) (pow_ne_zero 5 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring
  · dsimp only [quadraticKernelDerivative]
    have hp : HasDerivAt (fun t : ℝ => 840*(t-c)^4-1008*b*(t-c)^2+72*b^2)
        (3360*(x-c)^3-2016*b*(x-c)) x := by
      convert (((ht.pow 4).const_mul 840).sub ((ht.pow 2).const_mul (1008*b))).add_const
        (72*b^2) using 1
      ring
    convert hp.div (hq'.pow 6) (pow_ne_zero 6 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring
  · dsimp only [quadraticKernelDerivative]
    have hp : HasDerivAt (fun t : ℝ => -6720*(t-c)^5+13440*b*(t-c)^3-2880*b^2*(t-c))
        (-33600*(x-c)^4+40320*b*(x-c)^2-2880*b^2) x := by
      convert (((ht.pow 5).const_mul (-6720)).add ((ht.pow 3).const_mul (13440*b))).sub
        (ht.const_mul (2880*b^2)) using 1
      ring
    convert hp.div (hq'.pow 7) (pow_ne_zero 7 hq) using 1
    · funext t; rfl
    · simp only [Pi.pow_apply]
      field_simp [hq]
      ring

theorem quadraticKernel_contDiffOn (n : ℕ) (b c : ℝ) {s : Set ℝ}
    (hq : ∀ t ∈ s, (t-c)^2+b ≠ 0) : ContDiffOn ℝ n (quadraticKernel b c) s := by
  unfold quadraticKernel
  exact contDiffOn_const.div (by fun_prop) (fun t ht => pow_ne_zero 2 (hq t ht))

/-- The certificate is also valid for one-sided derivatives on closed cells. -/
theorem iteratedDerivWithin_quadraticKernel (n : ℕ) (hn : n ≤ 6) (b c : ℝ)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hq : ∀ t ∈ s, (t-c)^2+b ≠ 0)
    {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (quadraticKernel b c) s x = quadraticKernelDerivative n b c x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hn' : n < 6 := by omega
    have heq : Set.EqOn (iteratedDerivWithin n (quadraticKernel b c) s)
        (quadraticKernelDerivative n b c) s := fun _ ht => ih (by omega) ht
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (ih (by omega) hx)]
    exact (quadraticKernelDerivative_step ⟨n, hn'⟩ b c x (hq x hx)).hasDerivWithinAt.derivWithin
      (hs x hx)

/-- A coarse coefficient bound is enough for the far-cell error order. -/
theorem quadraticKernelDerivative_six_bound (b c x : ℝ) (hb : 0 ≤ b)
    (hq : 0 < (x-c)^2+b) :
    |quadraticKernelDerivative 6 b c x| ≤ 322560/((x-c)^2+b)^5 := by
  let z : ℝ := x-c
  let q : ℝ := z^2+b
  have hzq : z^2 ≤ q := by dsimp only [q]; linarith
  have hbq : b ≤ q := by dsimp only [q]; nlinarith [sq_nonneg z]
  have hqp : 0 < q := hq
  have hz6 : z^6 ≤ q^3 := by
    calc z^6 = (z^2)^3 := by ring
         _ ≤ q^3 := pow_le_pow_left₀ (sq_nonneg z) hzq 3
  have hz4 : z^4 ≤ q^2 := by
    calc z^4 = (z^2)^2 := by ring
         _ ≤ q^2 := pow_le_pow_left₀ (sq_nonneg z) hzq 2
  have hbz4 : b*z^4 ≤ q^3 := by
    calc b*z^4 ≤ q*q^2 := mul_le_mul hbq hz4 (by positivity) hqp.le
         _ = q^3 := by ring
  have hb2z2 : b^2*z^2 ≤ q^3 := by
    calc b^2*z^2 ≤ q^2*q :=
           mul_le_mul (pow_le_pow_left₀ hb hbq 2) hzq (sq_nonneg z) (by positivity)
         _ = q^3 := by ring
  have hb3 : b^3 ≤ q^3 := pow_le_pow_left₀ hb hbq 3
  have hA : 0 ≤ 60480*z^6 := by positivity
  have hB : 0 ≤ 181440*b*z^4 := by positivity
  have hC : 0 ≤ 77760*b^2*z^2 := by positivity
  have hD : 0 ≤ 2880*b^3 := by positivity
  have hnum : |60480*z^6-181440*b*z^4+77760*b^2*z^2-2880*b^3| ≤ 322560*q^3 := by
    calc
      _ ≤ 60480*z^6+181440*b*z^4+77760*b^2*z^2+2880*b^3 :=
        abs_le.mpr ⟨by linarith only [hA, hC], by linarith only [hB, hD]⟩
      _ ≤ 322560*q^3 := by
        have ha := mul_le_mul_of_nonneg_left hz6 (by norm_num : (0 : ℝ) ≤ 60480)
        have hb' := mul_le_mul_of_nonneg_left hbz4 (by norm_num : (0 : ℝ) ≤ 181440)
        have hc := mul_le_mul_of_nonneg_left hb2z2 (by norm_num : (0 : ℝ) ≤ 77760)
        have hd := mul_le_mul_of_nonneg_left hb3 (by norm_num : (0 : ℝ) ≤ 2880)
        nlinarith only [ha, hb', hc, hd]
  change |(60480*z^6-181440*b*z^4+77760*b^2*z^2-2880*b^3)/q^8| ≤ 322560/q^5
  rw [abs_div, abs_of_pos (pow_pos hqp 8)]
  calc
    _ ≤ (322560*q^3)/q^8 := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 322560/q^5 := by field_simp [hqp.ne']

theorem quadraticKernelDerivative_six_bound_radius (b c x r : ℝ) (hb : 0 ≤ b)
    (hr : 0 < r) (hsep : r^2 ≤ (x-c)^2+b) :
    |quadraticKernelDerivative 6 b c x| ≤ 322560/r^10 := by
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hq : 0 < (x-c)^2+b := hr2.trans_le hsep
  calc
    _ ≤ 322560/((x-c)^2+b)^5 := quadraticKernelDerivative_six_bound b c x hb hq
    _ ≤ 322560/(r^2)^5 := div_le_div_of_nonneg_left (by norm_num) (pow_pos hr2 5)
      (pow_le_pow_left₀ hr2.le hsep 5)
    _ = 322560/r^10 := by rw [← pow_mul]

#print axioms quadraticKernelDerivative_step
#print axioms iteratedDerivWithin_quadraticKernel
#print axioms quadraticKernelDerivative_six_bound_radius

end SphericalRiesz
