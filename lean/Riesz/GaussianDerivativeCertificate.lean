import Riesz.LocalCellQuadrature
import Mathlib.Analysis.Complex.Exponential

/-!
# Finite derivative certificates for damped quadratic Gaussians

The coefficients through order six are supplied, then checked by
first-derivative rules and `ring`. The parameter moment bound is uniform
on all u ≥ 0. Actual annular E8 geometry and the tail discrepancy remain
separate obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SphericalRiesz

def gaussianQuadratic (u a b c t : ℝ) : ℝ := Real.exp (-u*(a*t^2+b*t+c))

def gaussianQuadraticCoefficient (n : ℕ) (u d e : ℝ) : ℝ :=
  match n with
  | 0 => 1
  | 1 => -u*d
  | 2 => u^2*d^2-u*e
  | 3 => -u^3*d^3+3*u^2*d*e
  | 4 => u^4*d^4-6*u^3*d^2*e+3*u^2*e^2
  | 5 => -u^5*d^5+10*u^4*d^3*e-15*u^3*d*e^2
  | 6 => u^6*d^6-15*u^5*d^4*e+45*u^4*d^2*e^2-15*u^3*e^3
  | _ => 0

def gaussianQuadraticDerivative (n : ℕ) (u a b c t : ℝ) : ℝ :=
  gaussianQuadraticCoefficient n u (2*a*t+b) (2*a) * gaussianQuadratic u a b c t

theorem gaussianQuadraticCoefficient_step (n : Fin 6) (u a b x : ℝ) :
    HasDerivAt (fun t => gaussianQuadraticCoefficient n.val u (2*a*t+b) (2*a))
      (gaussianQuadraticCoefficient (n.val+1) u (2*a*x+b) (2*a) +
        u*(2*a*x+b)*gaussianQuadraticCoefficient n.val u (2*a*x+b) (2*a)) x := by
  have hd : HasDerivAt (fun t : ℝ => 2*a*t+b) (2*a) x :=
    by simpa using ((hasDerivAt_id x).const_mul (2*a)).add_const b
  fin_cases n
  · norm_num only [gaussianQuadraticCoefficient]
    convert hasDerivAt_const x (1 : ℝ) using 1 <;> ring
  · norm_num only [gaussianQuadraticCoefficient]
    convert hd.const_mul (-u) using 1 <;> ring
  · norm_num only [gaussianQuadraticCoefficient]
    convert ((hd.pow 2).const_mul (u^2)).sub_const (u*(2*a)) using 1 <;> ring
  · norm_num only [gaussianQuadraticCoefficient]
    convert ((hd.pow 3).const_mul (-u^3)).add (hd.const_mul (3*u^2*(2*a))) using 1
    · funext t; norm_num [gaussianQuadraticCoefficient, Pi.pow_apply, Pi.add_apply, id_eq]; ring
    · ring
  · norm_num only [gaussianQuadraticCoefficient]
    convert (((hd.pow 4).const_mul (u^4)).sub
      ((hd.pow 2).const_mul (6*u^3*(2*a)))).add_const (3*u^2*(2*a)^2) using 1
    · funext t; norm_num [gaussianQuadraticCoefficient, Pi.pow_apply, Pi.add_apply, id_eq]; ring
    · ring
  · norm_num only [gaussianQuadraticCoefficient]
    convert (((hd.pow 5).const_mul (-u^5)).add
      ((hd.pow 3).const_mul (10*u^4*(2*a)))).sub (hd.const_mul (15*u^3*(2*a)^2)) using 1
    · funext t; norm_num [gaussianQuadraticCoefficient, Pi.pow_apply, Pi.add_apply, id_eq]; ring
    · ring

theorem gaussianQuadraticDerivative_step (n : Fin 6) (u a b c x : ℝ) :
    HasDerivAt (gaussianQuadraticDerivative n.val u a b c)
      (gaussianQuadraticDerivative (n.val+1) u a b c x) x := by
  have hq : HasDerivAt (fun t : ℝ => a*t^2+b*t+c) (2*a*x+b) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul a).add
      ((hasDerivAt_id x).const_mul b)).add_const c using 1
    · funext t; simp only [Pi.add_apply, Pi.pow_apply, id_eq] <;> ring
    · norm_num <;> ring
  have hg : HasDerivAt (gaussianQuadratic u a b c)
      (-u*(2*a*x+b)*gaussianQuadratic u a b c x) x := by
    convert (hq.const_mul (-u)).exp using 1
    · funext t; rfl
    · change -u*(2*a*x+b)*Real.exp (-u*(a*x^2+b*x+c)) =
        Real.exp (-u*(a*x^2+b*x+c))*(-u*(2*a*x+b))
      ring
  unfold gaussianQuadraticDerivative
  convert (gaussianQuadraticCoefficient_step n u a b x).mul hg using 1
  ring

theorem iteratedDerivWithin_gaussianQuadratic (n : ℕ) (hn : n ≤ 6) (u a b c : ℝ)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (gaussianQuadratic u a b c) s x =
      gaussianQuadraticDerivative n u a b c x := by
  induction n generalizing x with
  | zero => simp [gaussianQuadraticDerivative, gaussianQuadraticCoefficient]
  | succ n ih =>
    have hn' : n < 6 := by omega
    have heq : Set.EqOn (iteratedDerivWithin n (gaussianQuadratic u a b c) s)
        (gaussianQuadraticDerivative n u a b c) s := fun _ ht => ih (by omega) ht
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (ih (by omega) hx)]
    exact (gaussianQuadraticDerivative_step ⟨n, hn'⟩ u a b c x).hasDerivWithinAt.derivWithin
      (hs x hx)

theorem iteratedDeriv_gaussianQuadratic (n : ℕ) (hn : n ≤ 6) (u a b c x : ℝ) :
    iteratedDeriv n (gaussianQuadratic u a b c) x = gaussianQuadraticDerivative n u a b c x := by
  rw [← iteratedDerivWithin_univ]
  exact iteratedDerivWithin_gaussianQuadratic n hn u a b c uniqueDiffOn_univ (Set.mem_univ x)

/-- The bound holds on the unbounded parameter interval, including u = 0. -/
theorem gaussianParameterMoment_bound (n : ℕ) {u δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ) :
    u^n * Real.exp (-δ*u) ≤ (n.factorial : ℝ)/δ^n := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (δ*u) (mul_nonneg hδ.le hu) n)
  have he : Real.exp (δ*u)*Real.exp (-δ*u) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hb : (δ*u)^n*Real.exp (-δ*u) ≤ (n.factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-δ*u)).le
    calc
      _ ≤ Real.exp (δ*u)*(n.factorial : ℝ)*Real.exp (-δ*u) := h
      _ = _ := by calc
        _ = (n.factorial : ℝ)*(Real.exp (δ*u)*Real.exp (-δ*u)) := by ring
        _ = _ := by rw [he, mul_one]
  calc
    _ = ((δ*u)^n*Real.exp (-δ*u))/δ^n := by
      rw [mul_pow]
      field_simp [hδ.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hb (pow_pos hδ n).le

theorem gaussianParameterMoment_bound_of_lower (n : ℕ) {u δ Q : ℝ}
    (hu : 0 ≤ u) (hδ : 0 < δ) (hQ : δ ≤ Q) :
    u^n * Real.exp (-u*Q) ≤ (n.factorial : ℝ)/δ^n := by
  calc
    _ ≤ u^n*Real.exp (-δ*u) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hu n)
      nlinarith
    _ ≤ _ := gaussianParameterMoment_bound n hu hδ

theorem gaussianParameterMonomial_bound (n k : ℕ) {u δ Q d D : ℝ}
    (hu : 0 ≤ u) (hδ : 0 < δ) (hQ : δ ≤ Q) (hd : |d| ≤ D) :
    |u^n*d^k*Real.exp (-u*Q)| ≤ (n.factorial : ℝ)/δ^n*D^k := by
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hu,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ = (u^n*Real.exp (-u*Q))*|d|^k := by ring
    _ ≤ (n.factorial : ℝ)/δ^n*D^k :=
      mul_le_mul (gaussianParameterMoment_bound_of_lower n hu hδ hQ)
        (pow_le_pow_left₀ (abs_nonneg d) hd k) (by positivity) (by positivity)

#print axioms gaussianQuadraticCoefficient_step
#print axioms gaussianQuadraticDerivative_step
#print axioms iteratedDerivWithin_gaussianQuadratic
#print axioms iteratedDeriv_gaussianQuadratic
#print axioms gaussianParameterMoment_bound
#print axioms gaussianParameterMoment_bound_of_lower
#print axioms gaussianParameterMonomial_bound

end SphericalRiesz
