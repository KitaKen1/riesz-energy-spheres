/-
Gaussian profile and radial Schwartz construction adapted from math-inc/Sphere-Packing-Lean,
commit 1e98fb493088948ca7bbf47d7faed49cc5b39fc4, rank-24 ThetaTransform.lean.
Apache 2.0; see third_party/SpherePacking/LICENSE and NOTICE.txt.
Modified: the actual rank-eight E8 Gaussian; existing Fourier formula used separately.
-/
import Riesz.E8ThetaFourier
import Riesz.RadialSchwartz
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped RealInnerProductSpace SchwartzMap FourierTransform
open Complex Filter MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SphericalRiesz

def e8ThetaProfile (τ : ℂ) : ℝ → ℂ :=
  fun r => Complex.exp (((Real.pi : ℂ) * Complex.I * τ) * (r : ℂ))

lemma e8ThetaProfile_contDiff (τ : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (e8ThetaProfile τ) := by
  have hlin :
      ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ((Real.pi : ℂ) * Complex.I * τ) * (r : ℂ)) := by
    simpa using (contDiff_const.mul (Complex.ofRealCLM.contDiff))
  exact hlin.cexp

lemma e8ThetaProfile_iteratedDeriv (τ : ℂ) (n : ℕ) (r : ℝ) :
    iteratedDeriv n (e8ThetaProfile τ) r =
      (((Real.pi : ℂ) * Complex.I * τ) ^ n) * e8ThetaProfile τ r := by
  let c : ℂ := (Real.pi : ℂ) * Complex.I * τ
  -- rewrite to a simpler statement with `c`.
  have hIH : ∀ n : ℕ, ∀ r : ℝ, iteratedDeriv n (e8ThetaProfile τ) r = c ^ n * e8ThetaProfile τ r := by
    intro n
    induction n with
    | zero =>
        intro r
        simp [e8ThetaProfile, c]
    | succ n hn =>
        intro r
        have hmul : HasDerivAt (fun z : ℂ => c * z) c (r : ℂ) := by
          simpa using (hasDerivAt_const_mul (c := c) (x := (r : ℂ)))
        have hlin : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c r :=
          HasDerivAt.comp_ofReal (z := r) hmul
        have hderiv : deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r =
            Complex.exp (c * (r : ℂ)) * c := (hlin.cexp).deriv
        have hfun :
            iteratedDeriv n (e8ThetaProfile τ) = fun x : ℝ => c ^ n * e8ThetaProfile τ x := by
          funext x
          exact hn x
        calc
          iteratedDeriv (n + 1) (e8ThetaProfile τ) r
              = deriv (iteratedDeriv n (e8ThetaProfile τ)) r := by
                  simp [iteratedDeriv_succ]
          _ = deriv (fun x : ℝ => c ^ n * e8ThetaProfile τ x) r := by
                  simp [hfun]
          _ = c ^ n * deriv (e8ThetaProfile τ) r := by
                  simp [deriv_const_mul_field (x := r) (u := c ^ n)
                    (v := fun x : ℝ => e8ThetaProfile τ x)]
          _ = c ^ n * (c * e8ThetaProfile τ r) := by
                  have hderiv' : deriv (e8ThetaProfile τ) r = c * e8ThetaProfile τ r := by
                    -- change to the linearized form
                    change deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r =
                      c * Complex.exp (c * (r : ℂ))
                    calc
                      deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r
                          = Complex.exp (c * (r : ℂ)) * c := hderiv
                      _ = c * Complex.exp (c * (r : ℂ)) := by ac_rfl
                  -- multiply both sides by `c^n`
                  simpa [mul_assoc] using congrArg (fun z => c ^ n * z) hderiv'
          _ = c ^ (n + 1) * e8ThetaProfile τ r := by
                  simp [pow_succ, mul_assoc]
  simpa [c] using hIH n r

lemma e8_exists_bound_pow_mul_exp_neg_mul_of_nonneg (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-a * x) ≤ C := by
  have hlim :
      Tendsto (fun x : ℝ => x ^ k * Real.exp (-a * x)) atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := a) ha)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ k * Real.exp (-a * x) ≤ 1 :=
    (hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)))
  rcases (Filter.eventually_atTop.1 hevent) with ⟨R, hR⟩
  let R0 : ℝ := max R 0
  have hcont : Continuous fun x : ℝ => x ^ k * Real.exp (-a * x) := by
    fun_prop
  have hne : (Set.Icc (0 : ℝ) R0).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · dsimp [R0]
      exact le_max_right R 0
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R0)).exists_isMaxOn hne hcont.continuousOn with
    ⟨x0, hx0, hxmax⟩
  refine ⟨max (x0 ^ k * Real.exp (-a * x0)) 1, ?_⟩
  intro x hx
  by_cases hxR : x ≤ R0
  · have hxIcc : x ∈ Set.Icc (0 : ℝ) R0 := ⟨hx, hxR⟩
    exact (hxmax hxIcc).trans (le_max_left _ _)
  · have hRR0 : R ≤ R0 := le_max_left R 0
    have hxR0 : R0 ≤ x := le_of_not_ge hxR
    exact (hR x (le_trans hRR0 hxR0)).trans (le_max_right _ _)

lemma e8ThetaProfile_decay (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (e8ThetaProfile τ) x‖ ≤ C := by
  intro k n
  let c : ℂ := (Real.pi : ℂ) * Complex.I * τ
  have hc_re : c.re = -Real.pi * τ.im := by
    simp [c]
  have ha : 0 < -c.re := by
    nlinarith [hc_re, Real.pi_pos, hτ]
  rcases e8_exists_bound_pow_mul_exp_neg_mul_of_nonneg k ha with ⟨C0, hC0⟩
  refine ⟨(‖c‖ ^ n) * C0, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hiter :
      ‖iteratedFDeriv ℝ n (e8ThetaProfile τ) x‖ = ‖iteratedDeriv n (e8ThetaProfile τ) x‖ := by
    simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n)
      (f := e8ThetaProfile τ) (x := x)]
  have hder_le :
      ‖iteratedDeriv n (e8ThetaProfile τ) x‖ ≤ (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by
    have hexp : ‖e8ThetaProfile τ x‖ = Real.exp (c.re * x) := by
      simp [e8ThetaProfile, c, Complex.norm_exp, Complex.mul_re]
    have hiter' :
        ‖iteratedDeriv n (e8ThetaProfile τ) x‖ = ‖c ^ n‖ * ‖e8ThetaProfile τ x‖ := by
      calc
        ‖iteratedDeriv n (e8ThetaProfile τ) x‖
            = ‖(c ^ n) * e8ThetaProfile τ x‖ := by
                simp [e8ThetaProfile_iteratedDeriv (τ := τ) (n := n) (r := x), c]
        _ = ‖c ^ n‖ * ‖e8ThetaProfile τ x‖ := by simp
    have hre : Real.exp (c.re * x) = Real.exp (-(-c.re) * x) := by simp
    have heq :
        ‖iteratedDeriv n (e8ThetaProfile τ) x‖ =
          (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by
      calc
        ‖iteratedDeriv n (e8ThetaProfile τ) x‖
            = ‖c ^ n‖ * Real.exp (-(-c.re) * x) := by simpa [hexp, hre] using hiter'
        _ = (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by simp [norm_pow]
    exact le_of_eq heq
  have hxpow : 0 ≤ x ^ k := by positivity
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (e8ThetaProfile τ) x‖
        = x ^ k * ‖iteratedDeriv n (e8ThetaProfile τ) x‖ := by
            simp [hxnorm, hiter]
    _ ≤ x ^ k * ((‖c‖ ^ n) * Real.exp (-(-c.re) * x)) :=
            mul_le_mul_of_nonneg_left hder_le hxpow
    _ = (‖c‖ ^ n) * (x ^ k * Real.exp (-(-c.re) * x)) := by ring_nf
    _ ≤ (‖c‖ ^ n) * C0 := by
            gcongr
            exact hC0 x hx

noncomputable def e8ThetaSchwartzKernel (τ : ℂ) (hτ : 0 < τ.im) : 𝓢(E8Ambient, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg (F := E8Ambient)
    (e8ThetaProfile τ) (e8ThetaProfile_contDiff τ) (e8ThetaProfile_decay (τ := τ) hτ)

@[simp] lemma e8ThetaSchwartzKernel_apply (τ : ℂ) (hτ : 0 < τ.im) (x : E8Ambient) :
    e8ThetaSchwartzKernel τ hτ x =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  simp [e8ThetaSchwartzKernel, e8ThetaProfile, mul_assoc, mul_comm]


theorem e8ThetaSchwartzKernel_eq (τ : ℂ) (hτ : 0 < τ.im) :
    (fun x : E8Ambient => e8ThetaSchwartzKernel τ hτ x) = e8ThetaKernel τ := by
  funext x
  rw [e8ThetaSchwartzKernel_apply]
  unfold e8ThetaKernel
  congr 1
  ring

#print axioms e8ThetaProfile_contDiff
#print axioms e8ThetaProfile_iteratedDeriv
#print axioms e8ThetaProfile_decay
#print axioms e8ThetaSchwartzKernel_apply
#print axioms e8ThetaSchwartzKernel_eq
end SphericalRiesz
