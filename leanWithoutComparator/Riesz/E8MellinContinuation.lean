import Riesz.E8RegularizedIntegral
import Riesz.E8Epstein
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-! The existing abstract Mellin functional equation, applied to actual E8 theta. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

def e8ThetaFEPair : WeakFEPair ℂ where
  f := e8ThetaImag
  g := e8ThetaImag
  k := 4
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := e8ThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := e8ThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq t ht := by
    simpa [one_div, Real.rpow_ofNat, smul_eq_mul] using e8ThetaImag_transform ht
  hf_top r := (e8ThetaTail_littleO_rpow r).isBigO
  hg_top r := (e8ThetaTail_littleO_rpow r).isBigO

def e8ThetaCompleted : ℂ → ℂ := e8ThetaFEPair.Λ

theorem e8ThetaCompleted_differentiableAt {s : ℂ} (h0 : s ≠ 0) (h4 : s ≠ 4) :
    DifferentiableAt ℂ e8ThetaCompleted s :=
  e8ThetaFEPair.differentiableAt_Λ (Or.inl h0) (Or.inl h4)

theorem e8ThetaCompleted_eq_mellin {s : ℂ} (hs : 4 < s.re) :
    e8ThetaCompleted s = mellin e8ThetaTail s :=
  (e8ThetaFEPair.hasMellin hs).2.symm

theorem e8ThetaTail_gaussian_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun z : Fin 8 → ℤ => if ‖e8EuclideanPoint z‖^2 = 0 then (0 : ℂ)
      else (Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*t) : ℂ)) (e8ThetaTail t) := by
  classical
  have h := hasSum_ite_sub_hasSum
    (e8Theta_hasSum (τ := (t : ℂ)*Complex.I) (by simpa using ht)) 0
  have hz0 (z : Fin 8 → ℤ) : ‖e8EuclideanPoint z‖^2 = 0 ↔ z = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero]
    exact ⟨fun hz => e8EuclideanPoint_injective (hz.trans e8EuclideanPoint_zero.symm),
      fun hz => by simp [hz]⟩
  simp only [e8EuclideanPoint_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero] at h
  change HasSum _ (e8ThetaTail t) at h
  apply h.congr_fun
  intro z
  simp only [hz0]
  split_ifs
  · rfl
  · rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]

theorem e8ThetaCompleted_eq_Epstein {s : ℂ} (hs : 4 < s.re) :
    e8ThetaCompleted s = (Real.pi : ℂ)^(-s) * Complex.Gamma s * e8EpsteinCandidate s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable (fun z : Fin 8 → ℤ => ‖(1 : ℂ)‖ / (‖e8EuclideanPoint z‖^2)^s.re) := by
    apply (e8Epstein_summable hs).norm.congr
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp [e8EpsteinTerm, Real.zero_rpow hs0.ne']
    · have hp : 0 < ‖e8EuclideanPoint z‖^2 :=
        lt_of_lt_of_le (by norm_num) (e8EuclideanPoint_norm_sq_ge_two hz)
      rw [e8EpsteinTerm, if_neg hz, Complex.norm_cpow_eq_rpow_re_of_pos hp,
        Complex.neg_re, norm_one, Real.rpow_neg hp.le, one_div]
  have hm := hasSum_mellin_pi_mul₀ (a := fun _ : Fin 8 → ℤ => (1 : ℂ))
    (F := e8ThetaTail) (s := s)
    (p := fun z => ‖e8EuclideanPoint z‖^2) (fun z => sq_nonneg _) hs0
    (fun t ht => by simpa only [one_mul] using e8ThetaTail_gaussian_hasSum ht) hsum
  have he := (e8Epstein_hasSum hs).mul_left ((Real.pi : ℂ)^(-s)*Complex.Gamma s)
  have he' : HasSum (fun z : Fin 8 → ℤ =>
      (Real.pi : ℂ)^(-s)*Complex.Gamma s*1 / ((‖e8EuclideanPoint z‖^2 : ℝ) : ℂ)^s)
      ((Real.pi : ℂ)^(-s)*Complex.Gamma s*e8EpsteinCandidate s) := by
    apply he.congr_fun
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · have hsne : s ≠ 0 := by intro h; simpa [h] using hs0
      simp [e8EpsteinTerm, Complex.zero_cpow hsne]
    · simp [e8EpsteinTerm, hz, Complex.cpow_neg, div_eq_mul_inv]
  rw [e8ThetaCompleted_eq_mellin hs]
  exact hm.unique he'

def e8CompletedCandidate (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^(-s) * Complex.Gamma s * e8EpsteinCandidate s

theorem e8CompletedCandidate_differentiableAt {s : ℂ} (hs : 0 < s.re)
    (h1 : s ≠ 1) (h4 : s ≠ 4) : DifferentiableAt ℂ e8CompletedCandidate s := by
  have hΓ := Complex.differentiableAt_Gamma s (fun m h => by
    have hneg : (- (m : ℂ)).re ≤ 0 := by simp
    rw [← h] at hneg
    exact (not_le_of_gt hs) hneg)
  exact ((differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hΓ).mul
      (e8EpsteinCandidate_differentiableAt h1 h4)

/-- Continue on an open convex quadrant, then approach the real point 2.
This avoids building a theory of connected punctured domains. -/
theorem e8ThetaCompleted_eq_candidate_at_two : e8ThetaCompleted 2 = e8CompletedCandidate 2 := by
  let U : Set ℂ := {s | 1 < s.re ∧ 0 < s.im}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (r := 1)).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected
  have hreal {s : ℂ} (hs : s ∈ U) (c : ℝ) : s ≠ (c : ℂ) := by
    intro h
    have hi := hs.2
    simpa [h] using hi
  have hf : AnalyticOnNhd ℂ e8ThetaCompleted U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    exact (e8ThetaCompleted_differentiableAt (hreal hs 0) (hreal hs 4)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ e8CompletedCandidate U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    exact (e8CompletedCandidate_differentiableAt (by linarith [hs.1])
      (hreal hs 1) (hreal hs 4)).differentiableWithinAt
  have hfg : e8ThetaCompleted =ᶠ[𝓝 ((5 : ℂ)+Complex.I)] e8CompletedCandidate := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (4 : ℝ) < ((5 : ℂ)+Complex.I).re by norm_num)] with s hs
    exact e8ThetaCompleted_eq_Epstein hs
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc
    (show ((5 : ℂ)+Complex.I) ∈ U by norm_num [U]) hfg
  have ht : Tendsto (fun ε : ℝ => (2 : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (2 : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hε |>.mul_const Complex.I)
  apply tendsto_nhds_unique_of_eventuallyEq
    ((e8ThetaCompleted_differentiableAt (s := 2) (by norm_num) (by norm_num)).continuousAt.tendsto.comp ht)
    ((e8CompletedCandidate_differentiableAt (s := 2) (by norm_num) (by norm_num)
      (by norm_num)).continuousAt.tendsto.comp ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heq (by simpa [U] using hε)

theorem e8ThetaCompleted_at_two : e8ThetaCompleted 2 = -(5 : ℂ)/6 := by
  rw [e8ThetaCompleted_eq_candidate_at_two, e8CompletedCandidate, e8EpsteinCandidate_at_two]
  have hΓ : Complex.Gamma 2 = 1 := by simpa using Complex.Gamma_nat_eq_factorial 1
  rw [hΓ]
  rw [show -(2 : ℂ) = (-2 : ℤ) by norm_num, Complex.cpow_intCast]
  field_simp [Real.pi_ne_zero]

#print axioms e8ThetaCompleted_differentiableAt
#print axioms e8ThetaCompleted_eq_mellin
#print axioms e8ThetaTail_gaussian_hasSum
#print axioms e8ThetaCompleted_eq_Epstein
#print axioms e8CompletedCandidate_differentiableAt
#print axioms e8ThetaCompleted_eq_candidate_at_two
#print axioms e8ThetaCompleted_at_two

end SphericalRiesz
