import FCCoefficientBridge
import Riesz.E8EpsteinTwo8
import Riesz.E8EpsteinNeg8
import Riesz.SphereLogCoefficient8

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
open Set MeasureTheory
namespace RieszSphereFC
open SphericalRiesz

def e8Continuation (u : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ u * (e8ThetaFEPair.Λ₀ u * (Complex.Gamma u)⁻¹ -
    (Complex.Gamma (u + 1))⁻¹ - (4 - u)⁻¹ * (Complex.Gamma u)⁻¹)

theorem epstein_eight_eq (s : ℂ) :
    epstein 8 (latticeTheta 8) s = e8Continuation (s / 2) := by
  have h := epstein_eq_weakFEPair 8 (latticeTheta 8) e8ThetaFEPair
    (by norm_num [e8ThetaFEPair]) rfl rfl rfl rfl
    (fun t ht => latticeTheta_eight_complex_eq (lt_trans zero_lt_one ht)) s
  simpa [e8Continuation, show (8 : ℂ) / 2 = 4 by norm_num] using h

theorem e8Continuation_eq_completed {u : ℂ} (hu : u ≠ 0) :
    e8Continuation u = (Real.pi : ℂ)^u * e8ThetaCompleted u / Complex.Gamma u := by
  unfold e8Continuation
  rw [e8ThetaFEPair.Λ₀_eq, Complex.Gamma_add_one u hu]
  change (Real.pi : ℂ)^u *
    ((e8ThetaCompleted u + (1/u)*1 + (1/(4-u))*1) * (Complex.Gamma u)⁻¹ -
      (u * Complex.Gamma u)⁻¹ - (4-u)⁻¹ * (Complex.Gamma u)⁻¹) = _
  simp only [mul_inv, mul_one, div_eq_mul_inv]
  ring

private theorem e8Continuation_eq_of_completed {u : ℂ}
    (hu : u ≠ 0) (hg : Complex.Gamma u ≠ 0)
    (h : e8ThetaCompleted u = e8CompletedCandidate u) :
    e8Continuation u = e8EpsteinCandidate u := by
  rw [e8Continuation_eq_completed hu, h, e8CompletedCandidate, Complex.cpow_neg]
  have hp : (Real.pi : ℂ)^u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  field_simp

private theorem gamma_ne_zero_strip {u : ℝ} (hu : -1 < u) (hu0 : u ≠ 0) :
    Complex.Gamma (u : ℂ) ≠ 0 := by
  rw [Complex.Gamma_ofReal]
  exact_mod_cast Real.Gamma_ne_zero (fun n hn => by
    rcases n with _ | n
    · apply hu0
      simpa using hn
    · have hn' : u = -((n + 1 : ℕ) : ℝ) := hn
      have hnon := Nat.cast_nonneg (α := ℝ) n
      push_cast at hn'
      linarith)

theorem epstein_eight_eq_candidate_pos {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    (hs2 : s ≠ 2) :
    epstein 8 (latticeTheta 8) (s : ℂ) = e8EpsteinCandidate ((s / 2 : ℝ) : ℂ) := by
  rw [epstein_eight_eq, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_div]
  apply e8Continuation_eq_of_completed
  · exact_mod_cast (show s/2 ≠ 0 by positivity)
  · exact gamma_ne_zero_strip (by linarith) (by positivity)
  · exact e8ThetaCompleted_eq_candidate_real (by linarith) (by linarith) (by intro h; apply hs2; linarith)

theorem epstein_eight_eq_candidate_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    epstein 8 (latticeTheta 8) (s : ℂ) = e8EpsteinCandidate ((s / 2 : ℝ) : ℂ) := by
  rw [epstein_eight_eq, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_div]
  apply e8Continuation_eq_of_completed
  · exact_mod_cast (show s/2 ≠ 0 by linarith)
  · exact gamma_ne_zero_strip (by linarith) (by linarith)
  · exact e8ThetaCompleted_eq_candidate_neg (by linarith) (by linarith)

theorem epstein_eight_at_two :
    epstein 8 (latticeTheta 8) 2 = 120 * deriv riemannZeta (-2) := by
  rw [epstein_eight_eq]
  norm_num only [div_self (by norm_num : (2 : ℂ) ≠ 0)]
  rw [e8Continuation_eq_completed (by norm_num), e8ThetaCompleted_at_one]
  simp [Complex.cpow_neg, Complex.Gamma_one]
  ring

private theorem gamma_deriv_one_re :
    (deriv Complex.Gamma 1).re = deriv Real.Gamma 1 := by
  have hg : DifferentiableAt ℂ Complex.Gamma 1 :=
    Complex.differentiableAt_Gamma _ (fun n hn => by
      have hr := congrArg Complex.re hn
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith)
  have h := hg.hasDerivAt.real_of_complex
  have he : (fun x : ℝ => (Complex.Gamma (x : ℂ)).re) = Real.Gamma := by
    funext x
    simp [Complex.Gamma_ofReal]
  rw [he] at h
  exact h.deriv.symm

private theorem reciprocal_gamma_shift_deriv_zero :
    HasDerivAt (fun u : ℂ => (Complex.Gamma (u + 1))⁻¹)
      (deriv (fun u : ℂ => (Complex.Gamma u)⁻¹) 1) 0 := by
  have h : HasDerivAt (fun u : ℂ => (Complex.Gamma u)⁻¹)
      (deriv (fun u : ℂ => (Complex.Gamma u)⁻¹) 1) ((0 : ℂ) + 1) := by
    simpa using (Complex.differentiable_one_div_Gamma 1).hasDerivAt
  exact h.comp_add_const 0 1

private theorem reciprocal_gamma_deriv_zero :
    HasDerivAt (fun u : ℂ => (Complex.Gamma u)⁻¹) 1 0 := by
  have h := (hasDerivAt_id (0 : ℂ)).mul
    reciprocal_gamma_shift_deriv_zero
  simp only [id_eq, zero_add, Complex.Gamma_one, inv_one, one_mul, zero_mul, add_zero] at h
  change HasDerivAt (fun u : ℂ => u * (Complex.Gamma (u + 1))⁻¹) 1 0 at h
  simpa only [← Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one] using h

theorem e8Continuation_deriv_re :
    (deriv e8Continuation 0).re = (deriv e8EpsteinCandidate 0).re := by
  have hP := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero))
  have hL := (e8ThetaFEPair.differentiable_Λ₀ 0).hasDerivAt
  have hG := reciprocal_gamma_shift_deriv_zero
  have hI := ((hasDerivAt_const (0 : ℂ) 4).sub (hasDerivAt_id 0)).inv (by norm_num : (4 : ℂ) - 0 ≠ 0)
  have hd := hP.mul (((hL.mul reciprocal_gamma_deriv_zero).sub hG).sub
    (hI.mul reciprocal_gamma_deriv_zero))
  have hRecip : deriv (fun u : ℂ => (Complex.Gamma u)⁻¹) 1 = -deriv Complex.Gamma 1 := by
    have hg : DifferentiableAt ℂ Complex.Gamma 1 :=
      Complex.differentiableAt_Gamma _ (fun n hn => by
        have hr := congrArg Complex.re hn
        simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)
    have h := (hg.hasDerivAt.inv (by simp : Complex.Gamma (1 : ℂ) ≠ 0)).deriv
    change deriv (fun u : ℂ => (Complex.Gamma u)⁻¹) 1 = _ at h
    simpa using h
  change HasDerivAt e8Continuation _ 0 at hd
  rw [hd.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.inv_apply, id_eq, Complex.Gamma_zero,
    inv_zero, zero_add, Complex.Gamma_one, inv_one, Complex.cpow_zero, one_mul,
    mul_one, mul_zero, zero_sub, sub_zero, hRecip]
  norm_num [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.log_re]
  rw [gamma_deriv_one_re, e8ThetaFEPair_Λ₀_zero_re]
  ring

theorem epstein_eight_deriv_re :
    (deriv (epstein 8 (latticeTheta 8)) 0).re =
      (1 / 2 : ℝ) * (deriv e8EpsteinCandidate 0).re := by
  have he : epstein 8 (latticeTheta 8) = fun s : ℂ => e8Continuation (s / 2) := funext epstein_eight_eq
  rw [he]
  have hf : DifferentiableAt ℂ e8Continuation 0 := by
    apply DifferentiableAt.mul
    · exact (differentiableAt_id (𝕜 := ℂ)).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (((e8ThetaFEPair.differentiable_Λ₀ 0).mul (Complex.differentiable_one_div_Gamma 0)).sub
        reciprocal_gamma_shift_deriv_zero.differentiableAt).sub
        (((differentiableAt_const (4 : ℂ)).sub (differentiableAt_id (𝕜 := ℂ))).inv (by norm_num) |>.mul
          (Complex.differentiable_one_div_Gamma 0))
  rw [deriv_comp_half_re hf, e8Continuation_deriv_re]

end RieszSphereFC
