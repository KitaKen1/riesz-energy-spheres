import Riesz.LeechRegularized24
import Riesz.SphereRieszLower24
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-! The coefficient of the S²⁴ Riesz asymptotics as the continued Epstein zeta value of the
Leech lattice.

The abstract Mellin functional equation applied to the Leech theta function gives the completed
function `Λ(u)`, differentiable away from `u = 0, 12`.  For `Re u > 12` it is
`π^(-u) Γ(u) Σ_{x ∈ Λ, x ≠ 0} (|x|²)^(-u)`; the lattice sum converges there by the general
summability of `‖x‖^r` over a lattice of rank 24.  In the strip `0 < u < 12` it is the Mellin
integral of the regularized theta function.  Hence

`ζ_Λ(2u) := π^u Λ(u)/Γ(u)`

is the Epstein zeta function of the Leech lattice where the series converges, is differentiable
for `Re u > 0`, `u ≠ 12`, and the sharp coefficient of the S²⁴ Riesz energy is
`C_s = A₂₄^(-s/24) ζ_Λ(s)` for every `0 < s < 24`.  A uniqueness statement shows that every
continuation of the series which is analytic in the open upper quadrant and continuous at the
real point gives the same value.  No closed formula (Eisenstein series minus the discriminant
form) is used or proved. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

/-- The abstract functional-equation pair of the Leech theta function on the imaginary axis. -/
def leechThetaFEPair : WeakFEPair ℂ where
  f := leechThetaImag
  g := leechThetaImag
  k := 12
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := leechThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := leechThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq t ht := by
    simpa [one_div, Real.rpow_ofNat, smul_eq_mul] using leechThetaImag_transform ht
  hf_top r := (leechThetaTail_littleO_rpow r).isBigO
  hg_top r := (leechThetaTail_littleO_rpow r).isBigO

/-- The completed Epstein function of the Leech lattice. -/
def leechThetaCompleted : ℂ → ℂ := leechThetaFEPair.Λ

theorem leechThetaCompleted_differentiableAt {s : ℂ} (h0 : s ≠ 0) (h12 : s ≠ 12) :
    DifferentiableAt ℂ leechThetaCompleted s :=
  leechThetaFEPair.differentiableAt_Λ (Or.inl h0) (Or.inl h12)

theorem leechThetaCompleted_eq_mellin {s : ℂ} (hs : 12 < s.re) :
    leechThetaCompleted s = mellin leechThetaTail s :=
  (leechThetaFEPair.hasMellin hs).2.symm

/-- The theta tail as a Gaussian sum over the nonzero lattice vectors. -/
theorem leechThetaTail_gaussian_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun x : leechLattice => if ‖(x : LeechAmbient)‖^2 = 0 then (0 : ℂ)
      else ((Real.exp (-Real.pi*‖(x : LeechAmbient)‖^2*t) : ℝ) : ℂ)) (leechThetaTail t) := by
  classical
  have h := hasSum_ite_sub_hasSum (leechLatticeGaussian_hasSum ht) (0 : leechLattice)
  have hz0 (x : leechLattice) : ‖(x : LeechAmbient)‖^2 = 0 ↔ x = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero]
    exact ⟨fun hx => Subtype.ext hx, fun hx => by rw [hx]; rfl⟩
  have hval : ((leechGaussianThetaReal24 t : ℝ) : ℂ)-
      ((Real.exp (-(Real.pi*t*‖((0 : leechLattice) : LeechAmbient)‖^2)) : ℝ) : ℂ) =
      leechThetaTail t := by
    unfold leechThetaTail
    rw [leechThetaImag_eq_real ht]
    simp
  rw [hval] at h
  apply h.congr_fun
  intro x
  simp only [hz0]
  split_ifs
  · rfl
  · congr 2
    ring

/-- Summability of the Epstein series of the Leech lattice beyond the critical exponent. -/
theorem leechEpstein_norm_summable {s : ℂ} (hs : 12 < s.re) :
    Summable (fun x : leechLattice => ‖(1 : ℂ)‖/(‖(x : LeechAmbient)‖^2)^s.re) := by
  have hr : -(2*s.re) < -(Module.finrank ℤ leechLattice : ℝ) := by
    rw [leechLattice_rank]
    push_cast
    linarith
  have h := ZLattice.summable_norm_rpow leechLattice (-(2*s.re)) hr
  apply h.congr
  intro x
  have hx : (‖(x : LeechAmbient)‖^2)^s.re = ‖(x : LeechAmbient)‖^(2*s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [norm_one, one_div, hx, ← Real.rpow_neg (norm_nonneg _)]
  try rfl

/-- Terms of the Epstein series of the Leech lattice, `(|x|²)^(-u)`; the term of `x = 0`
vanishes for `u ≠ 0`. -/
def leechEpsteinTerm (u : ℂ) (x : leechLattice) : ℂ :=
  ((‖(x : LeechAmbient)‖^2 : ℝ) : ℂ)^(-u)

/-- The completed function is `π^(-u) Γ(u)` times the Epstein series for `Re u > 12`. -/
theorem leechThetaCompleted_hasSum_epstein {s : ℂ} (hs : 12 < s.re) :
    HasSum (fun x : leechLattice => (Real.pi : ℂ)^(-s)*Complex.Gamma s*leechEpsteinTerm s x)
      (leechThetaCompleted s) := by
  have hs0 : 0 < s.re := by linarith
  have hm := hasSum_mellin_pi_mul₀ (a := fun _ : leechLattice => (1 : ℂ))
    (F := leechThetaTail) (s := s) (p := fun x => ‖(x : LeechAmbient)‖^2)
    (fun x => sq_nonneg _) hs0
    (fun t ht => by simpa only [one_mul] using leechThetaTail_gaussian_hasSum ht)
    (leechEpstein_norm_summable hs)
  rw [leechThetaCompleted_eq_mellin hs]
  apply hm.congr_fun
  intro x
  have hneg : ((‖(x : LeechAmbient)‖^2 : ℝ) : ℂ)^(-s) =
      (((‖(x : LeechAmbient)‖^2 : ℝ) : ℂ)^s)⁻¹ := Complex.cpow_neg _ _
  unfold leechEpsteinTerm
  rw [hneg, mul_one, div_eq_mul_inv]

/-- The Epstein zeta function of the Leech lattice in the variable `u = s/2`, continued:
`π^u Λ(u)/Γ(u)`. -/
def leechEpsteinZeta (u : ℂ) : ℂ := (Real.pi : ℂ)^u*leechThetaCompleted u/Complex.Gamma u

/-- Where the series converges, the continued function is the Epstein series. -/
theorem leechEpsteinZeta_hasSum {u : ℂ} (hu : 12 < u.re) :
    HasSum (leechEpsteinTerm u) (leechEpsteinZeta u) := by
  have hu0 : 0 < u.re := by linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπu : (Real.pi : ℂ)^u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hΓ : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu0
  have hneg : (Real.pi : ℂ)^(-u) = ((Real.pi : ℂ)^u)⁻¹ := Complex.cpow_neg _ _
  have h := (leechThetaCompleted_hasSum_epstein hu).mul_left ((Real.pi : ℂ)^u/Complex.Gamma u)
  have hval : (Real.pi : ℂ)^u/Complex.Gamma u*leechThetaCompleted u = leechEpsteinZeta u := by
    unfold leechEpsteinZeta
    ring
  rw [hval] at h
  apply h.congr_fun
  intro x
  rw [hneg, show (Real.pi : ℂ)^u/Complex.Gamma u*
      (((Real.pi : ℂ)^u)⁻¹*Complex.Gamma u*leechEpsteinTerm u x) =
      ((Real.pi : ℂ)^u*((Real.pi : ℂ)^u)⁻¹)*(Complex.Gamma u/Complex.Gamma u)*
        leechEpsteinTerm u x by ring,
    mul_inv_cancel₀ hπu, div_self hΓ, one_mul, one_mul]

theorem leechEpsteinZeta_differentiableAt {u : ℂ} (hu : 0 < u.re) (h12 : u ≠ 12) :
    DifferentiableAt ℂ leechEpsteinZeta u := by
  have h0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hΓ := Complex.differentiableAt_Gamma u (fun m h => by
    have hneg : (-(m : ℂ)).re ≤ 0 := by simp
    rw [← h] at hneg
    exact (not_le_of_gt hu) hneg)
  have hΓ0 : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu
  have hpow : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ)^v) u :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact (hpow.mul (leechThetaCompleted_differentiableAt h0 h12)).div hΓ hΓ0

theorem leechThetaFEPair_modified_weighted_ae_rpow (u : ℝ) :
    (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • leechThetaFEPair.f_modif t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t +
        (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(u-13) : ℝ) : ℂ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((u:ℂ)-1) = ((t^(u-1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht0.le]
    push_cast
    ring_nf
  have hc13 : ((t^(u-13) : ℝ) : ℂ) = ((t^(u-1) : ℝ) : ℂ) * ((t:ℂ)^12)⁻¹ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [show u-13 = (u-1)-(12:ℝ) by ring, Real.rpow_sub ht0, Real.rpow_ofNat, div_eq_mul_inv]
  have h12 : ((t^(-(12:ℝ)) : ℝ) : ℂ) = ((t:ℂ)^12)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  simp only [WeakFEPair.f_modif, leechThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h12]
    unfold leechThetaRegularized leechThetaTail
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, hc13]
    unfold leechThetaRegularized leechThetaTail
    ring

/-- In the strip, the completed value is the Mellin integral of the regularized theta. -/
theorem leechThetaCompleted_eq_integral_strip {u : ℝ} (hu0 : 0 < u) (hu12 : u < 12) :
    leechThetaCompleted (u:ℂ) =
      ∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t := by
  have hreg : IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t) (Ioi 0) :=
    leechThetaRegularized_mellinConvergent (s := (u:ℂ)) (by simpa using hu0) (by simpa using hu12)
  have hsmall : IntegrableOn (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)).ofReal
  have hlarge : IntegrableOn (fun t : ℝ => ((t^(u-13) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have hs := (hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi 0)
  have hl := (hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have Ismall : (∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t) =
      1/(u:ℂ) := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < u-1))]
    have hu : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hu0.ne', sub_zero]
    push_cast
    field_simp
  have Ilarge : (∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-13) : ℝ) : ℂ)) t) =
      1/(12-(u:ℂ)) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
      integral_complex_ofReal, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    have h12 : (u:ℂ)-12 ≠ 0 := by
      have : u-12 ≠ 0 := by linarith
      exact_mod_cast this
    have h12' : (12:ℂ)-(u:ℂ) ≠ 0 := by
      intro h; apply h12; linear_combination -h
    simp only [Real.one_rpow, show u-13+1 = u-12 by ring]
    push_cast
    field_simp
    ring
  have hm : mellin leechThetaFEPair.f_modif (u:ℂ) =
      (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t) + 1/(u:ℂ) +
        1/(12-(u:ℂ)) := by
    unfold mellin
    rw [integral_congr_ae (leechThetaFEPair_modified_weighted_ae_rpow u)]
    have e1 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
          (Ioi 1).indicator (fun t : ℝ => ((t^(u-13) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) +
        ∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-13) : ℝ) : ℂ)) t :=
      integral_add (hreg.add hs) hl
    have e2 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • leechThetaRegularized t) +
        ∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t :=
      integral_add hreg hs
    rw [e1, e2, Ismall, Ilarge]
  change mellin leechThetaFEPair.f_modif (u:ℂ) - (1/(u:ℂ))*1 - (1/(12-(u:ℂ)))*1 = _
  rw [hm]
  ring

/-- The profile integral is the real part of the completed value in the strip. -/
theorem leechGaussianRieszProfileRpow24_integral_eq {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    (∫ α : ℝ in Ioi 0, leechGaussianRieszProfileRpow24 s α) =
      (leechThetaCompleted ((s/2:ℝ):ℂ)).re := by
  rw [leechThetaCompleted_eq_integral_strip (by linarith) (by linarith)]
  have hint : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • leechThetaRegularized t) (Ioi 0) :=
    leechThetaRegularized_mellinConvergent (s := ((s/2:ℝ):ℂ)) (by simp; linarith)
      (by simp; linarith)
  have h := integral_re hint
  change (∫ t : ℝ in Ioi 0, (((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • leechThetaRegularized t).re) =
    (∫ t : ℝ in Ioi 0, ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • leechThetaRegularized t).re at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  exact leechGaussianRieszProfileRpow24_eq_re s hα

/-- The sharp coefficient of the S²⁴ Riesz energy is the continued Epstein zeta value of the
Leech lattice, `C_s = A₂₄^(-s/24) ζ_Λ(s)`, for every `0 < s < 24`. -/
theorem sphereRieszCoefficient24_eq_epstein {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    sphereRieszCoefficient24 s =
      ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re := by
  have hG : Complex.Gamma ((s/2:ℝ):ℂ) = ((Real.Gamma (s/2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (s/2)
  have hP : (Real.pi : ℂ)^((s/2:ℝ):ℂ) = ((Real.pi^(s/2) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow Real.pi_pos.le (s/2)).symm
  have hre : (((Real.pi^(s/2) : ℝ) : ℂ)*leechThetaCompleted ((s/2:ℝ):ℂ)/
      ((Real.Gamma (s/2) : ℝ) : ℂ)).re =
      Real.pi^(s/2)/Real.Gamma (s/2)*(leechThetaCompleted ((s/2:ℝ):ℂ)).re := by
    rw [mul_div_right_comm, ← Complex.ofReal_div, Complex.re_ofReal_mul]
  unfold sphereRieszCoefficient24 leechEpsteinZeta
  rw [leechGaussianRieszProfileRpow24_integral_eq hs hs24, hG, hP, hre]
  ring

/-- Uniqueness at the real points of the strip: a function which is analytic in the open upper
quadrant, equals the Epstein series where the series converges and is continuous at a real point
`0 < u`, `u ≠ 12`, has the value `leechEpsteinZeta u` there. -/
theorem leechEpsteinZeta_unique_real {Z : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z {v : ℂ | 0 < v.re ∧ 0 < v.im})
    (hser : ∀ v : ℂ, 12 < v.re → 0 < v.im → HasSum (leechEpsteinTerm v) (Z v))
    {u : ℝ} (hu0 : 0 < u) (hu12 : u ≠ 12) (hcont : ContinuousAt Z (u:ℂ)) :
    Z (u:ℂ) = leechEpsteinZeta (u:ℂ) := by
  let U : Set ℂ := {v | 0 < v.re ∧ 0 < v.im}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (r := 0)).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected
  have hreal {v : ℂ} (hv : v ∈ U) : v ≠ 12 := by
    intro h
    have hi : 0 < v.im := hv.2
    rw [h] at hi
    norm_num at hi
  have hf : AnalyticOnNhd ℂ Z U := hZ.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ leechEpsteinZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro v hv
    exact (leechEpsteinZeta_differentiableAt hv.1 (hreal hv)).differentiableWithinAt
  have hopen : IsOpen {v : ℂ | 12 < v.re ∧ 0 < v.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hbase : ((13 : ℂ)+Complex.I) ∈ {v : ℂ | 12 < v.re ∧ 0 < v.im} := by
    show 12 < ((13 : ℂ)+Complex.I).re ∧ 0 < ((13 : ℂ)+Complex.I).im
    constructor <;> norm_num
  have hfg : Z =ᶠ[𝓝 ((13 : ℂ)+Complex.I)] leechEpsteinZeta := by
    filter_upwards [hopen.mem_nhds hbase] with v hv
    exact (hser v hv.1 hv.2).unique (leechEpsteinZeta_hasSum hv.1)
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc
    (show 0 < ((13 : ℂ)+Complex.I).re ∧ 0 < ((13 : ℂ)+Complex.I).im by
      constructor <;> norm_num) hfg
  have ht : Tendsto (fun ε : ℝ => (u : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hε |>.mul_const Complex.I)
  have hu12' : (u:ℂ) ≠ 12 := by
    intro h
    have : u = 12 := by exact_mod_cast h
    exact hu12 this
  apply tendsto_nhds_unique_of_eventuallyEq (hcont.tendsto.comp ht)
    ((leechEpsteinZeta_differentiableAt (u := (u:ℂ)) (by simpa using hu0)
      hu12').continuousAt.tendsto.comp ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply heq
  have hε0 : 0 < ε := hε
  show 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).re ∧ 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).im
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
  exact ⟨hu0, hε0⟩

/-- The sharp lower bound of the S²⁴ Riesz energy with the Epstein coefficient, in the original
ordered-pair normalization, under all-scale Leech contact certificates. -/
theorem sphere24_riesz_sharp_lower_epstein
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) := by
  rw [← sphereRieszCoefficient24_eq_epstein hs hs24]
  exact sphere24_riesz_sharp_lower_conjecture_form hG24 hs hs24

end SphericalRiesz
