import Riesz.LeechTheta24
import Riesz.E8GaussianContact8
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # CKMRV-shaped sharp Gaussian certificates for the Leech lattice (stage P24-3)

`LeechGaussianContactCertificate24 β f` is the shape of the auxiliary functions of
Cohn–Kumar–Miller–Radchenko–Viazovska (Annals 2022, Lemma 6.2) in dimension `24`: a real
Schwartz function below `exp(-π β ‖x‖²)`, with real nonnegative Fourier transform, touching the
Gaussian at every nonzero Leech vector and with Fourier transform vanishing there. Proved here,
with no deep input:
* Poisson summation over the self-dual covolume-one Leech lattice turns one certificate into the
  value identity `Re 𝓕f(0) - Re f(0) = Θ_Λ(β) - 1`, `Θ_Λ(β) = Σ_{v ∈ Λ} exp(-π β |v|²)`;
* the reciprocal map `f ↦ g_β - β⁻¹² 𝓕f` (`𝓕 g_β = β⁻¹² g_{β⁻¹}` in dimension `24`) turns a
  certificate at `β⁻¹` into one at `β`, so certificates on one side of `β = 1` give all `β > 0`.
The existence of certificates is the CKMRV input (stage G24). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace SphericalRiesz

/-- The real Leech Gaussian theta sum `Σ_{v ∈ Λ} exp(-π β |v|²)`. -/
def leechGaussianThetaReal24 (β : ℝ) : ℝ :=
  ∑' x : leechLattice, Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2))

/-- The real Gaussian sum over the lattice has sum `Θ_Λ(β)`. -/
theorem leechLatticeGaussian_hasSum {β : ℝ} (hβ : 0 < β) :
    HasSum (fun x : leechLattice => ((Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ))
      (leechGaussianThetaReal24 β : ℂ) := by
  have hτ : 0 < ((β:ℂ)*Complex.I).im := by simpa using hβ
  have hs := leechLatticeThetaTerm_summable hτ
  have hterm : ∀ x : leechLattice, leechLatticeThetaTerm ((β:ℂ)*Complex.I) x =
      ((Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ) := by
    intro x
    unfold leechLatticeThetaTerm
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : leechLatticeThetaTerm ((β:ℂ)*Complex.I) = fun x : leechLattice =>
      ((Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ) := funext hterm
  have hs' : Summable (fun x : leechLattice =>
      ((Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ)) := by
    rw [← hfun]; exact hs
  have hr : Summable (fun x : leechLattice => Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2))) :=
    Complex.summable_ofReal.mp hs'
  rw [Complex.hasSum_ofReal]
  exact hr.hasSum

theorem leechGaussianThetaReal24_ge_one {β : ℝ} (hβ : 0 < β) : 1 ≤ leechGaussianThetaReal24 β := by
  have hs := (Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hβ)).summable
  have h0 : Real.exp (-(Real.pi*β*‖((0 : leechLattice) : LeechAmbient)‖^2)) = 1 := by simp
  calc (1:ℝ) = Real.exp (-(Real.pi*β*‖((0 : leechLattice) : LeechAmbient)‖^2)) := h0.symm
    _ ≤ leechGaussianThetaReal24 β :=
      hs.le_tsum (0 : leechLattice) (fun x _ => (Real.exp_pos _).le)

/-- The CKMRV-shaped sharp Gaussian certificate for the Leech lattice at parameter `β`. -/
structure LeechGaussianContactCertificate24 (β : ℝ) (f : 𝓢(LeechAmbient, ℂ)) : Prop where
  real : ∀ x, (f x).im = 0
  fourier_real : ∀ ξ, ((𝓕 f) ξ).im = 0
  fourier_nonneg : ∀ ξ, 0 ≤ ((𝓕 f) ξ).re
  minorant : ∀ x, (f x).re ≤ Real.exp (-(Real.pi*β*‖x‖^2))
  contact : ∀ v ∈ leechLattice, v ≠ 0 → (f v).re = Real.exp (-(Real.pi*β*‖v‖^2))
  fourier_zero : ∀ v ∈ leechLattice, v ≠ 0 → (𝓕 f) v = 0

theorem LeechGaussianContactCertificate24.apply_eq {β : ℝ} {f : 𝓢(LeechAmbient, ℂ)}
    (h : LeechGaussianContactCertificate24 β f) {v : LeechAmbient} (hv : v ∈ leechLattice)
    (hv0 : v ≠ 0) : f v = (Real.exp (-(Real.pi*β*‖v‖^2)) : ℂ) := by
  apply Complex.ext
  · rw [h.contact v hv hv0, Complex.ofReal_re]
  · rw [h.real v, Complex.ofReal_im]

/-- Poisson summation: the contact and Fourier-zero conditions force the sharp value. -/
theorem LeechGaussianContactCertificate24.value {β : ℝ} (hβ : 0 < β) {f : 𝓢(LeechAmbient, ℂ)}
    (h : LeechGaussianContactCertificate24 β f) :
    ((𝓕 f) 0).re-(f 0).re = leechGaussianThetaReal24 β-1 := by
  classical
  have hp := SchwartzMap.poissonSummation_lattice (L := leechLattice) f 0
  have hd : SchwartzMap.dualLattice leechLattice = leechLattice := leechLattice_selfDual
  rw [hd] at hp
  have hp' : (∑' x : leechLattice, f x) =
      ∑' m : leechLattice, 𝓕 (fun x : LeechAmbient => f x) m := by
    simpa [leechLattice_covolume] using hp
  have hrhs : (∑' m : leechLattice, 𝓕 (fun x : LeechAmbient => f x) m) = (𝓕 f) 0 := by
    rw [tsum_eq_single (0 : leechLattice)]
    · rfl
    · intro m hm
      have hm0 : (m : LeechAmbient) ≠ 0 := by
        intro h0
        exact hm (Subtype.ext h0)
      exact h.fourier_zero m m.property hm0
  let ψ : leechLattice → ℂ := fun x => ((Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ)
  have hψ : HasSum ψ (leechGaussianThetaReal24 β : ℂ) := leechLatticeGaussian_hasSum hβ
  have hupd := hψ.update (0 : leechLattice) (f 0)
  have hfun : Function.update ψ (0 : leechLattice) (f 0) = fun x : leechLattice => f x := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [Function.update_of_ne hx]
      have hx0 : (x : LeechAmbient) ≠ 0 := by
        intro h0
        exact hx (Subtype.ext h0)
      exact (h.apply_eq x.property hx0).symm
  rw [hfun] at hupd
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  rw [hupd.tsum_eq, hrhs, hψ0] at hp'
  have hre := congrArg Complex.re hp'
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith

/-- The Gaussian `exp(-π β ‖x‖²)` on `ℝ^24` as an actual Schwartz map. -/
def leechGaussianSchwartz24 (β : ℝ) (hβ : 0 < β) : 𝓢(LeechAmbient, ℂ) :=
  leechThetaSchwartzKernel ((β : ℂ)*Complex.I) (by simpa using hβ)

theorem leechGaussianSchwartz24_apply {β : ℝ} (hβ : 0 < β) (x : LeechAmbient) :
    leechGaussianSchwartz24 β hβ x = (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) := by
  rw [leechGaussianSchwartz24, leechThetaSchwartzKernel_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `𝓕 g_β = β⁻¹² g_{β⁻¹}` in dimension twenty-four. -/
theorem leechGaussianSchwartz24_fourier {β : ℝ} (hβ : 0 < β) (ξ : LeechAmbient) :
    (𝓕 (leechGaussianSchwartz24 β hβ)) ξ =
      (((β^12)⁻¹ : ℝ) : ℂ) * (Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) := by
  have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  set τ : ℂ := Complex.I*((β⁻¹ : ℝ) : ℂ) with hτdef
  have hτ : 0 < τ.im := by simpa [hτdef] using inv_pos.mpr hβ
  have hS : -1/τ = (β : ℂ)*Complex.I := by
    rw [hτdef]
    push_cast
    field_simp
    rw [Complex.I_sq]
  have hf : (fun x : LeechAmbient => leechGaussianSchwartz24 β hβ x) = leechThetaKernel (-1/τ) := by
    rw [hS]
    exact leechThetaSchwartzKernel_eq _ _
  change 𝓕 (fun x : LeechAmbient => leechGaussianSchwartz24 β hβ x) ξ = _
  rw [hf, leechThetaKernel_fourier_S hτ ξ]
  unfold leechThetaKernel
  rw [Complex.ofReal_exp]
  have hI12 : Complex.I^12 = 1 := by
    rw [show (12:ℕ) = 4*3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  have hpow : τ^12 = (((β^12)⁻¹ : ℝ) : ℂ) := by
    rw [hτdef]
    push_cast
    rw [mul_pow, hI12, one_mul, inv_pow]
  rw [hpow]
  congr 2
  rw [hτdef]
  push_cast
  have hI : Complex.I*Complex.I = -1 := by rw [← sq, Complex.I_sq]
  linear_combination ((Real.pi : ℂ)*((‖ξ‖ : ℂ))^2*(β : ℂ)⁻¹)*hI

/-- `𝓕 (𝓕 f) ξ = f (-ξ)` for Schwartz maps on `ℝ^24`. -/
theorem leechSchwartz_fourier_fourier (f : 𝓢(LeechAmbient, ℂ)) (ξ : LeechAmbient) :
    (𝓕 (𝓕 f)) ξ = f (-ξ) := by
  have h0 : 𝓕⁻ (𝓕 f : 𝓢(LeechAmbient, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h : (𝓕⁻ (𝓕 f : 𝓢(LeechAmbient, ℂ))) (-ξ) = f (-ξ) := by rw [h0]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]
  rfl

/-- The reciprocal certificate `g_β - β⁻¹² 𝓕 f`. -/
def leechReciprocalCertificate24 (β : ℝ) (hβ : 0 < β) (f : 𝓢(LeechAmbient, ℂ)) :
    𝓢(LeechAmbient, ℂ) :=
  leechGaussianSchwartz24 β hβ - (((β^12)⁻¹ : ℝ) : ℂ) • 𝓕 f

theorem leechReciprocalCertificate24_apply {β : ℝ} (hβ : 0 < β) (f : 𝓢(LeechAmbient, ℂ))
    (x : LeechAmbient) :
    leechReciprocalCertificate24 β hβ f x =
      (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) - (((β^12)⁻¹ : ℝ) : ℂ) * (𝓕 f) x := by
  rw [leechReciprocalCertificate24, sub_apply, smul_apply,
    leechGaussianSchwartz24_apply, smul_eq_mul]

theorem leechReciprocalCertificate24_fourier {β : ℝ} (hβ : 0 < β) (f : 𝓢(LeechAmbient, ℂ))
    (ξ : LeechAmbient) :
    (𝓕 (leechReciprocalCertificate24 β hβ f)) ξ =
      (((β^12)⁻¹ : ℝ) : ℂ) * ((Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) - f (-ξ)) := by
  have hlin : 𝓕 (leechReciprocalCertificate24 β hβ f) =
      𝓕 (leechGaussianSchwartz24 β hβ) - (((β^12)⁻¹ : ℝ) : ℂ) • 𝓕 (𝓕 f) := by
    change SchwartzMap.fourierTransformCLM ℂ
        (leechGaussianSchwartz24 β hβ - (((β^12)⁻¹ : ℝ) : ℂ) • 𝓕 f) =
      SchwartzMap.fourierTransformCLM ℂ (leechGaussianSchwartz24 β hβ) -
        (((β^12)⁻¹ : ℝ) : ℂ) • SchwartzMap.fourierTransformCLM ℂ (𝓕 f)
    rw [map_sub, map_smul]
  rw [hlin, sub_apply, smul_apply, leechGaussianSchwartz24_fourier,
    leechSchwartz_fourier_fourier, smul_eq_mul]
  ring

/-- A Leech certificate at `β⁻¹` gives one at `β`. -/
theorem LeechGaussianContactCertificate24.reciprocal {β : ℝ} (hβ : 0 < β)
    {f : 𝓢(LeechAmbient, ℂ)} (h : LeechGaussianContactCertificate24 β⁻¹ f) :
    LeechGaussianContactCertificate24 β (leechReciprocalCertificate24 β hβ f) := by
  have hc : 0 < (β^12)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [leechReciprocalCertificate24_apply, (e8_real_sub_mul_parts _ _ _).2, h.fourier_real x,
      mul_zero, neg_zero]
  · intro ξ
    rw [leechReciprocalCertificate24_fourier, (e8_real_mul_sub_parts _ _ _).2, h.real (-ξ),
      mul_zero, neg_zero]
  · intro ξ
    rw [leechReciprocalCertificate24_fourier, (e8_real_mul_sub_parts _ _ _).1]
    have hm := h.minorant (-ξ)
    rw [norm_neg] at hm
    exact mul_nonneg hc.le (by linarith)
  · intro x
    rw [leechReciprocalCertificate24_apply, (e8_real_sub_mul_parts _ _ _).1]
    have := mul_nonneg hc.le (h.fourier_nonneg x)
    linarith
  · intro v hv hv0
    rw [leechReciprocalCertificate24_apply, h.fourier_zero v hv hv0, mul_zero, sub_zero,
      Complex.ofReal_re]
  · intro v hv hv0
    have hnv : -v ∈ leechLattice := leechLattice.neg_mem hv
    have hnv0 : -v ≠ 0 := neg_ne_zero.mpr hv0
    rw [leechReciprocalCertificate24_fourier, h.apply_eq hnv hnv0, norm_neg, sub_self, mul_zero]

/-- Leech certificates on `β ≥ 1` give certificates for every `β > 0`. -/
theorem leechGaussianContact_all_of_ge_one
    (h : ∀ β : ℝ, 1 ≤ β → ∃ f, LeechGaussianContactCertificate24 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f := by
  intro β hβ
  rcases le_or_gt 1 β with h1 | h1
  · exact h β h1
  · obtain ⟨f, hf⟩ := h β⁻¹ ((one_le_inv₀ hβ).mpr h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- Leech certificates on `0 < β ≤ 1` give certificates for every `β > 0`. -/
theorem leechGaussianContact_all_of_le_one
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ f, LeechGaussianContactCertificate24 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f := by
  intro β hβ
  rcases le_or_gt β 1 with h1 | h1
  · exact h β hβ h1
  · obtain ⟨f, hf⟩ := h β⁻¹ (inv_pos.mpr hβ) (inv_le_one_of_one_le₀ h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- The real Leech theta function is continuous on `(0, ∞)` (locally uniform convergence). -/
theorem leechGaussianThetaReal24_continuousOn : ContinuousOn leechGaussianThetaReal24 (Set.Ioi 0) := by
  intro α hα
  have hα0 : (0:ℝ) < α := hα
  have hα2 : 0 < α/2 := half_pos hα0
  have hsum : Summable (fun x : leechLattice => Real.exp (-(Real.pi*(α/2)*‖(x : LeechAmbient)‖^2))) :=
    (Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hα2)).summable
  have hc : ContinuousOn leechGaussianThetaReal24 (Set.Ioi (α/2)) := by
    unfold leechGaussianThetaReal24
    refine continuousOn_tsum (fun x => by fun_prop) hsum ?_
    intro x β hβ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ ‖(x : LeechAmbient)‖^2 := sq_nonneg _
    have hβ' : α/2 < β := hβ
    have hprod := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hβ'.le)) h0
    nlinarith [hprod]
  exact (hc.continuousAt (isOpen_Ioi.mem_nhds (by linarith : α/2 < α))).continuousWithinAt

#print axioms leechGaussianThetaReal24_continuousOn
#print axioms leechLatticeGaussian_hasSum
#print axioms leechGaussianThetaReal24_ge_one
#print axioms LeechGaussianContactCertificate24.apply_eq
#print axioms LeechGaussianContactCertificate24.value
#print axioms leechGaussianSchwartz24_apply
#print axioms leechGaussianSchwartz24_fourier
#print axioms leechSchwartz_fourier_fourier
#print axioms leechReciprocalCertificate24_apply
#print axioms leechReciprocalCertificate24_fourier
#print axioms LeechGaussianContactCertificate24.reciprocal
#print axioms leechGaussianContact_all_of_ge_one
#print axioms leechGaussianContact_all_of_le_one

end SphericalRiesz
