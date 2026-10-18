import Riesz.SphereGaussianSchwartzProfile8
import Riesz.E8ThetaTransform

/-! CKMRV-shaped sharp Gaussian certificates for the actual E8 lattice.

`E8GaussianContactCertificate8 β f` is the shape of the auxiliary functions of
Cohn–Kumar–Miller–Radchenko–Viazovska (Annals 2022, Lemma 6.2): a real Schwartz
function below `exp(-π β ‖x‖²)`, with real nonnegative Fourier transform, touching
the Gaussian at every nonzero E8 vector and with Fourier transform vanishing there.

Proved here, with no deep input:
* Poisson summation over the self-dual covolume-one E8 lattice turns one certificate
  into the value identity `Re 𝓕f(0) - Re f(0) = Θ_E8(β) - 1`;
* the reciprocal map `f ↦ g_β - β⁻⁴ 𝓕f` turns a certificate at `β⁻¹` into one at `β`
  (`𝓕 g_β = β⁻⁴ g_{β⁻¹}`, `𝓕 (𝓕 f) = f ∘ neg`), so certificates for `β ≥ 1`
  (or for `β ≤ 1`) already give every `β > 0`;
* hence `S8s4Target` follows from certificates on one side of `β = 1`.

The existence of certificates is NOT proved here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace SphericalRiesz

/-- The CKMRV-shaped sharp Gaussian certificate at parameter `β`. -/
structure E8GaussianContactCertificate8 (β : ℝ) (f : 𝓢(E8Ambient, ℂ)) : Prop where
  real : ∀ x, (f x).im = 0
  fourier_real : ∀ ξ, ((𝓕 f) ξ).im = 0
  fourier_nonneg : ∀ ξ, 0 ≤ ((𝓕 f) ξ).re
  minorant : ∀ x, (f x).re ≤ Real.exp (-(Real.pi*β*‖x‖^2))
  contact : ∀ v ∈ e8Lattice, v ≠ 0 → (f v).re = Real.exp (-(Real.pi*β*‖v‖^2))
  fourier_zero : ∀ v ∈ e8Lattice, v ≠ 0 → (𝓕 f) v = 0

theorem E8GaussianContactCertificate8.apply_eq {β : ℝ} {f : 𝓢(E8Ambient, ℂ)}
    (h : E8GaussianContactCertificate8 β f) {v : E8Ambient} (hv : v ∈ e8Lattice)
    (hv0 : v ≠ 0) : f v = (Real.exp (-(Real.pi*β*‖v‖^2)) : ℂ) := by
  apply Complex.ext
  · rw [h.contact v hv hv0, Complex.ofReal_re]
  · rw [h.real v, Complex.ofReal_im]

/-- The real Gaussian sum over the lattice subtype has sum `Θ_E8(β)`. -/
theorem e8LatticeGaussian_hasSum {β : ℝ} (hβ : 0 < β) :
    HasSum (fun x : e8Lattice => ((Real.exp (-(Real.pi*β*‖(x : E8Ambient)‖^2)) : ℝ) : ℂ))
      (e8GaussianThetaReal8 β : ℂ) := by
  rw [Complex.hasSum_ofReal]
  rw [← e8LatticeEquiv.toEquiv.hasSum_iff]
  apply (e8GaussianThetaReal8_hasSum hβ).congr_fun
  intro z
  change Real.exp (-(Real.pi*β*‖(e8LatticeEquiv z : E8Ambient)‖^2)) = _
  rw [e8LatticeEquiv_coe]
  congr 1
  ring

/-- Poisson summation: the contact and Fourier-zero conditions force the sharp value. -/
theorem E8GaussianContactCertificate8.value {β : ℝ} (hβ : 0 < β) {f : 𝓢(E8Ambient, ℂ)}
    (h : E8GaussianContactCertificate8 β f) :
    ((𝓕 f) 0).re-(f 0).re = e8GaussianThetaReal8 β-1 := by
  classical
  have hp := SchwartzMap.poissonSummation_lattice (L := e8Lattice) f 0
  have hd : SchwartzMap.dualLattice e8Lattice = e8Lattice := e8Lattice_selfDual
  rw [hd] at hp
  have hp' : (∑' x : e8Lattice, f x) = ∑' m : e8Lattice, 𝓕 (fun x : E8Ambient => f x) m := by
    simpa [e8Lattice_covolume] using hp
  have hrhs : (∑' m : e8Lattice, 𝓕 (fun x : E8Ambient => f x) m) = (𝓕 f) 0 := by
    rw [tsum_eq_single (0 : e8Lattice)]
    · rfl
    · intro m hm
      have hm0 : (m : E8Ambient) ≠ 0 := by
        intro h0
        exact hm (Subtype.ext h0)
      exact h.fourier_zero m m.property hm0
  let ψ : e8Lattice → ℂ := fun x => ((Real.exp (-(Real.pi*β*‖(x : E8Ambient)‖^2)) : ℝ) : ℂ)
  have hψ : HasSum ψ (e8GaussianThetaReal8 β : ℂ) := e8LatticeGaussian_hasSum hβ
  have hupd := hψ.update (0 : e8Lattice) (f 0)
  have hfun : Function.update ψ (0 : e8Lattice) (f 0) = fun x : e8Lattice => f x := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [Function.update_of_ne hx]
      have hx0 : (x : E8Ambient) ≠ 0 := by
        intro h0
        exact hx (Subtype.ext h0)
      exact (h.apply_eq x.property hx0).symm
  rw [hfun] at hupd
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  rw [hupd.tsum_eq, hrhs, hψ0] at hp'
  have hre := congrArg Complex.re hp'
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith

/-- The Gaussian `exp(-π β ‖x‖²)` as an actual Schwartz map. -/
def e8GaussianSchwartz8 (β : ℝ) (hβ : 0 < β) : 𝓢(E8Ambient, ℂ) :=
  e8ThetaSchwartzKernel ((β : ℂ)*Complex.I) (by simpa using hβ)

theorem e8GaussianSchwartz8_apply {β : ℝ} (hβ : 0 < β) (x : E8Ambient) :
    e8GaussianSchwartz8 β hβ x = (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) := by
  rw [e8GaussianSchwartz8, e8ThetaSchwartzKernel_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `𝓕 g_β = β⁻⁴ g_{β⁻¹}` in dimension eight. -/
theorem e8GaussianSchwartz8_fourier {β : ℝ} (hβ : 0 < β) (ξ : E8Ambient) :
    (𝓕 (e8GaussianSchwartz8 β hβ)) ξ =
      (((β^4)⁻¹ : ℝ) : ℂ) * (Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) := by
  have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  set τ : ℂ := Complex.I*((β⁻¹ : ℝ) : ℂ) with hτdef
  have hτ : 0 < τ.im := by simpa [hτdef] using inv_pos.mpr hβ
  have hS : -1/τ = (β : ℂ)*Complex.I := by
    rw [hτdef]
    push_cast
    field_simp
    rw [Complex.I_sq]
  have hf : (fun x : E8Ambient => e8GaussianSchwartz8 β hβ x) = e8ThetaKernel (-1/τ) := by
    rw [hS]
    exact e8ThetaSchwartzKernel_eq _ _
  change 𝓕 (fun x : E8Ambient => e8GaussianSchwartz8 β hβ x) ξ = _
  rw [hf, e8ThetaKernel_fourier_S hτ ξ]
  unfold e8ThetaKernel
  rw [Complex.ofReal_exp]
  have hpow : τ^4 = (((β^4)⁻¹ : ℝ) : ℂ) := by
    rw [hτdef]
    push_cast
    rw [mul_pow, Complex.I_pow_four, one_mul, inv_pow]
  rw [hpow]
  congr 2
  rw [hτdef]
  push_cast
  have hI : Complex.I*Complex.I = -1 := by rw [← sq, Complex.I_sq]
  linear_combination ((Real.pi : ℂ)*((‖ξ‖ : ℂ))^2*(β : ℂ)⁻¹)*hI

/-- `𝓕 (𝓕 f) ξ = f (-ξ)` for Schwartz maps. -/
theorem e8Schwartz_fourier_fourier (f : 𝓢(E8Ambient, ℂ)) (ξ : E8Ambient) :
    (𝓕 (𝓕 f)) ξ = f (-ξ) := by
  have h0 : 𝓕⁻ (𝓕 f : 𝓢(E8Ambient, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h : (𝓕⁻ (𝓕 f : 𝓢(E8Ambient, ℂ))) (-ξ) = f (-ξ) := by rw [h0]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]
  rfl

/-- The reciprocal certificate `g_β - β⁻⁴ 𝓕 f`. -/
def e8ReciprocalCertificate8 (β : ℝ) (hβ : 0 < β) (f : 𝓢(E8Ambient, ℂ)) :
    𝓢(E8Ambient, ℂ) :=
  e8GaussianSchwartz8 β hβ - (((β^4)⁻¹ : ℝ) : ℂ) • 𝓕 f

theorem e8ReciprocalCertificate8_apply {β : ℝ} (hβ : 0 < β) (f : 𝓢(E8Ambient, ℂ))
    (x : E8Ambient) :
    e8ReciprocalCertificate8 β hβ f x =
      (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) - (((β^4)⁻¹ : ℝ) : ℂ) * (𝓕 f) x := by
  rw [e8ReciprocalCertificate8, sub_apply, smul_apply, e8GaussianSchwartz8_apply, smul_eq_mul]

theorem e8ReciprocalCertificate8_fourier {β : ℝ} (hβ : 0 < β) (f : 𝓢(E8Ambient, ℂ))
    (ξ : E8Ambient) :
    (𝓕 (e8ReciprocalCertificate8 β hβ f)) ξ =
      (((β^4)⁻¹ : ℝ) : ℂ) * ((Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) - f (-ξ)) := by
  have hlin : 𝓕 (e8ReciprocalCertificate8 β hβ f) =
      𝓕 (e8GaussianSchwartz8 β hβ) - (((β^4)⁻¹ : ℝ) : ℂ) • 𝓕 (𝓕 f) := by
    change SchwartzMap.fourierTransformCLM ℂ
        (e8GaussianSchwartz8 β hβ - (((β^4)⁻¹ : ℝ) : ℂ) • 𝓕 f) =
      SchwartzMap.fourierTransformCLM ℂ (e8GaussianSchwartz8 β hβ) -
        (((β^4)⁻¹ : ℝ) : ℂ) • SchwartzMap.fourierTransformCLM ℂ (𝓕 f)
    rw [map_sub, map_smul]
  rw [hlin, sub_apply, smul_apply, e8GaussianSchwartz8_fourier, e8Schwartz_fourier_fourier,
    smul_eq_mul]
  ring

/-- Real and imaginary parts of `a - c z` for real `a`, `c`. -/
theorem e8_real_sub_mul_parts (a c : ℝ) (z : ℂ) :
    ((a : ℂ) - (c : ℂ)*z).re = a - c*z.re ∧ ((a : ℂ) - (c : ℂ)*z).im = -(c*z.im) := by
  constructor
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, zero_sub]

/-- Real and imaginary parts of `c (a - z)` for real `a`, `c`. -/
theorem e8_real_mul_sub_parts (a c : ℝ) (z : ℂ) :
    ((c : ℂ)*((a : ℂ) - z)).re = c*(a - z.re) ∧ ((c : ℂ)*((a : ℂ) - z)).im = -(c*z.im) := by
  constructor
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub]
    ring

/-- A certificate at `β⁻¹` gives a certificate at `β`. -/
theorem E8GaussianContactCertificate8.reciprocal {β : ℝ} (hβ : 0 < β)
    {f : 𝓢(E8Ambient, ℂ)} (h : E8GaussianContactCertificate8 β⁻¹ f) :
    E8GaussianContactCertificate8 β (e8ReciprocalCertificate8 β hβ f) := by
  have hc : 0 < (β^4)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [e8ReciprocalCertificate8_apply, (e8_real_sub_mul_parts _ _ _).2, h.fourier_real x,
      mul_zero, neg_zero]
  · intro ξ
    rw [e8ReciprocalCertificate8_fourier, (e8_real_mul_sub_parts _ _ _).2, h.real (-ξ),
      mul_zero, neg_zero]
  · intro ξ
    rw [e8ReciprocalCertificate8_fourier, (e8_real_mul_sub_parts _ _ _).1]
    have hm := h.minorant (-ξ)
    rw [norm_neg] at hm
    exact mul_nonneg hc.le (by linarith)
  · intro x
    rw [e8ReciprocalCertificate8_apply, (e8_real_sub_mul_parts _ _ _).1]
    have := mul_nonneg hc.le (h.fourier_nonneg x)
    linarith
  · intro v hv hv0
    rw [e8ReciprocalCertificate8_apply, h.fourier_zero v hv hv0, mul_zero, sub_zero,
      Complex.ofReal_re]
  · intro v hv hv0
    have hnv : -v ∈ e8Lattice := e8Lattice.neg_mem hv
    have hnv0 : -v ≠ 0 := neg_ne_zero.mpr hv0
    rw [e8ReciprocalCertificate8_fourier, h.apply_eq hnv hnv0, norm_neg, sub_self, mul_zero]

/-- Certificates on `β ≥ 1` give certificates for every `β > 0`. -/
theorem e8GaussianContact_all_of_ge_one
    (h : ∀ β : ℝ, 1 ≤ β → ∃ f, E8GaussianContactCertificate8 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, E8GaussianContactCertificate8 β f := by
  intro β hβ
  rcases le_or_gt 1 β with h1 | h1
  · exact h β h1
  · obtain ⟨f, hf⟩ := h β⁻¹ ((one_le_inv₀ hβ).mpr h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- Certificates on `0 < β ≤ 1` give certificates for every `β > 0`. -/
theorem e8GaussianContact_all_of_le_one
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ f, E8GaussianContactCertificate8 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, E8GaussianContactCertificate8 β f := by
  intro β hβ
  rcases le_or_gt β 1 with h1 | h1
  · exact h β hβ h1
  · obtain ⟨f, hf⟩ := h β⁻¹ (inv_pos.mpr hβ) (inv_le_one_of_one_le₀ h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- The contact certificates imply the project's sharp Schwartz input. -/
theorem e8SharpGaussianSchwartzInput8_of_contact
    (h : ∀ β : ℝ, 0 < β → ∃ f, E8GaussianContactCertificate8 β f) :
    E8SharpGaussianSchwartzInput8 := by
  intro β hβ
  obtain ⟨f, hf⟩ := h β hβ
  refine ⟨f, hf.fourier_nonneg, hf.fourier_real, ?_, hf.value hβ⟩
  intro z
  exact hf.minorant z

/-- The main target from CKMRV-shaped certificates for `β ≥ 1` only. -/
theorem S8s4Target_of_contact_ge_one
    (h : ∀ β : ℝ, 1 ≤ β → ∃ f, E8GaussianContactCertificate8 β f) : S8s4Target :=
  S8s4Target_of_schwartz_input
    (e8SharpGaussianSchwartzInput8_of_contact (e8GaussianContact_all_of_ge_one h))

/-- The main target from CKMRV-shaped certificates for `0 < β ≤ 1` only. -/
theorem S8s4Target_of_contact_le_one
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ f, E8GaussianContactCertificate8 β f) : S8s4Target :=
  S8s4Target_of_schwartz_input
    (e8SharpGaussianSchwartzInput8_of_contact (e8GaussianContact_all_of_le_one h))

#print axioms E8GaussianContactCertificate8.apply_eq
#print axioms e8LatticeGaussian_hasSum
#print axioms E8GaussianContactCertificate8.value
#print axioms e8GaussianSchwartz8_apply
#print axioms e8GaussianSchwartz8_fourier
#print axioms e8Schwartz_fourier_fourier
#print axioms e8ReciprocalCertificate8_apply
#print axioms e8ReciprocalCertificate8_fourier
#print axioms e8_real_sub_mul_parts
#print axioms e8_real_mul_sub_parts
#print axioms E8GaussianContactCertificate8.reciprocal
#print axioms e8GaussianContact_all_of_ge_one
#print axioms e8GaussianContact_all_of_le_one
#print axioms e8SharpGaussianSchwartzInput8_of_contact
#print axioms S8s4Target_of_contact_ge_one
#print axioms S8s4Target_of_contact_le_one

end SphericalRiesz
