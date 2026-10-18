import Riesz.E8SchwartzInputOff8
import Riesz.E8CKMRVContract8

/-! From a Gaussian certificate with the lattice-energy calibration to the Gaussian input of `S⁸`.

The kernel inequality of `E8` (vendored development, library `E8Leech`) gives, for every scale
`α > 0`, `α ≠ π`, a Schwartz function `f` on `ℝ⁸` with real Fourier transform, nonnegative almost
everywhere, with `Re f(v) ≤ exp(-α |v|²)` for `v ≠ 0`, and with the calibration
`Σ_{y ∈ Λ, y ≠ 0} exp(-α |y|²) = Re 𝓕f(0) - Re f(0)`, the sum being an extended-real sum over the
`E8` set `Λ`.  This file states those four facts in the terms of Mathlib alone and derives the
four conditions of `E8SharpGaussianSchwartzInputOff8` at the scale `β = α/π`:

* a continuous function that is nonnegative almost everywhere is nonnegative everywhere;
* the minorant extends to the origin by continuity;
* the lattice sum without the origin is the theta value minus one. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace SphericalRiesz

/-- The Gaussian sum over the nonzero points of the `E8` lattice is `Θ(α/π) - 1`. -/
theorem e8Lattice_gaussian_hasSum_ne_zero {α : ℝ} (hα : 0 < α) :
    HasSum (fun y : e8Lattice => if (y : E8Ambient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : E8Ambient)‖^2)) (e8GaussianThetaReal8 (α/Real.pi)-1) := by
  have hβ : 0 < α/Real.pi := div_pos hα Real.pi_pos
  have h := e8GaussianThetaReal8_hasSum hβ
  have h1 : HasSum (fun z : Fin 8 → ℤ => if z = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have h2 := h.sub h1
  have hfun : (fun y : e8Lattice => if (y : E8Ambient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : E8Ambient)‖^2)) ∘ e8LatticeEquiv.toEquiv =
      fun z : Fin 8 → ℤ => Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*(α/Real.pi))-
        (if z = 0 then (1 : ℝ) else 0) := by
    funext z
    have hcoe : ((e8LatticeEquiv.toEquiv z : e8Lattice) : E8Ambient) = e8EuclideanPoint z :=
      e8LatticeEquiv_coe z
    simp only [Function.comp_apply, hcoe]
    have he : -Real.pi*‖e8EuclideanPoint z‖^2*(α/Real.pi) = -α*‖e8EuclideanPoint z‖^2 := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    rw [he]
    by_cases hz : z = 0
    · subst hz
      simp
    · have hne : e8EuclideanPoint z ≠ 0 := fun h0 =>
        hz (e8EuclideanPoint_injective (h0.trans e8EuclideanPoint_zero.symm))
      simp [hz, hne]
  have h3 : HasSum ((fun y : e8Lattice => if (y : E8Ambient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : E8Ambient)‖^2)) ∘ e8LatticeEquiv.toEquiv)
      (e8GaussianThetaReal8 (α/Real.pi)-1) := by
    rw [hfun]
    exact h2
  exact (Equiv.hasSum_iff e8LatticeEquiv.toEquiv).mp h3

/-- The extended-real Gaussian energy of a set that equals the `E8` lattice. -/
theorem e8_gaussian_lattice_energy_toReal {Λ : Set E8Ambient}
    (hΛ : Λ = (e8Lattice : Set E8Ambient)) {α : ℝ} (hα : 0 < α) :
    (∑' y : Λ, if (y : E8Ambient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : E8Ambient)-y‖^2))).toReal =
      e8GaussianThetaReal8 (α/Real.pi)-1 := by
  subst hΛ
  have hs := e8Lattice_gaussian_hasSum_ne_zero hα
  have hg : ∀ y : e8Lattice, 0 ≤ (if (y : E8Ambient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : E8Ambient)‖^2)) := by
    intro y
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hterm : (fun y : e8Lattice => if (y : E8Ambient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : E8Ambient)-y‖^2))) =
      fun y : e8Lattice => ENNReal.ofReal (if (y : E8Ambient) = 0 then (0 : ℝ)
        else Real.exp (-α*‖(y : E8Ambient)‖^2)) := by
    funext y
    split_ifs
    · exact ENNReal.ofReal_zero.symm
    · rw [zero_sub, norm_neg]
  change (∑' y : e8Lattice, if (y : E8Ambient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : E8Ambient)-y‖^2))).toReal = _
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg hg hs.summable,
    ENNReal.toReal_ofReal (tsum_nonneg hg), hs.tsum_eq]

/-- A continuous real function that is nonnegative almost everywhere on `ℝ⁸` is nonnegative. -/
theorem e8_nonneg_of_ae_nonneg {g : E8Ambient → ℝ} (hg : Continuous g)
    (h : ∀ᵐ ξ ∂(volume : Measure E8Ambient), 0 ≤ g ξ) (ξ : E8Ambient) : 0 ≤ g ξ := by
  by_contra hξ
  rw [not_le] at hξ
  have hopen : IsOpen {x : E8Ambient | g x < 0} := isOpen_lt hg continuous_const
  have hpos : 0 < (volume : Measure E8Ambient) {x : E8Ambient | g x < 0} :=
    hopen.measure_pos volume ⟨ξ, hξ⟩
  have hzero : (volume : Measure E8Ambient) {x : E8Ambient | g x < 0} = 0 := by
    have h' := ae_iff.mp h
    have hset : {x : E8Ambient | ¬ 0 ≤ g x} = {x : E8Ambient | g x < 0} := by
      ext x
      exact not_le
    rw [hset] at h'
    exact h'
  exact hpos.ne' hzero

/-- The four conditions of the Gaussian input of `S⁸` at the scale `β = α/π`, from a Schwartz
function with the properties of a Gaussian certificate for a set equal to the `E8` lattice. -/
theorem e8SchwartzInput_of_gaussian_certificate {Λ : Set E8Ambient}
    (hΛ : Λ = (e8Lattice : Set E8Ambient)) {α : ℝ} (hα : 0 < α) (f : 𝓢(E8Ambient, ℂ))
    (hreal : ∀ ξ, ((𝓕 f) ξ).im = 0)
    (hnn : ∀ᵐ ξ ∂(volume : Measure E8Ambient), 0 ≤ ((𝓕 f) ξ).re)
    (hmin : ∀ v : E8Ambient, v ≠ 0 → (f v).re ≤ Real.exp (-α*‖v‖^2))
    (hcal : (∑' y : Λ, if (y : E8Ambient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : E8Ambient)-y‖^2))).toReal =
        ((𝓕 f) (0 : E8Ambient)).re-(f 0).re) :
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧ (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = e8GaussianThetaReal8 (α/Real.pi)-1 := by
  have hπ : Real.pi*(α/Real.pi) = α := by
    have h0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  refine ⟨?_, hreal, ?_, ?_⟩
  · exact e8_nonneg_of_ae_nonneg (Complex.continuous_re.comp (𝓕 f).continuous) hnn
  · have hclosed : IsClosed {z : E8Ambient | (f z).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖z‖^2))} :=
      isClosed_le (Complex.continuous_re.comp f.continuous) (by fun_prop)
    intro z
    refine e8_mem_of_isClosed_of_ne_zero hclosed (fun v hv => ?_) z
    change (f v).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖v‖^2))
    rw [hπ]
    have := hmin v hv
    rwa [neg_mul] at this
  · rw [← hcal]
    exact e8_gaussian_lattice_energy_toReal hΛ hα

end SphericalRiesz
