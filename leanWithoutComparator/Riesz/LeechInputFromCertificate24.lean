import Riesz.LeechSchwartzInputOff24

/-! From a Gaussian certificate with the lattice-energy calibration to the Gaussian input of `S²⁴`.

The kernel inequalities of the Leech lattice (vendored development, library `E8Leech`) give,
for every scale `α > 0`, `α ≠ π`, a Schwartz function `f` on `ℝ²⁴` with real Fourier transform,
nonnegative almost everywhere, with `Re f(v) ≤ exp(-α |v|²)` for `v ≠ 0`, and with the
calibration `Σ_{y ∈ Λ, y ≠ 0} exp(-α |y|²) = Re 𝓕f(0) - Re f(0)`, the sum being an
extended-real sum over the Leech set `Λ`.  This file states those four facts in the terms of
Mathlib alone and derives the four conditions of `LeechSharpGaussianSchwartzInputOff24` at the
scale `β = α/π` (the dimension-24 form of `Riesz/E8InputFromCertificate8.lean`).

The Leech set of the vendored development is not the lattice `leechLattice` of this library but
its image under a relabelling of the coordinates (`Riesz/LeechModelRelabel24.lean`).  The
Gaussian sum only sees the norms of the lattice points, so the statements here take the set `Λ`
as the image of `leechLattice` under an arbitrary linear isometry `σ` of `ℝ²⁴`. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace SphericalRiesz

/-- The Gaussian sum over the nonzero points of the Leech lattice is `Θ(α/π) - 1`. -/
theorem leechLattice_gaussian_hasSum_ne_zero {α : ℝ} (hα : 0 < α) :
    HasSum (fun y : leechLattice => if (y : LeechAmbient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : LeechAmbient)‖^2)) (leechGaussianThetaReal24 (α/Real.pi)-1) := by
  have hβ : 0 < α/Real.pi := div_pos hα Real.pi_pos
  have h : HasSum (fun x : leechLattice =>
      Real.exp (-(Real.pi*(α/Real.pi)*‖(x : LeechAmbient)‖^2)))
      (leechGaussianThetaReal24 (α/Real.pi)) :=
    Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hβ)
  have h1 : HasSum (fun x : leechLattice => if x = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have h2 := h.sub h1
  have hπ : Real.pi*(α/Real.pi) = α := by
    have h0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  have hfun : (fun y : leechLattice => if (y : LeechAmbient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : LeechAmbient)‖^2)) =
      fun x : leechLattice => Real.exp (-(Real.pi*(α/Real.pi)*‖(x : LeechAmbient)‖^2))-
        (if x = 0 then (1 : ℝ) else 0) := by
    funext y
    rw [hπ]
    by_cases hy : y = 0
    · subst hy
      simp
    · have hne : (y : LeechAmbient) ≠ 0 := fun h0 => hy (Subtype.ext h0)
      simp [hy, hne]
  rw [hfun]
  exact h2

/-- The extended-real Gaussian energy of an isometric copy of the Leech lattice. -/
theorem leech_gaussian_lattice_energy_toReal {Λ : Set LeechAmbient}
    (σ : LeechAmbient ≃ₗᵢ[ℝ] LeechAmbient)
    (hΛ : Λ = σ '' (leechLattice : Set LeechAmbient)) {α : ℝ} (hα : 0 < α) :
    (∑' y : Λ, if (y : LeechAmbient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : LeechAmbient)-y‖^2))).toReal =
      leechGaussianThetaReal24 (α/Real.pi)-1 := by
  subst hΛ
  have hs := leechLattice_gaussian_hasSum_ne_zero hα
  have hg : ∀ y : leechLattice, 0 ≤ (if (y : LeechAmbient) = 0 then (0 : ℝ)
      else Real.exp (-α*‖(y : LeechAmbient)‖^2)) := by
    intro y
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hre : (∑' y : σ '' (leechLattice : Set LeechAmbient),
      if (y : LeechAmbient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : LeechAmbient)-y‖^2))) =
      ∑' x : leechLattice, ENNReal.ofReal (if (x : LeechAmbient) = 0 then (0 : ℝ)
        else Real.exp (-α*‖(x : LeechAmbient)‖^2)) := by
    refine ((Equiv.Set.image σ (leechLattice : Set LeechAmbient) σ.injective).tsum_eq
      (fun y : σ '' (leechLattice : Set LeechAmbient) =>
        if (y : LeechAmbient) = 0 then (0 : ℝ≥0∞)
        else ENNReal.ofReal (Real.exp (-α*‖(0 : LeechAmbient)-y‖^2)))).symm.trans ?_
    change (∑' x : leechLattice, if σ (x : LeechAmbient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : LeechAmbient)-σ (x : LeechAmbient)‖^2))) = _
    refine tsum_congr fun x => ?_
    have h0 : σ (x : LeechAmbient) = 0 ↔ (x : LeechAmbient) = 0 := σ.map_eq_zero_iff
    by_cases hx : (x : LeechAmbient) = 0
    · rw [ite_eq_left (h0.mpr hx), ite_eq_left hx, ENNReal.ofReal_zero]
    · rw [ite_eq_right (fun h => hx (h0.mp h)), ite_eq_right hx, zero_sub, norm_neg, σ.norm_map]
  rw [hre, ← ENNReal.ofReal_tsum_of_nonneg hg hs.summable,
    ENNReal.toReal_ofReal (tsum_nonneg hg), hs.tsum_eq]

/-- A continuous real function that is nonnegative almost everywhere on `ℝ²⁴` is nonnegative. -/
theorem leech_nonneg_of_ae_nonneg {g : LeechAmbient → ℝ} (hg : Continuous g)
    (h : ∀ᵐ ξ ∂(volume : Measure LeechAmbient), 0 ≤ g ξ) (ξ : LeechAmbient) : 0 ≤ g ξ := by
  by_contra hξ
  rw [not_le] at hξ
  have hopen : IsOpen {x : LeechAmbient | g x < 0} := isOpen_lt hg continuous_const
  have hpos : 0 < (volume : Measure LeechAmbient) {x : LeechAmbient | g x < 0} :=
    hopen.measure_pos volume ⟨ξ, hξ⟩
  have hzero : (volume : Measure LeechAmbient) {x : LeechAmbient | g x < 0} = 0 := by
    have h' := ae_iff.mp h
    have hset : {x : LeechAmbient | ¬ 0 ≤ g x} = {x : LeechAmbient | g x < 0} := by
      ext x
      exact not_le
    rw [hset] at h'
    exact h'
  exact hpos.ne' hzero

/-- A closed set that contains every nonzero point of `ℝ²⁴` is everything. -/
theorem leech_mem_of_isClosed_of_ne_zero {S : Set LeechAmbient} (hS : IsClosed S)
    (h : ∀ x : LeechAmbient, x ≠ 0 → x ∈ S) (y : LeechAmbient) : y ∈ S := by
  have hsub : ({0}ᶜ : Set LeechAmbient) ⊆ S := fun x hx => h x hx
  have hcl : closure ({0}ᶜ : Set LeechAmbient) ⊆ S := hS.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : LeechAmbient)).closure_eq] at hcl
  exact hcl (Set.mem_univ y)

/-- The four conditions of the Gaussian input of `S²⁴` at the scale `β = α/π`, from a Schwartz
function with the properties of a Gaussian certificate for an isometric copy of the Leech
lattice. -/
theorem leechSchwartzInput_of_gaussian_certificate {Λ : Set LeechAmbient}
    (σ : LeechAmbient ≃ₗᵢ[ℝ] LeechAmbient)
    (hΛ : Λ = σ '' (leechLattice : Set LeechAmbient)) {α : ℝ} (hα : 0 < α)
    (f : 𝓢(LeechAmbient, ℂ))
    (hreal : ∀ ξ, ((𝓕 f) ξ).im = 0)
    (hnn : ∀ᵐ ξ ∂(volume : Measure LeechAmbient), 0 ≤ ((𝓕 f) ξ).re)
    (hmin : ∀ v : LeechAmbient, v ≠ 0 → (f v).re ≤ Real.exp (-α*‖v‖^2))
    (hcal : (∑' y : Λ, if (y : LeechAmbient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-α*‖(0 : LeechAmbient)-y‖^2))).toReal =
        ((𝓕 f) (0 : LeechAmbient)).re-(f 0).re) :
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧ (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = leechGaussianThetaReal24 (α/Real.pi)-1 := by
  have hπ : Real.pi*(α/Real.pi) = α := by
    have h0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  refine ⟨?_, hreal, ?_, ?_⟩
  · exact leech_nonneg_of_ae_nonneg (Complex.continuous_re.comp (𝓕 f).continuous) hnn
  · have hclosed : IsClosed {z : LeechAmbient |
        (f z).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖z‖^2))} :=
      isClosed_le (Complex.continuous_re.comp f.continuous) (by fun_prop)
    intro z
    refine leech_mem_of_isClosed_of_ne_zero hclosed (fun v hv => ?_) z
    change (f v).re ≤ Real.exp (-(Real.pi*(α/Real.pi)*‖v‖^2))
    rw [hπ]
    have := hmin v hv
    rwa [neg_mul] at this
  · rw [← hcal]
    exact leech_gaussian_lattice_energy_toReal σ hΛ hα

end SphericalRiesz
