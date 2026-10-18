import E8Leech.E8Calibration

/-!
# The Lemma 6.2 interface (P5c)

For a covolume-one lattice `L` such that `|x|²` is even on `L` and on `L^*` (`E8`, and the Leech
lattice once its evenness and self-duality are proved), a Schwartz function of the CKMRV shape is a
Gaussian certificate for `L`:
* `f(v) = e^{−α|v|²} + 4 sin²(π|v|²/2) J(v)` with `J ≤ 0` (`v ≠ 0`);
* `f̂(ξ) = 4 sin²(π|ξ|²/2) Ĵ(ξ)` with `Ĵ ≥ 0` (`ξ ≠ 0`).

For `f = F(iα/π, ·)` one takes `J(v) = ∫₀^∞ 𝒦(iα/π, it) e^{−π|v|²t} dt` and
`Ĵ(ξ) = ∫₀^∞ 𝒦̂(iα/π, it) e^{−π|ξ|²t} dt`. The signs are the kernel inequality (6.4)(1) and the
`τ`-side relation `𝒦(iy, it) = −y^{−4} 𝒦̂(i/y, it)`. The Fourier formula is the identity (**).
`f̂(0)` is real by continuity, and the calibration comes from Poisson summation.
-/

noncomputable section

namespace E8Leech

open MeasureTheory
open scoped FourierTransform Real

/-- Calibration for an even lattice with even dual. -/
theorem calibration_of_even_vanishing {d : ℕ} (L : Submodule ℤ (Ambient d))
    [DiscreteTopology L] [IsZLattice ℝ L] (hcov : ZLattice.covolume L = 1)
    (heven : ∀ v ∈ L, ∃ n : ℤ, ‖v‖ ^ 2 = 2 * n)
    (hdual : ∀ m ∈ SchwartzMap.dualLattice L, ∃ n : ℤ, ‖m‖ ^ 2 = 2 * n)
    (f : SchwartzMap (Ambient d) ℂ) (α : ℝ)
    (hfin : latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α) ≠ ⊤)
    (hf : ∀ v : Ambient d, v ≠ 0 → (∃ n : ℤ, ‖v‖ ^ 2 = 2 * n) →
      f v = (gaussianKernel α v : ℂ))
    (hfhat : ∀ m : Ambient d, m ≠ 0 → (∃ n : ℤ, ‖m‖ ^ 2 = 2 * n) → 𝓕 (⇑f) m = 0) :
    (latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α)).toReal =
      (𝓕 (⇑f) 0).re - (f 0).re :=
  latticePotentialEnergy_gaussian_toReal_eq L hcov f α hfin
    (fun v hv hne => hf v hne (heven v hv)) (fun m hm hne => hfhat m hne (hdual m hm))

/-- **Lemma 6.2 interface.** -/
theorem gaussianSchwartzCertificate_of_sin_sq {d : ℕ} (hd : 0 < d) (L : Submodule ℤ (Ambient d))
    [DiscreteTopology L] [IsZLattice ℝ L] (hcov : ZLattice.covolume L = 1)
    (heven : ∀ v ∈ L, ∃ n : ℤ, ‖v‖ ^ 2 = 2 * n)
    (hdual : ∀ m ∈ SchwartzMap.dualLattice L, ∃ n : ℤ, ‖m‖ ^ 2 = 2 * n)
    (f : SchwartzMap (Ambient d) ℂ) {α : ℝ}
    (hfin : latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α) ≠ ⊤)
    (J Jhat : Ambient d → ℝ)
    (hf : ∀ v : Ambient d, v ≠ 0 →
      f v = ((gaussianKernel α v + 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * J v : ℝ) : ℂ))
    (hJ : ∀ v : Ambient d, v ≠ 0 → J v ≤ 0)
    (hfhat : ∀ ξ : Ambient d, ξ ≠ 0 →
      𝓕 (⇑f) ξ = ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 * Jhat ξ : ℝ) : ℂ))
    (hJhat : ∀ ξ : Ambient d, ξ ≠ 0 → 0 ≤ Jhat ξ) :
    GaussianSchwartzCertificate (L : Set (Ambient d)) α f := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcont : Continuous (𝓕 (⇑f)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 f).continuous
  have him : ∀ ξ : Ambient d, (𝓕 (⇑f) ξ).im = 0 := by
    have hcl : IsClosed {ξ : Ambient d | (𝓕 (⇑f) ξ).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp hcont) continuous_const
    have hsub : ({0}ᶜ : Set (Ambient d)) ⊆ {ξ | (𝓕 (⇑f) ξ).im = 0} := by
      intro ξ hξ
      show (𝓕 (⇑f) ξ).im = 0
      rw [hfhat ξ hξ, Complex.ofReal_im]
    have h := hcl.closure_subset_iff.mpr hsub
    rw [(dense_compl_singleton (0 : Ambient d)).closure_eq] at h
    exact fun ξ => h (Set.mem_univ ξ)
  refine ⟨him, ?_, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : Ambient d))]
      with ξ hξ0
    have hξ : ξ ≠ 0 := fun h => hξ0 (Set.mem_singleton_iff.mpr h)
    show 0 ≤ (𝓕 (⇑f) ξ).re
    rw [hfhat ξ hξ, Complex.ofReal_re]
    exact mul_nonneg (by positivity) (hJhat ξ hξ)
  · intro v hv
    rw [hf v hv, Complex.ofReal_re]
    have h4 : 0 ≤ 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 := by positivity
    linarith [mul_nonpos_of_nonneg_of_nonpos h4 (hJ v hv)]
  · exact calibration_of_even_vanishing L hcov heven hdual f α hfin
      (fun v hv ⟨n, hn⟩ => by rw [hf v hv, sin_pi_mul_sq_div_two_eq_zero hn]; simp)
      (fun m hm ⟨n, hn⟩ => by rw [hfhat m hm, sin_pi_mul_sq_div_two_eq_zero hn]; simp)

/-- **Lemma 6.2 interface for `E8`.** -/
theorem e8_gaussianSchwartzCertificate_of_sin_sq (f : SchwartzMap (Ambient 8) ℂ) {α : ℝ}
    (hα : 0 < α) (J Jhat : Ambient 8 → ℝ)
    (hf : ∀ v : Ambient 8, v ≠ 0 →
      f v = ((gaussianKernel α v + 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * J v : ℝ) : ℂ))
    (hJ : ∀ v : Ambient 8, v ≠ 0 → J v ≤ 0)
    (hfhat : ∀ ξ : Ambient 8, ξ ≠ 0 →
      𝓕 (⇑f) ξ = ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 * Jhat ξ : ℝ) : ℂ))
    (hJhat : ∀ ξ : Ambient 8, ξ ≠ 0 → 0 ≤ Jhat ξ) :
    GaussianSchwartzCertificate e8Set α f := by
  have hfin := e8_gaussian_lattice_energy_ne_top hα
  rw [← coe_e8Lattice] at hfin ⊢
  exact gaussianSchwartzCertificate_of_sin_sq (by norm_num) e8Lattice e8Lattice_covolume
    (fun v hv => e8Set_norm_sq_even (by rw [← coe_e8Lattice]; exact hv))
    (fun m hm => dualLattice_e8Lattice_norm_sq_even hm) f hfin J Jhat hf hJ hfhat hJhat

end E8Leech
