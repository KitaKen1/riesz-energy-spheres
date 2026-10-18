import E8Leech.LeechDuality

/-!
# The Lemma 6.2 interface for the Leech lattice, in the range of the Laplace representation

In dimension 24 the CKMRV kernels grow like `t e^{2πt}`, so the representation
`F̃(τ, x) = 4 sin²(π|x|²/2) ∫₀^∞ 𝒦̂(τ, it) e^{−π|x|²t} dt` holds for `|x|² > 2` only. On the sphere
`|x|² = 2` the auxiliary function is strictly below the Gaussian: the factor `sin²` vanishes there,
but the integral has a double pole. So the form `f = Gaussian + 4 sin² · J` with a finite `J`
cannot hold for all `v ≠ 0`, which is what `leech_gaussianSchwartzCertificate_of_sin_sq` asks for.

The Leech lattice has no vector with `0 < |v|² < 4`. The calibration therefore only needs the
`sin²` form for `|v|² > 2`. The minorant inequality and the sign of the Fourier transform are
separate hypotheses here; for `|v|² ≤ 2` they come from the continued representation
(CKMRV (6.4)(2), (3)).
-/

noncomputable section

namespace E8Leech

open MeasureTheory
open scoped FourierTransform Real SchwartzMap

/-- A nonzero vector of the Leech lattice has squared norm more than two. -/
theorem two_lt_norm_sq_of_mem_leechLattice {v : Ambient 24} (hv : v ∈ leechLattice)
    (hne : v ≠ 0) : 2 < ‖v‖ ^ 2 := by
  have hv' : v ∈ leechSet := by
    rw [← coe_leechLattice]
    exact hv
  linarith [leechSet_norm_sq_lower hv' hne]

/-- **Lemma 6.2 interface for the Leech lattice.** The `sin²` form of the function and of its
Fourier transform is asked for `|v|² > 2` only. -/
theorem leech_gaussianSchwartzCertificate_of_large_sin_sq (f : 𝓢(Ambient 24, ℂ)) {α : ℝ}
    (hα : 0 < α) (J Jhat : Ambient 24 → ℝ)
    (hf : ∀ v : Ambient 24, 2 < ‖v‖ ^ 2 →
      f v = ((gaussianKernel α v + 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * J v : ℝ) : ℂ))
    (hfhat : ∀ ξ : Ambient 24, 2 < ‖ξ‖ ^ 2 →
      𝓕 (⇑f) ξ = ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 * Jhat ξ : ℝ) : ℂ))
    (hminor : ∀ v : Ambient 24, v ≠ 0 → (f v).re ≤ gaussianKernel α v)
    (hreal : ∀ ξ : Ambient 24, (𝓕 (⇑f) ξ).im = 0)
    (hnonneg : ∀ ξ : Ambient 24, ξ ≠ 0 → 0 ≤ (𝓕 (⇑f) ξ).re) :
    GaussianSchwartzCertificate leechSet α f := by
  have hfin := leech_gaussian_lattice_energy_ne_top hα
  rw [← coe_leechLattice] at hfin ⊢
  refine ⟨hreal, ?_, hminor, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : Ambient 24))]
      with ξ hξ0
    exact hnonneg ξ fun h => hξ0 (Set.mem_singleton_iff.mpr h)
  · refine latticePotentialEnergy_gaussian_toReal_eq leechLattice leechLattice_covolume f α hfin
      (fun v hv hne => ?_) (fun m hm hne => ?_)
    · obtain ⟨n, hn⟩ := leechLattice_norm_sq_even hv
      rw [hf v (two_lt_norm_sq_of_mem_leechLattice hv hne), sin_pi_mul_sq_div_two_eq_zero hn]
      simp
    · have hmL := mem_leechLattice_of_mem_dualLattice hm
      obtain ⟨n, hn⟩ := leechLattice_norm_sq_even hmL
      rw [hfhat m (two_lt_norm_sq_of_mem_leechLattice hmL hne),
        sin_pi_mul_sq_div_two_eq_zero hn]
      simp

end E8Leech
