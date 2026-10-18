import Riesz.GaussianBlockUnion8
import Riesz.PatchNegMacroBound8

/-! Monotonicity of the macroscopic end in the cutoff, and the patch block (stage NEG, assembly).

With exact mass the block of the subtracted macroscopic kernel `K'(δ)` is
`∫_{(0,δ]} α^p block(G_{cα})`, and the integrand is nonnegative (positive definiteness of the
Gaussian block). Hence the block increases with the cutoff: one joint selection with `K'(1)`
controls the macroscopic end `∫_{(0,δ]}` for every `δ ≤ 1` at once, and no diagonal argument in
`δ` is needed in the sequence-level assembly. For a rational cube family the patch nodes have
exact mass `K (a m)^8 = (d m)^8 σ(S)`, so the patch block of `K'(w)` is the patch macroscopic end
bounded in `PatchNegMacroBound8`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem negMacroGaussian_integrand_nonneg {ι : Type*} [Fintype ι] {c p α : ℝ} (hc : 0 ≤ c)
    (hα : 0 < α) (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    0 ≤ α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M := by
  apply mul_nonneg (Real.rpow_nonneg hα.le _)
  rw [gaussianBlock8_eq_defect (mul_nonneg hc hα.le)]
  exact gaussianMeasureDefect_nonneg (mul_nonneg hc hα.le) M _ _

/-- At exact mass the block of `K'(δ)` is monotone in the cutoff `δ`. -/
theorem negMacroBlock8_mono_cutoff {ι : Type*} [Fintype ι] {c p δ δ' : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ)
    (hmass : (Fintype.card ι:ℝ) = M*sphereProbability8.real S) :
    kernelBlock8 (negMacroKernel8 c p δ) X S M ≤ kernelBlock8 (negMacroKernel8 c p δ') X S M := by
  have hδ' : 0 ≤ δ' := hδ.trans hδδ'
  rw [negMacroBlock8_eq_of_mass hc hp hδ X S M hmass,
    negMacroBlock8_eq_of_mass hc hp hδ' X S M hmass]
  apply setIntegral_mono_set (negMacroGaussian_integrable hc hp hδ' X S M hmass)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
    exact negMacroGaussian_integrand_nonneg hc hα.1 X S M
  · exact (Ioc_subset_Ioc_right hδδ').eventuallyLE

/-- At exact mass the block of `K'(δ)` is nonnegative and at most the block of `K'(δ')`. -/
theorem negMacroBlock8_cutoff_bounds {ι : Type*} [Fintype ι] {c p δ δ' : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ)
    (hmass : (Fintype.card ι:ℝ) = M*sphereProbability8.real S) :
    0 ≤ kernelBlock8 (negMacroKernel8 c p δ) X S M ∧
      kernelBlock8 (negMacroKernel8 c p δ) X S M ≤ kernelBlock8 (negMacroKernel8 c p δ') X S M := by
  refine ⟨?_, negMacroBlock8_mono_cutoff hc hp hδ hδδ' X S M hmass⟩
  rw [negMacroBlock8_eq_of_mass hc hp hδ X S M hmass]
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  exact negMacroGaussian_integrand_nonneg hc hα.1 X S M


/-- The patch block of the subtracted macroscopic kernel for a rational cube family (exact mass
`K (a m)^8 = (d m)^8 σ(S)`). -/
theorem rationalPatch_negMacroBlock_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C₁ C₄ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₄ ∧
      ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i))
        (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m),
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) →
      (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8 →
      ∀ {p w : ℝ}, -2 < p → 0 < w → w ≤ 1 →
      kernelBlock8 (negMacroKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p w)
          (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i))
          (((d*m)^8:ℕ):ℝ) ≤
        (((d*m)^8:ℕ):ℝ)*(C₁*(w^(p+3)/(p+3))+
          C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(w^(p+2)/(p+2))) := by
  obtain ⟨ρ, hρ, hρ1, C₁, C₄, hC₁, hC₄, h⟩ := rationalPatch_negMacroIntegral_le
  refine ⟨ρ, hρ, hρ1, C₁, C₄, hC₁, hC₄, ?_⟩
  intro K P hdis hsmall a d m ha hd hm hε hdens hmass p w hp hw hw1
  have hNpos : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd (by omega)) 8
  have hc := (sphereGaussianDensityFactor8_pos hNpos).le
  have hcard : (Fintype.card (Fin K × (Fin 8 → NodeIndex (a*m))):ℝ) =
      (((d*m)^8:ℕ):ℝ)*sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) := by
    rw [Fintype.card_prod, Fintype.card_fin, rationalPatchNodeIndex8_card a m ha hm, hmass]
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  rw [negMacroBlock8_eq_of_mass hc hp hw.le _ _ _ hcard]
  exact h P hdis hsmall a d m ha hd hm hε hdens hp hw hw1

#print axioms negMacroGaussian_integrand_nonneg
#print axioms negMacroBlock8_mono_cutoff
#print axioms negMacroBlock8_cutoff_bounds
#print axioms rationalPatch_negMacroBlock_le

end SphericalRiesz
