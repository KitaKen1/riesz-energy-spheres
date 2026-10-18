import Riesz.SphereGrid8
import Riesz.GridShrink8
import Riesz.EqualAreaFinitePatchMass8
import Mathlib.Algebra.Order.Ring.Pow

/-! Exact finite shrink accounting in the actual sphere probability measure.
Compactness and disjointness concern physical Sphere8 images, rather than
only their coordinates. These are interval cells; the affine unit-cube
parameterization and rational node counts are separate obligations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

theorem e8GridAffine8_eq_map : equalAreaE8Affine8 0 0 1 = e8Map := by
  funext x
  simp only [equalAreaE8Affine8,sub_zero,one_smul,zero_add]

theorem e8GridSpherePatch8_mono (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    {s t : Set (Fin 8 → ℝ)} (hst : s ⊆ t) :
    equalAreaE8SpherePatch8 g 0 0 1 s ⊆ equalAreaE8SpherePatch8 g 0 0 1 t :=
  preimage_mono (image_mono hst)

theorem e8GridSpherePatch8_isCompact (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (s : Set (Fin 8 → ℝ)) (hs : IsCompact s) :
    IsCompact (equalAreaE8SpherePatch8 g 0 0 1 s) := by
  let : CompactSpace Sphere8 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient9) 1)
  have hf : Continuous (equalAreaE8Patch g 0 0 1) := by
    unfold equalAreaE8Patch equalAreaMovingE8Chart
    exact g.continuous.comp (equalAreaPhi_continuous.comp (by fun_prop))
  exact ((hs.image hf).isClosed.preimage continuous_subtype_val).isCompact

theorem e8GridSpherePatch8_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s)
    (hdom : e8Map '' s ⊆ equalAreaChartDomain) :
    sphereProbability8 (equalAreaE8SpherePatch8 g 0 0 1 s) =
      ENNReal.ofReal (1/sphereArea8.real univ)*volume s := by
  simpa only [e8GridAffine8_eq_map,equalAreaE8PatchProbabilityDensity8,one_pow] using
    equalAreaE8SpherePatch8_probability g 0 0 1 zero_lt_one s hs (by
      simpa only [e8GridAffine8_eq_map] using hdom)

theorem e8GridSpherePatch8_measurable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s)
    (hdom : e8Map '' s ⊆ equalAreaChartDomain) :
    MeasurableSet (equalAreaE8SpherePatch8 g 0 0 1 s) :=
  equalAreaE8SpherePatch8_measurable g 0 0 1 zero_lt_one s hs (by
    simpa only [e8GridAffine8_eq_map] using hdom)

theorem e8GridSpherePatch8_disjoint (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (s t : Set (Fin 8 → ℝ)) (hs : e8Map '' s ⊆ equalAreaChartDomain)
    (ht : e8Map '' t ⊆ equalAreaChartDomain) (hd : Disjoint s t) :
    Disjoint (equalAreaE8SpherePatch8 g 0 0 1 s) (equalAreaE8SpherePatch8 g 0 0 1 t) :=
  equalAreaE8SpherePatch8_disjoint g 0 0 1 zero_lt_one s t
    (by simpa only [e8GridAffine8_eq_map] using hs)
    (by simpa only [e8GridAffine8_eq_map] using ht) hd

theorem e8GridShrunkSphereCell8_probability_factor (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (z : Fin 8 → ℤ)
    (hdom : e8Map '' gridClosedCell8 h z ⊆ equalAreaChartDomain) :
    sphereProbability8 (equalAreaE8SpherePatch8 g 0 0 1 (gridShrunkCell8 h γ z)) =
      ENNReal.ofReal ((1-γ)^8)*
        sphereProbability8 (equalAreaE8SpherePatch8 g 0 0 1 (gridHalfOpenCell8 h z)) := by
  have hs := gridShrunkCell8_subset_halfOpen h γ hh hγ z
  have ht := gridHalfOpenCell8_subset_closed h z
  rw [e8GridSpherePatch8_probability g _
    (gridShrunkCell8_isCompact h γ z).isClosed.measurableSet ((image_mono (hs.trans ht)).trans hdom),
    e8GridSpherePatch8_probability g _ (gridHalfOpenCell8_measurable h z)
      ((image_mono ht).trans hdom),gridShrunkCell8_volume_factor h γ hh.le hγ1 z]
  ring

theorem e8GridShrunkSphereFamily8_disjoint {ι : Type*}
    (g : ι → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (z : ι → Fin 8 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i)))
      (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridHalfOpenCell8 h (z j))))) :
    Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)))
      (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridShrunkCell8 h γ (z j)))) := by
  intro i j hij
  exact (hd hij).mono
    (e8GridSpherePatch8_mono _ (gridShrunkCell8_subset_halfOpen h γ hh hγ (z i)))
    (e8GridSpherePatch8_mono _ (gridShrunkCell8_subset_halfOpen h γ hh hγ (z j)))

theorem e8GridShrunkSphereFamily8_probability_factor {ι : Type*} [Fintype ι]
    (g : ι → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (z : ι → Fin 8 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, e8Map '' gridClosedCell8 h (z i) ⊆ equalAreaChartDomain)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i)))
      (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridHalfOpenCell8 h (z j))))) :
    sphereProbability8 (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) =
      ENNReal.ofReal ((1-γ)^8)*
        sphereProbability8 (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))) := by
  classical
  have hd' := e8GridShrunkSphereFamily8_disjoint g z h γ hh hγ hd
  have hsm : ∀ i, MeasurableSet
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) := fun i =>
    e8GridSpherePatch8_measurable _ _ (gridShrunkCell8_isCompact h γ (z i)).isClosed.measurableSet
      ((image_mono ((gridShrunkCell8_subset_halfOpen h γ hh hγ (z i)).trans
        (gridHalfOpenCell8_subset_closed h (z i)))).trans (hdom i))
  have hhm : ∀ i, MeasurableSet
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))) := fun i =>
    e8GridSpherePatch8_measurable _ _ (gridHalfOpenCell8_measurable h (z i))
      ((image_mono (gridHalfOpenCell8_subset_closed h (z i))).trans (hdom i))
  rw [measure_iUnion hd' hsm,measure_iUnion hd hhm,tsum_fintype,tsum_fintype,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    e8GridShrunkSphereCell8_probability_factor (g i) h γ hh hγ hγ1 (z i) (hdom i))

theorem e8GridShrunkSphereFamily8_probability_real_factor {ι : Type*} [Fintype ι]
    (g : ι → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (z : ι → Fin 8 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, e8Map '' gridClosedCell8 h (z i) ⊆ equalAreaChartDomain)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i)))
      (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridHalfOpenCell8 h (z j))))) :
    sphereProbability8.real (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) =
      (1-γ)^8*sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))) := by
  rw [Measure.real,e8GridShrunkSphereFamily8_probability_factor g z h γ hh hγ hγ1 hdom hd,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr hγ1) 8)]
  rfl

end SphericalRiesz
