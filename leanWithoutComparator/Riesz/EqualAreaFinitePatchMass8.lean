import Riesz.EqualAreaPatchMeasure8

/-! Exact mass accounting for a given finite, physically disjoint patch
family. This does not assume a covering theorem has been proved: the
existence of near-full separated families remains a separate obligation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

theorem equalAreaE8SpherePatch8_disjoint (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (s t : Set (Fin 8 → ℝ))
    (hs : equalAreaE8Affine8 v c ε '' s ⊆ equalAreaChartDomain)
    (ht : equalAreaE8Affine8 v c ε '' t ⊆ equalAreaChartDomain) (hd : Disjoint s t) :
    Disjoint (equalAreaE8SpherePatch8 g v c ε s) (equalAreaE8SpherePatch8 g v c ε t) := by
  apply Set.disjoint_left.mpr
  intro x hx hxt
  obtain ⟨y,hy,hxy⟩ := hx
  obtain ⟨z,hz,hxz⟩ := hxt
  have h : equalAreaPhi (equalAreaE8Affine8 v c ε y) =
      equalAreaPhi (equalAreaE8Affine8 v c ε z) := g.injective (hxy.trans hxz.symm)
  have he := equalAreaE8Affine8_injective v c ε hε.ne'
    (equalAreaPhi_injOn (hs ⟨y,hy,rfl⟩) (ht ⟨z,hz,rfl⟩) h)
  exact Set.disjoint_left.mp hd hy (he.symm ▸ hz)

def equalAreaE8PatchUnion8 {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin K → Fin 8 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 8 → ℝ)) : Set Sphere8 :=
  ⋃ i : Fin K, equalAreaE8SpherePatch8 (g i) (v i) (c i) (e i) (s i)

theorem equalAreaE8PatchUnion8_probability {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin K → Fin 8 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 8 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaE8Affine8 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomain)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) (e i) (s i))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) (e j) (s j)))) :
    sphereProbability8 (equalAreaE8PatchUnion8 g v c e s) =
      ∑ i : Fin K, ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 (e i))*volume (s i) := by
  rw [equalAreaE8PatchUnion8,measure_iUnion hd (fun i =>
    equalAreaE8SpherePatch8_measurable (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact equalAreaE8SpherePatch8_probability (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)

theorem equalAreaE8PatchUnion8_residual {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin K → Fin 8 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 8 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaE8Affine8 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomain)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) (e i) (s i))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) (e j) (s j)))) :
    sphereProbability8 (equalAreaE8PatchUnion8 g v c e s)ᶜ =
      1-∑ i : Fin K, ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 (e i))*volume (s i) := by
  have hm : MeasurableSet (equalAreaE8PatchUnion8 g v c e s) :=
    MeasurableSet.iUnion (fun i => equalAreaE8SpherePatch8_measurable
      (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i))
  rw [measure_compl hm (measure_ne_top _ _),measure_univ,
    equalAreaE8PatchUnion8_probability g v c e s he hs hdom hd]

theorem equalAreaE8CubeUnion8_probability {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin K → Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 8)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) ε (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) ε (UnitCube 8)))) :
    sphereProbability8 (equalAreaE8PatchUnion8 g v c (fun _ => ε) (fun _ => UnitCube 8)) =
      (K : ℝ≥0∞)*ENNReal.ofReal (ε^8/(sphereArea8.real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaE8PatchProbabilityDensity8] using
    equalAreaE8PatchUnion8_probability g v c (fun _ => ε) (fun _ => UnitCube 8)
      (fun _ => hε) (fun _ => unitCube_measurableSet 8)
      (fun i => equalAreaE8Affine8_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

theorem equalAreaE8CubeUnion8_residual {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin K → Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 8)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) ε (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) ε (UnitCube 8)))) :
    sphereProbability8 (equalAreaE8PatchUnion8 g v c (fun _ => ε) (fun _ => UnitCube 8))ᶜ =
      1-(K : ℝ≥0∞)*ENNReal.ofReal (ε^8/(sphereArea8.real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaE8PatchProbabilityDensity8] using
    equalAreaE8PatchUnion8_residual g v c (fun _ => ε) (fun _ => UnitCube 8)
      (fun _ => hε) (fun _ => unitCube_measurableSet 8)
      (fun i => equalAreaE8Affine8_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

end SphericalRiesz
