import Riesz.EqualAreaPatchMeasure24

/-! Exact mass accounting for a given finite, physically disjoint patch
family. This does not assume a covering theorem has been proved: the
existence of near-full separated families remains a separate obligation. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

theorem equalAreaLeechSpherePatch24_disjoint (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (s t : Set (Fin 24 → ℝ))
    (hs : equalAreaLeechAffine24 v c ε '' s ⊆ equalAreaChartDomainD)
    (ht : equalAreaLeechAffine24 v c ε '' t ⊆ equalAreaChartDomainD) (hd : Disjoint s t) :
    Disjoint (equalAreaLeechSpherePatch24 g v c ε s) (equalAreaLeechSpherePatch24 g v c ε t) := by
  apply Set.disjoint_left.mpr
  intro x hx hxt
  obtain ⟨y,hy,hxy⟩ := hx
  obtain ⟨z,hz,hxz⟩ := hxt
  have h : equalAreaPhiD (equalAreaLeechAffine24 v c ε y) =
      equalAreaPhiD (equalAreaLeechAffine24 v c ε z) := g.injective (hxy.trans hxz.symm)
  have he := equalAreaLeechAffine24_injective v c ε hε.ne'
    (equalAreaPhiD_injOn (hs ⟨y,hy,rfl⟩) (ht ⟨z,hz,rfl⟩) h)
  exact Set.disjoint_left.mp hd hy (he.symm ▸ hz)

def equalAreaLeechPatchUnion24 {K : ℕ} (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin K → Fin 24 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 24 → ℝ)) : Set (SphereD 24) :=
  ⋃ i : Fin K, equalAreaLeechSpherePatch24 (g i) (v i) (c i) (e i) (s i)

theorem equalAreaLeechPatchUnion24_probability {K : ℕ} (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin K → Fin 24 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 24 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaLeechAffine24 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) (c i) (e i) (s i))
      (equalAreaLeechSpherePatch24 (g j) (v j) (c j) (e j) (s j)))) :
    (sphereProbabilityD 24) (equalAreaLeechPatchUnion24 g v c e s) =
      ∑ i : Fin K, ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 (e i))*volume (s i) := by
  rw [equalAreaLeechPatchUnion24,measure_iUnion hd (fun i =>
    equalAreaLeechSpherePatch24_measurable (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact equalAreaLeechSpherePatch24_probability (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)

theorem equalAreaLeechPatchUnion24_residual {K : ℕ} (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin K → Fin 24 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 24 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaLeechAffine24 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) (c i) (e i) (s i))
      (equalAreaLeechSpherePatch24 (g j) (v j) (c j) (e j) (s j)))) :
    (sphereProbabilityD 24) (equalAreaLeechPatchUnion24 g v c e s)ᶜ =
      1-∑ i : Fin K, ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 (e i))*volume (s i) := by
  have hm : MeasurableSet (equalAreaLeechPatchUnion24 g v c e s) :=
    MeasurableSet.iUnion (fun i => equalAreaLeechSpherePatch24_measurable
      (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i))
  rw [measure_compl hm (measure_ne_top _ _),measure_univ,
    equalAreaLeechPatchUnion24_probability g v c e s he hs hdom hd]

theorem equalAreaLeechCubeUnion24_probability {K : ℕ} (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin K → Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 24)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius24 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) (c i) ε (UnitCube 24))
      (equalAreaLeechSpherePatch24 (g j) (v j) (c j) ε (UnitCube 24)))) :
    (sphereProbabilityD 24) (equalAreaLeechPatchUnion24 g v c (fun _ => ε) (fun _ => UnitCube 24)) =
      (K : ℝ≥0∞)*ENNReal.ofReal (ε^24/((sphereAreaD 24).real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaLeechPatchProbabilityDensity24] using
    equalAreaLeechPatchUnion24_probability g v c (fun _ => ε) (fun _ => UnitCube 24)
      (fun _ => hε) (fun _ => unitCube_measurableSet 24)
      (fun i => equalAreaLeechAffine24_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

theorem equalAreaLeechCubeUnion24_residual {K : ℕ} (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin K → Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 24)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius24 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) (c i) ε (UnitCube 24))
      (equalAreaLeechSpherePatch24 (g j) (v j) (c j) ε (UnitCube 24)))) :
    (sphereProbabilityD 24) (equalAreaLeechPatchUnion24 g v c (fun _ => ε) (fun _ => UnitCube 24))ᶜ =
      1-(K : ℝ≥0∞)*ENNReal.ofReal (ε^24/((sphereAreaD 24).real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaLeechPatchProbabilityDensity24] using
    equalAreaLeechPatchUnion24_residual g v c (fun _ => ε) (fun _ => UnitCube 24)
      (fun _ => hε) (fun _ => unitCube_measurableSet 24)
      (fun i => equalAreaLeechAffine24_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

end SphericalRiesz
