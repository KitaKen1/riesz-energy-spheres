import Riesz.EqualAreaMovingBounds24

/-! Actual rotated and centered sphere patches. The radius in the C7
result is independent of the rotation, coordinate center and cube center.
This is a local chart class; finite global patch coverage is separate. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaLeechPatch (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ)
    (ε : ℝ) (x : Fin 24 → ℝ) : (AmbientD 24) :=
  g (equalAreaMovingLeechChart v ε (x-c))

def equalAreaNormalizedLeechPatch (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) : (AmbientD 24) :=
  g (equalAreaMovingNormalizedLeechChart v ε (x-c))

def equalAreaRotatedFlatDerivative24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    (Fin 24 → ℝ) →L[ℝ] (AmbientD 24) :=
  (g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp equalAreaFlatDerivative24

theorem unitCube24_sub_norm (x c : Fin 24 → ℝ) (hx : x ∈ UnitCube 24)
    (hc : c ∈ UnitCube 24) : ‖x-c‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Pi.sub_apply,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(hx i).1,(hc i).2],by linarith [(hx i).2,(hc i).1]⟩

theorem equalAreaNormalizedLeechPatch_eq (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) :
    equalAreaNormalizedLeechPatch g v c ε x =
      ε⁻¹ • (equalAreaLeechPatch g v c ε x-equalAreaLeechPatch g v c ε c) := by
  simp [equalAreaNormalizedLeechPatch,equalAreaLeechPatch,equalAreaMovingNormalizedLeechChart,
    equalAreaMovingLeechChart]

theorem equalAreaNormalizedLeechPatch_center (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) : equalAreaNormalizedLeechPatch g v c ε c = 0 := by
  rw [equalAreaNormalizedLeechPatch_eq]
  simp

theorem equalAreaLeechPatch_norm (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ)
    (ε : ℝ) (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (v+ε • leechMap (x-c)) < 1) :
    ‖equalAreaLeechPatch g v c ε x‖ = 1 := by
  rw [equalAreaLeechPatch,g.norm_map]
  exact mem_sphere_zero_iff_norm.mp (equalAreaPhiD_mem_sphere _ hx)

theorem equalAreaNormalizedLeechPatch_contDiffAt (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap (x-c)) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedLeechPatch g v c ε) x := by
  have hshift : ContDiffAt ℝ ∞ (fun z : Fin 24 → ℝ => z-c) x :=
    contDiffAt_id.sub contDiffAt_const
  have hf : ContDiffAt ℝ ∞ (fun z => equalAreaMovingNormalizedLeechChart v ε (z-c)) x :=
    ContDiffAt.comp (g := equalAreaMovingNormalizedLeechChart v ε) (f := fun z => z-c) x
      (equalAreaMovingNormalizedLeechChart_contDiffAt v ε (x-c) hx) hshift
  exact ContDiffAt.comp (g := g.toContinuousLinearMap)
    (f := fun z => equalAreaMovingNormalizedLeechChart v ε (z-c)) x
    g.toContinuousLinearMap.contDiff.contDiffAt hf

theorem equalAreaNormalizedLeechPatch_hasFDerivAt (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : ε ≠ 0) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap (x-c)) < 1) :
    HasFDerivAt (equalAreaNormalizedLeechPatch g v c ε)
      ((g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp
        ((equalAreaPhiDerivativeD (v+ε • leechMap (x-c))).comp leechMap)) x := by
  have hf : HasFDerivAt (fun z => equalAreaMovingNormalizedLeechChart v ε (z-c))
      ((equalAreaPhiDerivativeD (v+ε • leechMap (x-c))).comp leechMap) x :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaMovingNormalizedLeechChart_hasFDerivAt v ε hε (x-c) hx)
  exact g.toContinuousLinearMap.hasFDerivAt.comp x hf

theorem equalAreaNormalizedLeechPatch_fderiv (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) :
    fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) x =
      (g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp
        (fderiv ℝ (equalAreaMovingNormalizedLeechChart v ε) (x-c)) := by
  change fderiv ℝ (g ∘ (fun z => equalAreaMovingNormalizedLeechChart v ε (z-c))) x = _
  rw [g.comp_fderiv,fderiv_comp_sub]

theorem equalAreaNormalizedLeechPatch_iterated_norm (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedLeechPatch g v c ε) x‖ =
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedLeechChart v ε) (x-c)‖ := by
  change ‖iteratedFDeriv ℝ k (g ∘ (fun z => equalAreaMovingNormalizedLeechChart v ε (z-c))) x‖ = _
  rw [g.norm_iteratedFDeriv_comp_left,iteratedFDeriv_comp_sub]

theorem equalAreaRotation24_comp_norm_le (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (L : (Fin 24 → ℝ) →L[ℝ] (AmbientD 24)) :
    ‖(g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  change ‖g (L x)‖ ≤ ‖L‖*‖x‖
  rw [g.norm_map]
  exact L.le_opNorm x

theorem equalAreaNormalizedLeechPatch_first_error (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) :
    ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) x-equalAreaRotatedFlatDerivative24 g‖ ≤
      ‖fderiv ℝ (equalAreaMovingNormalizedLeechChart v ε) (x-c)-equalAreaFlatDerivative24‖ := by
  rw [equalAreaNormalizedLeechPatch_fderiv]
  change ‖(g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp _-(g : (AmbientD 24) →L[ℝ] (AmbientD 24)).comp _‖ ≤ _
  rw [←ContinuousLinearMap.comp_sub]
  exact equalAreaRotation24_comp_norm_le g _

theorem equalAreaNormalizedLeechPatch_increment_error (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hs : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (C : ℝ)
    (hb : ∀ z ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) z-equalAreaRotatedFlatDerivative24 g‖ ≤ C)
    (x y : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) (hy : y ∈ UnitCube 24) :
    ‖(equalAreaNormalizedLeechPatch g v c ε y-equalAreaRotatedFlatDerivative24 g (y-c))-
      (equalAreaNormalizedLeechPatch g v c ε x-equalAreaRotatedFlatDerivative24 g (x-c))‖ ≤ C*‖y-x‖ := by
  apply unitCube24_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) z-equalAreaRotatedFlatDerivative24 g)
    _ hb hx hy
  intro z hz
  have hn : ‖v+ε • leechMap (z-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledLeech_norm v ε (z-c) (unitCube24_sub_norm z c hz hc)).trans
      (by simpa only [abs_of_pos hε] using hs)
  have hf := equalAreaNormalizedLeechPatch_hasFDerivAt g v c ε hε.ne' z
    (equalArea24_small_norm_domain _ hn)
  have hl : HasFDerivAt (fun w => equalAreaRotatedFlatDerivative24 g (w-c))
      (equalAreaRotatedFlatDerivative24 g) z :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaRotatedFlatDerivative24 g).hasFDerivAt
  rw [hf.fderiv]
  exact (hf.sub hl).hasFDerivWithinAt

theorem equalAreaRotatedFlatDerivative24_dist (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (c x y : Fin 24 → ℝ) :
    dist (equalAreaRotatedFlatDerivative24 g (x-c)) (equalAreaRotatedFlatDerivative24 g (y-c)) =
      dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  change dist (g (equalAreaFlatDerivative24 (x-c))) (g (equalAreaFlatDerivative24 (y-c))) = _
  rw [g.dist_map,dist_eq_norm,←map_sub]
  have h : (x-c)-(y-c) = x-y := by abel
  rw [h,map_sub,←dist_eq_norm,equalAreaFlatDerivative24_dist]

theorem equalAreaNormalizedLeechPatch_relative_distance_of_derivative
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ) (hc : c ∈ UnitCube 24)
    (ε : ℝ) (hε : 0 < ε) (hs : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) z-equalAreaRotatedFlatDerivative24 g‖ ≤ C)
    (x y : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) (hy : y ∈ UnitCube 24) :
    |dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y)-
      dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))| ≤
      (C*(1+‖leechInverseMap‖))*
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  rw [←equalAreaRotatedFlatDerivative24_dist g c,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedLeechPatch g v c ε x-equalAreaNormalizedLeechPatch g v c ε y)-
      (equalAreaRotatedFlatDerivative24 g (x-c)-equalAreaRotatedFlatDerivative24 g (y-c)) =
      (equalAreaNormalizedLeechPatch g v c ε x-equalAreaRotatedFlatDerivative24 g (x-c))-
        (equalAreaNormalizedLeechPatch g v c ε y-equalAreaRotatedFlatDerivative24 g (y-c)) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedLeechPatch g v c ε x-equalAreaNormalizedLeechPatch g v c ε y)-
        (equalAreaRotatedFlatDerivative24 g (x-c)-equalAreaRotatedFlatDerivative24 g (y-c))‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedLeechPatch_increment_error g v c hc ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖leechInverseMap‖)*
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))) :=
      mul_le_mul_of_nonneg_left (equalAreaLeech_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaRotatedFlatDerivative24_dist g c,dist_eq_norm]; ring

/-- Uniform C7 closeness of actual normalized sphere patches to the
rotated flat E8 embedding. The derivatives are actual fderiv/iteratedFDeriv. -/
theorem equalAreaNormalizedLeechPatch_C7_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 24 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), ∀ c ∈ UnitCube 24, ∀ x ∈ UnitCube 24,
      ContDiffAt ℝ ∞ (equalAreaNormalizedLeechPatch g v c ε) x ∧
      ‖equalAreaNormalizedLeechPatch g v c ε x-equalAreaRotatedFlatDerivative24 g (x-c)‖ ≤ η ∧
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) x-equalAreaRotatedFlatDerivative24 g‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedLeechPatch g v c ε) x‖ ≤ η := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaMovingNormalizedLeechChart_C7_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx
  have hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8 := by linarith
  have hnorm : ‖v+ε • leechMap (x-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledLeech_norm v ε (x-c) (unitCube24_sub_norm x c hx hc)).trans
      (by simpa only [abs_of_pos hε] using hsmall)
  have hfirst : ∀ z ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) z-equalAreaRotatedFlatDerivative24 g‖ ≤ η := by
    intro z hz
    exact (equalAreaNormalizedLeechPatch_first_error g v c ε z).trans
      (hb v hv ε hε hs (z-c) (unitCube24_sub_norm z c hz hc)).1
  refine ⟨equalAreaNormalizedLeechPatch_contDiffAt g v c ε x (equalArea24_small_norm_domain _ hnorm),
    ?_,hfirst x hx,?_⟩
  · have h := equalAreaNormalizedLeechPatch_increment_error g v c hc ε hε hsmall η hfirst c x hc hx
    simp only [equalAreaNormalizedLeechPatch_center,sub_self,map_zero,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hη.le (unitCube24_sub_norm x c hx hc))
  · intro k hk hk7
    rw [equalAreaNormalizedLeechPatch_iterated_norm]
    exact (hb v hv ε hε hs (x-c) (unitCube24_sub_norm x c hx hc)).2 k hk hk7

theorem equalAreaNormalizedLeechPatch_relative_distance_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 24 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), ∀ c ∈ UnitCube 24,
      ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      |dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y)-
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))| ≤
        η*dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  have hd : 0 < 1+‖leechInverseMap‖ := by positivity
  let C : ℝ := η/(1+‖leechInverseMap‖)
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedLeechPatch_C7_uniform C (by dsimp [C]; positivity)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have h := equalAreaNormalizedLeechPatch_relative_distance_of_derivative g v c hc ε hε
    (by linarith) C (by dsimp [C]; positivity)
    (fun z hz => (hb v hv ε hε hs g c hc z hz).2.2.1) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

/-- A single positive lower Lipschitz constant for the actual patch class,
needed by the singular far-kernel estimates. -/
theorem equalAreaNormalizedLeechPatch_lower_distance_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 24 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), ∀ c ∈ UnitCube 24,
      ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      (1/(2*(1+‖leechInverseMap‖)))*‖x-y‖ ≤
        dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedLeechPatch_relative_distance_uniform
    (1/2) (by norm_num)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have hd := (abs_le.mp (hb v hv ε hε hs g c hc x hx y hy)).1
  have hflat : dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) ≤
      2*dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y) := by
    linarith
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+‖leechInverseMap‖))).mpr
  have h := mul_le_mul_of_nonneg_left hflat (by positivity : 0 ≤ 1+‖leechInverseMap‖)
  have hcxy := equalAreaLeech_distance_controls_coordinates x y
  nlinarith

end SphericalRiesz
