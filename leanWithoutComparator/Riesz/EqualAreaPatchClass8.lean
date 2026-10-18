import Riesz.EqualAreaMovingBounds8

/-! Actual rotated and centered sphere patches. The radius in the C7
result is independent of the rotation, coordinate center and cube center.
This is a local chart class; finite global patch coverage is separate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaE8Patch (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : Fin 8 → ℝ)
    (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  g (equalAreaMovingE8Chart v ε (x-c))

def equalAreaNormalizedE8Patch (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  g (equalAreaMovingNormalizedE8Chart v ε (x-c))

def equalAreaRotatedFlatDerivative8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    (Fin 8 → ℝ) →L[ℝ] Ambient9 :=
  (g : Ambient9 →L[ℝ] Ambient9).comp equalAreaFlatDerivative8

theorem unitCube8_sub_norm (x c : Fin 8 → ℝ) (hx : x ∈ UnitCube 8)
    (hc : c ∈ UnitCube 8) : ‖x-c‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Pi.sub_apply,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(hx i).1,(hc i).2],by linarith [(hx i).2,(hc i).1]⟩

theorem equalAreaNormalizedE8Patch_eq (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) :
    equalAreaNormalizedE8Patch g v c ε x =
      ε⁻¹ • (equalAreaE8Patch g v c ε x-equalAreaE8Patch g v c ε c) := by
  simp [equalAreaNormalizedE8Patch,equalAreaE8Patch,equalAreaMovingNormalizedE8Chart,
    equalAreaMovingE8Chart]

theorem equalAreaNormalizedE8Patch_center (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) : equalAreaNormalizedE8Patch g v c ε c = 0 := by
  rw [equalAreaNormalizedE8Patch_eq]
  simp

theorem equalAreaE8Patch_norm (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : Fin 8 → ℝ)
    (ε : ℝ) (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (v+ε • e8Map (x-c)) < 1) :
    ‖equalAreaE8Patch g v c ε x‖ = 1 := by
  rw [equalAreaE8Patch,g.norm_map]
  exact mem_sphere_zero_iff_norm.mp (equalAreaPhi_mem_sphere _ hx)

theorem equalAreaNormalizedE8Patch_contDiffAt (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map (x-c)) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedE8Patch g v c ε) x := by
  have hshift : ContDiffAt ℝ ∞ (fun z : Fin 8 → ℝ => z-c) x :=
    contDiffAt_id.sub contDiffAt_const
  have hf : ContDiffAt ℝ ∞ (fun z => equalAreaMovingNormalizedE8Chart v ε (z-c)) x :=
    ContDiffAt.comp (g := equalAreaMovingNormalizedE8Chart v ε) (f := fun z => z-c) x
      (equalAreaMovingNormalizedE8Chart_contDiffAt v ε (x-c) hx) hshift
  exact ContDiffAt.comp (g := g.toContinuousLinearMap)
    (f := fun z => equalAreaMovingNormalizedE8Chart v ε (z-c)) x
    g.toContinuousLinearMap.contDiff.contDiffAt hf

theorem equalAreaNormalizedE8Patch_hasFDerivAt (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : ε ≠ 0) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map (x-c)) < 1) :
    HasFDerivAt (equalAreaNormalizedE8Patch g v c ε)
      ((g : Ambient9 →L[ℝ] Ambient9).comp
        ((equalAreaPhiDerivative (v+ε • e8Map (x-c))).comp e8Map)) x := by
  have hf : HasFDerivAt (fun z => equalAreaMovingNormalizedE8Chart v ε (z-c))
      ((equalAreaPhiDerivative (v+ε • e8Map (x-c))).comp e8Map) x :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaMovingNormalizedE8Chart_hasFDerivAt v ε hε (x-c) hx)
  exact g.toContinuousLinearMap.hasFDerivAt.comp x hf

theorem equalAreaNormalizedE8Patch_fderiv (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) :
    fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) x =
      (g : Ambient9 →L[ℝ] Ambient9).comp
        (fderiv ℝ (equalAreaMovingNormalizedE8Chart v ε) (x-c)) := by
  change fderiv ℝ (g ∘ (fun z => equalAreaMovingNormalizedE8Chart v ε (z-c))) x = _
  rw [g.comp_fderiv,fderiv_comp_sub]

theorem equalAreaNormalizedE8Patch_iterated_norm (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Patch g v c ε) x‖ =
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) (x-c)‖ := by
  change ‖iteratedFDeriv ℝ k (g ∘ (fun z => equalAreaMovingNormalizedE8Chart v ε (z-c))) x‖ = _
  rw [g.norm_iteratedFDeriv_comp_left,iteratedFDeriv_comp_sub]

theorem equalAreaRotation_comp_norm_le (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (L : (Fin 8 → ℝ) →L[ℝ] Ambient9) :
    ‖(g : Ambient9 →L[ℝ] Ambient9).comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  change ‖g (L x)‖ ≤ ‖L‖*‖x‖
  rw [g.norm_map]
  exact L.le_opNorm x

theorem equalAreaNormalizedE8Patch_first_error (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) :
    ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) x-equalAreaRotatedFlatDerivative8 g‖ ≤
      ‖fderiv ℝ (equalAreaMovingNormalizedE8Chart v ε) (x-c)-equalAreaFlatDerivative8‖ := by
  rw [equalAreaNormalizedE8Patch_fderiv]
  change ‖(g : Ambient9 →L[ℝ] Ambient9).comp _-(g : Ambient9 →L[ℝ] Ambient9).comp _‖ ≤ _
  rw [←ContinuousLinearMap.comp_sub]
  exact equalAreaRotation_comp_norm_le g _

theorem equalAreaNormalizedE8Patch_increment_error (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (hc : c ∈ UnitCube 8) (ε : ℝ) (hε : 0 < ε)
    (hs : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (C : ℝ)
    (hb : ∀ z ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) z-equalAreaRotatedFlatDerivative8 g‖ ≤ C)
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    ‖(equalAreaNormalizedE8Patch g v c ε y-equalAreaRotatedFlatDerivative8 g (y-c))-
      (equalAreaNormalizedE8Patch g v c ε x-equalAreaRotatedFlatDerivative8 g (x-c))‖ ≤ C*‖y-x‖ := by
  apply unitCube8_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) z-equalAreaRotatedFlatDerivative8 g)
    _ hb hx hy
  intro z hz
  have hn : ‖v+ε • e8Map (z-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledE8_norm v ε (z-c) (unitCube8_sub_norm z c hz hc)).trans
      (by simpa only [abs_of_pos hε] using hs)
  have hf := equalAreaNormalizedE8Patch_hasFDerivAt g v c ε hε.ne' z
    (equalArea_small_norm_domain _ hn)
  have hl : HasFDerivAt (fun w => equalAreaRotatedFlatDerivative8 g (w-c))
      (equalAreaRotatedFlatDerivative8 g) z :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaRotatedFlatDerivative8 g).hasFDerivAt
  rw [hf.fderiv]
  exact (hf.sub hl).hasFDerivWithinAt

theorem equalAreaRotatedFlatDerivative8_dist (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (c x y : Fin 8 → ℝ) :
    dist (equalAreaRotatedFlatDerivative8 g (x-c)) (equalAreaRotatedFlatDerivative8 g (y-c)) =
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  change dist (g (equalAreaFlatDerivative8 (x-c))) (g (equalAreaFlatDerivative8 (y-c))) = _
  rw [g.dist_map,dist_eq_norm,←map_sub]
  have h : (x-c)-(y-c) = x-y := by abel
  rw [h,map_sub,←dist_eq_norm,equalAreaFlatDerivative8_dist]

theorem equalAreaNormalizedE8Patch_relative_distance_of_derivative
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : Fin 8 → ℝ) (hc : c ∈ UnitCube 8)
    (ε : ℝ) (hε : 0 < ε) (hs : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) z-equalAreaRotatedFlatDerivative8 g‖ ≤ C)
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    |dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
      (C*(1+‖e8InverseMap‖))*
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  rw [←equalAreaRotatedFlatDerivative8_dist g c,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedE8Patch g v c ε x-equalAreaNormalizedE8Patch g v c ε y)-
      (equalAreaRotatedFlatDerivative8 g (x-c)-equalAreaRotatedFlatDerivative8 g (y-c)) =
      (equalAreaNormalizedE8Patch g v c ε x-equalAreaRotatedFlatDerivative8 g (x-c))-
        (equalAreaNormalizedE8Patch g v c ε y-equalAreaRotatedFlatDerivative8 g (y-c)) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedE8Patch g v c ε x-equalAreaNormalizedE8Patch g v c ε y)-
        (equalAreaRotatedFlatDerivative8 g (x-c)-equalAreaRotatedFlatDerivative8 g (y-c))‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedE8Patch_increment_error g v c hc ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖e8InverseMap‖)*
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))) :=
      mul_le_mul_of_nonneg_left (equalAreaE8_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaRotatedFlatDerivative8_dist g c,dist_eq_norm]; ring

/-- Uniform C7 closeness of actual normalized sphere patches to the
rotated flat E8 embedding. The derivatives are actual fderiv/iteratedFDeriv. -/
theorem equalAreaNormalizedE8Patch_C7_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8, ∀ x ∈ UnitCube 8,
      ContDiffAt ℝ ∞ (equalAreaNormalizedE8Patch g v c ε) x ∧
      ‖equalAreaNormalizedE8Patch g v c ε x-equalAreaRotatedFlatDerivative8 g (x-c)‖ ≤ η ∧
      ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) x-equalAreaRotatedFlatDerivative8 g‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Patch g v c ε) x‖ ≤ η := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaMovingNormalizedE8Chart_C7_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx
  have hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8 := by linarith
  have hnorm : ‖v+ε • e8Map (x-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledE8_norm v ε (x-c) (unitCube8_sub_norm x c hx hc)).trans
      (by simpa only [abs_of_pos hε] using hsmall)
  have hfirst : ∀ z ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) z-equalAreaRotatedFlatDerivative8 g‖ ≤ η := by
    intro z hz
    exact (equalAreaNormalizedE8Patch_first_error g v c ε z).trans
      (hb v hv ε hε hs (z-c) (unitCube8_sub_norm z c hz hc)).1
  refine ⟨equalAreaNormalizedE8Patch_contDiffAt g v c ε x (equalArea_small_norm_domain _ hnorm),
    ?_,hfirst x hx,?_⟩
  · have h := equalAreaNormalizedE8Patch_increment_error g v c hc ε hε hsmall η hfirst c x hc hx
    simp only [equalAreaNormalizedE8Patch_center,sub_self,map_zero,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hη.le (unitCube8_sub_norm x c hx hc))
  · intro k hk hk7
    rw [equalAreaNormalizedE8Patch_iterated_norm]
    exact (hb v hv ε hε hs (x-c) (unitCube8_sub_norm x c hx hc)).2 k hk hk7

theorem equalAreaNormalizedE8Patch_relative_distance_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
      |dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y)-
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
        η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  have hd : 0 < 1+‖e8InverseMap‖ := by positivity
  let C : ℝ := η/(1+‖e8InverseMap‖)
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedE8Patch_C7_uniform C (by dsimp [C]; positivity)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have h := equalAreaNormalizedE8Patch_relative_distance_of_derivative g v c hc ε hε
    (by linarith) C (by dsimp [C]; positivity)
    (fun z hz => (hb v hv ε hε hs g c hc z hz).2.2.1) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

/-- A single positive lower Lipschitz constant for the actual patch class,
needed by the singular far-kernel estimates. -/
theorem equalAreaNormalizedE8Patch_lower_distance_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
      (1/(2*(1+‖e8InverseMap‖)))*‖x-y‖ ≤
        dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedE8Patch_relative_distance_uniform
    (1/2) (by norm_num)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have hd := (abs_le.mp (hb v hv ε hε hs g c hc x hx y hy)).1
  have hflat : dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) ≤
      2*dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y) := by
    linarith
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+‖e8InverseMap‖))).mpr
  have h := mul_le_mul_of_nonneg_left hflat (by positivity : 0 ≤ 1+‖e8InverseMap‖)
  have hcxy := equalAreaE8_distance_controls_coordinates x y
  nlinarith

end SphericalRiesz
