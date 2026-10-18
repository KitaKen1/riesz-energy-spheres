import Riesz.NormalizedBumpError24
import Riesz.AmbientBumpSquare25

/-! Localized order-twelve error on actual physical Leech sphere patches.
One radius and one error constant apply to every rotation and center. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedLeechPatch_Cn_uniform (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 24 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), ∀ c ∈ UnitCube 24, ∀ x ∈ UnitCube 24,
      ContDiffAt ℝ ∞ (equalAreaNormalizedLeechPatch g v c ε) x ∧
      ‖equalAreaNormalizedLeechPatch g v c ε x-equalAreaRotatedFlatDerivative24 g (x-c)‖ ≤ η ∧
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch g v c ε) x-equalAreaRotatedFlatDerivative24 g‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedLeechPatch g v c ε) x‖ ≤ η := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaMovingNormalizedLeechChart_Cn_uniform n η hη
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

structure SmallLeechCubePatch24 where
  g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24
  v : Fin 24 → ℝ
  c : Fin 24 → ℝ
  ε : ℝ
  ε_pos : 0 < ε
  c_mem : c ∈ UnitCube 24
  small : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8

def smallLeechCubeMap24 (p : SmallLeechCubePatch24) : (Fin 24 → ℝ) → AmbientD 24 :=
  equalAreaLeechPatch p.g p.v p.c p.ε

def smallLeechCubeEmbedding24 (p : SmallLeechCubePatch24) : UnitCube 24 ↪ SphereD 24 :=
  equalAreaLeechCubeEmbedding24 p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

/-- Upper derivative and Lipschitz constant of the normalized patch charts. -/
def patchChartUpper24 : ℝ := ‖equalAreaFlatDerivative24‖+1

/-- Lower Lipschitz constant of the normalized patch charts. -/
def patchChartLower24 : ℝ := 1/(2*(1+‖leechInverseMap‖))

theorem one_le_patchChartUpper24 : 1 ≤ patchChartUpper24 := by
  unfold patchChartUpper24
  linarith [norm_nonneg equalAreaFlatDerivative24]

theorem patchChartLower24_pos : 0 < patchChartLower24 := by
  unfold patchChartLower24
  positivity

theorem smallLeechPatch_normalized_chart_bounds12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      (∀ x ∈ UnitCube 24, ContDiffAt ℝ 12 (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x) ∧
      (∀ x ∈ UnitCube 24, ∀ j, 1 ≤ j → j ≤ 12 →
        ‖iteratedFDeriv ℝ j (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper24) ∧
      (∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24, patchChartLower24*‖x-y‖ ≤
        ‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-equalAreaNormalizedLeechPatch p.g p.v p.c p.ε y‖) ∧
      (∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
        ‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-equalAreaNormalizedLeechPatch p.g p.v p.c p.ε y‖ ≤
          patchChartUpper24*‖x-y‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁', h₁⟩ := equalAreaNormalizedLeechPatch_Cn_uniform 12 1 one_pos
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε
  have hv₁ : ‖p.v‖ ≤ ρ₁ := hv.trans (min_le_left _ _)
  have hv₂ : ‖p.v‖ ≤ ρ₂ := hv.trans (min_le_right _ _)
  have hε₁ : p.ε*equalAreaScaleRadius24 ≤ ρ₁ := hε.trans (min_le_left _ _)
  have hε₂ : p.ε*equalAreaScaleRadius24 ≤ ρ₂ := hε.trans (min_le_right _ _)
  have hb := fun x hx => h₁ p.v hv₁ p.ε p.ε_pos hε₁ p.g p.c p.c_mem x hx
  have hflat : ‖equalAreaRotatedFlatDerivative24 p.g‖ ≤ ‖equalAreaFlatDerivative24‖ :=
    equalAreaRotation24_comp_norm_le p.g equalAreaFlatDerivative24
  have hfd : ∀ x ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper24 := by
    intro x hx
    have h := (hb x hx).2.2.1
    calc ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x‖
        = ‖(fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative24 p.g)+equalAreaRotatedFlatDerivative24 p.g‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative24 p.g‖+‖equalAreaRotatedFlatDerivative24 p.g‖ :=
          norm_add_le _ _
      _ ≤ 1+‖equalAreaFlatDerivative24‖ := add_le_add h hflat
      _ = patchChartUpper24 := by rw [patchChartUpper24]; ring
  refine ⟨fun x hx => (hb x hx).1.of_le (by simp), ?_, ?_, ?_⟩
  · intro x hx j hj hj6
    rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 1 := by omega
      subst this
      rw [norm_iteratedFDeriv_one]
      exact hfd x hx
    · exact ((hb x hx).2.2.2 j h (by omega)).trans one_le_patchChartUpper24
  · intro x hx y hy
    have h := h₂ p.v hv₂ p.ε p.ε_pos hε₂ p.g p.c p.c_mem x hx y hy
    rw [dist_eq_norm] at h
    simpa only [patchChartLower24] using h
  · intro x hx y hy
    exact unitCube24_convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hb z hz).1.differentiableAt (by simp))) hfd hy hx

/-- The patch map in normalized form. -/
theorem smallLeechCubeMap24_sub_eq (p : SmallLeechCubePatch24) (z : AmbientD 24) (x : Fin 24 → ℝ) :
    smallLeechCubeMap24 p x-z = p.ε • (equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallLeechCubeMap24 p p.c)) := by
  have hε := p.ε_pos.ne'
  rw [equalAreaNormalizedLeechPatch_eq, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hε, one_smul,
    one_smul]
  change equalAreaLeechPatch p.g p.v p.c p.ε x-z = _
  unfold smallLeechCubeMap24
  abel

theorem smallLeechCubeMap24_sub_norm_sq (p : SmallLeechCubePatch24) (z : AmbientD 24) (x : Fin 24 → ℝ) :
    ‖smallLeechCubeMap24 p x-z‖^2 = p.ε^2*‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallLeechCubeMap24 p p.c)‖^2 := by
  rw [smallLeechCubeMap24_sub_eq, norm_smul, Real.norm_eq_abs, abs_of_pos p.ε_pos, mul_pow]

/-- Localized twelfth-order error of an ambient Gaussian bump on one small patch. -/
theorem smallLeechPatch_bump_quadrature12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ n : ℕ, 74 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2*patchChartLower24^2/384 ≤ (n:ℝ)^2 →
      ∀ z : AmbientD 24,
      |twelveCubeQuadrature 24 n (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)-
        cubeIntegral 24 (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)| ≤
        bumpErrorConst24 patchChartUpper24 patchChartLower24/(n:ℝ)^12*(1+(2*t*p.ε^2)^6)*
          cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallLeechPatch_normalized_chart_bounds12
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτn z
  obtain ⟨hcd, hder, hlow, hup⟩ := hb p hv hε
  set w := p.ε⁻¹ • (z-smallLeechCubeMap24 p p.c) with hw
  set τ := 2*t*p.ε^2 with hτdef
  have hτ : 0 < τ := by have := p.ε_pos; positivity
  have hf1 : (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z) =
      fun x => Real.exp (-(τ*‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    unfold ambientBump25
    rw [smallLeechCubeMap24_sub_norm_sq, ← hw, hτdef]
    ring_nf
  have hf2 : (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) =
      fun x => Real.exp (-(τ/8*‖equalAreaNormalizedLeechPatch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    rw [smallLeechCubeMap24_sub_norm_sq, ← hw, hτdef]
    ring_nf
  rw [hf1, hf2]
  exact normalized_bump_quadrature_error24 one_le_patchChartUpper24 patchChartLower24_pos hcd hder
    hlow hup hn hτ (by rw [hτdef]; exact hτn) w

/-- Squaring the actual patch error cancels its exact n^24 point density. -/
theorem smallLeechPatch_bump_squared_density12 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ n : ℕ, 74 ≤ n → ∀ t : ℝ, 0 < t →
      2*t*p.ε^2*patchChartLower24^2/384 ≤ (n:ℝ)^2 → ∀ z : AmbientD 24,
      (n:ℝ)^24*(twelveCubeQuadrature 24 n (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)-
        cubeIntegral 24 (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z))^2 ≤
      (bumpErrorConst24 patchChartUpper24 patchChartLower24*(1+(2*t*p.ε^2)^6)*
        cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))))^2 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_quadrature12
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht hmesh z
  have h := hb p hv hε n hn t ht hmesh z
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : (n:ℝ)^12*|twelveCubeQuadrature 24 n (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)-
      cubeIntegral 24 (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z)| ≤
      bumpErrorConst24 patchChartUpper24 patchChartLower24*(1+(2*t*p.ε^2)^6)*
        cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) := by
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n:ℝ)^12)
    calc
      _ ≤ (n:ℝ)^12*(bumpErrorConst24 patchChartUpper24 patchChartLower24/(n:ℝ)^12*
        (1+(2*t*p.ε^2)^6)*cubeIntegral 24 (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2)))) := h'
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (by positivity) he 2
  simpa only [mul_pow,←pow_mul,sq_abs] using hh

end SphericalRiesz
