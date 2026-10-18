import Riesz.LeechTwelfthSmallBudget24
import Riesz.LeechTwelfthGaussianBudget24

/-! Physical sphere form of the twelfth-order bump error at exact mass.

For one small Leech cube patch at the exact-mass rational allocation `ε d = r₀ a`, `n = a m`,
`N = (d m)^24`, the node sum of an ambient Gaussian bump differs from `N ∫_patch` by at most
`K (n⁻¹² + (2πα)⁶) N ∫_patch` of the softened bump.  Summing over a finite disjoint family of one
common scale bounds the foreground bump error by the softened bump field of the whole sphere.
No configuration, budget or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

/-- The physical sphere patch of a small Leech cube patch. -/
def smallLeechSpherePatch24 (p : SmallLeechCubePatch24) : Set (SphereD 24) :=
  equalAreaLeechSpherePatch24 p.g p.v p.c p.ε (UnitCube 24)

theorem smallLeechSpherePatch24_measurable (p : SmallLeechCubePatch24) :
    MeasurableSet (smallLeechSpherePatch24 p) :=
  equalAreaLeechSpherePatch24_measurable p.g p.v p.c p.ε p.ε_pos _ (unitCube_measurableSet 24)
    (equalAreaLeechAffine24_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small)

theorem smallLeechCubeMap24_continuousOn (p : SmallLeechCubePatch24) :
    ContinuousOn (smallLeechCubeMap24 p) (UnitCube 24) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp
    (equalAreaLeechCubeEmbedding24_continuous p.g p.v p.c p.ε p.ε_pos p.c_mem p.small)

/-- Transport of a patch integral to the coordinate cube, for continuous ambient functions. -/
theorem smallLeechSpherePatch24_setIntegral (p : SmallLeechCubePatch24) (f : AmbientD 24 → ℝ)
    (hf : Continuous f) :
    (∫ y in smallLeechSpherePatch24 p, f (y : AmbientD 24) ∂(sphereProbabilityD 24)) =
      equalAreaLeechPatchProbabilityDensity24 p.ε*
        cubeIntegral 24 (fun x => f (smallLeechCubeMap24 p x)) := by
  have h := cubeIntegral_eq_setIntegral_on 24 (fun x => f (smallLeechCubeMap24 p x))
    (hf.comp_continuousOn (smallLeechCubeMap24_continuousOn p))
  rw [h]
  exact equalAreaLeechSpherePatch24_integral p.g p.v p.c p.ε p.ε_pos p.c_mem p.small f

/-- Twelfth-order nodes of a small patch on the sphere. -/
def smallLeechPatchNodes24 (p : SmallLeechCubePatch24) (n : ℕ) (hn : 74 ≤ n) :
    (Fin 24 → TwelveNodeIndex n) → SphereD 24 :=
  leechTwelfthSphereNodes24 n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallLeechPatchNodes24_injective (p : SmallLeechCubePatch24) (n : ℕ) (hn : 74 ≤ n) :
    Function.Injective (smallLeechPatchNodes24 p n hn) :=
  leechTwelfthSphereNodes24_injective n hn p.g p.v p.c p.c_mem p.ε p.ε_pos p.small

theorem smallLeechPatchNodes24_coe (p : SmallLeechCubePatch24) (n : ℕ) (hn : 74 ≤ n)
    (u : Fin 24 → TwelveNodeIndex n) :
    (smallLeechPatchNodes24 p n hn u : AmbientD 24) = smallLeechCubeMap24 p (twelveCubeNode 24 n u) :=
  rfl

theorem smallLeechPatchNodes24_mem (p : SmallLeechCubePatch24) (n : ℕ) (hn : 74 ≤ n)
    (u : Fin 24 → TwelveNodeIndex n) :
    smallLeechPatchNodes24 p n hn u ∈ smallLeechSpherePatch24 p := by
  refine ⟨twelveCubeNode 24 n u, fun i => ⟨(twelveCubeNode_mem_open 24 n hn u i).1.le,
    (twelveCubeNode_mem_open 24 n hn u i).2.le⟩, rfl⟩

theorem ambientBump25_sphere_integrable {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 24) :
    Integrable (fun y : SphereD 24 => ambientBump25 t (y : AmbientD 24) z)
      (sphereProbabilityD 24) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold ambientBump25; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (ambientBump25_nonneg _ _ _)]
  exact ambientBump25_le_one ht _ _

theorem bumpField25_sphere_eq (t : ℝ) (z : AmbientD 24) :
    bumpField25 t ambientSphereProbability24 z =
      ∫ y : SphereD 24, ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24) := by
  unfold bumpField25 ambientSphereProbability24
  rw [integral_map (by fun_prop) (by unfold ambientBump25; fun_prop)]

/-- One patch, exact mass: the node sum against `N ∫_patch` of the bump. -/
theorem smallLeechPatch_bump_sphere_error24 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 24,
      |(∑ u : Fin 24 → TwelveNodeIndex (a*m),
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α)
            (smallLeechPatchNodes24 p (a*m) hn u : AmbientD 24) z)-
        (((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)| ≤
      bumpErrorConst24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6)*
        ((((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 p,
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α/8) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_rational_small_alpha24
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε a d m hd hm hratio hn α hα z
  have hquad := hb p hv hε leechUnitDensityRadius24 leechUnitDensityRadius24_twelfth_mesh_bound
    a d m hd hm hratio hn α hα z
  have hτ := sphereGaussian_exact_mass_bump_scale24 a d m hd p.ε α hratio
  set t := sphereGaussianScale24 ((d*m)^24) α with ht
  have hn0 : (0:ℝ) < ((a*m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < a*m)
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdens := leechTwelfth_rational_exact_patch_mass24 a d m hd hm p.ε hratio
  have hsum : (∑ u : Fin 24 → TwelveNodeIndex (a*m),
      ambientBump25 t (smallLeechPatchNodes24 p (a*m) hn u : AmbientD 24) z) =
      ((a*m:ℕ):ℝ)^24*twelveCubeQuadrature 24 (a*m)
        (fun x => ambientBump25 t (smallLeechCubeMap24 p x) z) := by
    rw [twelveCubeQuadrature_as_node_sum, mul_div_cancel₀ _ (pow_pos hn0 24).ne']
    exact Finset.sum_congr rfl fun u _ => by rw [smallLeechPatchNodes24_coe]
  have hI : ∀ τ : ℝ, (((d*m)^24:ℕ):ℝ)*(∫ y in smallLeechSpherePatch24 p,
      ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24)) =
      ((a*m:ℕ):ℝ)^24*cubeIntegral 24 (fun x => ambientBump25 τ (smallLeechCubeMap24 p x) z) := by
    intro τ
    rw [smallLeechSpherePatch24_setIntegral p (fun y => ambientBump25 τ y z)
      (by unfold ambientBump25; fun_prop), hdens]
    push_cast
    field_simp
  have hsoft : (fun x => Real.exp (-(t/4*‖smallLeechCubeMap24 p x-z‖^2))) =
      fun x => ambientBump25 (t/8) (smallLeechCubeMap24 p x) z := by
    funext x
    unfold ambientBump25
    rw [show t/4*‖smallLeechCubeMap24 p x-z‖^2 = 2*(t/8)*‖smallLeechCubeMap24 p x-z‖^2 by ring]
  rw [hsoft] at hquad
  rw [hsum, hI t, hI (t/8), ← mul_sub, abs_mul, abs_of_pos (pow_pos hn0 24)]
  calc
    _ ≤ ((a*m:ℕ):ℝ)^24*(bumpErrorConst24 patchChartUpper24 patchChartLower24/((a*m:ℕ):ℝ)^12*
        (1+(2*t*p.ε^2)^6)*
        cubeIntegral 24 (fun x => ambientBump25 (t/8) (smallLeechCubeMap24 p x) z)) :=
      mul_le_mul_of_nonneg_left hquad (by positivity)
    _ = _ := by
      rw [hτ]
      field_simp

/-- A finite disjoint family of one common scale: the foreground bump error is bounded by the
softened bump field of the whole sphere. -/
theorem leechPatchFamily_bump_error24 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 24,
      |(∑ i, ∑ u : Fin 24 → TwelveNodeIndex (a*m),
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α)
            (smallLeechPatchNodes24 (P i) (a*m) hn u : AmbientD 24) z)-
        (((d*m)^24:ℕ):ℝ)*∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
          ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (y : AmbientD 24) z
            ∂(sphereProbabilityD 24)| ≤
      bumpErrorConst24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6)*
        ((((d*m)^24:ℕ):ℝ)*
          bumpField25 (sphereGaussianScale24 ((d*m)^24) α/8) ambientSphereProbability24 z) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_sphere_error24
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα z
  have hts : 0 < sphereGaussianScale24 ((d*m)^24) α :=
    sphereGaussianScale24_pos (by positivity) hα.1
  set t := sphereGaussianScale24 ((d*m)^24) α with ht
  set C := bumpErrorConst24 patchChartUpper24 patchChartLower24*
    (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6) with hC
  have hC0 : 0 ≤ C := by
    have hK : 0 ≤ bumpErrorConst24 patchChartUpper24 patchChartLower24 := by
      unfold bumpErrorConst24 twelfthConst
      have := one_le_patchChartUpper24
      have := gaussRuleConst12_nonneg
      positivity
    have hα0 := hα.1
    rw [hC]
    positivity
  have hsplit : ∀ τ : ℝ, 0 ≤ τ → (∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
      ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24)) =
      ∑ i, ∫ y in smallLeechSpherePatch24 (P i),
        ambientBump25 τ (y : AmbientD 24) z ∂(sphereProbabilityD 24) := by
    intro τ hτ
    rw [integral_iUnion (fun i => smallLeechSpherePatch24_measurable (P i))
      (fun i j hij => hdisj hij) (ambientBump25_sphere_integrable hτ z).integrableOn,
      tsum_fintype]
  have hle : (∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
      ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) ≤
      bumpField25 (t/8) ambientSphereProbability24 z := by
    rw [bumpField25_sphere_eq]
    exact setIntegral_le_integral (ambientBump25_sphere_integrable (by positivity) z)
      (Filter.Eventually.of_forall fun y => ambientBump25_nonneg _ _ _)
  rw [hsplit t hts.le, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ u : Fin 24 → TwelveNodeIndex (a*m),
          ambientBump25 t (smallLeechPatchNodes24 (P i) (a*m) hn u : AmbientD 24) z)-
        (((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*((((d*m)^24:ℕ):ℝ)*∫ y in smallLeechSpherePatch24 (P i),
          ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) :=
      Finset.sum_le_sum fun i _ => hb (P i) (hv i) (hε i) a d m hd hm (hratio i) hn α hα z
    _ = C*((((d*m)^24:ℕ):ℝ)*∫ y in ⋃ i, smallLeechSpherePatch24 (P i),
          ambientBump25 (t/8) (y : AmbientD 24) z ∂(sphereProbabilityD 24)) := by
      rw [hsplit (t/8) (by positivity), Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact mul_le_mul_of_nonneg_left hle (by positivity)

end SphericalRiesz
