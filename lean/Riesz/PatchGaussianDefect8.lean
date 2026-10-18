import Riesz.SmallPatchBumpError8
import Riesz.RationalResidualPoints8

/-! The Gaussian defect of the rational patch nodes against their own background.

For the nodes of a rational family of small disjoint E8 patches (`n = a m` nodes per side,
`N = (d m)⁸`, common density `(a/d)⁸`) and the background `N σ|_S`, the bump error of the whole
family is the sum of the patch bump errors, each bounded by the localized sixth-order estimate.
The patches are disjoint, so the localized majorants add up to one sphere bump field, and the
square form of the defect gives, with `τ = 2tε²`,

  `D_P(t) ≤ 8^{9/2} (K n² (1+τ³)/(a/d)⁸)² B_σ(t/8)`,

as long as `τ C₀²/128 ≤ n²`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The background of the patch union as a measure on `Ambient9`. -/
def patchBackground8 (S : Set Sphere8) : Measure Ambient9 :=
  (sphereProbability8.restrict S).map (fun x : Sphere8 => (x:Ambient9))

instance patchBackground8_finite (S : Set Sphere8) : IsFiniteMeasure (patchBackground8 S) := by
  unfold patchBackground8
  infer_instance

theorem patchBackground8_bump (S : Set Sphere8) (t : ℝ) (z : Ambient9) :
    bumpField9 t (patchBackground8 S) z =
      ∫ y in S, ambientBump9 t (y:Ambient9) z ∂sphereProbability8 := by
  unfold bumpField9 patchBackground8
  rw [integral_map (by fun_prop)]
  exact (continuous_ambientBump9 t).comp (continuous_id.prodMk continuous_const) |>.aestronglyMeasurable

theorem ambientSphere_bump (t : ℝ) (z : Ambient9) :
    bumpField9 t ambientSphereProbability8 z =
      ∫ y, ambientBump9 t (y:Ambient9) z ∂sphereProbability8 := by
  unfold bumpField9 ambientSphereProbability8
  rw [integral_map (by fun_prop)]
  exact (continuous_ambientBump9 t).comp (continuous_id.prodMk continuous_const) |>.aestronglyMeasurable

/-- One patch: the node sum minus the background is the scaled tensor quadrature error. -/
theorem patch_bump_error_eq (p : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n) {M : ℝ}
    (hM : M*smallE8CubeDensity8 p = (n:ℝ)^8) (t : ℝ) (z : Ambient9) :
    (∑ u : Fin 8 → NodeIndex n, ambientBump9 t (smallE8CubeMap8 p (cubeNode 8 n u)) z)-
      M*∫ y in smallE8CubeSet8 p, ambientBump9 t (y:Ambient9) z ∂sphereProbability8 =
      (n:ℝ)^8*(cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)) := by
  have hcont : ContinuousOn (fun x => ambientBump9 t (smallE8CubeMap8 p x) z) (UnitCube 8) := by
    intro x hx
    have hc : ContinuousAt (smallE8CubeMap8 p) x := (smallE8CubeMap8_contDiffAt p x hx).continuousAt
    exact ((continuous_ambientBump9 t).continuousAt.comp
      (hc.prodMk continuousAt_const)).continuousWithinAt
  have hI := smallE8CubeSet8_integral p (fun y => ambientBump9 t y z)
  rw [hI, ← cubeIntegral_eq_setIntegral_on 8 _ hcont, cubeQuadrature_as_node_sum]
  have hn0 : (n:ℝ)^8 ≠ 0 := by positivity
  rw [← mul_assoc, hM]
  field_simp

/-- The patch union integral splits over the disjoint patches. -/
theorem patchUnion_integral {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (f : Ambient9 → ℝ) (hf : Continuous f) :
    ∫ y in ⋃ i, smallE8CubeSet8 (P i), f (y:Ambient9) ∂sphereProbability8 =
      ∑ i, ∫ y in smallE8CubeSet8 (P i), f (y:Ambient9) ∂sphereProbability8 := by
  have hint : IntegrableOn (fun y : Sphere8 => f (y:Ambient9)) (⋃ i, smallE8CubeSet8 (P i))
      sphereProbability8 := by
    exact (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact
      (isCompact_iUnion fun i => smallE8CubeSet8_isCompact (P i))
  rw [integral_iUnion (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
    (fun i j hij => hdis hij) hint, tsum_fintype]

/-- Physical form of the per-patch majorant. -/
theorem patch_majorant_eq (p : SmallE8CubePatch8) (t : ℝ) (z : Ambient9) :
    cubeIntegral 8 (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2))) =
      (∫ y in smallE8CubeSet8 p, ambientBump9 (t/8) (y:Ambient9) z ∂sphereProbability8)/
        smallE8CubeDensity8 p := by
  have hcont : ContinuousOn (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2))) (UnitCube 8) := by
    intro x hx
    have hc : ContinuousAt (smallE8CubeMap8 p) x := (smallE8CubeMap8_contDiffAt p x hx).continuousAt
    exact (Real.continuous_exp.continuousAt.comp
      ((((hc.sub continuousAt_const).norm).pow 2).const_mul (t/4)).neg).continuousWithinAt
  have hI := smallE8CubeSet8_integral p (fun y => ambientBump9 (t/8) y z)
  have hρ := (smallE8CubeDensity8_pos p).ne'
  rw [hI, cubeIntegral_eq_setIntegral_on 8 _ hcont]
  field_simp
  congr 1
  funext x
  unfold ambientBump9
  ring_nf

/-- A pointwise majorant of the bump error by the sphere bump field at `t/8` bounds the defect. -/
theorem gaussianMeasureDefect_le_sphere_bump {t : ℝ} (ht : 0 < t) (M : ℝ) (μ ν : Measure Ambient9)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {K' : ℝ}
    (hle : ∀ z, |bumpField9 t μ z-M*bumpField9 t ν z| ≤
      K'*bumpField9 (t/8) ambientSphereProbability8 z) :
    gaussianMeasureDefect t M μ ν ≤ (8:ℝ)^((9:ℝ)/2)*K'^2*sphereGaussianBackground8 (t/8) := by
  have ht8 : 0 < t/8 := by positivity
  have hW : Integrable (fun z => (K'*bumpField9 (t/8) ambientSphereProbability8 z)^2) := by
    refine ((bumpField9_mul_integrable ht8 ambientSphereProbability8
      ambientSphereProbability8).const_mul (K'^2)).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  have h := gaussianMeasureDefect_le_of_bump ht M μ ν hW hle
  refine h.trans (le_of_eq ?_)
  have hpair := gaussianMeasurePair_eq_bump ht8 ambientSphereProbability8 ambientSphereProbability8
  rw [ambientSphereProbability8_kernel_pair] at hpair
  have hsq : (fun z => (K'*bumpField9 (t/8) ambientSphereProbability8 z)^2) =
      fun z => K'^2*(bumpField9 (t/8) ambientSphereProbability8 z*
        bumpField9 (t/8) ambientSphereProbability8 z) := by
    funext z; ring
  rw [hsq, integral_const_mul]
  have hc : (0:ℝ) < (4*(t/8)/Real.pi)^((9:ℝ)/2) := by positivity
  have hint : (∫ z, bumpField9 (t/8) ambientSphereProbability8 z*
      bumpField9 (t/8) ambientSphereProbability8 z) =
      sphereGaussianBackground8 (t/8)/(4*(t/8)/Real.pi)^((9:ℝ)/2) := by
    rw [hpair]; field_simp
  rw [hint]
  have h8 : (4*t/Real.pi)^((9:ℝ)/2)/(4*(t/8)/Real.pi)^((9:ℝ)/2) = (8:ℝ)^((9:ℝ)/2) := by
    rw [← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc (4*t/Real.pi)^((9:ℝ)/2)*(K'^2*(sphereGaussianBackground8 (t/8)/
        (4*(t/8)/Real.pi)^((9:ℝ)/2)))
      = ((4*t/Real.pi)^((9:ℝ)/2)/(4*(t/8)/Real.pi)^((9:ℝ)/2))*K'^2*
          sphereGaussianBackground8 (t/8) := by ring
    _ = (8:ℝ)^((9:ℝ)/2)*K'^2*sphereGaussianBackground8 (t/8) := by rw [h8]

theorem rationalPatchNodes_bumpField {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (a m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) (t : ℝ) (z : Ambient9) :
    bumpField9 t (finitePointMeasure
        (fun u => (rationalCubePatchNodes8 P a m ha hm u : Ambient9))) z =
      ∑ i, ∑ u : Fin 8 → NodeIndex (a*m),
        ambientBump9 t (smallE8CubeMap8 (P i) (cubeNode 8 (a*m) u)) z := by
  unfold bumpField9
  rw [finitePointMeasure_integral, Fintype.sum_prod_type]
  rfl

theorem patchUnion_bump_integral {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (s : ℝ) (z : Ambient9) :
    ∫ y in ⋃ i, smallE8CubeSet8 (P i), ambientBump9 s (y:Ambient9) z ∂sphereProbability8 =
      ∑ i, ∫ y in smallE8CubeSet8 (P i), ambientBump9 s (y:Ambient9) z ∂sphereProbability8 := by
  have hint : IntegrableOn (fun y : Sphere8 => ambientBump9 s (y:Ambient9) z)
      (⋃ i, smallE8CubeSet8 (P i)) sphereProbability8 :=
    ((continuous_ambientBump9 s).comp (continuous_subtype_val.prodMk continuous_const)).continuousOn.integrableOn_compact
      (isCompact_iUnion fun i => smallE8CubeSet8_isCompact (P i))
  rw [integral_iUnion (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
    (fun i j hij => hdis hij) hint, tsum_fintype]

theorem patchBackground8_bumpField_union {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (t : ℝ) (z : Ambient9) :
    bumpField9 t (patchBackground8 (⋃ i, smallE8CubeSet8 (P i))) z =
      ∑ i, ∫ y in smallE8CubeSet8 (P i), ambientBump9 t (y:Ambient9) z ∂sphereProbability8 := by
  rw [patchBackground8_bump]
  exact patchUnion_bump_integral P hdis t z

theorem patchUnion_bump_le_sphere {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (s : ℝ) (z : Ambient9) :
    (∑ i, ∫ y in smallE8CubeSet8 (P i), ambientBump9 s (y:Ambient9) z ∂sphereProbability8) ≤
      bumpField9 s ambientSphereProbability8 z := by
  rw [← patchUnion_bump_integral P hdis s z, ambientSphere_bump]
  apply setIntegral_le_integral
  · exact ((continuous_ambientBump9 s).comp
      (continuous_subtype_val.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact Filter.Eventually.of_forall fun y => ambientBump9_nonneg _ _ _

/-- Summation of patch majorants. -/
theorem family_bump_error_le {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (n : ℕ) {N K' t : ℝ} (hK' : 0 ≤ K') (z : Ambient9)
    (hpatch : ∀ i, |(∑ u : Fin 8 → NodeIndex n,
        ambientBump9 t (smallE8CubeMap8 (P i) (cubeNode 8 n u)) z)-
        N*∫ y in smallE8CubeSet8 (P i), ambientBump9 t (y:Ambient9) z ∂sphereProbability8| ≤
        K'*∫ y in smallE8CubeSet8 (P i), ambientBump9 (t/8) (y:Ambient9) z ∂sphereProbability8) :
    |(∑ i, ∑ u : Fin 8 → NodeIndex n, ambientBump9 t (smallE8CubeMap8 (P i) (cubeNode 8 n u)) z)-
      N*∑ i, ∫ y in smallE8CubeSet8 (P i), ambientBump9 t (y:Ambient9) z ∂sphereProbability8| ≤
      K'*bumpField9 (t/8) ambientSphereProbability8 z := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hpatch i).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (patchUnion_bump_le_sphere P hdis (t/8) z) hK'

/-- One patch: the scaled localized error. -/
theorem patch_bump_error_le (p : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n) {N δ Kb τ t : ℝ}
    (hNδ : N*smallE8CubeDensity8 p = (n:ℝ)^8) (hδ : smallE8CubeDensity8 p = δ) (hδ0 : 0 < δ)
    (z : Ambient9)
    (h : |cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)| ≤
        Kb/(n:ℝ)^6*(1+τ^3)*cubeIntegral 8 (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2)))) :
    |(∑ u : Fin 8 → NodeIndex n, ambientBump9 t (smallE8CubeMap8 p (cubeNode 8 n u)) z)-
      N*∫ y in smallE8CubeSet8 p, ambientBump9 t (y:Ambient9) z ∂sphereProbability8| ≤
      (Kb*(n:ℝ)^2*(1+τ^3)/δ)*∫ y in smallE8CubeSet8 p, ambientBump9 (t/8) (y:Ambient9) z
        ∂sphereProbability8 := by
  rw [patch_bump_error_eq p n hn hNδ t z, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)^8)]
  rw [patch_majorant_eq, hδ] at h
  have hn0 : (0:ℝ) < (n:ℝ)^6 := by
    have : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  calc (n:ℝ)^8*|cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)|
      ≤ (n:ℝ)^8*(Kb/(n:ℝ)^6*(1+τ^3)*((∫ y in smallE8CubeSet8 p,
          ambientBump9 (t/8) (y:Ambient9) z ∂sphereProbability8)/δ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Kb*(n:ℝ)^2*(1+τ^3)/δ)*∫ y in smallE8CubeSet8 p, ambientBump9 (t/8) (y:Ambient9) z
          ∂sphereProbability8 := by
        field_simp

/-- The Gaussian defect of the rational patch nodes against the background `N σ|_S`. -/
theorem rationalPatchDefect_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m) {ε : ℝ},
      (∀ i, (P i).ε = ε) → (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ t : ℝ, 0 < t → 2*t*ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 →
      diffuseGaussianDefect t (((d*m)^8:ℕ):ℝ)
          (fun u => (rationalCubePatchNodes8 P a m ha hm u : Ambient9))
          (patchBackground8 (⋃ i, smallE8CubeSet8 (P i))) ≤
        (8:ℝ)^((9:ℝ)/2)*(bumpErrorConst patchChartUpper8 patchChartLower8*((a*m:ℕ):ℝ)^2*
          (1+(2*t*ε^2)^3)/((a:ℝ)/d)^8)^2*sphereGaussianBackground8 (t/8) := by
  obtain ⟨ρ, hρ, hρ1, hbump⟩ := smallPatch_bump_quadrature
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro K P hdis hsmall a d m ha hd hm ε hε hdens t ht htn
  have hn : 8 ≤ a*m := hm.trans (Nat.le_mul_of_pos_left m ha)
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hδ : (0:ℝ) < ((a:ℝ)/d)^8 := by positivity
  have hKb : 0 ≤ bumpErrorConst patchChartUpper8 patchChartLower8 := by
    rw [bumpErrorConst, sixthConst]
    positivity
  have hK' : 0 ≤ bumpErrorConst patchChartUpper8 patchChartLower8*((a*m:ℕ):ℝ)^2*
      (1+(2*t*ε^2)^3)/((a:ℝ)/d)^8 := by
    have : 0 ≤ 2*t*ε^2 := by positivity
    positivity
  have hNdens : ∀ i, (((d*m)^8:ℕ):ℝ)*smallE8CubeDensity8 (P i) = ((a*m:ℕ):ℝ)^8 := by
    intro i
    rw [hdens i]
    push_cast
    field_simp
  rw [diffuseGaussianDefect_eq_measureDefect ht.le]
  apply gaussianMeasureDefect_le_sphere_bump ht
  intro z
  rw [rationalPatchNodes_bumpField, patchBackground8_bumpField_union P hdis]
  apply family_bump_error_le P hdis (a*m) hK' z
  intro i
  have hβ : 2*t*(P i).ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 := by
    rw [hε i]; exact htn
  have h := hbump (P i) (hsmall i).1 (hsmall i).2 (a*m) hn t ht hβ z
  rw [hε i] at h
  exact patch_bump_error_le (P i) (a*m) hn (hNdens i) (hdens i) hδ z h

end SphericalRiesz
