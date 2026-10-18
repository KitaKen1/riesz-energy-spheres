import Riesz.Definitions
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
The actual uniform probability measure on the unit S8, normalized from ambient
Lebesgue volume. Orthogonal invariance and a single explicit reflection give
constant inverse-fourth potential. Its integrability and value 7/16 are still
separate analytic obligations: symmetry of the total Bochner integral does not
prove either of them.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise
namespace SphericalRiesz

abbrev Ambient9 := EuclideanSpace ℝ (Fin 9)

def sphereArea8 : Measure Sphere8 := (volume : Measure Ambient9).toSphere

theorem sphereArea8_ne_zero : sphereArea8 ≠ 0 :=
  Measure.toSphere_ne_zero (volume : Measure Ambient9)

instance sphereArea8_nonzero : NeZero sphereArea8 := ⟨sphereArea8_ne_zero⟩
instance sphereArea8_finite : IsFiniteMeasure sphereArea8 := by
  unfold sphereArea8
  infer_instance

def sphereProbability8 : Measure Sphere8 := (sphereArea8 univ)⁻¹ • sphereArea8

instance sphereProbability8_probability : IsProbabilityMeasure sphereProbability8 := by
  unfold sphereProbability8
  infer_instance

theorem sphereProbability8_mass : sphereProbability8 univ = 1 := measure_univ

def sphereRotation8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) : Sphere8 ≃ₜ Sphere8 where
  toFun x := ⟨g x, by simpa only [mem_sphere_zero_iff_norm, g.norm_map] using x.property⟩
  invFun x := ⟨g.symm x, by simpa only [mem_sphere_zero_iff_norm, g.symm.norm_map] using x.property⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x)
  right_inv x := Subtype.ext (g.apply_symm_apply x)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sphereRotation8_dist (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x y : Sphere8) :
    dist (sphereRotation8 g x) (sphereRotation8 g y) = dist x y :=
  g.dist_map x y

/-- Radial cones commute with the actual ambient isometry. -/
theorem sphereRotation8_cone_preimage (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (s : Set Sphere8) :
    g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereRotation8 g) ⁻¹' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, h⟩
    refine ⟨r, hr, g.symm y, ⟨sphereRotation8 g.symm y, ?_, rfl⟩, ?_⟩
    · change sphereRotation8 g (sphereRotation8 g.symm y) ∈ s
      convert hy using 1
      apply Subtype.ext
      exact g.apply_symm_apply y
    · simpa only [map_smul, g.symm_apply_apply] using congrArg g.symm h
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, h⟩
    refine ⟨r, hr, g y, ⟨sphereRotation8 g y, hy, rfl⟩, ?_⟩
    simpa only [map_smul] using congrArg g h

theorem sphereArea8_rotation_preserving (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    MeasurePreserving (sphereRotation8 g) sphereArea8 sphereArea8 := by
  refine ⟨(sphereRotation8 g).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation8 g).measurable hs]
  change (volume : Measure Ambient9).toSphere ((sphereRotation8 g) ⁻¹' s) =
    (volume : Measure Ambient9).toSphere s
  rw [Measure.toSphere_apply' _ (hs.preimage (sphereRotation8 g).measurable),
    Measure.toSphere_apply' _ hs, ← sphereRotation8_cone_preimage g s,
    g.measurePreserving.measure_preimage_emb g.toHomeomorph.measurableEmbedding]

theorem sphereProbability8_rotation_preserving (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    MeasurePreserving (sphereRotation8 g) sphereProbability8 sphereProbability8 :=
  (sphereArea8_rotation_preserving g).smul_measure (sphereArea8 univ)⁻¹

theorem sphereProbability8_integral_rotation (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (f : Sphere8 → ℝ) :
    (∫ y, f (sphereRotation8 g y) ∂sphereProbability8) = ∫ y, f y ∂sphereProbability8 :=
  (sphereProbability8_rotation_preserving g).integral_comp
    (sphereRotation8 g).measurableEmbedding f

/-- A reflection in the orthogonal complement of x-y moves x to y. -/
theorem sphereRotation8_transitive (x y : Sphere8) :
    ∃ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, sphereRotation8 g x = y := by
  refine ⟨Submodule.reflection (ℝ ∙ ((x : Ambient9) - y))ᗮ, ?_⟩
  apply Subtype.ext
  apply Submodule.reflection_sub
  exact (mem_sphere_zero_iff_norm.1 x.property).trans
    (mem_sphere_zero_iff_norm.1 y.property).symm

def sphereKernel4 (x y : Sphere8) : ℝ := (dist x y)⁻¹ ^ 4

def spherePotential4 (x : Sphere8) : ℝ := ∫ y, sphereKernel4 x y ∂sphereProbability8

theorem spherePotential4_rotation (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    spherePotential4 (sphereRotation8 g x) = spherePotential4 x := by
  unfold spherePotential4
  rw [← sphereProbability8_integral_rotation g (sphereKernel4 (sphereRotation8 g x))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (dist (sphereRotation8 g x) (sphereRotation8 g y))⁻¹ ^ 4 = (dist x y)⁻¹ ^ 4
    rw [sphereRotation8_dist]

/-- Constancy only; this is not an integrability or numerical-value theorem. -/
theorem spherePotential4_constant (x y : Sphere8) : spherePotential4 x = spherePotential4 y := by
  obtain ⟨g, hg⟩ := sphereRotation8_transitive x y
  rw [← hg, spherePotential4_rotation]

/-- An actual analytic integrability proof at one pole suffices for every center. -/
theorem sphereKernel4_integrable_iff (x y : Sphere8) :
    Integrable (sphereKernel4 x) sphereProbability8 ↔
      Integrable (sphereKernel4 y) sphereProbability8 := by
  obtain ⟨g, hg⟩ := sphereRotation8_transitive x y
  have hcomp : sphereKernel4 y ∘ sphereRotation8 g = sphereKernel4 x := by
    funext z
    change sphereKernel4 y (sphereRotation8 g z) = sphereKernel4 x z
    rw [← hg]
    unfold sphereKernel4
    rw [sphereRotation8_dist]
  simpa only [hcomp] using
    (sphereProbability8_rotation_preserving g).integrable_comp_emb
      (sphereRotation8 g).measurableEmbedding (g := sphereKernel4 y)

theorem spherePotential4_integral (p : Sphere8) :
    (∫ x, spherePotential4 x ∂sphereProbability8) = spherePotential4 p := by
  calc
    _ = ∫ _x : Sphere8, spherePotential4 p ∂sphereProbability8 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => spherePotential4_constant x p)
    _ = _ := by simp

/-- The complete global background quadrature error is exactly zero. -/
theorem spherePotential4_quadrature_cancel {N : ℕ} (X : Configuration N)
    (hN : 0 < N) :
    (∑ i : Fin N, spherePotential4 (X i)) / (N : ℝ) -
      (∫ x, spherePotential4 x ∂sphereProbability8) = 0 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  let p : Sphere8 := X ⟨0, hN⟩
  have hsum : (∑ i : Fin N, spherePotential4 (X i)) = (N : ℝ) * spherePotential4 p := by
    calc
      _ = ∑ _i : Fin N, spherePotential4 p :=
        Finset.sum_congr rfl (fun i _ => spherePotential4_constant (X i) p)
      _ = _ := by simp
  rw [hsum, spherePotential4_integral p]
  simp [hp.ne']

#print axioms sphereArea8_ne_zero
#print axioms sphereProbability8_mass
#print axioms sphereRotation8_dist
#print axioms sphereRotation8_cone_preimage
#print axioms sphereArea8_rotation_preserving
#print axioms sphereProbability8_rotation_preserving
#print axioms sphereProbability8_integral_rotation
#print axioms sphereRotation8_transitive
#print axioms spherePotential4_rotation
#print axioms spherePotential4_constant
#print axioms sphereKernel4_integrable_iff
#print axioms spherePotential4_integral
#print axioms spherePotential4_quadrature_cancel

end SphericalRiesz
