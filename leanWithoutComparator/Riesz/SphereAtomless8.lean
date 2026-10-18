import Riesz.SphereIntegrable8
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! The actual sphere measure has no atoms. A cone over the north pole
lies in the ambient null axis already used for kernel integrability.
Rotation invariance then handles every point. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace SphericalRiesz

theorem sphereArea8_northPole_singleton : sphereArea8 {northPole8} = 0 := by
  have haxis : (volume : Measure Ambient9) {v | transverse8 v = 0} = 0 := by
    simpa only [not_not] using (ae_iff.mp transverse8_ae_ne_zero)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' ({northPole8} : Set Sphere8)) ⊆
      {v | transverse8 v = 0} := by
    rintro z ⟨r,hr,w,⟨y,hy,rfl⟩,rfl⟩
    rw [mem_singleton_iff] at hy
    subst y
    change transverse8 (r • (northPole8 : Ambient9)) = 0
    rw [transverse8_smul,transverse8_northPole,smul_zero]
  unfold sphereArea8
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _),
    measure_mono_null hcone haxis,mul_zero]

theorem sphereArea8_singleton (p : Sphere8) : sphereArea8 {p} = 0 := by
  obtain ⟨g,hg⟩ := sphereRotation8_transitive northPole8 p
  have hpre : (sphereRotation8 g) ⁻¹' ({p} : Set Sphere8) = {northPole8} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,← hg,
      (sphereRotation8 g).injective.eq_iff]
  have hm := (sphereArea8_rotation_preserving g).measure_preimage_emb
    (sphereRotation8 g).measurableEmbedding ({p} : Set Sphere8)
  rw [hpre,sphereArea8_northPole_singleton] at hm
  exact hm.symm

instance sphereArea8_nullSingleton : NullSingletonClass sphereArea8 :=
  ⟨sphereArea8_singleton⟩

instance sphereProbability8_nullSingleton : NullSingletonClass sphereProbability8 := by
  refine ⟨fun p => ?_⟩
  simp [sphereProbability8,Measure.smul_apply]

theorem sphereProbability8_finite_null (B : Set Sphere8) (hB : B.Finite) :
    sphereProbability8 B = 0 := hB.measure_zero sphereProbability8

end SphericalRiesz
