import Riesz.RationalResidualBudget8
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded

/-! Concrete small affine E8 sphere patches, with their checked chart
parameters bundled. The cross kernel is the actual ambient chordal inverse
fourth power. Physical disjointness excludes its singularities on the compact
product of coordinate cubes and supplies a finite sixth-derivative bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace SphericalRiesz
open Boundary

structure SmallE8CubePatch8 where
  g : Ambient9 ≃ₗᵢ[ℝ] Ambient9
  v : Fin 8 → ℝ
  c : Fin 8 → ℝ
  ε : ℝ
  ε_pos : 0 < ε
  c_mem : c ∈ UnitCube 8
  small : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8

def smallE8CubeMap8 (p : SmallE8CubePatch8) : (Fin 8 → ℝ) → Ambient9 :=
  equalAreaE8Patch p.g p.v p.c p.ε

def smallE8CubeSet8 (p : SmallE8CubePatch8) : Set Sphere8 :=
  equalAreaE8SpherePatch8 p.g p.v p.c p.ε (UnitCube 8)

def smallE8CubeEmbedding8 (p : SmallE8CubePatch8) : UnitCube 8 ↪ Sphere8 :=
  equalAreaE8CubeEmbedding8 p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

def smallE8CrossKernel8 (p q : SmallE8CubePatch8)
    (z : (Fin 8 → ℝ) × (Fin 8 → ℝ)) : ℝ :=
  ‖smallE8CubeMap8 p z.1-smallE8CubeMap8 q z.2‖⁻¹^4

theorem smallE8CubeMap8_contDiffAt (p : SmallE8CubePatch8) (x : Fin 8 → ℝ)
    (hx : x ∈ UnitCube 8) : ContDiffAt ℝ ∞ (smallE8CubeMap8 p) x := by
  have hdom := equalAreaE8Affine8_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small
    ⟨x,hx,rfl⟩
  have hshift : ContDiffAt ℝ ∞ (fun y : Fin 8 → ℝ => y-p.c) x := by fun_prop
  have hf : ContDiffAt ℝ ∞ (fun y => equalAreaMovingE8Chart p.v p.ε (y-p.c)) x :=
    ContDiffAt.comp (g := equalAreaMovingE8Chart p.v p.ε)
      (f := fun y : Fin 8 → ℝ => y-p.c) x
      (equalAreaMovingE8Chart_contDiffAt p.v p.ε (x-p.c) hdom.1) hshift
  exact p.g.toContinuousLinearMap.contDiff.contDiffAt.comp x hf

theorem smallE8CubeMap8_norm (p : SmallE8CubePatch8) (x : Fin 8 → ℝ)
    (hx : x ∈ UnitCube 8) : ‖smallE8CubeMap8 p x‖ = 1 :=
  equalAreaE8Patch_norm p.g p.v p.c p.ε x
    ((equalAreaE8Affine8_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small) ⟨x,hx,rfl⟩).1

theorem smallE8CubeEmbedding8_coe (p : SmallE8CubePatch8) (x : UnitCube 8) :
    (smallE8CubeEmbedding8 p x : Ambient9) = smallE8CubeMap8 p x := rfl

theorem smallE8CubeEmbedding8_mem (p : SmallE8CubePatch8) (x : UnitCube 8) :
    smallE8CubeEmbedding8 p x ∈ smallE8CubeSet8 p := ⟨x,x.property,rfl⟩

theorem smallE8CubeMap8_ne_of_disjoint (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    smallE8CubeMap8 p x ≠ smallE8CubeMap8 q y := by
  intro h
  have he : smallE8CubeEmbedding8 p ⟨x,hx⟩ = smallE8CubeEmbedding8 q ⟨y,hy⟩ :=
    Subtype.ext h
  apply disjoint_left.mp hd (smallE8CubeEmbedding8_mem p ⟨x,hx⟩)
  rw [he]
  exact smallE8CubeEmbedding8_mem q ⟨y,hy⟩

theorem smallE8CrossKernel8_squared_norm (p q : SmallE8CubePatch8)
    (z : (Fin 8 → ℝ) × (Fin 8 → ℝ)) :
    smallE8CrossKernel8 p q z =
      ((‖smallE8CubeMap8 p z.1-smallE8CubeMap8 q z.2‖^2)⁻¹)^2 := by
  unfold smallE8CrossKernel8
  simp only [← inv_pow,← pow_mul]

theorem smallE8CrossKernel8_contDiffAt (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (z : (Fin 8 → ℝ) × (Fin 8 → ℝ)) (hz : z ∈ (UnitCube 8).prod (UnitCube 8)) :
    ContDiffAt ℝ ∞ (smallE8CrossKernel8 p q) z := by
  have hp : ContDiffAt ℝ ∞ (fun w : (Fin 8 → ℝ) × (Fin 8 → ℝ) =>
      smallE8CubeMap8 p w.1) z := (smallE8CubeMap8_contDiffAt p z.1 hz.1).comp z (by fun_prop)
  have hq : ContDiffAt ℝ ∞ (fun w : (Fin 8 → ℝ) × (Fin 8 → ℝ) =>
      smallE8CubeMap8 q w.2) z := (smallE8CubeMap8_contDiffAt q z.2 hz.2).comp z (by fun_prop)
  have hne : smallE8CubeMap8 p z.1-smallE8CubeMap8 q z.2 ≠ 0 :=
    sub_ne_zero.mpr (smallE8CubeMap8_ne_of_disjoint p q hd z.1 z.2 hz.1 hz.2)
  have hs : ContDiffAt ℝ ∞ (fun w : (Fin 8 → ℝ) × (Fin 8 → ℝ) =>
      ‖smallE8CubeMap8 p w.1-smallE8CubeMap8 q w.2‖^2) z := (hp.sub hq).norm_sq ℝ
  have hf : smallE8CrossKernel8 p q =
      (fun w => ((‖smallE8CubeMap8 p w.1-smallE8CubeMap8 q w.2‖^2)⁻¹)^2) :=
    funext (smallE8CrossKernel8_squared_norm p q)
  rw [hf]
  exact (hs.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).pow 2

theorem smallE8CrossKernel8_continuousOn (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ContinuousOn (smallE8CrossKernel8 p q) ((UnitCube 8).prod (UnitCube 8)) :=
  fun z hz => (smallE8CrossKernel8_contDiffAt p q hd z hz).continuousAt.continuousWithinAt

theorem smallE8CrossKernel8_joint_sixth_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ (UnitCube 8).prod (UnitCube 8),
      ‖iteratedFDeriv ℝ 6 (smallE8CrossKernel8 p q) z‖ ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ 6 (smallE8CrossKernel8 p q))
      ((UnitCube 8).prod (UnitCube 8)) := fun z hz =>
    ((smallE8CrossKernel8_contDiffAt p q hd z hz).continuousAt_iteratedFDeriv
      (by simp : (6 : ℕ∞ω) ≤ ∞)).continuousWithinAt
  obtain ⟨C,hC⟩ := ((unitCube_isCompact 8).prod (unitCube_isCompact 8)).exists_bound_of_continuousOn hcont
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC z hz).trans (le_max_left _ _)⟩

end SphericalRiesz
