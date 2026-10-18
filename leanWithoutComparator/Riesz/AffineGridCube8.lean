import Riesz.CappedSphereGrid8

/-! Identify the constructed interval cells with the actual common-scale
affine E8 unit-cube class. The original probability, compactness and physical
gap are retained. This constructs the small patch family, not a global node
configuration or its energy estimate. Rational node counts remain separate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def cubeMidpoint8 : Fin 8 → ℝ := fun _ => 1/2

def gridCenter8 (h : ℝ) (z : Fin 8 → ℤ) : Fin 8 → ℝ :=
  fun i => h*((z i : ℝ)+1/2)

def gridCubeParam8 (h γ : ℝ) (z : Fin 8 → ℤ) (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  gridCenter8 h z+(h*(1-γ)) • (x-cubeMidpoint8)

theorem cubeMidpoint8_mem_unitCube : cubeMidpoint8 ∈ UnitCube 8 := by
  intro i
  norm_num [cubeMidpoint8]

theorem gridCenter8_mem_shrunk (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 8 → ℤ) : gridCenter8 h z ∈ gridShrunkCell8 h γ z := by
  intro i
  dsimp [gridCenter8]
  have hg : h*γ ≤ h := by nlinarith
  constructor <;> nlinarith

theorem gridCubeParam8_image_unitCube (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1)
    (z : Fin 8 → ℤ) : gridCubeParam8 h γ z '' UnitCube 8 = gridShrunkCell8 h γ z := by
  have hl : 0 < h*(1-γ) := by positivity
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ i
    change h*((z i : ℝ)+γ/2) ≤ h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ∧
      h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ≤ h*((z i : ℝ)+1-γ/2)
    have hi := hx i
    have hlo := mul_nonneg hl.le hi.1
    have hhi := mul_nonneg hl.le (sub_nonneg.mpr hi.2)
    constructor <;> nlinarith
  · intro hy
    let x : Fin 8 → ℝ := fun i => (y i-gridCenter8 h z i)/(h*(1-γ))+1/2
    have hx : x ∈ UnitCube 8 := by
      intro i
      have lo : -(1/2) ≤ (y i-gridCenter8 h z i)/(h*(1-γ)) :=
        (le_div_iff₀ hl).mpr (by dsimp [gridCenter8]; nlinarith [(hy i).1])
      have hi : (y i-gridCenter8 h z i)/(h*(1-γ)) ≤ 1/2 :=
        (div_le_iff₀ hl).mpr (by dsimp [gridCenter8]; nlinarith [(hy i).2])
      change 0 ≤ (y i-gridCenter8 h z i)/(h*(1-γ))+1/2 ∧
        (y i-gridCenter8 h z i)/(h*(1-γ))+1/2 ≤ 1
      constructor <;> linarith
    refine ⟨x,hx,?_⟩
    funext i
    change gridCenter8 h z i+h*(1-γ)*
      ((y i-gridCenter8 h z i)/(h*(1-γ))+1/2-1/2) = y i
    field_simp [hh.ne', (sub_pos.mpr hγ).ne']
    <;> ring

theorem equalAreaE8GridCube8_affine_identity (h γ : ℝ) (z : Fin 8 → ℤ)
    (x : Fin 8 → ℝ) :
    e8Map (gridCubeParam8 h γ z x) =
      equalAreaE8Affine8 (e8Map (gridCenter8 h z)) cubeMidpoint8 (h*(1-γ)) x := by
  simp [gridCubeParam8,equalAreaE8Affine8]

theorem equalAreaE8GridCube8_patch_identity (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (h γ : ℝ) (z : Fin 8 → ℤ) (x : Fin 8 → ℝ) :
    equalAreaE8Patch g 0 0 1 (gridCubeParam8 h γ z x) =
      equalAreaE8Patch g (e8Map (gridCenter8 h z)) cubeMidpoint8 (h*(1-γ)) x := by
  simp [equalAreaE8Patch,equalAreaMovingE8Chart,gridCubeParam8]

theorem gridShrunkSphere8_eq_affineCube (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1) (z : Fin 8 → ℤ) :
    equalAreaE8SpherePatch8 g 0 0 1 (gridShrunkCell8 h γ z) =
      equalAreaE8SpherePatch8 g (e8Map (gridCenter8 h z)) cubeMidpoint8
        (h*(1-γ)) (UnitCube 8) := by
  have hf : (fun x => equalAreaE8Patch g 0 0 1 (gridCubeParam8 h γ z x)) =
      equalAreaE8Patch g (e8Map (gridCenter8 h z)) cubeMidpoint8 (h*(1-γ)) := by
    funext x
    exact equalAreaE8GridCube8_patch_identity g h γ z x
  simp only [equalAreaE8SpherePatch8,← gridCubeParam8_image_unitCube h γ hh hγ z,
    image_image,hf]

theorem equalAreaE8CubeUnion8_probability_real {K : ℕ}
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : Fin K → Fin 8 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 8)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) ε (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) ε (UnitCube 8)))) :
    sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) (c i) ε (UnitCube 8)) =
      (K : ℝ)*(ε^8/sphereArea8.real univ) := by
  change sphereProbability8.real (equalAreaE8PatchUnion8 g v c (fun _ => ε)
    (fun _ => UnitCube 8)) = _
  have hden : 0 ≤ ε^8/sphereArea8.real univ :=
    (equalAreaE8PatchProbabilityDensity8_pos ε hε).le
  rw [Measure.real,equalAreaE8CubeUnion8_probability g v c ε hε hc hsmall hd,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hden]

theorem sphere8_near_full_small_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ v : Fin K → Fin 8 → ℝ, ∃ ε > 0, ε*equalAreaScaleRadius ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ε*equalAreaScaleRadius ≤ 1/8 ∧
        IsCompact (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8))
        (equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ε (UnitCube 8))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8),
        ∀ y ∈ equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ε (UnitCube 8), δ < dist x y) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8)) ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8)) < 1 ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8)) =
        (K : ℝ)*(ε^8/sphereArea8.real univ) := by
  let a := min ρ (1/16)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have haρ : a ≤ ρ/2 := by
    dsimp [a]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have ha1 : a ≤ 1/32 := by dsimp [a]; linarith [min_le_right ρ (1/16)]
  have hR := equalAreaScaleRadius_pos
  obtain ⟨K,g,z,h,hh,hhcap,γ,hγ,hγ1,hcell,hd,hgap,hl,hu⟩ :=
    sphere8_near_full_separated_shrunk_grid_capped a b (a/equalAreaScaleRadius)
      ha hb (by positivity)
  let ε := h*(1-γ)
  let v : Fin K → Fin 8 → ℝ := fun i => e8Map (gridCenter8 h (z i))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : ε*equalAreaScaleRadius < a := by
    have heh : ε ≤ h := by dsimp [ε]; nlinarith
    exact (mul_le_mul_of_nonneg_right heh hR.le).trans_lt ((lt_div_iff₀ hR).mp hhcap)
  have hv : ∀ i, ‖v i‖ < a := fun i =>
    (hcell i).2.1 _ (gridCenter8_mem_shrunk h γ hh.le hγ1.le (z i))
  have hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius ≤ 1/8 := by
    intro i
    linarith [hv i]
  have heq : ∀ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)) =
      equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8) := fun i =>
    gridShrunkSphere8_eq_affineCube (g i) h γ hh hγ1 (z i)
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ε (UnitCube 8))) := by
    simpa only [heq] using hd
  refine ⟨K,g,v,ε,hε,by linarith,?_,hd',?_,?_,?_,
    equalAreaE8CubeUnion8_probability_real g v (fun _ => cubeMidpoint8) ε hε
      (fun _ => cubeMidpoint8_mem_unitCube) hsmall hd'⟩
  · intro i
    exact ⟨by linarith [hv i],hsmall i,
      equalAreaE8SpherePatch8_cube_isCompact (g i) (v i) cubeMidpoint8 ε hε
        cubeMidpoint8_mem_unitCube (hsmall i)⟩
  · simpa only [heq] using hgap
  · simpa only [heq] using hl
  · simpa only [heq] using hu

end SphericalRiesz
