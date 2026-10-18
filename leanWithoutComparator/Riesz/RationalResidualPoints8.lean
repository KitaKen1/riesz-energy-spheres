import Riesz.SphereResidual8
import Riesz.CrossPatchFamily8

/-! Complete the original rational patch index budget with actual residual
points. The original corrected E8 nodes are retained, the combined map is
injective, and the actual residual-plus-fixed-cross neutralized block is
nonpositive. Assembly of the whole physical energy remains separate. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

theorem smallE8CubeSet8_isCompact (p : SmallE8CubePatch8) :
    IsCompact (smallE8CubeSet8 p) :=
  equalAreaE8SpherePatch8_cube_isCompact p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

def rationalCubePatchNodes8 {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (a m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) :
    (Fin K × (Fin 8 → NodeIndex (a*m))) → Sphere8 := fun t =>
  smallE8CubeEmbedding8 (P t.1) ⟨cubeNode 8 (a*m) t.2,fun i =>
    ⟨(cubeNode_mem_open 8 (a*m) (hm.trans (Nat.le_mul_of_pos_left m ha)) t.2 i).1.le,
     (cubeNode_mem_open 8 (a*m) (hm.trans (Nat.le_mul_of_pos_left m ha)) t.2 i).2.le⟩⟩

theorem rationalCubePatchNodes8_mem {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (a m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) (t : Fin K × (Fin 8 → NodeIndex (a*m))) :
    rationalCubePatchNodes8 P a m ha hm t ∈ smallE8CubeSet8 (P t.1) :=
  smallE8CubeEmbedding8_mem _ _

theorem rationalCubePatchNodes8_injective {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hd : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (a m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) :
    Function.Injective (rationalCubePatchNodes8 P a m ha hm) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have hij : i = j := by
    by_contra hn
    apply disjoint_left.mp (hd hn) (rationalCubePatchNodes8_mem P a m ha hm (i,x))
    rw [he]
    exact rationalCubePatchNodes8_mem P a m ha hm (j,y)
  subst j
  have hn := (smallE8CubeEmbedding8 (P i)).injective he
  have hxy := cubeNode_injective 8 (a*m) (hm.trans (Nat.le_mul_of_pos_left m ha))
    (congrArg Subtype.val hn)
  exact congrArg (fun z => (i,z)) hxy

theorem sphere8_complement_mass_ne_zero (S : Set Sphere8) (hS : MeasurableSet S)
    (hmass : sphereProbability8.real S < 1) : sphereProbability8 Sᶜ ≠ 0 := by
  have hp : 0 < sphereProbability8.real Sᶜ := by
    rw [measureReal_compl hS,probReal_univ]
    linarith
  intro hz
  simpa [Measure.real,hz] using hp

theorem rationalCubeFamily8_exists_residual_configuration {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hd : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) (hbudget : K*a^8 ≤ d^8) :
    let S := ⋃ i, smallE8CubeSet8 (P i)
    let nodes := rationalCubePatchNodes8 P a m ha hm
    let X := nodes ∘ (Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))).symm
    ∃ Z : Fin ((d^8-K*a^8)*m^8) → Sphere8,
      Function.Injective Z ∧ (∀ j, Z j ∈ Sᶜ) ∧
      Function.Injective (Sum.elim nodes Z) ∧
      Fintype.card (rationalCubeNodeIndex8 K a d m) = (d*m)^8 ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) sphereKernel4
        (sphereResidualCrossRow8 X S (((d*m)^8:ℕ):ℝ)) Z ≤ 0 := by
  classical
  dsimp only
  let S := ⋃ i, smallE8CubeSet8 (P i)
  let nodes := rationalCubePatchNodes8 P a m ha hm
  let X := nodes ∘ (Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))).symm
  have hS : MeasurableSet S := MeasurableSet.iUnion
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
  obtain ⟨Z,hZ,havoid,_,hzero⟩ := sphere8_exists_residual_points X Sᶜ S ∅ hS.compl
    (sphere8_complement_mass_ne_zero S hS hu) finite_empty (((d*m)^8:ℕ):ℝ)
    ((d^8-K*a^8)*m^8)
  have hzS : ∀ j, Z j ∈ Sᶜ := fun j => (havoid j).1
  have hnS : ∀ t, nodes t ∈ S := fun t => mem_iUnion.mpr
    ⟨t.1,rationalCubePatchNodes8_mem P a m ha hm t⟩
  have hnodes := rationalCubePatchNodes8_injective P hd a m ha hm
  have hinj : Function.Injective (Sum.elim nodes Z) := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (hnodes huv)
      | inr v =>
        change nodes u = Z v at huv
        exact False.elim ((hzS v) (huv ▸ hnS u))
    | inr u =>
      cases v with
      | inl v =>
        change Z u = nodes v at huv
        exact False.elim ((hzS u) (huv.symm ▸ hnS v))
      | inr v => exact congrArg Sum.inr (hZ huv)
  exact ⟨Z,hZ,hzS,hinj,rationalCubeNodeIndex8_card K a d m ha hm hbudget,hzero⟩

theorem rationalCubeFamily8_exists_configuration {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hd : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hm : 8 ≤ m) (hbudget : K*a^8 ≤ d^8) :
    let S := ⋃ i, smallE8CubeSet8 (P i)
    let nodes := rationalCubePatchNodes8 P a m ha hm
    let X := nodes ∘ (Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))).symm
    ∃ Z : Fin ((d^8-K*a^8)*m^8) → Sphere8,
      Function.Injective Z ∧ (∀ j, Z j ∈ Sᶜ) ∧
      Function.Injective (Sum.elim nodes Z) ∧
      Fintype.card (rationalCubeNodeIndex8 K a d m) = (d*m)^8 ∧
      residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) sphereKernel4
        (sphereResidualCrossRow8 X S (((d*m)^8:ℕ):ℝ)) Z ≤ 0 ∧
      ∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∃ Y : Configuration ((d*m)^8), ∀ u, Y (e u) = Sum.elim nodes Z u := by
  classical
  dsimp only
  obtain ⟨Z,hZ,hmem,hinj,hcard,henergy⟩ :=
    rationalCubeFamily8_exists_residual_configuration P hd hu a d m ha hm hbudget
  let e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8) := Fintype.equivFinOfCardEq hcard
  let Y : Configuration ((d*m)^8) :=
    ⟨(Sum.elim (rationalCubePatchNodes8 P a m ha hm) Z) ∘ e.symm,hinj.comp e.symm.injective⟩
  refine ⟨Z,hZ,hmem,hinj,hcard,henergy,e,Y,?_⟩
  intro u
  simp [Y,Function.comp_def]

theorem sphere8_near_full_rational_residual_configuration (ρ b : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ P : Fin K → SmallE8CubePatch8, ∃ a d : ℕ,
      ∃ ha : 0 < a, 0 < d ∧
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) ∧
        ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ ∧
        smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) ∧
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) ∧
      1-b < sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1 ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8 ∧
      K*a^8 < d^8 ∧
      Filter.Tendsto (fun m : ℕ => (∑ i, ∑ j ∈ Finset.univ.erase i,
        smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/((d*m:ℕ):ℝ)^12)
        Filter.atTop (nhds 0) ∧
      (∀ m : ℕ, ∀ hm : 8 ≤ m,
        let S := ⋃ i, smallE8CubeSet8 (P i)
        let nodes := rationalCubePatchNodes8 P a m ha hm
        let X := nodes ∘ (Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))).symm
        ∃ Z : Fin ((d^8-K*a^8)*m^8) → Sphere8,
          Function.Injective Z ∧ (∀ j, Z j ∈ Sᶜ) ∧
          Function.Injective (Sum.elim nodes Z) ∧
          Fintype.card (rationalCubeNodeIndex8 K a d m) = (d*m)^8 ∧
          residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) sphereKernel4
            (sphereResidualCrossRow8 X S (((d*m)^8:ℕ):ℝ)) Z ≤ 0 ∧
          ∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
            ∃ Y : Configuration ((d*m)^8), ∀ u, Y (e u) = Sum.elim nodes Z u) := by
  obtain ⟨K,P,a,d,ha,hd,hdata,hdisj,hl,hu,hmass,hbudget,_,hcross⟩ :=
    sphere8_near_full_rational_cubes_cross_zero ρ b hρ hb
  refine ⟨K,P,a,d,ha,hd,hdata,hdisj,hl,hu,hmass,hbudget,hcross,?_⟩
  intro m hm
  exact rationalCubeFamily8_exists_configuration P hdisj hu a d m ha hm hbudget.le

end SphericalRiesz
