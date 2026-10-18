import Riesz.CrossPatchPhysical8

/-! Fixed rational node scales and the constructed near-full sphere family.
Constants may depend on the fixed separated family. No uniform bound as the
physical gap shrinks, residual physical configuration, or all-N is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem smallE8CrossPhysicalBlock8_fixed_scale_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (a : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m →
      |smallE8CrossPhysicalBlock8 p q (a*m)| ≤ C*(m:ℝ)^10 := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossPhysicalBlock8_bound p q hd
  refine ⟨C*(a:ℝ)^10,by positivity,?_⟩
  intro m hm
  have ham : 8 ≤ a*m := hm.trans (Nat.le_mul_of_pos_left m ha)
  calc
    |smallE8CrossPhysicalBlock8 p q (a*m)| ≤ C*((a*m:ℕ):ℝ)^10 := hb (a*m) ham
    _ = C*(a:ℝ)^10*(m:ℝ)^10 := by rw [Nat.cast_mul,mul_pow]; ring

theorem smallE8CrossPhysicalBlock8_rational_normalized_zero (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (a d : ℕ) (ha : 0 < a) (hd0 : 0 < d) :
    Tendsto (fun m : ℕ => smallE8CrossPhysicalBlock8 p q (a*m)/((d*m:ℕ):ℝ)^12)
      atTop (nhds 0) := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossPhysicalBlock8_fixed_scale_bound p q hd a ha
  exact nat_power12_normalized_zero_of_power10_bound
    (F := fun m => smallE8CrossPhysicalBlock8 p q (a*m)) d hd0 C hb

theorem smallE8CrossFamily8_normalized_zero {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hd : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (a d : ℕ) (ha : 0 < a) (hd0 : 0 < d) :
    Tendsto (fun m : ℕ => (∑ i, ∑ j ∈ Finset.univ.erase i,
      smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/((d*m:ℕ):ℝ)^12) atTop (nhds 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum (Finset.univ.erase i) (fun j hj =>
      smallE8CrossPhysicalBlock8_rational_normalized_zero (P i) (P j)
        (hd (Finset.ne_of_mem_erase hj).symm) a d ha hd0))
  simpa only [Finset.sum_const_zero,← Finset.sum_div] using h

theorem sphere8_near_full_rational_cubes_cross_zero (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ P : Fin K → SmallE8CubePatch8, ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) ∧
        ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ ∧
        smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) ∧
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) ∧
      1-b < sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1 ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8 ∧
      K*a^8 < d^8 ∧
      (∀ m : ℕ, 8 ≤ m → Fintype.card (rationalCubeNodeIndex8 K a d m) = (d*m)^8 ∧
        Fintype.card (Fin 8 → NodeIndex (a*m)) = (a*m)^8 ∧ 0 < (d^8-K*a^8)*m^8) ∧
      Tendsto (fun m : ℕ => (∑ i, ∑ j ∈ Finset.univ.erase i,
        smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/((d*m:ℕ):ℝ)^12) atTop (nhds 0) := by
  obtain ⟨K,g,v,a,d,ha,hd0,ℓ,hℓ,heℓ,hscale,hcell,hdisj,hgap,hl,hu,heq,hmass,hbudget,hcounts⟩ :=
    sphere8_near_full_rational_affine_cubes ρ b hρ hb
  let P : Fin K → SmallE8CubePatch8 := fun i =>
    ⟨g i,v i,cubeMidpoint8,ℓ,hℓ,cubeMidpoint8_mem_unitCube,(hcell i).2.1⟩
  have hdisj' : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) := hdisj
  refine ⟨K,P,a,d,ha,hd0,?_,hdisj',hl,hu,heq,hbudget,?_,
    smallE8CrossFamily8_normalized_zero P hdisj' a d ha hd0⟩
  · intro i
    refine ⟨heℓ,(hcell i).1,hscale,?_⟩
    change ℓ^8/sphereArea8.real univ = ((a:ℝ)/d)^8
    rw [heℓ,equalAreaE8NormalizedScale8_density]
  · intro m hm
    exact ⟨(hcounts m hm).1,(hcounts m hm).2.1,(hcounts m hm).2.2.1⟩

end SphericalRiesz
