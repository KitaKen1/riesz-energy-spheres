import Riesz.SphereFiniteFamilyAssembly4
import Riesz.RationalResidualEnergy8
import Riesz.EqualAreaPatchRieszTransport8

/-! The original corrected E8 nodes and the actual physical four-term blocks.
Exact common patch mass matches the empirical cardinality. The already
checked physical cross blocks are identified with the finite-family assembly,
and actual local blocks retain the existing normalized local coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def smallE8CubeNodes8 (p : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n) :
    (Fin 8 → NodeIndex n) → Sphere8 := fun u =>
  smallE8CubeEmbedding8 p ⟨cubeNode 8 n u,originalNode8_mem_cube n hn u⟩

theorem smallE8CubeNodes8_kernel (p q : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n)
    (u v : Fin 8 → NodeIndex n) :
    sphereKernel4 (smallE8CubeNodes8 p n hn u) (smallE8CubeNodes8 q n hn v) =
      smallE8CrossKernel8 p q (cubeNode 8 n u,cubeNode 8 n v) := by
  change (dist (smallE8CubeMap8 p (cubeNode 8 n u))
    (smallE8CubeMap8 q (cubeNode 8 n v)))⁻¹^4 = _
  rw [dist_eq_norm]
  rfl

theorem smallE8CubeNodes8_pair (p : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n) :
    sphereFinitePair4 (smallE8CubeNodes8 p n hn) =
      curvedOriginalPairEnergy8 (equalAreaE8Patch p.g p.v p.c p.ε) n := by
  rw [curvedOriginalPairEnergy8_eq_full]
  rfl

theorem smallE8CubeNodes8_mixed_quadrature (p q : SmallE8CubePatch8)
    (n : ℕ) (hn : 8 ≤ n) :
    cubeQuadrature 8 n (fun x => cubeQuadrature 8 n
      (fun y => smallE8CrossKernel8 p q (x,y))) =
      sphereFiniteMixedPair4 (smallE8CubeNodes8 p n hn) (smallE8CubeNodes8 q n hn)/(n:ℝ)^16 := by
  simp_rw [cubeQuadrature_as_node_sum]
  rw [← Finset.sum_div,div_div,← pow_add]
  simp only [sphereFiniteMixedPair4,smallE8CubeNodes8_kernel]

theorem smallE8CubeNodes8_row_quadrature (p q : SmallE8CubePatch8)
    (n : ℕ) (hn : 8 ≤ n) :
    cubeQuadrature 8 n (fun x => ∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y:Ambient9)‖⁻¹^4 ∂sphereProbability8) =
      (∑ u, sphereRestrictedPotential4 (smallE8CubeSet8 q) (smallE8CubeNodes8 p n hn u))/(n:ℝ)^8 := by
  rw [cubeQuadrature_as_node_sum]
  rfl

theorem smallE8CubeNodes8_integral_quadrature (p q : SmallE8CubePatch8)
    (n : ℕ) (hn : 8 ≤ n) :
    (∫ x in smallE8CubeSet8 p, cubeQuadrature 8 n
      (fun y => ‖(x:Ambient9)-smallE8CubeMap8 q y‖⁻¹^4) ∂sphereProbability8) =
      (∑ u, sphereRestrictedPotential4 (smallE8CubeSet8 p) (smallE8CubeNodes8 q n hn u))/(n:ℝ)^8 := by
  have he (x : Sphere8) :
      cubeQuadrature 8 n (fun y => ‖(x:Ambient9)-smallE8CubeMap8 q y‖⁻¹^4) =
        (∑ u, sphereKernel4 (smallE8CubeNodes8 q n hn u) x)/(n:ℝ)^8 := by
    rw [cubeQuadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    change _ = (dist (smallE8CubeMap8 q (cubeNode 8 n u)) (x:Ambient9))⁻¹^4
    rw [dist_eq_norm,norm_sub_rev]
  simp_rw [he]
  rw [integral_div,integral_finsetSum _
    (fun u _ => (sphereKernel4_integrable (smallE8CubeNodes8 q n hn u)).restrict)]
  rfl

theorem smallE8CubeNodes8_cross_mass_match (p q : SmallE8CubePatch8)
    (n : ℕ) (hn : 8 ≤ n) (M : ℝ)
    (hρ : smallE8CubeDensity8 p = smallE8CubeDensity8 q)
    (hM : M*smallE8CubeDensity8 p = (n:ℝ)^8) :
    sphereFiniteCrossBlock4 (smallE8CubeNodes8 p n hn) (smallE8CubeNodes8 q n hn)
      (smallE8CubeSet8 p) (smallE8CubeSet8 q) M = smallE8CrossPhysicalBlock8 p q n := by
  have hρ0 := (smallE8CubeDensity8_pos p).ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hM' : M = (n:ℝ)^8/smallE8CubeDensity8 p :=
    (eq_div_iff hρ0).mpr hM
  have hr : cubeQuadrature 8 n (fun x => (∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y:Ambient9)‖⁻¹^4 ∂sphereProbability8)/smallE8CubeDensity8 q) =
      ((∑ u, sphereRestrictedPotential4 (smallE8CubeSet8 q)
        (smallE8CubeNodes8 p n hn u))/(n:ℝ)^8)/smallE8CubeDensity8 q := by
    simp_rw [div_eq_mul_inv,mul_comm _ (smallE8CubeDensity8 q)⁻¹]
    rw [cubeQuadrature_const_mul,smallE8CubeNodes8_row_quadrature p q n hn]
    rfl
  unfold sphereFiniteCrossBlock4 smallE8CrossPhysicalBlock8
  rw [smallE8CubeNodes8_mixed_quadrature p q n hn,hr,
    smallE8CubeNodes8_integral_quadrature p q n hn]
  have hb : (∫ x in smallE8CubeSet8 p, ∫ y in smallE8CubeSet8 q,
      ‖(x:Ambient9)-(y:Ambient9)‖⁻¹^4 ∂sphereProbability8 ∂sphereProbability8) =
      sphereBackgroundPair4 (smallE8CubeSet8 p) (smallE8CubeSet8 q) := by
    unfold sphereBackgroundPair4 sphereRestrictedPotential4
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => integral_congr_ae
      (Filter.Eventually.of_forall (fun y => by
        change _ = (dist (x:Ambient9) (y:Ambient9))⁻¹^4
        rw [dist_eq_norm])))
  rw [hb,← hρ,hM']
  field_simp [hn0,hρ0] <;> ring

theorem smallE8CubeNodes8_local_scaled (p : SmallE8CubePatch8)
    (n : ℕ) (hn : 8 ≤ n) (M : ℝ)
    (hM : M*smallE8CubeDensity8 p = (n:ℝ)^8) :
    p.ε^4*sphereFiniteBlock4 (smallE8CubeNodes8 p n hn) (smallE8CubeSet8 p) M =
      (n:ℝ)^12*curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) n := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : p.ε^4*sphereFinitePair4 (smallE8CubeNodes8 p n hn) =
      curvedOriginalPairEnergy8 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) n := by
    rw [smallE8CubeNodes8_pair]
    exact equalAreaE8Patch_pair_energy_scaling p.g p.v p.c p.ε p.ε_pos n
  have hr : p.ε^4*(∑ u, sphereRestrictedPotential4 (smallE8CubeSet8 p)
      (smallE8CubeNodes8 p n hn u)) = smallE8CubeDensity8 p*
      (∑ u : Fin 8 → NodeIndex n, curvedPotential8
        (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) (cubeNode 8 n u)) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact equalAreaE8SpherePatch8_scaled_potential p.g p.v p.c p.ε p.ε_pos p.c_mem p.small
      ⟨cubeNode 8 n u,originalNode8_mem_cube n hn u⟩
  have hb : p.ε^4*sphereBackgroundPair4 (smallE8CubeSet8 p) (smallE8CubeSet8 p) =
      (smallE8CubeDensity8 p)^2*∫ x in UnitCube 8,
        curvedPotential8 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x :=
    equalAreaE8SpherePatch8_scaled_background p.g p.v p.c p.ε p.ε_pos p.c_mem p.small
  calc
    _ = p.ε^4*sphereFinitePair4 (smallE8CubeNodes8 p n hn)-
        2*M*(p.ε^4*(∑ u, sphereRestrictedPotential4 (smallE8CubeSet8 p)
          (smallE8CubeNodes8 p n hn u)))+
        M^2*(p.ε^4*sphereBackgroundPair4 (smallE8CubeSet8 p) (smallE8CubeSet8 p)) := by
      unfold sphereFiniteBlock4
      ring
    _ = curvedOriginalPairEnergy8 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) n-
        2*(M*smallE8CubeDensity8 p)*(∑ u : Fin 8 → NodeIndex n, curvedPotential8
          (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) (cubeNode 8 n u))+
        (M*smallE8CubeDensity8 p)^2*(∫ x in UnitCube 8,
          curvedPotential8 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x) := by
      rw [hp,hr,hb]
      ring
    _ = _ := by
      rw [hM,curvedNeutralizedEnergy8,cubeQuadrature_as_node_sum]
      field_simp [hn0] <;> ring

theorem rationalCubeFamily8_patch_node_mass_match {K : ℕ}
    (P : Fin K → SmallE8CubePatch8) (a d m : ℕ) (hd : 0 < d)
    (hρ : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) (i : Fin K) :
    (((d*m)^8:ℕ):ℝ)*smallE8CubeDensity8 (P i) = (((a*m):ℕ):ℝ)^8 := by
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hρ i]
  simp only [Nat.cast_pow,Nat.cast_mul]
  field_simp [hd0] <;> ring

theorem rationalCubeFamily8_fixed_union_local_cross {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hρ : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) :
    let hn := hm.trans (Nat.le_mul_of_pos_left m ha)
    sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
      (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ) =
      (∑ i, sphereFiniteBlock4 (smallE8CubeNodes8 (P i) (a*m) hn)
        (smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ))+
      ∑ i, ∑ j ∈ Finset.univ.erase i, smallE8CrossPhysicalBlock8 (P i) (P j) (a*m) := by
  dsimp only
  let hn := hm.trans (Nat.le_mul_of_pos_left m ha)
  have he : rationalCubePatchNodes8 P a m ha hm =
      fun t => smallE8CubeNodes8 (P t.1) (a*m) hn t.2 := rfl
  rw [he,sphereFiniteBlock4_iUnion_local_cross
    (fun i => smallE8CubeNodes8 (P i) (a*m) hn) (fun i => smallE8CubeSet8 (P i))
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet) hdis]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smallE8CubeNodes8_cross_mass_match (P i) (P j) (a*m) hn _
    ((hρ i).trans (hρ j).symm)
    (rationalCubeFamily8_patch_node_mass_match P a d m hd hρ i)

theorem sphereAreaRoot8_pow_four : sphereAreaRoot8^4 = Real.sqrt (sphereArea8.real univ) := by
  have h : (sphereAreaRoot8^4)^2 = sphereArea8.real univ := by
    rw [← pow_mul]
    exact sphereAreaRoot8_pow
  rw [← h,Real.sqrt_sq (pow_nonneg sphereAreaRoot8_pos.le 4)]

theorem rationalCubeFamily8_local_normalized {K : ℕ}
    (P : Fin K → SmallE8CubePatch8) (a d m : ℕ)
    (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d))
    (hρ : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) (i : Fin K) :
    let hn := hm.trans (Nat.le_mul_of_pos_left m ha)
    sphereFiniteBlock4 (smallE8CubeNodes8 (P i) (a*m) hn)
      (smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)/((d*m:ℕ):ℝ)^12 =
      (((a:ℝ)/d)^8/Real.sqrt (sphereArea8.real univ))*
        curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
          (P i).g (P i).v (P i).c (P i).ε) (a*m) := by
  dsimp only
  let hn := hm.trans (Nat.le_mul_of_pos_left m ha)
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdm : ((d*m:ℕ):ℝ)^12 ≠ 0 := by
    exact_mod_cast (pow_ne_zero 12 (Nat.mul_pos hd (by omega)).ne')
  have hA : Real.sqrt (sphereArea8.real univ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    rw [sphereArea8_mass_real]
    positivity
  have hε0 : (P i).ε^4 ≠ 0 := pow_ne_zero 4 (P i).ε_pos.ne'
  have hscale : (P i).ε^4*((d*m:ℕ):ℝ)^12*
      (((a:ℝ)/d)^8/Real.sqrt (sphereArea8.real univ)) = ((a*m:ℕ):ℝ)^12 := by
    rw [hε i,equalAreaE8NormalizedScale8,mul_pow,sphereAreaRoot8_pow_four]
    simp only [Nat.cast_mul]
    field_simp [hd0,hA] <;> ring
  apply (div_eq_iff hdm).mpr
  apply mul_left_cancel₀ hε0
  calc
    _ = ((a*m:ℕ):ℝ)^12*curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
        (P i).g (P i).v (P i).c (P i).ε) (a*m) :=
      smallE8CubeNodes8_local_scaled (P i) (a*m) hn _
        (rationalCubeFamily8_patch_node_mass_match P a d m hd hρ i)
    _ = _ := by rw [← hscale]; ring

theorem rationalCubeFamily8_exists_normalized_energy_upper {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8)
    (hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d))
    (hρ : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) :
    ∃ Y : Configuration ((d*m)^8),
      (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
      (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 ≤
        (((a:ℝ)/d)^8/Real.sqrt (sphereArea8.real univ))*
          (∑ i, curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
            (P i).g (P i).v (P i).c (P i).ε) (a*m))+
        (∑ i, ∑ j ∈ Finset.univ.erase i, smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/
          ((d*m:ℕ):ℝ)^12 := by
  obtain ⟨Y,hY,hE⟩ := rationalCubeFamily8_exists_energy_upper
    P hdis hu a d m ha hd hm hbudget hmass
  refine ⟨Y,hY,?_⟩
  calc
    _ ≤ sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
        (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)/((d*m:ℕ):ℝ)^12 :=
      div_le_div_of_nonneg_right hE (by positivity)
    _ = _ := by
      rw [rationalCubeFamily8_fixed_union_local_cross P hdis a d m ha hd hm hρ,
        add_div,Finset.sum_div]
      simp_rw [rationalCubeFamily8_local_normalized P a d m ha hd hm hε hρ]
      rw [← Finset.mul_sum]

end SphericalRiesz
