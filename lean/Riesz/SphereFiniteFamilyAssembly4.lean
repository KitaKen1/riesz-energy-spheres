import Riesz.SphereResidualAssembly8

/-! Finite disjoint physical sphere patches split the actual neutralized
energy into local diagonal blocks and every ordered distinct cross block.
No integrability assumption is supplied: actual global kernel and potential
integrability discharge all finite-union and finite-sum exchanges. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

def sphereFiniteMixedPair4 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Sphere8) (Y : κ → Sphere8) : ℝ :=
  ∑ i, ∑ j, sphereKernel4 (X i) (Y j)

def sphereFiniteCrossBlock4 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Sphere8) (Y : κ → Sphere8) (S T : Set Sphere8) (M : ℝ) : ℝ :=
  sphereFiniteMixedPair4 X Y - M*(∑ i, sphereRestrictedPotential4 T (X i)) -
    M*(∑ j, sphereRestrictedPotential4 S (Y j)) + M^2*sphereBackgroundPair4 S T

theorem sphereFiniteMixedPair4_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Sphere8) (Y : κ → Sphere8) :
    sphereFiniteMixedPair4 X Y = sphereFiniteMixedPair4 Y X := by
  unfold sphereFiniteMixedPair4
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_congr rfl (fun i _ => sphereKernel4_symm (X i) (Y j))

theorem sphereFiniteCrossBlock4_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Sphere8) (Y : κ → Sphere8) (S T : Set Sphere8) (M : ℝ) :
    sphereFiniteCrossBlock4 X Y S T M = sphereFiniteCrossBlock4 Y X T S M := by
  unfold sphereFiniteCrossBlock4
  rw [sphereFiniteMixedPair4_symm X Y,sphereBackgroundPair4_symm S T]
  ring

theorem sphereFiniteCrossBlock4_diag {ι : Type*} [Fintype ι]
    (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    sphereFiniteCrossBlock4 X X S S M = sphereFiniteBlock4 X S M := by
  unfold sphereFiniteCrossBlock4 sphereFiniteMixedPair4 sphereFiniteBlock4 sphereFinitePair4
  ring

theorem sphereRestrictedPotential4_iUnion {ι : Type*} [Fintype ι]
    (S : ι → Set Sphere8) (hs : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (x : Sphere8) :
    sphereRestrictedPotential4 (⋃ i, S i) x = ∑ i, sphereRestrictedPotential4 (S i) x := by
  exact integral_iUnion_fintype hs hd (fun _ => (sphereKernel4_integrable x).restrict)

theorem sphereBackgroundPair4_iUnion_left {ι : Type*} [Fintype ι]
    (S : ι → Set Sphere8) (hs : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (T : Set Sphere8) :
    sphereBackgroundPair4 (⋃ i, S i) T = ∑ i, sphereBackgroundPair4 (S i) T := by
  exact integral_iUnion_fintype hs hd
    (fun _ => (sphereRestrictedPotential4_integrable T).restrict)

theorem sphereBackgroundPair4_iUnion_right {ι : Type*} [Fintype ι]
    (S : Set Sphere8) (T : ι → Set Sphere8) (ht : ∀ i, MeasurableSet (T i))
    (hd : Pairwise (fun i j => Disjoint (T i) (T j))) :
    sphereBackgroundPair4 S (⋃ i, T i) = ∑ i, sphereBackgroundPair4 S (T i) := by
  rw [sphereBackgroundPair4_symm,sphereBackgroundPair4_iUnion_left T ht hd S]
  exact Finset.sum_congr rfl (fun i _ => sphereBackgroundPair4_symm (T i) S)

theorem sphereBackgroundPair4_iUnion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : ι → Set Sphere8) (T : κ → Set Sphere8)
    (hs : ∀ i, MeasurableSet (S i)) (ht : ∀ j, MeasurableSet (T j))
    (hds : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdt : Pairwise (fun i j => Disjoint (T i) (T j))) :
    sphereBackgroundPair4 (⋃ i, S i) (⋃ j, T j) =
      ∑ i, ∑ j, sphereBackgroundPair4 (S i) (T j) := by
  rw [sphereBackgroundPair4_iUnion_left S hs hds]
  simp_rw [sphereBackgroundPair4_iUnion_right _ T ht hdt]

theorem sphereFinitePair4_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → Sphere8) :
    sphereFinitePair4 (fun t : ι × κ => X t.1 t.2) =
      ∑ i, ∑ j, sphereFiniteMixedPair4 (X i) (X j) := by
  unfold sphereFinitePair4 sphereFiniteMixedPair4
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

theorem sphereFiniteBlock4_iUnion_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → Sphere8) (S : ι → Set Sphere8)
    (hs : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (M : ℝ) :
    sphereFiniteBlock4 (fun t : ι × κ => X t.1 t.2) (⋃ i, S i) M =
      ∑ i, ∑ j, sphereFiniteCrossBlock4 (X i) (X j) (S i) (S j) M := by
  have hv : (∑ t : ι × κ, sphereRestrictedPotential4 (⋃ i, S i) (X t.1 t.2)) =
      ∑ i, ∑ j, ∑ u, sphereRestrictedPotential4 (S j) (X i u) := by
    simp only [Fintype.sum_prod_type]
    simp_rw [sphereRestrictedPotential4_iUnion S hs hd]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hrev : (∑ i, ∑ j, ∑ u, sphereRestrictedPotential4 (S i) (X j u)) =
      ∑ i, ∑ j, ∑ u, sphereRestrictedPotential4 (S j) (X i u) := Finset.sum_comm
  unfold sphereFiniteBlock4
  rw [sphereFinitePair4_prod,hv,sphereBackgroundPair4_iUnion S S hs hs hd hd]
  simp only [sphereFiniteCrossBlock4,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hrev]
  ring

theorem sphereFiniteBlock4_iUnion_local_cross {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (X : ι → κ → Sphere8) (S : ι → Set Sphere8)
    (hs : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (M : ℝ) :
    sphereFiniteBlock4 (fun t : ι × κ => X t.1 t.2) (⋃ i, S i) M =
      (∑ i, sphereFiniteBlock4 (X i) (S i) M) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        sphereFiniteCrossBlock4 (X i) (X j) (S i) (S j) M := by
  classical
  rw [sphereFiniteBlock4_iUnion_prod X S hs hd]
  have hi (i : ι) : (∑ j, sphereFiniteCrossBlock4 (X i) (X j) (S i) (S j) M) =
      sphereFiniteBlock4 (X i) (S i) M + ∑ j ∈ Finset.univ.erase i,
        sphereFiniteCrossBlock4 (X i) (X j) (S i) (S j) M := by
    have h := Finset.sum_erase_add Finset.univ
      (fun j => sphereFiniteCrossBlock4 (X i) (X j) (S i) (S j) M) (Finset.mem_univ i)
    rw [sphereFiniteCrossBlock4_diag] at h
    simpa only [add_comm] using h.symm
  simp_rw [hi]
  rw [Finset.sum_add_distrib]

end SphericalRiesz
