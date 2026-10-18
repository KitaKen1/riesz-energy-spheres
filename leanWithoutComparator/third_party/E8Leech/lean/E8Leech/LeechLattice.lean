import E8Leech.LeechGeometry
import E8Leech.LatticeEnergy

/-!
# The Leech coordinate set as a full-rank discrete lattice

Subtraction closure supplies its integer module structure. The minimum distance
gives discreteness, and the coordinate vectors 8 e_i supply full real span.
This suffices to reuse lattice Riesz summability. Covolume one is proved separately
in LeechBasis.lean using explicit integer reconstruction.
-/

noncomputable section

namespace E8Leech

open Set
open scoped ENNReal

def leechNumeratorSubgroup : AddSubgroup (Fin 24 → ℤ) where
  carrier := leechNumerators
  zero_mem' := leechNumerators_zero
  neg_mem' := by
    intro z hz
    simpa using leechNumerators_sub leechNumerators_zero hz
  add_mem' := by
    intro z w hz hw
    have hneg : -w ∈ leechNumerators := by
      simpa using leechNumerators_sub leechNumerators_zero hw
    simpa using leechNumerators_sub hz hneg

def leechCoordinatesLinear : (Fin 24 → ℤ) →ₗ[ℤ] Ambient 24 where
  toFun := leechCoordinates
  map_add' z w := by ext i; simp [leechCoordinates, add_div]
  map_smul' k z := by ext i; simp [leechCoordinates]; ring

def leechLattice : Submodule ℤ (Ambient 24) :=
  leechNumeratorSubgroup.toIntSubmodule.map leechCoordinatesLinear

theorem coe_leechLattice : (leechLattice : Set (Ambient 24)) = leechSet := by
  ext x
  change x ∈ leechLattice ↔ x ∈ leechSet
  rw [leechLattice, Submodule.mem_map]
  rfl

instance : DiscreteTopology leechLattice := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have hball : Metric.ball (0 : leechLattice) 1 = {0} := by
    ext x
    simp only [Metric.mem_ball, Set.mem_singleton_iff, dist_zero_right]
    constructor
    · intro hx
      by_contra hne
      have hne' : (x : Ambient 24) ≠ 0 := by
        intro h
        exact hne (Subtype.ext h)
      have hl := leechSet_norm_sq_lower (coe_leechLattice ▸ x.property) hne'
      change ‖(x : Ambient 24)‖ < 1 at hx
      nlinarith [norm_nonneg (x : Ambient 24)]
    · rintro rfl
      simp
  rw [← hball]
  exact Metric.isOpen_ball

theorem leechEightCoordinate_mem (i : Fin 24) :
    leechCoordinates (fun j => if j = i then 8 else 0) ∈ leechSet := by
  refine ⟨_, ⟨0, ?_, ?_, ?_⟩, rfl⟩
  · intro j
    by_cases h : j = i <;> simp [h]
  · simp
  · have he : leechResidue (fun j => if j = i then 8 else 0) 0 = 0 := by
      ext j
      by_cases h : j = i
      · simp [leechResidue, h]
        decide
      · simp [leechResidue, h]
    rw [he]
    exact golayCode.zero_mem

theorem leechLattice_span : Submodule.span ℝ (leechLattice : Set (Ambient 24)) = ⊤ := by
  let b := (EuclideanSpace.basisFun (Fin 24) ℝ).toBasis
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hv : leechCoordinates (fun j => if j = i then 8 else 0) ∈
      Submodule.span ℝ (leechLattice : Set (Ambient 24)) := by
    rw [coe_leechLattice]
    exact Submodule.subset_span (leechEightCoordinate_mem i)
  have he : (Real.sqrt 8 / 8) • leechCoordinates (fun j => if j = i then 8 else 0) = b i := by
    ext j
    by_cases h : j = i
    · subst j
      simp [b, EuclideanSpace.basisFun_apply, leechCoordinates]
      field_simp
      norm_num [Real.sq_sqrt]
    · simp [b, EuclideanSpace.basisFun_apply, leechCoordinates, h]
  rw [← he]
  exact Submodule.smul_mem _ _ hv

instance : IsZLattice ℝ leechLattice := ⟨leechLattice_span⟩

theorem leechLattice_rank : Module.finrank ℤ leechLattice = 24 := by
  rw [ZLattice.rank ℝ leechLattice]
  simp [Ambient]

theorem leech_latticeRieszEnergy_ne_top {s : ℝ} (hs : 24 < s) :
    latticeRieszEnergy leechSet s ≠ ∞ := by
  rw [← coe_leechLattice]
  apply latticeRieszEnergy_ne_top
  simpa [leechLattice_rank] using hs

end E8Leech
