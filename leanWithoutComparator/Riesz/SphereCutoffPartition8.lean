import Riesz.FiniteCutoffSquarePartition
import Riesz.EqualAreaEuclideanGeometry8
import Riesz.SphereSmallChartCores8

/-!
An actual finite partition of supported Sphere8 cutoff squares.
Continuity across the hemisphere boundary is proved from the support chord
bound, and compactness selects finitely many fixed rotations. No rotation
Haar measure, measurable rotation choice, sharp Gaussian certificate or
uniform row approximate-identity limit is assumed or supplied here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem sphereEqualAreaCoordinates8_continuousAt (x : Sphere8)
    (hx : 0 < (x : Ambient9) 0) : ContinuousAt sphereEqualAreaCoordinates8 x := by
  have hs : IsOpen {q : Ambient9 | q 0 ≠ 0} := isOpen_ne.preimage (by fun_prop)
  have hi := equalAreaInverse8_continuousOn.continuousAt (hs.mem_nhds hx.ne')
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).symm.continuousAt.comp
    (hi.comp continuous_subtype_val.continuousAt)

theorem sphereChartCutoff8_continuousAt_positive (ρ : ℝ) (hρ : 0 < ρ)
    (x : Sphere8) (hx : 0 < (x : Ambient9) 0) :
    ContinuousAt (sphereChartCutoff8 ρ hρ) x := by
  have he : ∀ᶠ y : Sphere8 in 𝓝 x, 0 < (y : Ambient9) 0 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx
  apply ((coordinateCutoff_continuous ρ hρ).continuousAt.comp
    (sphereEqualAreaCoordinates8_continuousAt x hx)).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  simp only [sphereChartCutoff8, ite_eq_left hy, Function.comp_apply]

theorem sphereChartCutoff8_support_height_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖)
    (x : Sphere8) (hx : sphereChartCutoff8 ρ hρ x ≠ 0) :
    1/2 < (x : Ambient9) 0 := by
  have hxs : x ∈ Function.support (sphereChartCutoff8 ρ hρ) := hx
  rw [sphereChartCutoff8_support] at hxs
  have hp : sphereChartCutoff8 ρ hρ northPole8 ≠ 0 := by
    rw [sphereChartCutoff8_northPole]
    exact one_ne_zero
  have hd := hB x northPole8 hx hp
  rw [sphereEqualAreaCoordinates8_northPole, sub_zero] at hd
  apply northPole8_ball_first_pos x (1/2) le_rfl
  change dist x northPole8 < 1/2
  linarith [hxs.2]

theorem sphereChartCutoff8_continuous_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖) :
    Continuous (sphereChartCutoff8 ρ hρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < (x : Ambient9) 0
  · exact sphereChartCutoff8_continuousAt_positive ρ hρ x hx
  · have hx0 : (x : Ambient9) 0 < (1/2 : ℝ) :=
      lt_of_le_of_lt (not_lt.mp hx) (by norm_num)
    have ho : IsOpen {y : Sphere8 | (y : Ambient9) 0 < (1/2 : ℝ)} :=
      isOpen_lt (by fun_prop) continuous_const
    have he : ∀ᶠ y : Sphere8 in 𝓝 x, (y : Ambient9) 0 < 1/2 := ho.mem_nhds hx0
    apply (continuousAt_const : ContinuousAt (fun _ : Sphere8 => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    by_contra hn
    have hh := sphereChartCutoff8_support_height_of_chord_bound ρ hρ hr hB y hn
    linarith

def rotatedSphereChartCutoff8 (ρ : ℝ) (hρ : 0 < ρ)
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) : ℝ :=
  sphereChartCutoff8 ρ hρ (sphereRotation8 g.symm x)

def rotatedSphereEqualAreaCoordinates8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (x : Sphere8) : EuclideanSpace ℝ (Fin 8) :=
  sphereEqualAreaCoordinates8 (sphereRotation8 g.symm x)

theorem rotatedSphereChartCutoff8_nonneg (ρ : ℝ) (hρ : 0 < ρ)
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    0 ≤ rotatedSphereChartCutoff8 ρ hρ g x := sphereChartCutoff8_nonneg ρ hρ _

theorem rotatedSphereChartCutoff8_le_one (ρ : ℝ) (hρ : 0 < ρ)
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    rotatedSphereChartCutoff8 ρ hρ g x ≤ 1 := sphereChartCutoff8_le_one ρ hρ _

theorem rotatedSphereChartCutoff8_center (ρ : ℝ) (hρ : 0 < ρ)
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    rotatedSphereChartCutoff8 ρ hρ g (sphereRotation8 g northPole8) = 1 := by
  unfold rotatedSphereChartCutoff8
  rw [show sphereRotation8 g.symm (sphereRotation8 g northPole8) = northPole8 from
    (sphereRotation8 g).left_inv northPole8, sphereChartCutoff8_northPole]

theorem rotatedSphereChartCutoff8_continuous (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff8 ρ hρ)) (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    Continuous (rotatedSphereChartCutoff8 ρ hρ g) :=
  hc.comp (sphereRotation8 g.symm).continuous

theorem sphere8_finite_rotated_cutoff_cover (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff8 ρ hρ)) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∀ x : Sphere8, ∃ i, 0 < rotatedSphereChartCutoff8 ρ hρ (g i) x := by
  classical
  let : CompactSpace Sphere8 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient9) 1)
  have ht : ∀ p : Sphere8, ∃ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      sphereRotation8 g northPole8 = p := fun p => sphereRotation8_transitive northPole8 p
  choose g hg using ht
  let U : Sphere8 → Set Sphere8 := fun p => {x | 0 < rotatedSphereChartCutoff8 ρ hρ (g p) x}
  have hU : ∀ p, IsOpen (U p) := fun p =>
    isOpen_lt continuous_const (rotatedSphereChartCutoff8_continuous ρ hρ hc (g p))
  have hcenter (p : Sphere8) : p ∈ U p := by
    change 0 < rotatedSphereChartCutoff8 ρ hρ (g p) p
    have he := rotatedSphereChartCutoff8_center ρ hρ (g p)
    rw [hg p] at he
    rw [he]
    exact zero_lt_one
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set Sphere8)).elim_finite_subcover
    U hU (fun p _ => mem_iUnion.mpr ⟨p,hcenter p⟩)
  let gs : Fin t.card → Ambient9 ≃ₗᵢ[ℝ] Ambient9 := fun i => g (t.equivFin.symm i).val
  refine ⟨t.card,gs,?_⟩
  intro x
  obtain ⟨p,hp⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hpt,hxp⟩ := mem_iUnion.mp hp
  change 0 < rotatedSphereChartCutoff8 ρ hρ (g p) x at hxp
  refine ⟨t.equivFin ⟨p,hpt⟩,?_⟩
  simpa only [gs, Equiv.symm_apply_apply] using hxp

def sphereFiniteCutoffMass8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) : Sphere8 → ℝ :=
  finiteCutoffSquareMass (fun i => rotatedSphereChartCutoff8 ρ hρ (g i))

def sphereFiniteCutoffWeight8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) : Fin K → Sphere8 → ℝ :=
  finiteCutoffSquarePartition (fun i => rotatedSphereChartCutoff8 ρ hρ (g i))

theorem sphereFiniteCutoffMass8_pos {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hcover : ∀ x : Sphere8, ∃ i, 0 < rotatedSphereChartCutoff8 ρ hρ (g i) x) (x : Sphere8) :
    0 < sphereFiniteCutoffMass8 ρ hρ g x :=
  finiteCutoffSquareMass_pos_of_cover _ hcover x

theorem sphereFiniteCutoffWeight8_nonneg {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (x : Sphere8) :
    0 ≤ sphereFiniteCutoffWeight8 ρ hρ g i x :=
  finiteCutoffSquarePartition_nonneg _ (fun j y => rotatedSphereChartCutoff8_nonneg ρ hρ (g j) y) i x

theorem sphereFiniteCutoffWeight8_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) (x : Sphere8) :
    sphereFiniteCutoffWeight8 ρ hρ g i x ≤ 1 :=
  finiteCutoffSquarePartition_le_one _ hpos i x

theorem sphereFiniteCutoffWeight8_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffWeight8 ρ hρ g i) :=
  finiteCutoffSquarePartition_continuous _ (fun j => rotatedSphereChartCutoff8_continuous ρ hρ hc (g j))
    hpos i

theorem sphereFiniteCutoffWeight8_sum_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (x : Sphere8) :
    (∑ i, (sphereFiniteCutoffWeight8 ρ hρ g i x)^2) = 1 :=
  finiteCutoffSquarePartition_sum_square _ hpos x

theorem sphereFiniteCutoffWeight8_ne_zero_iff {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) (x : Sphere8) :
    sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 ↔ rotatedSphereChartCutoff8 ρ hρ (g i) x ≠ 0 :=
  finiteCutoffSquarePartition_ne_zero_iff _ hpos i x

theorem sphereFiniteCutoffWeight8_correlation_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (x y : Sphere8) :
    (∑ i, sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y) ≤ 1 :=
  finiteCutoffSquarePartition_correlation_le_one _ hpos x y

theorem sphereFiniteCutoffWeight8_chord_bound {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (L : ℝ)
    (hB : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖)
    (i : Fin K) (x y : Sphere8)
    (hx : sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0)
    (hy : sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0) :
    dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
      rotatedSphereEqualAreaCoordinates8 (g i) y‖ := by
  have hx' := (sphereFiniteCutoffWeight8_ne_zero_iff ρ hρ g hpos i x).mp hx
  have hy' := (sphereFiniteCutoffWeight8_ne_zero_iff ρ hρ g hpos i y).mp hy
  have h := hB (sphereRotation8 (g i).symm x) (sphereRotation8 (g i).symm y) hx' hy'
  rw [sphereRotation8_dist] at h
  exact h

theorem sphere8_exists_finite_cutoff_square_partition (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ∃ hρ : 0 < ρ, ρ ≤ 1/8 ∧
      ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
        Continuous (sphereChartCutoff8 ρ hρ) ∧
        (∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) ∧
        (∀ i, Continuous (sphereFiniteCutoffWeight8 ρ hρ g i)) ∧
        (∀ i x, 0 ≤ sphereFiniteCutoffWeight8 ρ hρ g i x ∧ sphereFiniteCutoffWeight8 ρ hρ g i x ≤ 1) ∧
        (∀ x, (∑ i, (sphereFiniteCutoffWeight8 ρ hρ g i x)^2) = 1) ∧
        (∀ i x y, sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 →
          sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0 →
          dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
            rotatedSphereEqualAreaCoordinates8 (g i) y‖) := by
  have hL0 : 1 < min L 2 := lt_min hL (by norm_num)
  obtain ⟨ρ,hρ,hr,hLip⟩ := equalAreaPhiEuclidean8_near_isometry (min L 2) hL0
  have hB : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ min L 2*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖ :=
    fun x y hx hy => sphereChartCutoff8_chord_bound ρ hρ (min L 2) hLip x y hx hy
  have hB2 : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_right L 2) (norm_nonneg _))
  have hBL : ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 →
      sphereChartCutoff8 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_left L 2) (norm_nonneg _))
  have hc := sphereChartCutoff8_continuous_of_chord_bound ρ hρ hr hB2
  obtain ⟨K,g,hcover⟩ := sphere8_finite_rotated_cutoff_cover ρ hρ hc
  have hpos := sphereFiniteCutoffMass8_pos ρ hρ g hcover
  refine ⟨ρ,hρ,hρ,hr,K,g,hc,hpos,?_,?_,?_,?_⟩
  · exact sphereFiniteCutoffWeight8_continuous ρ hρ g hc hpos
  · exact fun i x => ⟨sphereFiniteCutoffWeight8_nonneg ρ hρ g i x,
      sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i x⟩
  · exact sphereFiniteCutoffWeight8_sum_square ρ hρ g hpos
  · exact sphereFiniteCutoffWeight8_chord_bound ρ hρ g hpos L hBL

end SphericalRiesz
