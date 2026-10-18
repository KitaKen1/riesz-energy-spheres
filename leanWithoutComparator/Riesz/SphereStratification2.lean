import Riesz.HexConstruction2
import Riesz.SphereCellConstruction2
import Mathlib.Analysis.Normed.Module.Connected
import Riesz.EqualAreaHex2

/-! Exact-mass density-scale stratifications on S².
The whole sphere and the complements of actual pairwise disjoint small triangular patches are
partitioned with a common diameter-square budget. The proof uses a compact connected carrier,
a local exterior coordinate box with a common area lower bound, finite separated covers and
the checked tree partition of SphereCellConstruction2. No residual partition is assumed. -/

section

/-! Local topology of the exact-area S² chart. No residual partition is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Topology
open scoped Pointwise ContDiff NNReal
namespace SphericalRiesz
open Boundary

/-- The image of a coordinate set under the rotated equal-area chart. -/
def chartImage2 (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (S : Set (Fin 2 → ℝ)) :
    Set (SphereD 2) :=
  {x | ∃ p ∈ S, (x : AmbientD 2) = g (equalAreaPhiD p)}

theorem chartImage2_eq_preimage (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (S : Set (Fin 2 → ℝ)) :
    chartImage2 g S = (sphereRotationD g.symm) ⁻¹' equalAreaSpherePatchD S := by
  ext x
  simp only [chartImage2, mem_ofPred_eq, mem_preimage, equalAreaSpherePatchD, mem_image]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhiD p = g.symm (x : AmbientD 2)
    rw [hx, g.symm_apply_apply]
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhiD p = g.symm (x : AmbientD 2) at hx
    rw [hx, g.apply_symm_apply]

theorem chartImage2_measurable (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S : Set (Fin 2 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomainD) :
    MeasurableSet (chartImage2 g S) := by
  rw [chartImage2_eq_preimage]
  exact (equalAreaSpherePatchD_measurable S hS hsub).preimage (sphereRotationD g.symm).measurable

theorem chartImage2_area (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S : Set (Fin 2 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomainD) :
    (sphereAreaD 2) (chartImage2 g S) = (volume : Measure (Fin 2 → ℝ)) S := by
  rw [chartImage2_eq_preimage, (sphereAreaD_rotation_preserving g.symm).measure_preimage_emb
    (sphereRotationD g.symm).measurableEmbedding, sphereAreaD_equalAreaSpherePatch S hS hsub]

theorem chartImage2_mono (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S T : Set (Fin 2 → ℝ)}
    (h : S ⊆ T) : chartImage2 g S ⊆ chartImage2 g T := by
  rintro x ⟨p, hp, hx⟩
  exact ⟨p, h hp, hx⟩

theorem chartImage2_disjoint (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S T : Set (Fin 2 → ℝ)}
    (hS : S ⊆ equalAreaChartDomainD) (hT : T ⊆ equalAreaChartDomainD) (hST : Disjoint S T) :
    Disjoint (chartImage2 g S) (chartImage2 g T) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hx⟩ ⟨q, hq, hx'⟩
  have : equalAreaPhiD p = equalAreaPhiD q := g.injective (hx.symm.trans hx')
  have hpq := equalAreaPhiD_injOn (hS hp) (hT hq) this
  subst hpq
  exact Set.disjoint_left.mp hST hp hq

/-- The image of a compact coordinate set is closed. -/
theorem chartImage2_isClosed (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S : Set (Fin 2 → ℝ)}
    (hS : IsCompact S) : IsClosed (chartImage2 g S) := by
  have hc : IsCompact ((fun p : Fin 2 → ℝ => g (equalAreaPhiD p)) '' S) :=
    hS.image (g.continuous.comp equalAreaPhiD_continuous)
  have he : chartImage2 g S =
      Subtype.val ⁻¹' ((fun p : Fin 2 → ℝ => g (equalAreaPhiD p)) '' S) := by
    ext x
    simp only [chartImage2, mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
  rw [he]
  exact hc.isClosed.preimage continuous_subtype_val

/-- The image of an open coordinate set inside the chart domain is open. -/
theorem chartImage2_isOpen (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S : Set (Fin 2 → ℝ)}
    (hS : IsOpen S) (hsub : S ⊆ equalAreaChartDomainD) : IsOpen (chartImage2 g S) := by
  rw [chartImage2_eq_preimage]
  apply IsOpen.preimage (sphereRotationD g.symm).continuous
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, hp, hx⟩
  have hx0 : 0 < (x : AmbientD 2) 0 := by
    rw [← hx]
    exact equalAreaPhiD_first_pos p (hsub hp)
  have hcoord : WithLp.ofLp (sphereEqualAreaCoordinates2 x) = p := by
    have h := equalAreaInverseD_phi p (hsub hp)
    rw [hx] at h
    simpa [sphereEqualAreaCoordinates2] using h
  have hca := sphereEqualAreaCoordinates2_continuousAt x hx0
  have hS' : IsOpen ((fun u : EuclideanSpace ℝ (Fin 2) => WithLp.ofLp u) ⁻¹' S) :=
    hS.preimage (PiLp.continuous_ofLp 2 _)
  have hnb : (fun u : EuclideanSpace ℝ (Fin 2) => WithLp.ofLp u) ⁻¹' S ∈
      𝓝 (sphereEqualAreaCoordinates2 x) := by
    apply hS'.mem_nhds
    simp only [mem_preimage]
    rw [hcoord]; exact hp
  have hpos : {y : SphereD 2 | 0 < (y : AmbientD 2) 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx0
  filter_upwards [hca hnb, hpos] with y hy hy0
  refine ⟨WithLp.ofLp (sphereEqualAreaCoordinates2 y), hy, ?_⟩
  have h := equalAreaPhiD_inverse8 y hy0
  simpa [sphereEqualAreaCoordinates2] using h


/-- Chart images of convex coordinate sets are preconnected. -/
theorem chartImage2_preconnected_of_preconnected (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) {S : Set (Fin 2 → ℝ)}
    (hS : IsPreconnected S) (hsub : S ⊆ equalAreaChartDomainD) :
    IsPreconnected (chartImage2 g S) := by
  have himg : Subtype.val '' chartImage2 g S =
      (fun p : Fin 2 → ℝ => g (equalAreaPhiD p)) '' S := by
    ext y
    simp only [chartImage2, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨p, hp, hxp⟩, rfl⟩
      exact ⟨p, hp, hxp.symm⟩
    · rintro ⟨p, hp, rfl⟩
      have hm : g (equalAreaPhiD p) ∈ sphere (0 : AmbientD 2) 1 := by
        rw [mem_sphere_zero_iff_norm, g.norm_map]
        have := equalAreaPhiD_mem_sphere p (hsub hp).1
        rwa [mem_sphere_zero_iff_norm] at this
      exact ⟨⟨g (equalAreaPhiD p), hm⟩, ⟨p, hp, rfl⟩, rfl⟩
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
  exact hS.image _ (g.continuous.comp equalAreaPhiD_continuous).continuousOn


theorem chartImage2_coe_image (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
    {S : Set (Fin 2 → ℝ)} (hS : S ⊆ equalAreaChartDomainD) :
    Subtype.val '' chartImage2 g S = (fun p : Fin 2 → ℝ => g (equalAreaPhiD p)) '' S := by
  ext y
  constructor
  · rintro ⟨x,⟨p,hp,hxp⟩,rfl⟩
    exact ⟨p,hp,hxp.symm⟩
  · rintro ⟨p,hp,rfl⟩
    have hm : g (equalAreaPhiD p) ∈ sphere (0 : AmbientD 2) 1 := by
      rw [mem_sphere_zero_iff_norm,g.norm_map]
      have h := equalAreaPhiD_mem_sphere p (hS hp).1
      rwa [mem_sphere_zero_iff_norm] at h
    exact ⟨⟨g (equalAreaPhiD p),hm⟩,⟨p,hp,rfl⟩,rfl⟩

theorem chartImage2_interior (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
    {S : Set (Fin 2 → ℝ)} (hS : S ⊆ equalAreaChartDomainD) :
    interior (chartImage2 g S) = chartImage2 g (interior S) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨p,hp,hxp⟩ := interior_subset hx
    let B := equalAreaCoordinateBuffer2 g (interior (chartImage2 g S))
    have hBo : IsOpen B := equalAreaCoordinateBuffer2_isOpen g _ isOpen_interior
    have hBS : B ⊆ S := by
      intro u hu
      obtain ⟨huD,q,hq,hqu⟩ := equalAreaCoordinateBuffer2_mem g _ u hu
      obtain ⟨v,hv,hqv⟩ := interior_subset hq
      have huv : u = v := equalAreaPhiD_injOn huD (hS hv)
        (g.injective (hqu.trans hqv))
      exact huv ▸ hv
    have hpB : p ∈ B := by
      refine ⟨⟨p,hS hp⟩,?_,rfl⟩
      have he : equalAreaRotatedSphereChart2 g ⟨p,hS hp⟩ = x := Subtype.ext hxp.symm
      simpa only [mem_preimage,he] using hx
    exact ⟨p,interior_maximal hBS hBo hpB,hxp⟩
  · exact interior_maximal (chartImage2_mono g interior_subset)
      (chartImage2_isOpen g isOpen_interior (interior_subset.trans hS))

theorem chartImage2_sdiff (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
    {S T : Set (Fin 2 → ℝ)} (hS : S ⊆ equalAreaChartDomainD)
    (hT : T ⊆ equalAreaChartDomainD) :
    chartImage2 g (S \ T) = chartImage2 g S \ chartImage2 g T := by
  ext x
  constructor
  · rintro ⟨p,⟨hp,hpT⟩,hxp⟩
    refine ⟨⟨p,hp,hxp⟩,?_⟩
    rintro ⟨q,hq,hxq⟩
    have hpq : p = q := equalAreaPhiD_injOn (hS hp) (hT hq)
      (g.injective (hxp.symm.trans hxq))
    exact hpT (hpq ▸ hq)
  · rintro ⟨⟨p,hp,hxp⟩,hxT⟩
    exact ⟨p,⟨hp,fun hpT => hxT ⟨p,hpT,hxp⟩⟩,hxp⟩

theorem chartImage2_frontier_exact (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
    {S : Set (Fin 2 → ℝ)} (hS : IsCompact S) (hD : S ⊆ equalAreaChartDomainD) :
    frontier (chartImage2 g S) = chartImage2 g (frontier S) := by
  rw [(chartImage2_isClosed g hS).frontier_eq,chartImage2_interior g hD,
    ← chartImage2_sdiff g hD (interior_subset.trans hD),← hS.isClosed.frontier_eq]

theorem chartImage2_closure (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2)
    {S : Set (Fin 2 → ℝ)} (hS : IsCompact (closure S))
    (hD : closure S ⊆ equalAreaChartDomainD) :
    closure (chartImage2 g S) = chartImage2 g (closure S) := by
  apply subset_antisymm
  · exact closure_minimal (chartImage2_mono g subset_closure) (chartImage2_isClosed g hS)
  · intro x hx
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      chartImage2_coe_image g (subset_closure.trans hD)]
    obtain ⟨p,hp,hxp⟩ := hx
    exact image_closure_subset_closure_image (g.continuous.comp equalAreaPhiD_continuous)
      ⟨p,hp,hxp.symm⟩

theorem unitCube2_eq_closedBall : UnitCube 2 =
    closedBall (fun _ : Fin 2 => (1/2:ℝ)) (1/2) := by
  ext w
  rw [mem_closedBall,dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
  change (∀ i, 0 ≤ w i ∧ w i ≤ 1) ↔ ∀ i, dist (w i) (1/2:ℝ) ≤ 1/2
  simp only [Real.dist_eq,abs_le]
  constructor <;> intro h i <;> have hi := h i <;> constructor <;> linarith

def unitCubeOpen2 : Set (Fin 2 → ℝ) := interior (UnitCube 2)

theorem unitCubeOpen2_eq_ball : unitCubeOpen2 =
    ball (fun _ : Fin 2 => (1/2:ℝ)) (1/2) := by
  rw [unitCubeOpen2,unitCube2_eq_closedBall,interior_closedBall _ (by norm_num)]

theorem unitCubeOpen2_eq_piIoo : unitCubeOpen2 = Set.pi univ (fun _ => Ioo (0:ℝ) 1) := by
  ext w
  rw [unitCubeOpen2_eq_ball,mem_ball,dist_pi_lt_iff (by norm_num : (0:ℝ) < 1/2)]
  simp only [mem_pi,mem_univ,forall_true_left]
  change (∀ i, dist (w i) (1/2:ℝ) < 1/2) ↔ ∀ i, 0 < w i ∧ w i < 1
  simp only [Real.dist_eq,abs_lt]
  constructor <;> intro h i <;> have hi := h i <;> constructor <;> linarith

theorem unitCubeOpen2_closure : closure unitCubeOpen2 = UnitCube 2 := by
  rw [unitCubeOpen2_eq_ball,closure_ball _ (by norm_num),unitCube2_eq_closedBall]

theorem unitCube2_frontier_preconnected : IsPreconnected (frontier (UnitCube 2)) := by
  rw [unitCube2_eq_closedBall,frontier_closedBall _ (by norm_num)]
  exact isPreconnected_sphere (by simp : 1 < Module.rank ℝ (Fin 2 → ℝ))
    (fun _ => (1/2:ℝ)) (1/2)

theorem equalAreaWideCube2_domain {p : Fin 2 → ℝ} (hp : ‖p‖ ≤ 1/4) :
    p ∈ equalAreaChartDomainD := by
  have h1 := (norm_le_pi_norm p (1:Fin 2)).trans hp
  have h0 := (norm_le_pi_norm p (0:Fin 2)).trans hp
  have hsq : equalAreaSquaredNormD p < 1 := by
    simp only [equalAreaSquaredNormD,Fin.sum_univ_one]
    change p (1:Fin 2)^2 < 1
    rw [Real.norm_eq_abs] at h1
    nlinarith [sq_abs (p 1),abs_nonneg (p 1)]
  refine ⟨hsq,?_⟩
  rw [Real.norm_eq_abs,abs_le] at h0
  have hpi := Real.pi_gt_three
  constructor <;> linarith

theorem equalAreaWideCube2_lipschitz :
    ∃ L : ℝ≥0, 1 ≤ L ∧ LipschitzOnWith L (equalAreaPhiD (n := 1))
      (closedBall (0 : Fin 2 → ℝ) (1/4:ℝ)) := by
  have hcd : ContDiffOn ℝ ∞ (equalAreaPhiD (n := 1))
      (closedBall (0 : Fin 2 → ℝ) (1/4:ℝ)) := by
    intro p hp
    have hpn : ‖p‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_zero_right] using hp
    exact (equalAreaPhi2_contDiffAt p (equalAreaWideCube2_domain hpn).1).contDiffWithinAt
  obtain ⟨L,hL⟩ := hcd.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  exact ⟨L+1,le_add_of_nonneg_left (show (0:ℝ≥0) ≤ L from zero_le),hL.weaken (by simp)⟩

def hexAffineHomeomorph2 (p : SmallHexCubePatch2) : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) :=
  (((Homeomorph.subRight p.c).trans hexCoordinateInverse2.symm.toHomeomorph).trans
    (Homeomorph.smulOfNeZero p.ε p.ε_pos.ne')).trans (Homeomorph.addLeft p.v)

theorem hexAffineHomeomorph2_apply (p : SmallHexCubePatch2) (w : Fin 2 → ℝ) :
    hexAffineHomeomorph2 p w = equalAreaHexAffine2 p.v p.c p.ε w := rfl

theorem smallHexSpherePatch2_eq_chartImage (p : SmallHexCubePatch2) :
    smallHexSpherePatch2 p = chartImage2 p.g (hexAffineHomeomorph2 p '' UnitCube 2) := by
  rw [smallHexSpherePatch2,equalAreaHexSpherePatch2_rotation_preimage,chartImage2_eq_preimage]
  rfl

theorem smallHexSpherePatch2_isCompact (p : SmallHexCubePatch2) :
    IsCompact (smallHexSpherePatch2 p) :=
  equalAreaHexSpherePatch2_cube_isCompact p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

theorem smallHexSpherePatch2_frontier_preconnected (p : SmallHexCubePatch2) :
    IsPreconnected (frontier (smallHexSpherePatch2 p)) := by
  let S := hexAffineHomeomorph2 p '' UnitCube 2
  have hSc : IsCompact S := (unitCube_isCompact 2).image (hexAffineHomeomorph2 p).continuous
  have hSD : S ⊆ equalAreaChartDomainD :=
    equalAreaHexAffine2_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small
  rw [smallHexSpherePatch2_eq_chartImage,chartImage2_frontier_exact p.g hSc hSD,
    ← (hexAffineHomeomorph2 p).image_frontier]
  apply chartImage2_preconnected_of_preconnected p.g
  · exact unitCube2_frontier_preconnected.image _ (hexAffineHomeomorph2 p).continuous.continuousOn
  · rw [(hexAffineHomeomorph2 p).image_frontier]
    exact ((hSc.isClosed.frontier_subset).trans hSD)

theorem smallHexSpherePatch2_closure_interior (p : SmallHexCubePatch2) :
    closure (interior (smallHexSpherePatch2 p)) = smallHexSpherePatch2 p := by
  let S := hexAffineHomeomorph2 p '' UnitCube 2
  have hSc : IsCompact S := (unitCube_isCompact 2).image (hexAffineHomeomorph2 p).continuous
  have hSD : S ⊆ equalAreaChartDomainD :=
    equalAreaHexAffine2_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small
  have hreg : closure (interior S) = S := by
    rw [← (hexAffineHomeomorph2 p).image_interior,← unitCubeOpen2,
      ← (hexAffineHomeomorph2 p).image_closure,unitCubeOpen2_closure]
  rw [smallHexSpherePatch2_eq_chartImage,chartImage2_interior p.g hSD,
    chartImage2_closure p.g (by rwa [hreg]) (by rwa [hreg]),hreg]

theorem smallHexSpherePatch2_interior_frontier_preconnected (p : SmallHexCubePatch2) :
    IsPreconnected (frontier (interior (smallHexSpherePatch2 p))) := by
  rw [frontier,smallHexSpherePatch2_closure_interior,interior_interior,
    ← (smallHexSpherePatch2_isCompact p).isClosed.frontier_eq]
  exact smallHexSpherePatch2_frontier_preconnected p

def hexResidualCarrier2 {K : ℕ} (P : Fin K → SmallHexCubePatch2) : Set (SphereD 2) :=
  (⋃ i, interior (smallHexSpherePatch2 (P i)))ᶜ

theorem sphere2_univ_preconnected : IsPreconnected (univ : Set (SphereD 2)) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  have hs : IsPreconnected (sphere (0 : AmbientD 2) 1) :=
    isPreconnected_sphere (by simp [AmbientD,← Module.finrank_eq_rank] : 1 < Module.rank ℝ (AmbientD 2))
      (0 : AmbientD 2) 1
  convert hs using 1
  ext x
  simp [SphereD]

theorem hexResidualCarrier2_preconnected {K : ℕ} (P : Fin K → SmallHexCubePatch2)
    (hdisj : Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i)) (smallHexSpherePatch2 (P j)))) :
    IsPreconnected (hexResidualCarrier2 P) := by
  have h := isPreconnected_sdiff_finite_open_holes2 (univ : Set (SphereD 2)) isClosed_univ
    sphere2_univ_preconnected (fun i => interior (smallHexSpherePatch2 (P i)))
    (fun _ => isOpen_interior) (fun _ => subset_univ _)
    (fun i => smallHexSpherePatch2_interior_frontier_preconnected (P i))
    (fun i j hij => by simpa only [smallHexSpherePatch2_closure_interior] using hdisj hij)
    Finset.univ
  convert h using 1
  ext x
  simp [hexResidualCarrier2]

theorem hexResidualCarrier2_isCompact {K : ℕ} (P : Fin K → SmallHexCubePatch2) :
    IsCompact (hexResidualCarrier2 P) := by
  apply IsClosed.isCompact
  exact (isOpen_iUnion fun _ => isOpen_interior).isClosed_compl

theorem hexResidual2_subset_carrier {K : ℕ} (P : Fin K → SmallHexCubePatch2) :
    (hexFamilyUnion2 P)ᶜ ⊆ hexResidualCarrier2 P := by
  intro x hx hxi
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxi
  exact hx (mem_iUnion.mpr ⟨i,interior_subset hi⟩)

end SphericalRiesz
end
end

section

/-! A small coordinate box outside the closed square, adjacent to any point outside
its interior. All side lengths equal `a`, hence its area is exactly `a²`. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
namespace SphericalRiesz
open Boundary

theorem exists_outside_cube_box2 {w : Fin 2 → ℝ} (hw : w ∉ unitCubeOpen2)
    {a : ℝ} (ha : 0 < a) :
    ∃ S : Set (Fin 2 → ℝ), MeasurableSet S ∧ volume S = ENNReal.ofReal (a^2) ∧
      (∀ q ∈ S, q ∉ UnitCube 2) ∧ (∀ q ∈ S, dist q w ≤ a) := by
  classical
  rw [unitCubeOpen2_eq_piIoo] at hw
  have hwi : ∃ i, w i ≤ 0 ∨ 1 ≤ w i := by
    by_contra hi
    push Not at hi
    apply hw
    intro i _
    exact ⟨(hi i).1,(hi i).2⟩
  obtain ⟨i,hi⟩ := hwi
  let v : Fin 2 → ℝ := fun j => if j = i ∧ w i ≤ 0 then w j-a else w j
  let S : Set (Fin 2 → ℝ) := Set.pi univ (fun j => Ioo (v j) (v j+a))
  have hSm : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hSv : volume S = ENNReal.ofReal (a^2) := by
    change volume (Set.pi univ (fun j => Ioo (v j) (v j+a))) = _
    rw [volume_pi_pi]
    simp only [Real.volume_Ioo,add_sub_cancel_left,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
    exact (ENNReal.ofReal_pow ha.le 2).symm
  refine ⟨S,hSm,hSv,?_,?_⟩
  · intro q hq hqu
    have hqi := hq i (mem_univ i)
    have hqu_i := hqu i
    rcases hi with hi | hi
    · simp [v,hi] at hqi
      linarith [hqi.1,hqi.2,hqu_i.1,hqu_i.2]
    · by_cases hlow : w i ≤ 0
      · linarith
      · simp [v,hlow] at hqi
        linarith [hqi.1,hqi.2,hqu_i.1,hqu_i.2]
  · intro q hq
    rw [dist_pi_le_iff ha.le]
    intro j
    have hqj := hq j (mem_univ j)
    rw [Real.dist_eq,abs_le]
    by_cases hj : j = i ∧ w i ≤ 0
    · simp only [v,ite_eq_left hj] at hqj
      constructor <;> linarith [hqj.1,hqj.2]
    · simp only [v,ite_eq_right hj] at hqj
      constructor <;> linarith [hqj.1,hqj.2]

end SphericalRiesz
end
end

section

/-! Local exterior mass near an actual small triangular patch. The coordinate box has
side `H/(4 L B ε)`, so the chart area factor `ε²` cancels the patch size. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal
namespace SphericalRiesz
open Boundary

def hexResidualLocalMassConst2 (L : ℝ≥0) : ℝ :=
  1/(16*(L:ℝ)^2*(‖hexMap‖+1)^2*(sphereAreaD 2).real univ)

theorem hexResidualLocalMassConst2_pos {L : ℝ≥0} (hL : 1 ≤ L) :
    0 < hexResidualLocalMassConst2 L := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hA := sphereAreaD_univ_pos 2
  unfold hexResidualLocalMassConst2
  positivity

theorem exists_hex_patch_exterior_box2 {L : ℝ≥0} (hL : 1 ≤ L)
    (hLip : LipschitzOnWith L (equalAreaPhiD (n := 1))
      (closedBall (0 : Fin 2 → ℝ) (1/4:ℝ)))
    (p : SmallHexCubePatch2) (x : SphereD 2) (u : Fin 2 → ℝ)
    (hu : ‖u‖ ≤ 1/6) (hxu : (x : AmbientD 2) = p.g (equalAreaPhiD u))
    (hxout : x ∉ interior (smallHexSpherePatch2 p))
    {H : ℝ} (hH : 0 < H) (hHsmall : H ≤ 1/12) :
    ∃ E : Set (SphereD 2), MeasurableSet E ∧
      E ⊆ (smallHexSpherePatch2 p)ᶜ ∩ ball x H ∧
      (sphereProbabilityD 2).real E = hexResidualLocalMassConst2 L*H^2 := by
  classical
  let B : ℝ := ‖hexMap‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hε := p.ε_pos
  have huD : u ∈ equalAreaChartDomainD := equalAreaWideCube2_domain (hu.trans (by norm_num))
  let w : Fin 2 → ℝ := (hexAffineHomeomorph2 p).symm u
  have hw : equalAreaHexAffine2 p.v p.c p.ε w = u :=
    (hexAffineHomeomorph2 p).apply_symm_apply u
  have hwout : w ∉ unitCubeOpen2 := by
    intro hwo
    apply hxout
    have hPD : hexAffineHomeomorph2 p '' UnitCube 2 ⊆ equalAreaChartDomainD :=
      equalAreaHexAffine2_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small
    rw [smallHexSpherePatch2_eq_chartImage,chartImage2_interior p.g hPD,
      ← (hexAffineHomeomorph2 p).image_interior]
    exact ⟨u,⟨w,hwo,hw⟩,hxu⟩
  let a : ℝ := H/(4*(L:ℝ)*B*p.ε)
  have ha : 0 < a := div_pos hH (by positivity)
  obtain ⟨S,hSm,hSv,hSout,hSr⟩ := exists_outside_cube_box2 hwout ha
  have hcalc : (L:ℝ)*p.ε*B*a = H/4 := by
    dsimp [a]
    field_simp [hL0.ne',hB.ne',p.ε_pos.ne']
  have hsmall : p.ε*B*a ≤ H/4 := by
    have hle := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ L from hL)
      (show 0 ≤ p.ε*B*a by positivity)
    rw [one_mul] at hle
    nlinarith [hcalc]
  have hdist : ∀ q ∈ S, dist (equalAreaHexAffine2 p.v p.c p.ε q) u ≤ p.ε*B*a := by
    intro q hq
    have hqa : ‖q-w‖ ≤ a := by simpa only [dist_eq_norm] using hSr q hq
    have hdiff : equalAreaHexAffine2 p.v p.c p.ε q-u = p.ε • hexMap (q-w) := by
      rw [← hw]
      simp only [equalAreaHexAffine2,map_sub,smul_sub]
      abel
    rw [dist_eq_norm,hdiff,norm_smul,Real.norm_eq_abs,abs_of_pos p.ε_pos]
    rw [mul_assoc p.ε B a]
    apply mul_le_mul_of_nonneg_left _ p.ε_pos.le
    calc ‖hexMap (q-w)‖ ≤ ‖hexMap‖*‖q-w‖ := hexMap.le_opNorm _
      _ ≤ B*a := mul_le_mul (by dsimp [B]; linarith [norm_nonneg hexMap]) hqa
        (norm_nonneg _) hB.le
  have hqnorm : ∀ q ∈ S, ‖equalAreaHexAffine2 p.v p.c p.ε q‖ ≤ 1/4 := by
    intro q hq
    have ht : ‖equalAreaHexAffine2 p.v p.c p.ε q‖ ≤ ‖u‖+‖equalAreaHexAffine2 p.v p.c p.ε q-u‖ := by
      calc ‖equalAreaHexAffine2 p.v p.c p.ε q‖ =
          ‖u+(equalAreaHexAffine2 p.v p.c p.ε q-u)‖ := by congr 1; abel
        _ ≤ ‖u‖+‖equalAreaHexAffine2 p.v p.c p.ε q-u‖ := norm_add_le _ _
    have hd := hdist q hq
    rw [dist_eq_norm] at hd
    nlinarith
  have hSD : equalAreaHexAffine2 p.v p.c p.ε '' S ⊆ equalAreaChartDomainD := by
    rintro _ ⟨q,hq,rfl⟩
    exact equalAreaWideCube2_domain (hqnorm q hq)
  let E := equalAreaHexSpherePatch2 p.g p.v p.c p.ε S
  refine ⟨E,equalAreaHexSpherePatch2_measurable _ _ _ _ p.ε_pos S hSm hSD,?_,?_⟩
  · intro y hy
    obtain ⟨q,hq,hqy⟩ := hy
    change p.g (equalAreaPhiD (equalAreaHexAffine2 p.v p.c p.ε q)) = (y : AmbientD 2) at hqy
    refine ⟨?_,?_⟩
    · intro hyp
      obtain ⟨q',hq',hqy'⟩ := hyp
      change p.g (equalAreaPhiD (equalAreaHexAffine2 p.v p.c p.ε q')) = (y : AmbientD 2) at hqy'
      have hAq : equalAreaHexAffine2 p.v p.c p.ε q = equalAreaHexAffine2 p.v p.c p.ε q' :=
        equalAreaPhiD_injOn (hSD ⟨q,hq,rfl⟩)
          (equalAreaHexAffine2_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small ⟨q',hq',rfl⟩)
          (p.g.injective (hqy.trans hqy'.symm))
      have hqq' := equalAreaHexAffine2_injective p.v p.c p.ε p.ε_pos.ne' hAq
      exact hSout q hq (hqq' ▸ hq')
    · rw [mem_ball,Subtype.dist_eq,← hqy,hxu,p.g.dist_map]
      have hqB : equalAreaHexAffine2 p.v p.c p.ε q ∈ closedBall (0 : Fin 2 → ℝ) (1/4) := by
        simpa only [mem_closedBall,dist_zero_right] using hqnorm q hq
      have huB : u ∈ closedBall (0 : Fin 2 → ℝ) (1/4) := by
        simpa only [mem_closedBall,dist_zero_right] using hu.trans (by norm_num : (1/6:ℝ) ≤ 1/4)
      calc dist (equalAreaPhiD (equalAreaHexAffine2 p.v p.c p.ε q)) (equalAreaPhiD u)
          ≤ (L:ℝ)*dist (equalAreaHexAffine2 p.v p.c p.ε q) u := hLip.dist_le_mul _ hqB _ huB
        _ ≤ (L:ℝ)*(p.ε*B*a) := mul_le_mul_of_nonneg_left (hdist q hq) L.coe_nonneg
        _ = H/4 := by nlinarith [hcalc]
        _ < H := by linarith
  · rw [equalAreaHexSpherePatch2_probability_real p.g p.v p.c p.ε p.ε_pos S hSm hSD,
      Measure.real,hSv,ENNReal.toReal_ofReal (by positivity)]
    unfold equalAreaHexPatchProbabilityDensity2 hexResidualLocalMassConst2
    have hA := sphereAreaD_univ_pos 2
    dsimp [a,B]
    field_simp [hL0.ne',p.ε_pos.ne',hA.ne',hB.ne']
    ring

theorem sphereProbability2_real_eq_area (s : Set (SphereD 2)) :
    (sphereProbabilityD 2).real s = (sphereAreaD 2).real s/(sphereAreaD 2).real univ := by
  simp only [Measure.real,sphereProbabilityD,Measure.smul_apply,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  ring

theorem equalAreaPhiD2_zero : equalAreaPhiD (0 : Fin 2 → ℝ) = (northPole2 : AmbientD 2) := by
  have hinv : equalAreaInverseD (northPole2 : AmbientD 2) = 0 := by
    have h := congrArg (WithLp.ofLp) sphereEqualAreaCoordinates2_northPole
    simpa only [sphereEqualAreaCoordinates2,WithLp.ofLp_toLp,WithLp.ofLp_zero] using h
  have h := equalAreaPhiD_inverse8 northPole2 (by simp [northPole2])
  rwa [hinv] at h

theorem sphere2_ball_mass_lower2 {L : ℝ≥0} (hL : 1 ≤ L)
    (hLip : LipschitzOnWith L (equalAreaPhiD (n := 1))
      (closedBall (0 : Fin 2 → ℝ) (1/4:ℝ)))
    (x : SphereD 2) {H : ℝ} (hH : 0 < H) (hHsmall : H ≤ 1/12) :
    hexResidualLocalMassConst2 L*H^2 ≤ (sphereProbabilityD 2).real (ball x H) := by
  classical
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hA := sphereAreaD_univ_pos 2
  let a : ℝ := H/(4*(L:ℝ))
  have ha : 0 < a := div_pos hH (by positivity)
  have haSmall : a ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL]
  let S : Set (Fin 2 → ℝ) := Set.pi univ (fun _ => Ioo (-a) a)
  have hSm : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hSn : ∀ q ∈ S, ‖q‖ ≤ a := by
    intro q hq
    rw [pi_norm_le_iff_of_nonneg ha.le]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨(hq i (mem_univ i)).1.le,(hq i (mem_univ i)).2.le⟩
  have hSD : S ⊆ equalAreaChartDomainD := fun q hq =>
    equalAreaWideCube2_domain ((hSn q hq).trans haSmall)
  obtain ⟨g,hg⟩ := sphereRotation2_transitive northPole2 x
  have hSub : chartImage2 g S ⊆ ball x H := by
    rintro y ⟨q,hq,hyq⟩
    rw [mem_ball,Subtype.dist_eq,hyq,← hg]
    change dist (g (equalAreaPhiD q)) (g (northPole2 : AmbientD 2)) < H
    rw [g.dist_map,← equalAreaPhiD2_zero]
    have hqB : q ∈ closedBall (0 : Fin 2 → ℝ) (1/4) := by
      simpa only [mem_closedBall,dist_zero_right] using (hSn q hq).trans haSmall
    calc dist (equalAreaPhiD q) (equalAreaPhiD (0 : Fin 2 → ℝ))
        ≤ (L:ℝ)*dist q 0 := hLip.dist_le_mul _ hqB _ (mem_closedBall_self (by norm_num))
      _ ≤ (L:ℝ)*a := mul_le_mul_of_nonneg_left (by simpa using hSn q hq) L.coe_nonneg
      _ = H/4 := by dsimp [a]; field_simp
      _ < H := by linarith
  have hSv : volume S = ENNReal.ofReal ((2*a)^2) := by
    change volume (Set.pi univ (fun _ : Fin 2 => Ioo (-a) a)) = _
    rw [volume_pi_pi]
    simp only [Real.volume_Ioo,sub_neg_eq_add,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    ring
  have hMass : (sphereProbabilityD 2).real (chartImage2 g S) = (2*a)^2/(sphereAreaD 2).real univ := by
    rw [sphereProbability2_real_eq_area,Measure.real,chartImage2_area g hSm hSD,hSv,
      ENNReal.toReal_ofReal (by positivity)]
  have hB : 1 ≤ ‖hexMap‖+1 := by linarith [norm_nonneg hexMap]
  have hcoeff : hexResidualLocalMassConst2 L ≤ 1/(4*(L:ℝ)^2*(sphereAreaD 2).real univ) := by
    unfold hexResidualLocalMassConst2
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hBsq : 1 ≤ (‖hexMap‖+1)^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hBsq
      (show 0 ≤ 4*(L:ℝ)^2*(sphereAreaD 2).real univ by positivity)
    nlinarith
  calc hexResidualLocalMassConst2 L*H^2
      ≤ (1/(4*(L:ℝ)^2*(sphereAreaD 2).real univ))*H^2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _ = (sphereProbabilityD 2).real (chartImage2 g S) := by
        rw [hMass]
        dsimp [a]
        field_simp [hL0.ne',hA.ne']
        ring
    _ ≤ (sphereProbabilityD 2).real (ball x H) := measureReal_mono (μ := sphereProbabilityD 2) hSub

def hexPatchWideBuffer2 (p : SmallHexCubePatch2) : Set (SphereD 2) :=
  chartImage2 p.g (ball (0 : Fin 2 → ℝ) (1/6))

theorem hexPatchWideBuffer2_isOpen (p : SmallHexCubePatch2) : IsOpen (hexPatchWideBuffer2 p) := by
  apply chartImage2_isOpen p.g isOpen_ball
  intro q hq
  have hqn : ‖q‖ < 1/6 := by simpa only [mem_ball,dist_zero_right] using hq
  exact equalAreaWideCube2_domain (hqn.le.trans (by norm_num : (1/6:ℝ) ≤ 1/4))

theorem smallHexSpherePatch2_subset_wideBuffer (p : SmallHexCubePatch2) :
    smallHexSpherePatch2 p ⊆ hexPatchWideBuffer2 p := by
  intro x hx
  obtain ⟨w,hw,hwx⟩ := hx
  change p.g (equalAreaPhiD (equalAreaHexAffine2 p.v p.c p.ε w)) = (x : AmbientD 2) at hwx
  refine ⟨equalAreaHexAffine2 p.v p.c p.ε w,?_,hwx.symm⟩
  rw [mem_ball,dist_zero_right]
  have hnorm : ‖equalAreaHexAffine2 p.v p.c p.ε w‖ ≤ 1/8 := by
    have h := equalAreaMovingScaledHex_norm p.v p.ε (w-p.c) (unitCube2_sub_norm w p.c hw p.c_mem)
    exact h.trans (by simpa only [abs_of_pos p.ε_pos] using p.small)
  exact hnorm.trans_lt (by norm_num)

theorem hexResidual2_measurable {K : ℕ} (P : Fin K → SmallHexCubePatch2) :
    MeasurableSet ((hexFamilyUnion2 P)ᶜ) :=
  (MeasurableSet.iUnion fun i => smallHexSpherePatch2_measurable (P i)).compl

theorem exists_hex_residual_local_mass2 : ∃ C : ℝ, 0 < C ∧
    (∀ x : SphereD 2, ∀ H : ℝ, 0 < H → H ≤ 1/12 →
      C*H^2 ≤ (sphereProbabilityD 2).real (ball x H)) ∧
    ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i)) (smallHexSpherePatch2 (P j))) →
      ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ x ∈ hexResidualCarrier2 P, ∀ H : ℝ, 0 < H → H ≤ H₀ →
        C*H^2 ≤ (sphereProbabilityD 2).real ((hexFamilyUnion2 P)ᶜ ∩ ball x H) := by
  classical
  obtain ⟨L,hL,hLip⟩ := equalAreaWideCube2_lipschitz
  refine ⟨hexResidualLocalMassConst2 L,hexResidualLocalMassConst2_pos hL,
    fun x H hH hHsmall => sphere2_ball_mass_lower2 hL hLip x hH hHsmall,?_⟩
  intro K P hdisj
  obtain ⟨ρ,hρ,hbuffer,hthdisj⟩ := finite2_compact_chart_buffers8
    (fun i => smallHexSpherePatch2 (P i)) (fun i => hexPatchWideBuffer2 (P i))
    (fun i => smallHexSpherePatch2_isCompact (P i)) hdisj
    (fun i => hexPatchWideBuffer2_isOpen (P i)) (fun i => smallHexSpherePatch2_subset_wideBuffer (P i))
  refine ⟨min (1/12) (ρ/2),lt_min (by norm_num) (by positivity),?_⟩
  intro x hx H hH hH0
  have hHsmall : H ≤ 1/12 := hH0.trans (min_le_left _ _)
  have hHρ : H < ρ := lt_of_le_of_lt (hH0.trans (min_le_right _ _)) (by linarith)
  by_cases hhit : ∃ i, ∃ y ∈ smallHexSpherePatch2 (P i), dist x y < H
  · obtain ⟨i,y,hy,hxy⟩ := hhit
    have hxTh : x ∈ thickening ρ (smallHexSpherePatch2 (P i)) :=
      mem_thickening_iff.mpr ⟨y,hy,hxy.trans hHρ⟩
    obtain ⟨u,hu,hxu⟩ := (hbuffer i).2.2 hxTh
    have hun : ‖u‖ ≤ 1/6 := (show ‖u‖ < 1/6 by simpa only [mem_ball,dist_zero_right] using hu).le
    have hxout : x ∉ interior (smallHexSpherePatch2 (P i)) :=
      fun hxi => hx (mem_iUnion.mpr ⟨i,hxi⟩)
    obtain ⟨E,hEm,hES,hMass⟩ := exists_hex_patch_exterior_box2 hL hLip (P i) x u hun hxu hxout hH hHsmall
    have hER : E ⊆ (hexFamilyUnion2 P)ᶜ ∩ ball x H := by
      intro z hz
      refine ⟨?_,(hES hz).2⟩
      intro hzp
      obtain ⟨j,hzj⟩ := mem_iUnion.mp hzp
      by_cases hij : i = j
      · exact (hES hz).1 (hij ▸ hzj)
      · have hxThj : x ∈ thickening ρ (smallHexSpherePatch2 (P j)) := by
          refine mem_thickening_iff.mpr ⟨z,hzj,?_⟩
          rw [dist_comm]
          exact (hES hz).2.trans hHρ
        exact Set.disjoint_left.mp (hthdisj hij) hxTh hxThj
    rw [← hMass]
    exact measureReal_mono (μ := sphereProbabilityD 2) hER
  · have hball : ball x H ⊆ (hexFamilyUnion2 P)ᶜ := by
      intro z hz hzp
      obtain ⟨i,hzi⟩ := mem_iUnion.mp hzp
      exact hhit ⟨i,z,hzi,by simpa only [dist_comm] using (mem_ball.mp hz)⟩
    rw [inter_eq_right.mpr hball]
    exact sphere2_ball_mass_lower2 hL hLip x hH hHsmall

end SphericalRiesz
end
end

section

/-! Convert a uniform local mass lower bound into density-scale exact-mass cells on S². -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal
namespace SphericalRiesz

theorem sphereGaussianDensityFactor2_eq_quarter (N : ℕ) :
    sphereGaussianDensityFactor2 N = (N:ℝ)/4 := by
  rw [sphereGaussianDensityFactor2,sphereGaussianScale2_eq,sphereArea2_univ_real]
  have hπ := Real.pi_pos
  field_simp

theorem sphere2_cells_of_local_mass_lower {A R : Set (SphereD 2)}
    (hAc : IsCompact A) (hAconn : IsPreconnected A) (hRm : MeasurableSet R) (hRA : R ⊆ A)
    {C H₀ : ℝ} (hC : 0 < C) (hH₀ : 0 < H₀)
    (hlower : ∀ x ∈ A, ∀ H : ℝ, 0 < H → H ≤ H₀ →
      C*H^2 ≤ (sphereProbabilityD 2).real (R ∩ ball x H)) :
    ∃ N₀ : ℕ, ∀ N r : ℕ, N₀ ≤ N → 0 < r →
      (r:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real R →
      ∃ Q : Fin r → Set (SphereD 2), ∃ dm : Fin r → ℝ,
        (∀ j, MeasurableSet (Q j)) ∧ Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
        (⋃ j, Q j) = R ∧ (∀ j, (sphereProbabilityD 2).real (Q j) = 1/(N:ℝ)) ∧
        (∀ j, ∀ x ∈ Q j, ∀ y ∈ Q j, dist x y ≤ dm j) ∧
        ∑ j, sphereGaussianDensityFactor2 N*(dm j)^2 ≤ (162/C)*(r:ℝ) := by
  classical
  let N₀ : ℕ := ⌈2/(C*H₀^2)⌉₊+1
  refine ⟨N₀,?_⟩
  intro N r hN₀ hr hrN
  have hN : 0 < N := by dsimp [N₀] at hN₀; omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmass : (sphereProbabilityD 2).real R = (r:ℝ)*(1/(N:ℝ)) := by
    field_simp
    linarith
  have hRpos : 0 < (sphereProbabilityD 2).real R := by rw [hmass]; positivity
  have hRn : R.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn,measureReal_empty] at hRpos
    exact (lt_irrefl 0) hRpos
  have hAn : A.Nonempty := hRn.mono hRA
  have hNbound : 2/(C*H₀^2) ≤ (N:ℝ) := by
    have hceil := Nat.le_ceil (2/(C*H₀^2))
    have hnceil : ⌈2/(C*H₀^2)⌉₊ ≤ N := by dsimp [N₀] at hN₀; omega
    exact hceil.trans (by exact_mod_cast hnceil)
  let H : ℝ≥0 := ⟨Real.sqrt (2/(C*(N:ℝ))),Real.sqrt_nonneg _⟩
  have hH : 0 < H := Real.sqrt_pos.mpr (by positivity)
  have hHsq : (H:ℝ)^2 = 2/(C*(N:ℝ)) := Real.sq_sqrt (by positivity)
  have hHH₀ : (H:ℝ) ≤ H₀ := by
    have hnb : 2 ≤ (N:ℝ)*(C*H₀^2) := (div_le_iff₀ (by positivity)).mp hNbound
    have hsq : (H:ℝ)^2 ≤ H₀^2 := by
      rw [hHsq,div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith [H.coe_nonneg]
  have hCH : C*(H:ℝ)^2 = 2/(N:ℝ) := by
    rw [hHsq]
    field_simp
  have hball : ∀ x ∈ A, 1/(N:ℝ) < (sphereProbabilityD 2).real (R ∩ ball x H) := by
    intro x hx
    have hl := hlower x hx H hH hHH₀
    rw [hCH,show (2:ℝ)/(N:ℝ) = 2*(1/(N:ℝ)) by ring] at hl
    have hpos : (0:ℝ) < 1/(N:ℝ) := by positivity
    linarith
  obtain ⟨Q,hQm,hQd,hQu,hQmass,hQdiam⟩ := exists_exact_compact_metric_cells2
    (sphereProbabilityD 2) (f := fun x : SphereD 2 => (x : AmbientD 2) 0)
    (by fun_prop) sphere2_abs_first_coord_le_one sphereProbability2_coord_level_null
    hAc hAconn hAn hRm hRA hH (by positivity : (0:ℝ) < 1/(N:ℝ)) hball hmass
  refine ⟨Q,fun _ => 18*(H:ℝ),hQm,hQd,hQu,hQmass,hQdiam,?_⟩
  have hcost : sphereGaussianDensityFactor2 N*(18*(H:ℝ))^2 = 162/C := by
    rw [sphereGaussianDensityFactor2_eq_quarter,mul_pow,hHsq]
    field_simp
    ring
  simp only [hcost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact (mul_comm _ _).le

theorem sphereProbability2_eq_div_of_real {s R : Set (SphereD 2)} {N r : ℕ} (hN : 0 < N)
    (hr : 0 < r) (hrN : (r:ℝ) = N*(sphereProbabilityD 2).real R)
    (hs : (sphereProbabilityD 2).real s = 1/N) :
    (sphereProbabilityD 2) s = (sphereProbabilityD 2) R/(r:ℝ≥0∞) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hσR : 0 < (sphereProbabilityD 2).real R := by
    by_contra hle
    have h0 : (sphereProbabilityD 2).real R ≤ 0 := not_lt.mp hle
    nlinarith
  have hfin1 : (sphereProbabilityD 2) s ≠ ⊤ := measure_ne_top _ _
  have hfin2 : (sphereProbabilityD 2) R/(r:ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) (by exact_mod_cast hr.ne')
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2,ENNReal.toReal_div,ENNReal.toReal_natCast]
  change (sphereProbabilityD 2).real s = (sphereProbabilityD 2).real R/r
  rw [hs,hrN]
  field_simp

end SphericalRiesz
end
end

section

/-! Density-scale exact-mass stratifications of S² and complements of separated hexagonal
patches. This replaces the invalid dimension-24 grid carry-over argument in the old draft. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace SphericalRiesz

def SphereStratifiable2 (B : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ Q : Fin r → Set (SphereD 2), ∃ dm : Fin r → ℝ,
    (∀ j, MeasurableSet (Q j)) ∧ Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
    (⋃ j, Q j) = univ ∧
    (∀ j, sphereProbabilityD 2 (Q j) = sphereProbabilityD 2 univ/(r:ℝ≥0∞)) ∧
    (∀ j, ∀ x ∈ Q j, ∀ y ∈ Q j, dist x y ≤ dm j) ∧
    ∑ j, sphereGaussianDensityFactor2 r*(dm j)^2 ≤ B*r

def NegStratifiable2 (A : Set (SphereD 2)) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N r : ℕ, N₀ ≤ N → 0 < r →
    (r:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real A →
    ∃ Q : Fin r → Set (SphereD 2), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (Q j)) ∧ Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      (⋃ j, Q j) = A ∧
      (∀ j, sphereProbabilityD 2 (Q j) = sphereProbabilityD 2 A/(r:ℝ≥0∞)) ∧
      (∀ j, ∀ x ∈ Q j, ∀ y ∈ Q j, dist x y ≤ dm j) ∧
      ∑ j, sphereGaussianDensityFactor2 N*(dm j)^2 ≤ B*r+ε*N

theorem sphere2_dist_le_two_cells (x y : SphereD 2) : dist x y ≤ 2 := by
  calc dist x y = ‖(x : AmbientD 2)-(y : AmbientD 2)‖ := rfl
    _ ≤ ‖(x : AmbientD 2)‖+‖(y : AmbientD 2)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_of_mem_sphere x,norm_eq_of_mem_sphere y]; norm_num

theorem sphereProbability2_eq_inv_of_real {s : Set (SphereD 2)} {r : ℕ} (hr : 0 < r)
    (hs : (sphereProbabilityD 2).real s = 1/r) :
    (sphereProbabilityD 2) s = (sphereProbabilityD 2) univ/(r:ℝ≥0∞) := by
  rw [measure_univ,← ofReal_measureReal (measure_ne_top _ _),hs,one_div,one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hr),ENNReal.ofReal_natCast]

theorem sphere2_stratifiable : ∃ B : ℝ, 0 ≤ B ∧ SphereStratifiable2 B := by
  classical
  obtain ⟨C,hC,hBall,_⟩ := exists_hex_residual_local_mass2
  have hupper : ∀ x ∈ (univ : Set (SphereD 2)), ∀ H : ℝ, 0 < H → H ≤ 1/12 →
      C*H^2 ≤ (sphereProbabilityD 2).real (univ ∩ ball x H) := by
    intro x _ H hH hHsmall
    simpa only [univ_inter] using hBall x H hH hHsmall
  obtain ⟨N₀,hN₀⟩ := sphere2_cells_of_local_mass_lower (R := univ) isCompact_univ
    sphere2_univ_preconnected MeasurableSet.univ subset_rfl hC (by norm_num) hupper
  have hB : 0 ≤ 162/C := by positivity
  refine ⟨max (162/C) (N₀:ℝ),le_max_of_le_left hB,?_⟩
  intro r hr
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  by_cases hlarge : N₀ ≤ r
  · obtain ⟨Q,dm,hQm,hQd,hQu,hQmass,hQdiam,hQcost⟩ :=
      hN₀ r r hlarge hr (by simp only [probReal_univ,mul_one])
    exact ⟨Q,dm,hQm,hQd,hQu,fun j => sphereProbability2_eq_inv_of_real hr (hQmass j),
      hQdiam,hQcost.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrR.le)⟩
  · obtain ⟨Q,hQm,hQd,hQu,hQmass⟩ := exists_sphere2_equal_mass_cells hr hr
      MeasurableSet.univ (by rw [probReal_univ,div_self hrR.ne'])
    refine ⟨Q,fun _ => 2,hQm,hQd,hQu,?_,fun _ x _ y _ => sphere2_dist_le_two_cells x y,?_⟩
    · intro j
      simpa only [measure_univ,one_div] using hQmass j
    · simp only [sphereGaussianDensityFactor2_eq_quarter,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      have hrN : (r:ℝ) ≤ N₀ := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))
      have hNmax : (N₀:ℝ) ≤ max (162/C) (N₀:ℝ) := le_max_right _ _
      nlinarith

theorem NegStratifiable2.mono {A : Set (SphereD 2)} {B B' : ℝ} (h : NegStratifiable2 A B)
    (hB : B ≤ B') : NegStratifiable2 A B' := by
  intro ε hε
  obtain ⟨N₀,hN₀⟩ := h ε hε
  refine ⟨N₀,fun N r hN hr hrN => ?_⟩
  obtain ⟨Q,dm,h1,h2,h3,h4,h5,h6⟩ := hN₀ N r hN hr hrN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨Q,dm,h1,h2,h3,h4,h5,h6.trans (by nlinarith)⟩

theorem SphereStratifiable2.mono {B B' : ℝ} (h : SphereStratifiable2 B) (hB : B ≤ B') :
    SphereStratifiable2 B' := by
  intro r hr
  obtain ⟨Q,dm,h1,h2,h3,h4,h5,h6⟩ := h r hr
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨Q,dm,h1,h2,h3,h4,h5,h6.trans (by nlinarith)⟩

theorem sphere2_stratification_hypotheses : ∃ B : ℝ, 0 ≤ B ∧
    (∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i)) (smallHexSpherePatch2 (P j))) →
      NegStratifiable2 (hexFamilyUnion2 P)ᶜ B) ∧ SphereStratifiable2 B := by
  obtain ⟨C,hC,_,hLocal⟩ := exists_hex_residual_local_mass2
  obtain ⟨B₀,hB₀,hSphere⟩ := sphere2_stratifiable
  refine ⟨max (162/C) B₀,le_max_of_le_right hB₀,?_,hSphere.mono (le_max_right _ _)⟩
  intro K P hdisj ε hε
  obtain ⟨H₀,hH₀,hLower⟩ := hLocal P hdisj
  obtain ⟨N₀,hN₀⟩ := sphere2_cells_of_local_mass_lower
    (hexResidualCarrier2_isCompact P) (hexResidualCarrier2_preconnected P hdisj)
    (hexResidual2_measurable P) (hexResidual2_subset_carrier P) hC hH₀ hLower
  refine ⟨max 1 N₀,?_⟩
  intro N r hN hr hrN
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hN)
  obtain ⟨Q,dm,hQm,hQd,hQu,hQmass,hQdiam,hQcost⟩ :=
    hN₀ N r ((le_max_right _ _).trans hN) hr hrN
  refine ⟨Q,dm,hQm,hQd,hQu,fun j => sphereProbability2_eq_div_of_real hNpos hr hrN (hQmass j),hQdiam,?_⟩
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  exact hQcost.trans (by nlinarith [le_max_left (162/C) B₀])

end SphericalRiesz
end
end
