import Riesz.CurvedNearComparison
import Riesz.SphereValue8
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# An explicit small spherical graph over the unchanged E8 coordinates

The actual spherical point is (sqrt(1-ε²|Ax|²), ε Ax). After translating
the pole and dividing by ε its horizontal part is exactly Ax. Its relative
chordal-distance error on the original unit cube is at most 4(ε M)².
Only square identities and norm bounds are used for this estimate.
This graph is smooth near the cube, but its surface Jacobian is NOT one;
it does not yet supply the exact-area charts needed by spherical recovery.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def e8GraphRadius : ℝ := 1+‖e8CoordinateLinearEquiv.toContinuousLinearMap‖

theorem e8GraphRadius_pos : 0 < e8GraphRadius := by
  unfold e8GraphRadius
  positivity

theorem e8Graph_cube_norm_bound (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    ‖e8CoordinateLinearEquiv x‖ ≤ e8GraphRadius := by
  calc
    _ ≤ ‖e8CoordinateLinearEquiv.toContinuousLinearMap‖*‖x‖ :=
      e8CoordinateLinearEquiv.toContinuousLinearMap.le_opNorm x
    _ ≤ ‖e8CoordinateLinearEquiv.toContinuousLinearMap‖*1 := by
      gcongr
      exact unitCube_norm_le_one 8 x hx
    _ ≤ e8GraphRadius := by unfold e8GraphRadius; linarith

def e8GraphHeight (ε : ℝ) (x : Fin 8 → ℝ) : ℝ :=
  Real.sqrt (1-ε^2*‖e8CoordinateLinearEquiv x‖^2)

def e8SphereGraph (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  ambientCons9 (e8GraphHeight ε x, ε • e8Map x)

def e8NormalizedSphereGraph (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  ambientCons9 ((e8GraphHeight ε x-1)/ε, e8Map x)

theorem ambientCons9_dist_sq (p q : ℝ × (Fin 8 → ℝ)) :
    dist (ambientCons9 p) (ambientCons9 q)^2 =
      (p.1-q.1)^2+dist (WithLp.toLp 2 p.2 : PoleTransverse8) (WithLp.toLp 2 q.2)^2 := by
  have he : ambientCons9 p-ambientCons9 q = ambientCons9 (p.1-q.1,p.2-q.2) := by
    rw [ambientCons9_apply,ambientCons9_apply,ambientCons9_apply,← WithLp.toLp_sub]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [dist_eq_norm,he,ambientCons9_norm_sq,dist_eq_norm,← WithLp.toLp_sub]

theorem e8Graph_radicand_lower (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    3/4 ≤ 1-ε^2*‖e8CoordinateLinearEquiv x‖^2 := by
  have h := mul_le_mul_of_nonneg_left (e8Graph_cube_norm_bound x hx) hε
  have hn := norm_nonneg (e8CoordinateLinearEquiv x)
  nlinarith [mul_nonneg hε hn, sq_nonneg (ε*‖e8CoordinateLinearEquiv x‖)]

theorem e8GraphHeight_lower (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    1/2 ≤ e8GraphHeight ε x := by
  have hr := e8Graph_radicand_lower ε hε hsmall x hx
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-ε^2*‖e8CoordinateLinearEquiv x‖^2)
  have hn := Real.sqrt_nonneg (1-ε^2*‖e8CoordinateLinearEquiv x‖^2)
  unfold e8GraphHeight
  nlinarith

theorem e8SphereGraph_mem_sphere (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    e8SphereGraph ε x ∈ Metric.sphere (0 : Ambient9) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hr := e8Graph_radicand_lower ε hε hsmall x hx
  have hs : ‖e8SphereGraph ε x‖^2 = 1 := by
    rw [e8SphereGraph,ambientCons9_norm_sq,WithLp.toLp_smul,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg hε,mul_pow,e8GraphHeight,
      Real.sq_sqrt (by linarith : 0 ≤ 1-ε^2*‖e8CoordinateLinearEquiv x‖^2)]
    change 1-ε^2*‖e8CoordinateLinearEquiv x‖^2+
      ε^2*‖e8CoordinateLinearEquiv x‖^2 = 1
    ring
  nlinarith [norm_nonneg (e8SphereGraph ε x)]

theorem e8GraphHeight_continuous (ε : ℝ) : Continuous (e8GraphHeight ε) := by
  unfold e8GraphHeight
  fun_prop

theorem e8NormalizedSphereGraph_continuous (ε : ℝ) :
    Continuous (e8NormalizedSphereGraph ε) := by
  have hh := e8GraphHeight_continuous ε
  have hA := e8Map.continuous
  unfold e8NormalizedSphereGraph
  simp_rw [ambientCons9_apply]
  fun_prop

theorem e8GraphHeight_difference (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x y : Fin 8 → ℝ)
    (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    |e8GraphHeight ε x-e8GraphHeight ε y| ≤
      2*ε^2*e8GraphRadius*dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y) := by
  have hrx := e8Graph_radicand_lower ε hε hsmall x hx
  have hry := e8Graph_radicand_lower ε hε hsmall y hy
  have hsx : (e8GraphHeight ε x)^2 = 1-ε^2*‖e8CoordinateLinearEquiv x‖^2 :=
    Real.sq_sqrt (by linarith)
  have hsy : (e8GraphHeight ε y)^2 = 1-ε^2*‖e8CoordinateLinearEquiv y‖^2 :=
    Real.sq_sqrt (by linarith)
  have hlx := e8GraphHeight_lower ε hε hsmall x hx
  have hly := e8GraphHeight_lower ε hε hsmall y hy
  have he : |e8GraphHeight ε x-e8GraphHeight ε y| *
      (e8GraphHeight ε x+e8GraphHeight ε y) =
      ε^2*|‖e8CoordinateLinearEquiv x‖^2-‖e8CoordinateLinearEquiv y‖^2| := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ e8GraphHeight ε x+e8GraphHeight ε y),
      ← abs_mul,show (e8GraphHeight ε x-e8GraphHeight ε y)*
        (e8GraphHeight ε x+e8GraphHeight ε y) =
        -ε^2*(‖e8CoordinateLinearEquiv x‖^2-‖e8CoordinateLinearEquiv y‖^2) by nlinarith,
      abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ε)]
  have hnorm : |‖e8CoordinateLinearEquiv x‖^2-‖e8CoordinateLinearEquiv y‖^2| ≤
      2*e8GraphRadius*dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y) := by
    have hb := abs_norm_sub_norm_le (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)
    rw [← dist_eq_norm] at hb
    rw [show ‖e8CoordinateLinearEquiv x‖^2-‖e8CoordinateLinearEquiv y‖^2 =
        (‖e8CoordinateLinearEquiv x‖-‖e8CoordinateLinearEquiv y‖)*
        (‖e8CoordinateLinearEquiv x‖+‖e8CoordinateLinearEquiv y‖) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hh := add_le_add (e8Graph_cube_norm_bound x hx) (e8Graph_cube_norm_bound y hy)
    calc
      _ ≤ dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)*(2*e8GraphRadius) := by
        gcongr
        linarith
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hnorm (sq_nonneg ε)
  have ht := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ e8GraphHeight ε x+e8GraphHeight ε y)
    (abs_nonneg (e8GraphHeight ε x-e8GraphHeight ε y))
  rw [he] at ht
  nlinarith

theorem e8NormalizedSphereGraph_relative_distance (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x y : Fin 8 → ℝ)
    (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    |dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y)-
      dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)| ≤
      4*(ε*e8GraphRadius)^2*dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y) := by
  let a := dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)
  let b := dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y)
  let z := (e8GraphHeight ε x-e8GraphHeight ε y)/ε
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hs : b^2 = z^2+a^2 := by
    dsimp only [b,a,e8NormalizedSphereGraph]
    rw [ambientCons9_dist_sq]
    change ((e8GraphHeight ε x-1)/ε-(e8GraphHeight ε y-1)/ε)^2+_ = _
    dsimp only [z]
    congr 1
    ring
  have hz : |z| ≤ 2*ε*e8GraphRadius*a := by
    dsimp only [z]
    rw [abs_div,abs_of_pos hε]
    apply (div_le_iff₀ hε).mpr
    have h := e8GraphHeight_difference ε hε.le hsmall x y hx hy
    dsimp only [a]
    nlinarith
  have hab : a ≤ b := by nlinarith [sq_nonneg z]
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  by_cases ha0 : a = 0
  · have hz0 : z = 0 := abs_eq_zero.mp (le_antisymm (by simpa [ha0] using hz) (abs_nonneg z))
    have hb0 : b = 0 := by nlinarith [hs]
    change b-a ≤ 4*(ε*e8GraphRadius)^2*a
    simp [ha0,hb0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hzsq : z^2 ≤ (2*ε*e8GraphRadius*a)^2 := by
    nlinarith [sq_abs z,abs_nonneg z,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε.le) e8GraphRadius_pos.le) ha]
  have hprod : a*(b-a) ≤ 4*(ε*e8GraphRadius)^2*a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hb]
  nlinarith

theorem e8NormalizedSphereGraph_dist_lower (ε : ℝ) (x y : Fin 8 → ℝ) :
    dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y) ≤
      dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y) := by
  have hs := ambientCons9_dist_sq
    ((e8GraphHeight ε x-1)/ε,e8Map x) ((e8GraphHeight ε y-1)/ε,e8Map y)
  change dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y)^2 =
    _+dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)^2 at hs
  nlinarith [sq_nonneg ((e8GraphHeight ε x-1)/ε-(e8GraphHeight ε y-1)/ε),
    (dist_nonneg : 0 ≤ dist (e8CoordinateLinearEquiv x) (e8CoordinateLinearEquiv y)),
    (dist_nonneg : 0 ≤ dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y))]

theorem e8NormalizedSphereGraph_smul_sub (ε : ℝ) (x y : Fin 8 → ℝ) (hε : ε ≠ 0) :
    ε • (e8NormalizedSphereGraph ε x-e8NormalizedSphereGraph ε y) =
      e8SphereGraph ε x-e8SphereGraph ε y := by
  simp only [e8NormalizedSphereGraph,e8SphereGraph,ambientCons9_apply,
    ← WithLp.toLp_sub,← WithLp.toLp_smul]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Pi.smul_apply,Pi.sub_apply,Fin.cons_zero,smul_eq_mul]
    field_simp
    ring
  · simp
    ring

theorem e8SphereGraph_scaled_distance (ε : ℝ) (hε : 0 < ε) (x y : Fin 8 → ℝ) :
    dist (e8SphereGraph ε x) (e8SphereGraph ε y) =
      ε*dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y) := by
  simp only [dist_eq_norm]
  rw [← e8NormalizedSphereGraph_smul_sub ε x y hε.ne',norm_smul,
    Real.norm_eq_abs,abs_of_pos hε]

theorem e8SphereGraph_injective (ε : ℝ) (hε : 0 < ε) : Function.Injective (e8SphereGraph ε) := by
  intro x y hxy
  have hz : dist (e8NormalizedSphereGraph ε x) (e8NormalizedSphereGraph ε y) = 0 := by
    have h := e8SphereGraph_scaled_distance ε hε x y
    rw [hxy,dist_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hε.ne'
  have ha := e8NormalizedSphereGraph_dist_lower ε x y
  rw [hz] at ha
  exact e8CoordinateLinearEquiv.injective (dist_eq_zero.mp (le_antisymm ha dist_nonneg))

theorem e8GraphHeight_contDiffOn (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) : ContDiffOn ℝ ∞ (e8GraphHeight ε) (UnitCube 8) := by
  have hn : ContDiff ℝ ∞ (fun x => ‖e8CoordinateLinearEquiv x‖^2) :=
    e8CoordinateLinearEquiv.contDiff.norm_sq (𝕜 := ℝ)
  apply (contDiff_const.sub (contDiff_const.mul hn)).contDiffOn.sqrt
  intro x hx
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/4)
    (e8Graph_radicand_lower ε hε hsmall x hx))

theorem e8NormalizedSphereGraph_contDiffOn (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) :
    ContDiffOn ℝ ∞ (e8NormalizedSphereGraph ε) (UnitCube 8) := by
  have hh : ContDiffOn ℝ ∞ (fun x => (e8GraphHeight ε x-1)/ε) (UnitCube 8) :=
    ((e8GraphHeight_contDiffOn ε hε hsmall).sub contDiffOn_const).div_const ε
  have hA : ContDiffOn ℝ ∞ e8Map (UnitCube 8) := e8Map.contDiff.contDiffOn
  unfold e8NormalizedSphereGraph
  simp_rw [ambientCons9_apply]
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using hh
  · simpa only [Fin.cons_succ] using (contDiffOn_pi.mp hA j)

def e8SphereGraphCubeEmbedding (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) : (UnitCube 8) ↪ Sphere8 where
  toFun x := ⟨e8SphereGraph ε x, e8SphereGraph_mem_sphere ε hε.le hsmall x x.property⟩
  inj' := fun _ _ h => Subtype.ext (e8SphereGraph_injective ε hε (congrArg Subtype.val h))

def e8SphereGraphNodeEmbedding (m : ℕ) (hm : 8 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) : (Fin 8 → NodeIndex m) ↪ Sphere8 where
  toFun w := ⟨e8SphereGraph ε (cubeNode 8 m w),
    e8SphereGraph_mem_sphere ε hε.le hsmall _
      (fun i => ⟨(cubeNode_mem_open 8 m hm w i).1.le,(cubeNode_mem_open 8 m hm w i).2.le⟩)⟩
  inj' := fun _ _ h => cubeNode_injective 8 m hm
    (e8SphereGraph_injective ε hε (congrArg Subtype.val h))

theorem e8SphereGraphNode_separated (m : ℕ) (hm : 8 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (v w : Fin 8 → NodeIndex m) (hvw : v ≠ w) :
    ε*e8SeparationConstant/(m:ℝ) <
      dist (e8SphereGraphNodeEmbedding m hm ε hε hsmall v)
        (e8SphereGraphNodeEmbedding m hm ε hε hsmall w) := by
  change ε*e8SeparationConstant/(m:ℝ) <
    dist (e8SphereGraph ε (cubeNode 8 m v)) (e8SphereGraph ε (cubeNode 8 m w))
  rw [e8SphereGraph_scaled_distance ε hε]
  have h := (e8TensorNode_dist_separated hm v w hvw).trans_le
    (e8NormalizedSphereGraph_dist_lower ε (cubeNode 8 m v) (cubeNode 8 m w))
  simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left h hε

theorem e8SphereGraph_near_background_error (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/4) (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 8 ≤ m) :
    |(m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)) x)-
      (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))| ≤
      512*(ε*e8GraphRadius)^2*e8NearIntegralConstant*R^4 := by
  have he : 0 ≤ ε*e8GraphRadius := mul_nonneg hε.le e8GraphRadius_pos.le
  have hη : 4*(ε*e8GraphRadius)^2 ≤ (1:ℝ)/2 := by nlinarith
  have h := curvedNearPotential_scaled_background_error (e8NormalizedSphereGraph ε)
    (e8NormalizedSphereGraph_continuous ε).measurable R hR (4*(ε*e8GraphRadius)^2)
    (by positivity) hη (fun x hx y hy =>
      e8NormalizedSphereGraph_relative_distance ε hε (by linarith) x y hx hy) m hm
  convert h using 1
  ring

-- Rationalizing the square root removes the apparent singularity at ε=0.
def e8SmoothGraphHeight (ε : ℝ) (x : Fin 8 → ℝ) : ℝ :=
  -ε*‖e8CoordinateLinearEquiv x‖^2/(1+e8GraphHeight ε x)

def e8SmoothNormalizedSphereGraph (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  ambientCons9 (e8SmoothGraphHeight ε x,e8Map x)

theorem e8SmoothGraphHeight_eq (ε : ℝ) (hε : ε ≠ 0) (x : Fin 8 → ℝ)
    (hr : 0 ≤ 1-ε^2*‖e8CoordinateLinearEquiv x‖^2) :
    e8SmoothGraphHeight ε x = (e8GraphHeight ε x-1)/ε := by
  have hs : (e8GraphHeight ε x)^2 = 1-ε^2*‖e8CoordinateLinearEquiv x‖^2 := Real.sq_sqrt hr
  have hp : 0 < 1+e8GraphHeight ε x := by
    have hn := Real.sqrt_nonneg (1-ε^2*‖e8CoordinateLinearEquiv x‖^2)
    change 0 < 1+Real.sqrt _
    linarith
  unfold e8SmoothGraphHeight
  apply (div_eq_div_iff hp.ne' hε).mpr
  nlinarith

theorem e8SmoothNormalizedSphereGraph_eq (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    e8SmoothNormalizedSphereGraph ε x = e8NormalizedSphereGraph ε x := by
  unfold e8SmoothNormalizedSphereGraph e8NormalizedSphereGraph
  rw [e8SmoothGraphHeight_eq ε hε.ne' x
    (le_trans (by norm_num : (0:ℝ) ≤ 3/4) (e8Graph_radicand_lower ε hε.le hsmall x hx))]

theorem e8SmoothNormalizedSphereGraph_zero (x : Fin 8 → ℝ) :
    e8SmoothNormalizedSphereGraph 0 x = ambientCons9 (0,e8Map x) := by
  simp [e8SmoothNormalizedSphereGraph,e8SmoothGraphHeight]

theorem e8SmoothNormalizedSphereGraph_continuous :
    Continuous (fun p : ℝ × (Fin 8 → ℝ) => e8SmoothNormalizedSphereGraph p.1 p.2) := by
  have hh : Continuous (fun p : ℝ × (Fin 8 → ℝ) => e8GraphHeight p.1 p.2) := by
    unfold e8GraphHeight
    fun_prop
  have hn : ∀ p : ℝ × (Fin 8 → ℝ), 1+e8GraphHeight p.1 p.2 ≠ 0 := by
    intro p
    have hp := Real.sqrt_nonneg (1-p.1^2*‖e8CoordinateLinearEquiv p.2‖^2)
    change 1+Real.sqrt _ ≠ 0
    linarith
  unfold e8SmoothNormalizedSphereGraph e8SmoothGraphHeight
  simp_rw [ambientCons9_apply]
  fun_prop

theorem e8SmoothNormalizedSphereGraph_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 8 → ℝ) => e8SmoothNormalizedSphereGraph p.1 p.2)
      {p | p.1^2*‖e8CoordinateLinearEquiv p.2‖^2 < 1} := by
  intro p hp
  change p.1^2*‖e8CoordinateLinearEquiv p.2‖^2 < 1 at hp
  apply ContDiffAt.contDiffWithinAt
  have hA : ContDiff ℝ ∞ (fun q : ℝ × (Fin 8 → ℝ) => e8CoordinateLinearEquiv q.2) := by
    fun_prop
  have hh : ContDiffAt ℝ ∞ (fun q : ℝ × (Fin 8 → ℝ) => e8GraphHeight q.1 q.2) p := by
    apply (contDiffAt_const.sub ((contDiffAt_fst.pow 2).mul (hA.norm_sq (𝕜 := ℝ)).contDiffAt)).sqrt
    exact ne_of_gt (by linarith : 0 < 1-p.1^2*‖e8CoordinateLinearEquiv p.2‖^2)
  have hn : 1+e8GraphHeight p.1 p.2 ≠ 0 := by
    have hs := Real.sqrt_nonneg (1-p.1^2*‖e8CoordinateLinearEquiv p.2‖^2)
    change 1+Real.sqrt _ ≠ 0
    linarith
  have hheight : ContDiffAt ℝ ∞ (fun q : ℝ × (Fin 8 → ℝ) => e8SmoothGraphHeight q.1 q.2) p :=
    ((contDiffAt_fst.neg.mul (hA.norm_sq (𝕜 := ℝ)).contDiffAt).div (contDiffAt_const.add hh) hn)
  unfold e8SmoothNormalizedSphereGraph
  simp_rw [ambientCons9_apply]
  apply PiLp.contDiff_toLp.contDiffAt.comp p
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using hheight
  · simp only [Fin.cons_succ]
    fun_prop

end SphericalRiesz
