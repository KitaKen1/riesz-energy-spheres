import Riesz.CrossPatchKernel8
import Riesz.CurvedAnnularQuadrature8

/-! One-sided sixth-order quadrature for actual separated sphere patches.
The neutralized cross block is bounded by two norm-one averages of one row
error. This avoids differentiating an integral or requiring mixed derivatives
of total order twelve. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem rightSlice8_sixth_norm_le
    {F : ((Fin 8 → ℝ) × (Fin 8 → ℝ)) → ℝ} (x y : Fin 8 → ℝ)
    (hf : ContDiffAt ℝ 6 F (x,y)) :
    ‖iteratedFDeriv ℝ 6 (fun z => F (x,z)) y‖ ≤ ‖iteratedFDeriv ℝ 6 F (x,y)‖ := by
  let g : (Fin 8 → ℝ) →L[ℝ] ((Fin 8 → ℝ) × (Fin 8 → ℝ)) :=
    ContinuousLinearMap.inr ℝ (Fin 8 → ℝ) (Fin 8 → ℝ)
  let a : (Fin 8 → ℝ) × (Fin 8 → ℝ) := (x,0)
  let H : ((Fin 8 → ℝ) × (Fin 8 → ℝ)) → ℝ := fun z => F (z+a)
  have hepoint : g y+a = (x,y) := by ext <;> simp [g,a]
  have hH : ContDiffAt ℝ 6 H (g y) := by
    apply ContDiffAt.comp (g := F) (f := fun z => z+a) (g y)
    · rw [hepoint]; exact hf
    · fun_prop
  have heq : (fun z => F (x,z)) = H ∘ g := by
    funext z
    congr 1
    ext <;> simp [g,a]
  obtain ⟨U,hU,hgyU,hHU⟩ := hH.contDiffOn' le_rfl (by simp)
  have hHU' : ContDiffOn ℝ 6 H U := by simpa using hHU
  have hp : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hline := g.iteratedFDerivWithin_comp_right hHU' hU.uniqueDiffOn hp.uniqueDiffOn hgyU
    (i := 6) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 6 hp hgyU,
    iteratedFDerivWithin_of_isOpen 6 hU hgyU] at hline
  have hshift : iteratedFDeriv ℝ 6 H (g y) = iteratedFDeriv ℝ 6 F (x,y) := by
    dsimp only [H]
    rw [iteratedFDeriv_comp_add_right,hepoint]
  rw [heq,hline,hshift]
  have hn : ‖g‖ = 1 := ContinuousLinearMap.norm_inr ℝ (Fin 8 → ℝ) (Fin 8 → ℝ)
  simpa only [hn,Finset.prod_const_one,mul_one] using
    (iteratedFDeriv ℝ 6 F (x,y)).norm_compContinuousLinearMap_le (fun _ => g)

theorem smallE8CrossKernel8_row_contDiffAt (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    ContDiffAt ℝ ∞ (fun z => smallE8CrossKernel8 p q (x,z)) y :=
  (smallE8CrossKernel8_contDiffAt p q hd (x,y) ⟨hx,hy⟩).comp y (by fun_prop)

theorem smallE8CrossKernel8_row_quadrature_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ x ∈ UnitCube 8,
      |cubeQuadrature 8 m (fun y => smallE8CrossKernel8 p q (x,y))-
        cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))| ≤ C/(m:ℝ)^6 := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossKernel8_joint_sixth_bound p q hd
  refine ⟨512*C,by positivity,?_⟩
  intro m hm x hx
  let f : (Fin 8 → ℝ) → ℝ := fun y => smallE8CrossKernel8 p q (x,y)
  have hloc : ∀ y ∈ UnitCube 8, ContDiffAt ℝ 6 f y :=
    fun y hy => (smallE8CrossKernel8_row_contDiffAt p q hd x y hx hy).of_le (by simp)
  have hs : ∀ i v, v ∈ UnitCube 8 →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Icc (0:ℝ) 1) := by
    intro i v hv t ht
    have hu : ContDiffAt ℝ 6 (fun u : ℝ => Function.update v i u) t := by
      rw [show (fun u : ℝ => Function.update v i u) =
        (fun u => ContinuousLinearMap.single ℝ (fun _ : Fin 8 => ℝ) i u+Function.update v i 0)
        from funext (coordinate_update_as_line 8 i v)]
      fun_prop
    exact ((hloc _ (update_mem_unitCube hv i ht)).comp t hu).contDiffWithinAt
  have hbound : ∀ i v, v ∈ UnitCube 8 → ∀ t ∈ Icc (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤ C := by
    intro i v hv t ht
    have hy := update_mem_unitCube hv i ht
    exact (sixth_coordinate_within_abs_le_of_contDiffAt 8 i v t ht (hloc _ hy)).trans
      ((rightSlice8_sixth_norm_le x (Function.update v i t)
        ((smallE8CrossKernel8_contDiffAt p q hd _ ⟨hx,hy⟩).of_le (by simp))).trans
          (hb _ ⟨hx,hy⟩))
  have h := cubeQuadrature_sixth_order_bound_on 8 hm
    (fun y hy => (hloc y hy).continuousAt.continuousWithinAt) hs (fun _ => C) hbound
  calc
    |cubeQuadrature 8 m f-cubeIntegral 8 f| ≤ (64/(m:ℝ)^6)*(∑ _ : Fin 8, C) := h
    _ = (512*C)/(m:ℝ)^6 := by simp; ring

def smallE8CrossRowError8 (p q : SmallE8CubePatch8) (m : ℕ) (x : Fin 8 → ℝ) : ℝ :=
  cubeQuadrature 8 m (fun y => smallE8CrossKernel8 p q (x,y))-
    cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))

def smallE8CrossNeutralized8 (p q : SmallE8CubePatch8) (m : ℕ) : ℝ :=
  cubeQuadrature 8 m (smallE8CrossRowError8 p q m)-
    cubeIntegral 8 (smallE8CrossRowError8 p q m)

theorem smallE8CrossNeutralized8_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m →
      |smallE8CrossNeutralized8 p q m| ≤ C/(m:ℝ)^6 := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossKernel8_row_quadrature_bound p q hd
  refine ⟨2*C,by positivity,?_⟩
  intro m hm
  have hrow : ∀ x ∈ UnitCube 8, |smallE8CrossRowError8 p q m x| ≤ C/(m:ℝ)^6 := hb m hm
  calc
    |smallE8CrossNeutralized8 p q m| ≤
        |cubeQuadrature 8 m (smallE8CrossRowError8 p q m)|+
        |cubeIntegral 8 (smallE8CrossRowError8 p q m)| := abs_sub _ _
    _ ≤ C/(m:ℝ)^6+C/(m:ℝ)^6 := add_le_add
      (cubeQuadrature_abs_le 8 m hm _ _ hrow) (cubeIntegral_abs_le 8 _ _ hrow)
    _ = (2*C)/(m:ℝ)^6 := by ring

end SphericalRiesz
