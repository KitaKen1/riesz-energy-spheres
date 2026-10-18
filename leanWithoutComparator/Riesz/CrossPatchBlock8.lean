import Riesz.CrossPatchQuadrature8
import Riesz.E8PotentialAveraging

/-! The actual four-term coordinate block and its original finite nodes.
Compact cube extensions justify linearity of the background integrals only;
the kernel and quadrature points in the conclusions remain the actual ones. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem cubeIntegral_sub_on8 {f g : (Fin 8 → ℝ) → ℝ}
    (hf : ContinuousOn f (UnitCube 8)) (hg : ContinuousOn g (UnitCube 8)) :
    cubeIntegral 8 (fun x => f x-g x) = cubeIntegral 8 f-cubeIntegral 8 g := by
  let F := fun x => f (cubeClamp 8 x)
  let G := fun x => g (cubeClamp 8 x)
  have heF : EqOn F f (UnitCube 8) := fun x hx => by dsimp [F]; rw [cubeClamp_eq hx]
  have heG : EqOn G g (UnitCube 8) := fun x hx => by dsimp [G]; rw [cubeClamp_eq hx]
  calc
    cubeIntegral 8 (fun x => f x-g x) = cubeIntegral 8 (fun x => F x-G x) :=
      cubeIntegral_congr 8 (fun x hx => by rw [heF hx,heG hx])
    _ = cubeIntegral 8 F-cubeIntegral 8 G :=
      cubeIntegral_sub 8 F G (continuous_cube_extension hf) (continuous_cube_extension hg)
    _ = cubeIntegral 8 f-cubeIntegral 8 g := by
      rw [cubeIntegral_congr 8 heF,cubeIntegral_congr 8 heG]

def smallE8CrossExtension8 (p q : SmallE8CubePatch8)
    (z : (Fin 8 → ℝ) × (Fin 8 → ℝ)) : ℝ :=
  smallE8CrossKernel8 p q (cubeClamp 8 z.1,cubeClamp 8 z.2)

theorem smallE8CrossExtension8_continuous (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    Continuous (smallE8CrossExtension8 p q) :=
  (smallE8CrossKernel8_continuousOn p q hd).comp_continuous
    (((continuous_cubeClamp 8).comp continuous_fst).prodMk
      ((continuous_cubeClamp 8).comp continuous_snd))
    (fun _ => ⟨cubeClamp_mem 8 _,cubeClamp_mem 8 _⟩)

theorem smallE8CrossExtension8_eq (p q : SmallE8CubePatch8)
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    smallE8CrossExtension8 p q (x,y) = smallE8CrossKernel8 p q (x,y) := by
  simp only [smallE8CrossExtension8,cubeClamp_eq hx,cubeClamp_eq hy]

theorem smallE8CrossQuadratureRow8_continuousOn (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) (m : ℕ) (hm : 8 ≤ m) :
    ContinuousOn (fun x => cubeQuadrature 8 m (fun y => smallE8CrossKernel8 p q (x,y)))
      (UnitCube 8) := by
  have hc := cubeQuadrature_continuous_parameter 8 m
    ((smallE8CrossExtension8_continuous p q hd).comp (by fun_prop : Continuous Prod.swap))
  apply hc.continuousOn.congr
  intro x hx
  apply cubeQuadrature_congr 8 m hm
  intro y hy
  exact (smallE8CrossExtension8_eq p q x y hx hy).symm

theorem smallE8CrossIntegralRow8_continuousOn (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ContinuousOn (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)))
      (UnitCube 8) := by
  have hc := continuous_cubeIntegral_param 8
    (F := fun x y => smallE8CrossExtension8 p q (x,y)) (smallE8CrossExtension8_continuous p q hd)
  apply hc.continuousOn.congr
  intro x hx
  apply cubeIntegral_congr 8
  intro y hy
  exact (smallE8CrossExtension8_eq p q x y hx hy).symm

theorem smallE8CrossNeutralized8_four_terms (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) (m : ℕ) (hm : 8 ≤ m) :
    smallE8CrossNeutralized8 p q m =
      cubeQuadrature 8 m (fun x => cubeQuadrature 8 m (fun y => smallE8CrossKernel8 p q (x,y)))-
      cubeQuadrature 8 m (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)))-
      cubeIntegral 8 (fun x => cubeQuadrature 8 m (fun y => smallE8CrossKernel8 p q (x,y)))+
      cubeIntegral 8 (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))) := by
  unfold smallE8CrossNeutralized8 smallE8CrossRowError8
  rw [cubeQuadrature_sub,cubeIntegral_sub_on8
    (smallE8CrossQuadratureRow8_continuousOn p q hd m hm)
    (smallE8CrossIntegralRow8_continuousOn p q hd)]
  ring

theorem smallE8CrossNeutralized8_node_sum (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) (m : ℕ) (hm : 8 ≤ m) :
    smallE8CrossNeutralized8 p q m =
      (∑ a : Fin 8 → NodeIndex m, ∑ b : Fin 8 → NodeIndex m,
        smallE8CrossKernel8 p q (cubeNode 8 m a,cubeNode 8 m b))/(m:ℝ)^16-
      (∑ a : Fin 8 → NodeIndex m, cubeIntegral 8
        (fun y => smallE8CrossKernel8 p q (cubeNode 8 m a,y)))/(m:ℝ)^8-
      cubeIntegral 8 (fun x => (∑ b : Fin 8 → NodeIndex m,
        smallE8CrossKernel8 p q (x,cubeNode 8 m b))/(m:ℝ)^8)+
      cubeIntegral 8 (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))) := by
  rw [smallE8CrossNeutralized8_four_terms p q hd m hm]
  simp_rw [cubeQuadrature_as_node_sum]
  rw [← Finset.sum_div,div_div,← pow_add]

-- n^8 original nodes in each block. The unnormalized error is O(n^10).
def smallE8CrossWeightedBlock8 (p q : SmallE8CubePatch8) (n : ℕ) : ℝ :=
  (n:ℝ)^16*smallE8CrossNeutralized8 p q n

theorem smallE8CrossWeightedBlock8_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n → |smallE8CrossWeightedBlock8 p q n| ≤ C*(n:ℝ)^10 := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossNeutralized8_bound p q hd
  refine ⟨C,hC,?_⟩
  intro n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    |smallE8CrossWeightedBlock8 p q n| = (n:ℝ)^16*|smallE8CrossNeutralized8 p q n| := by
      rw [smallE8CrossWeightedBlock8,abs_mul,abs_of_nonneg (by positivity)]
    _ ≤ (n:ℝ)^16*(C/(n:ℝ)^6) := mul_le_mul_of_nonneg_left (hb n hn) (by positivity)
    _ = C*(n:ℝ)^10 := by field_simp [hn0]

/-- A small abstract sequence avoids unfolding a large physical kernel during
asymptotic arithmetic. The supplied bound is discharged by the concrete theorem. -/
theorem nat_power12_normalized_zero_of_power10_bound {F : ℕ → ℝ}
    (d : ℕ) (hd : 0 < d) (C : ℝ)
    (hF : ∀ n : ℕ, 8 ≤ n → |F n| ≤ C*(n:ℝ)^10) :
    Tendsto (fun n : ℕ => F n/((d*n:ℕ):ℝ)^12) atTop (nhds 0) := by
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have ht : Tendsto (fun n : ℕ => (C/(d:ℝ)^12)/(n:ℝ)^2) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).pow 2
    simpa only [div_pow,one_pow,mul_one_div,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero]
      using h.const_mul (C/(d:ℝ)^12)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop 8] with n hn
  have hnz : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have habs : |((d*n:ℕ):ℝ)^12| = ((d*n:ℕ):ℝ)^12 :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (d*n)) 12)
  rw [abs_div,habs]
  calc
    |F n|/((d*n:ℕ):ℝ)^12 ≤ C*(n:ℝ)^10/((d*n:ℕ):ℝ)^12 :=
      div_le_div_of_nonneg_right (hF n hn) (by positivity)
    _ = (C/(d:ℝ)^12)/(n:ℝ)^2 := by rw [Nat.cast_mul,mul_pow]; field_simp [hdz,hnz]

theorem smallE8CrossWeightedBlock8_normalized_zero (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    Tendsto (fun n : ℕ => smallE8CrossWeightedBlock8 p q n/(n:ℝ)^12) atTop (nhds 0) := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossWeightedBlock8_bound p q hd
  simpa only [one_mul] using nat_power12_normalized_zero_of_power10_bound
    (F := smallE8CrossWeightedBlock8 p q) 1 (by decide) C hb

end SphericalRiesz
