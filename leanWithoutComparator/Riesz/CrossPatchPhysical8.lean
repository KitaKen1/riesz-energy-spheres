import Riesz.CrossPatchBlock8
import Riesz.EqualAreaPatchTransport8

/-! Connect the separated coordinate kernel to actual spherical probability
backgrounds. The density factors are the checked physical chart densities;
no substitute measure or abstract cross-energy oracle is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def smallE8CubeDensity8 (p : SmallE8CubePatch8) : ℝ :=
  equalAreaE8PatchProbabilityDensity8 p.ε

theorem smallE8CubeDensity8_pos (p : SmallE8CubePatch8) : 0 < smallE8CubeDensity8 p :=
  equalAreaE8PatchProbabilityDensity8_pos p.ε p.ε_pos

theorem smallE8CubeSet8_integral (p : SmallE8CubePatch8) (f : Ambient9 → ℝ) :
    (∫ x in smallE8CubeSet8 p, f x ∂sphereProbability8) =
      smallE8CubeDensity8 p * ∫ x in UnitCube 8, f (smallE8CubeMap8 p x) :=
  equalAreaE8SpherePatch8_integral p.g p.v p.c p.ε p.ε_pos p.c_mem p.small f

theorem smallE8CrossPhysicalRow8 (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q))
    (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    (∫ y in smallE8CubeSet8 q, ‖smallE8CubeMap8 p x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8) =
      smallE8CubeDensity8 q * cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)) := by
  rw [smallE8CubeSet8_integral q (fun y : Ambient9 => ‖smallE8CubeMap8 p x-y‖⁻¹^4)]
  rw [cubeIntegral_eq_setIntegral_on 8 (fun y => smallE8CrossKernel8 p q (x,y))
    (fun y hy => (smallE8CrossKernel8_row_contDiffAt p q hd x y hx hy).continuousAt.continuousWithinAt)]
  rfl

theorem smallE8CrossPhysicalQuadratureBackground8 (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) (n : ℕ) (hn : 8 ≤ n) :
    (∫ x in smallE8CubeSet8 p, cubeQuadrature 8 n
      (fun y => ‖(x : Ambient9)-smallE8CubeMap8 q y‖⁻¹^4) ∂sphereProbability8) =
      smallE8CubeDensity8 p * cubeIntegral 8
        (fun x => cubeQuadrature 8 n (fun y => smallE8CrossKernel8 p q (x,y))) := by
  rw [smallE8CubeSet8_integral p (fun x : Ambient9 =>
    cubeQuadrature 8 n (fun y => ‖x-smallE8CubeMap8 q y‖⁻¹^4))]
  rw [cubeIntegral_eq_setIntegral_on 8 (fun x => cubeQuadrature 8 n (fun y => smallE8CrossKernel8 p q (x,y))) (smallE8CrossQuadratureRow8_continuousOn p q hd n hn)]
  rfl

theorem smallE8CrossPhysicalDoubleBackground8 (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    (∫ x in smallE8CubeSet8 p, ∫ y in smallE8CubeSet8 q,
      ‖(x : Ambient9)-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8 ∂sphereProbability8) =
      smallE8CubeDensity8 p*smallE8CubeDensity8 q *
        cubeIntegral 8 (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))) := by
  rw [smallE8CubeSet8_integral p (fun x : Ambient9 =>
    ∫ y in smallE8CubeSet8 q, ‖x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8)]
  have he : (∫ x in UnitCube 8, ∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8) =
      smallE8CubeDensity8 q * cubeIntegral 8
        (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))) := by
    calc
      _ = ∫ x in UnitCube 8, smallE8CubeDensity8 q *
          cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)) := by
        apply setIntegral_congr_fun (unitCube_measurableSet 8)
        intro x hx
        exact smallE8CrossPhysicalRow8 p q hd x hx
      _ = smallE8CubeDensity8 q * ∫ x in UnitCube 8,
          cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)) := integral_const_mul _ _
      _ = _ := congrArg (fun z => smallE8CubeDensity8 q*z)
        (cubeIntegral_eq_setIntegral_on 8
          (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y)))
          (smallE8CrossIntegralRow8_continuousOn p q hd)).symm
  rw [he]
  exact (mul_assoc _ _ _).symm

def smallE8CrossPhysicalBlock8 (p q : SmallE8CubePatch8) (n : ℕ) : ℝ :=
  (n:ℝ)^16 * (
    cubeQuadrature 8 n (fun x => cubeQuadrature 8 n (fun y => smallE8CrossKernel8 p q (x,y)))-
    cubeQuadrature 8 n (fun x => (∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8)/smallE8CubeDensity8 q)-
    (∫ x in smallE8CubeSet8 p, cubeQuadrature 8 n
      (fun y => ‖(x : Ambient9)-smallE8CubeMap8 q y‖⁻¹^4) ∂sphereProbability8)/smallE8CubeDensity8 p+
    (∫ x in smallE8CubeSet8 p, ∫ y in smallE8CubeSet8 q,
      ‖(x : Ambient9)-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8 ∂sphereProbability8)/
        (smallE8CubeDensity8 p*smallE8CubeDensity8 q))

theorem smallE8CrossPhysicalBlock8_eq (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) (n : ℕ) (hn : 8 ≤ n) :
    smallE8CrossPhysicalBlock8 p q n = smallE8CrossWeightedBlock8 p q n := by
  have hp := (smallE8CubeDensity8_pos p).ne'
  have hq := (smallE8CubeDensity8_pos q).ne'
  have he : cubeQuadrature 8 n (fun x => (∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8)/smallE8CubeDensity8 q) =
      cubeQuadrature 8 n (fun x => cubeIntegral 8 (fun y => smallE8CrossKernel8 p q (x,y))) := by
    apply cubeQuadrature_congr 8 n hn
    intro x hx
    change (∫ y in smallE8CubeSet8 q,
      ‖smallE8CubeMap8 p x-(y : Ambient9)‖⁻¹^4 ∂sphereProbability8)/smallE8CubeDensity8 q = _
    rw [smallE8CrossPhysicalRow8 p q hd x hx,mul_div_cancel_left₀ _ hq]
  rw [smallE8CrossPhysicalBlock8,he,smallE8CrossPhysicalQuadratureBackground8 p q hd n hn,
    smallE8CrossPhysicalDoubleBackground8 p q hd,mul_div_cancel_left₀ _ hp,
    mul_div_cancel_left₀ _ (mul_ne_zero hp hq),smallE8CrossWeightedBlock8,
    smallE8CrossNeutralized8_four_terms p q hd n hn]

theorem smallE8CrossPhysicalBlock8_bound (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n → |smallE8CrossPhysicalBlock8 p q n| ≤ C*(n:ℝ)^10 := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossWeightedBlock8_bound p q hd
  exact ⟨C,hC,fun n hn => by rw [smallE8CrossPhysicalBlock8_eq p q hd n hn]; exact hb n hn⟩

theorem smallE8CrossPhysicalBlock8_normalized_zero (p q : SmallE8CubePatch8)
    (hd : Disjoint (smallE8CubeSet8 p) (smallE8CubeSet8 q)) :
    Tendsto (fun n : ℕ => smallE8CrossPhysicalBlock8 p q n/(n:ℝ)^12) atTop (nhds 0) := by
  obtain ⟨C,hC,hb⟩ := smallE8CrossPhysicalBlock8_bound p q hd
  simpa only [one_mul] using nat_power12_normalized_zero_of_power10_bound
    (F := smallE8CrossPhysicalBlock8 p q) 1 (by decide) C hb

end SphericalRiesz
