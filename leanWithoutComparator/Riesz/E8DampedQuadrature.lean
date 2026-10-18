import Riesz.E8ScaledDampedAnnulus
import Riesz.CubeLebesgue

/-! Uniform damped E8 annular errors on the original corrected tensor nodes. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory
namespace SphericalRiesz
open Boundary

theorem e8ScaledDampedAnnulus_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ m : ℕ, 8 ≤ m →
      ∀ r : ℝ, 0 < r → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (e8ScaledDampedAnnulus u r x)-
        cubeIntegral 8 (e8ScaledDampedAnnulus u r x)| ≤
        (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := by
  obtain ⟨C, hC, hb⟩ := e8ScaledDampedAnnulus_sixth_bounded
  refine ⟨C, hC, ?_⟩
  intro u hu m hm r hr x
  have hf : ContDiff ℝ 6 (e8ScaledDampedAnnulus u r x) :=
    (e8ScaledDampedAnnulus_contDiff hu r x).of_le (by simp)
  have hs : ∀ i v, v ∈ UnitCube 8 → ContDiffOn ℝ 6
      (fun t => e8ScaledDampedAnnulus u r x (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
    intro i v _
    have ht : ContDiff ℝ 6 (fun t : ℝ => Function.update v i t) := by
      rw [show (fun t : ℝ => Function.update v i t) =
        (fun t => ContinuousLinearMap.single ℝ (fun _ : Fin 8 => ℝ) i t+Function.update v i 0)
        from funext (coordinate_update_as_line 8 i v)]
      fun_prop
    exact (hf.comp ht).contDiffOn
  have h := cubeQuadrature_local_sixth_order_bound 8 hm x (2*r) (C/r^10)
    (by positivity) (by positivity) hf.continuous
    hs
    (fun i v _ t ht => (sixth_coordinate_within_abs_le 8 hf i v t ht).trans (hb u hu r hr x _))
    (fun v _ hn => e8ScaledDampedAnnulus_zero_outside u r hr x v hn) ?_
  · simpa only [Nat.cast_ofNat, show 2*(2*r) = 4*r by ring] using h
  · intro i v _ t ht hn
    apply abs_nonpos_iff.mp
    have h := sixth_coordinate_within_abs_le 8 hf i v t ht
    rw [e8ScaledDampedAnnulus_sixth_zero_outside hu r hr x _ hn, norm_zero] at h
    exact h

theorem e8ScaledDampedAnnulus_eight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ m : ℕ, 8 ≤ m →
      ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (e8ScaledDampedAnnulus u r x)-
        cubeIntegral 8 (e8ScaledDampedAnnulus u r x)| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := e8ScaledDampedAnnulus_quadrature_bound
  refine ⟨859963392*C, by positivity, ?_⟩
  intro u hu m hm r hr hmesh x
  have hmesh' : 2/(m:ℝ) ≤ 2*r := by
    convert mul_le_mul_of_nonneg_left hmesh (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  have hrad : 4*r+2/(m:ℝ) ≤ 6*r := by linarith
  calc
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := hb u hu m hm r hr x
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(6*r)^8*(C/r^10) := by gcongr
    _ = (859963392*C)/((m:ℝ)^6*r^2) := by
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp [hr.ne', hm0]
      ring

theorem e8DampedAnnulus_heat_cube_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ m : ℕ, 8 ≤ m →
      ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (fun v => obliqueRieszFour 8 e8Map x v *
        unitAnnularCutoff 8 (r⁻¹ • (v-x))*e8CoordinateGaussian ε (v-x)) -
       ∫ v in UnitCube 8, obliqueRieszFour 8 e8Map x v *
        unitAnnularCutoff 8 (r⁻¹ • (v-x))*e8CoordinateGaussian ε (v-x)| ≤
          C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := e8ScaledDampedAnnulus_eight_bound
  refine ⟨C, hC, ?_⟩
  intro ε hε m hm r hr hmesh x
  have hu : 0 ≤ ε*r^2 := mul_nonneg hε (sq_nonneg r)
  have h := hb (ε*r^2) hu m hm r hr hmesh x
  rw [cubeIntegral_eq_setIntegral 8 _ (e8ScaledDampedAnnulus_contDiff hu r x).continuous] at h
  have heq : e8ScaledDampedAnnulus (ε*r^2) r x =
      fun v => obliqueRieszFour 8 e8Map x v *
        unitAnnularCutoff 8 (r⁻¹ • (v-x))*e8CoordinateGaussian ε (v-x) :=
    funext (e8ScaledDampedAnnulus_eq_heat ε r hr x)
  simpa only [heq] using h

def e8HeatAnnulus (ε r : ℝ) (x : Fin 8 → ℝ) : (Fin 8 → ℝ) → ℝ :=
  e8ScaledDampedAnnulus (ε*r^2) r x

/-- Finite sums of actual damped annular errors, uniformly in ε and the number of annuli. -/
theorem e8HeatAnnulus_error_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ m : ℕ, 8 ≤ m →
      ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ n : ℕ, ∀ x : Fin 8 → ℝ,
      |∑ k ∈ Finset.range n,
        (cubeQuadrature 8 m (e8HeatAnnulus ε ((2:ℝ)^k*r) x)-
          cubeIntegral 8 (e8HeatAnnulus ε ((2:ℝ)^k*r) x))| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := e8ScaledDampedAnnulus_eight_bound
  refine ⟨(4/3:ℝ)*C, by positivity, ?_⟩
  intro ε hε m hm r hr hmesh n x
  let e (k : ℕ) := cubeQuadrature 8 m (e8HeatAnnulus ε ((2:ℝ)^k*r) x)-
    cubeIntegral 8 (e8HeatAnnulus ε ((2:ℝ)^k*r) x)
  have he (k : ℕ) : |e k| ≤ (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k := by
    have h2 : 0 < (2:ℝ)^k := by positivity
    have hr' : r ≤ (2:ℝ)^k*r := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]
    have h := hb (ε*((2:ℝ)^k*r)^2) (mul_nonneg hε (sq_nonneg _))
      m hm _ (by positivity) (hmesh.trans hr') x
    have hp : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc
      _ ≤ C/((m:ℝ)^6*((2:ℝ)^k*r)^2) := h
      _ = (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k := by
        simp only [mul_pow, div_pow, one_pow, hp]
        field_simp [hr.ne', h2.ne']
  calc
    _ ≤ ∑ k ∈ Finset.range n, |e k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k :=
      Finset.sum_le_sum (fun k _ => he k)
    _ = (C/((m:ℝ)^6*r^2))*(∑ k ∈ Finset.range n, (1/4:ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/((m:ℝ)^6*r^2))*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_quarter_sum_le n) (by positivity)
    _ = _ := by ring

#print axioms e8ScaledDampedAnnulus_quadrature_bound
#print axioms e8ScaledDampedAnnulus_eight_bound
#print axioms e8DampedAnnulus_heat_cube_bound
#print axioms e8HeatAnnulus_error_sum_bound
end SphericalRiesz
