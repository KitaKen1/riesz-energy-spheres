import Riesz.AnnularCutoff
import Riesz.LocalizedQuadrature
import Riesz.DyadicShell

/-!
# The actual smooth annular-kernel error on the original nodes

The constant is supplied by the proved compact-support certificate.
No derivative bound, support count, or quadrature error is assumed.
The result concerns flat orthogonal coordinates; oblique E8 coordinates,
spherical patches, near interactions, and boundary errors remain separate.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace SphericalRiesz
open Boundary

theorem coordinate_update_as_line (d : ℕ) (i : Fin d) (v : Fin d → ℝ) (t : ℝ) :
    Function.update v i t =
      ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i t+Function.update v i 0 := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- A coordinate inclusion has norm one; no high-order coordinate expansion. -/
theorem sixth_coordinate_within_abs_le (d : ℕ) {F : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ 6 F) (i : Fin d) (v : Fin d → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |iteratedDerivWithin 6 (fun u => F (Function.update v i u)) (Set.Icc (0:ℝ) 1) t| ≤
      ‖iteratedFDeriv ℝ 6 F (Function.update v i t)‖ := by
  let g : ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i
  let a := Function.update v i 0
  let H : (Fin d → ℝ) → ℝ := fun z => F (z+a)
  have hH : ContDiff ℝ 6 H := hf.comp (by fun_prop)
  have heq : (fun u => F (Function.update v i u)) = H ∘ g := by
    funext u
    rw [coordinate_update_as_line]
    rfl
  rw [heq, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hH.comp g.contDiff).contDiffAt ht, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    g.iteratedFDeriv_comp_right hH t (by rfl)]
  have hshift : iteratedFDeriv ℝ 6 H (g t) = iteratedFDeriv ℝ 6 F (Function.update v i t) := by
    dsimp only [H]
    rw [iteratedFDeriv_comp_add_right]
    rw [coordinate_update_as_line]
  rw [hshift]
  have hnorm : ‖g‖ = 1 := ContinuousLinearMap.norm_single ℝ (fun _ : Fin d => ℝ) i
  simpa only [hnorm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ 6 F (Function.update v i t)).norm_compContinuousLinearMap_le (fun _ => g)

/-- The same C works for all m ≥ 8, radii, and centers. -/
theorem scaledAnnularRieszFour_quadrature_bound (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → ∀ x : Fin d → ℝ,
      |cubeQuadrature d m (scaledAnnularRieszFour d r x)-
        cubeIntegral d (scaledAnnularRieszFour d r x)| ≤
        (64/(m:ℝ)^6)*(d:ℝ)*(4*r+2/(m:ℝ))^d*(C/r^10) := by
  obtain ⟨C, hC, hb⟩ := scaledAnnularRieszFour_sixth_bounded d
  refine ⟨C, hC, ?_⟩
  intro m hm r hr x
  have hf : ContDiff ℝ 6 (scaledAnnularRieszFour d r x) :=
    (scaledAnnularRieszFour_contDiff d r x).of_le (by simp)
  have hs : ∀ i v, v ∈ UnitCube d → ContDiffOn ℝ 6
      (fun t => scaledAnnularRieszFour d r x (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
    intro i v _
    have hu : ContDiff ℝ 6 (fun t : ℝ => Function.update v i t) := by
      rw [show (fun t : ℝ => Function.update v i t) =
        (fun t => ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i t+Function.update v i 0)
        from funext (coordinate_update_as_line d i v)]
      fun_prop
    exact (hf.comp hu).contDiffOn
  have hbound : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => scaledAnnularRieszFour d r x (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ C/r^10 :=
    fun i v _ t ht => (sixth_coordinate_within_abs_le d hf i v t ht).trans (hb r hr x _)
  have hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-x i| ≤ 2*r) →
      scaledAnnularRieszFour d r x v = 0 :=
    fun v _ hn => scaledAnnularRieszFour_zero_outside d r hr x v hn
  have hDsupport : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      (¬ ∀ j, |Function.update v i t j-x j| ≤ 2*r) →
      iteratedDerivWithin 6 (fun u => scaledAnnularRieszFour d r x (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t = 0 := by
    intro i v _ t ht hn
    apply abs_nonpos_iff.mp
    have h := sixth_coordinate_within_abs_le d hf i v t ht
    rw [scaledAnnularRieszFour_sixth_zero_outside d r hr x _ hn, norm_zero] at h
    exact h
  have h := cubeQuadrature_local_sixth_order_bound d hm x (2*r) (C/r^10)
    (by positivity) (by positivity) hf.continuous hs hbound hsupport hDsupport
  simpa only [show 2*(2*r) = 4*r by ring] using h

/-- In dimension eight, resolved annuli have the required m^-6 r^-2 scale. -/
theorem scaledAnnularRieszFour_eight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (scaledAnnularRieszFour 8 r x)-
        cubeIntegral 8 (scaledAnnularRieszFour 8 r x)| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := scaledAnnularRieszFour_quadrature_bound 8
  refine ⟨859963392*C, by positivity, ?_⟩
  intro m hm r hr hmesh x
  have hrad : 0 ≤ 4*r+2/(m:ℝ) := by positivity
  have hmesh' : 2/(m:ℝ) ≤ 2*r := by
    convert mul_le_mul_of_nonneg_left hmesh (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  have hrad' : 4*r+2/(m:ℝ) ≤ 6*r := by linarith
  have h := hb m hm r hr x
  calc
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := h
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(6*r)^8*(C/r^10) := by
      gcongr
    _ = (859963392*C)/((m:ℝ)^6*r^2) := by
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp [hr.ne', hm0]
      ring

/-- This estimates the actual dyadic cutoff kernels at the original m^8 nodes. -/
theorem scaledAnnularRieszFour_dyadic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ k : ℕ, ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x)-
        cubeIntegral 8 (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x)| ≤
        (C/(m:ℝ)^4)*(1/4:ℝ)^k := by
  obtain ⟨C, hC, hb⟩ := scaledAnnularRieszFour_eight_bound
  refine ⟨C, hC, ?_⟩
  intro m hm k x
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h2 : 0 < (2:ℝ)^k := by positivity
  have hmesh : 1/(m:ℝ) ≤ (2:ℝ)^k/(m:ℝ) :=
    div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hm0.le
  have h := hb m hm _ (div_pos h2 hm0) hmesh x
  have hp : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  calc
    _ ≤ C/((m:ℝ)^6*((2:ℝ)^k/(m:ℝ))^2) := h
    _ = (C/(m:ℝ)^4)*(1/4:ℝ)^k := by
      simp only [div_pow, one_pow, hp]
      field_simp [hm0.ne', h2.ne']

/-- Finite annular error sums are uniformly O(m^-4).
Identifying the annular sum with the full singular kernel is not claimed. -/
theorem scaledAnnularRieszFour_dyadic_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ n : ℕ, ∀ x : Fin 8 → ℝ,
      |∑ k ∈ Finset.range n,
        (cubeQuadrature 8 m (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x)-
          cubeIntegral 8 (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x))| ≤
        (4/3:ℝ)*C/(m:ℝ)^4 := by
  obtain ⟨C, hC, hb⟩ := scaledAnnularRieszFour_dyadic_bound
  refine ⟨C, hC, ?_⟩
  intro m hm n x
  have h := dyadic_shell_error_bound n
    (fun k => cubeQuadrature 8 m (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x)-
      cubeIntegral 8 (scaledAnnularRieszFour 8 ((2:ℝ)^k/(m:ℝ)) x)) C (1/(m:ℝ)) hC (by
        intro k _
        simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, mul_assoc] using hb m hm k x)
  simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, mul_assoc] using h

#print axioms sixth_coordinate_within_abs_le
#print axioms scaledAnnularRieszFour_quadrature_bound
#print axioms scaledAnnularRieszFour_eight_bound
#print axioms scaledAnnularRieszFour_dyadic_bound
#print axioms scaledAnnularRieszFour_dyadic_sum_bound

end SphericalRiesz
