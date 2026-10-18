import Riesz.SmallE8PhysicalAssembly4
import Riesz.EqualAreaFinitePatchGeometry8
import Riesz.SphereShortRangeSeparated8

/-! Density-scale separation of the rational patch nodes.

Inside one patch the actual chart has a uniform lower Lipschitz constant `C₀` at the patch scale
`ε = A^(1/8)·a/d`, and distinct grid nodes are `1/(2am)` apart, so distinct nodes are at least
`A^(1/8) C₀/(2dm)` apart.  Distinct patches are a fixed positive distance apart.  With
`N = (dm)^8` and the density factor `c⁴ = π⁴ N/A`, this gives `c·|x-y|² ≥ π (C₀/2)²` for all
distinct nodes once `dm` is large. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz
open Boundary

/-- A uniform lower Lipschitz bound for the actual small patch maps. -/
theorem smallE8CubeMap8_dist_lower :
    ∃ ρ > 0, ∃ C₀ > 0, ∀ p : SmallE8CubePatch8, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius ≤ ρ →
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
        p.ε*C₀*‖x-y‖ ≤ dist (smallE8CubeMap8 p x) (smallE8CubeMap8 p y) := by
  obtain ⟨ρ, hρ, _, h⟩ := equalAreaNormalizedE8Patch_lower_distance_uniform
  refine ⟨ρ, hρ, 1/(2*(1+‖e8InverseMap‖)), by positivity, ?_⟩
  intro p hv hε x hx y hy
  have hd := h p.v hv p.ε p.ε_pos hε p.g p.c p.c_mem x hx y hy
  have hε0 := p.ε_pos
  have heq : dist (equalAreaNormalizedE8Patch p.g p.v p.c p.ε x)
      (equalAreaNormalizedE8Patch p.g p.v p.c p.ε y) =
      p.ε⁻¹*dist (smallE8CubeMap8 p x) (smallE8CubeMap8 p y) := by
    rw [equalAreaNormalizedE8Patch_eq, equalAreaNormalizedE8Patch_eq, dist_eq_norm, dist_eq_norm,
      ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hε0]
    rfl
  rw [heq] at hd
  calc p.ε*(1/(2*(1+‖e8InverseMap‖)))*‖x-y‖ = p.ε*((1/(2*(1+‖e8InverseMap‖)))*‖x-y‖) := by ring
    _ ≤ p.ε*(p.ε⁻¹*dist (smallE8CubeMap8 p x) (smallE8CubeMap8 p y)) :=
        mul_le_mul_of_nonneg_left hd hε0.le
    _ = dist (smallE8CubeMap8 p x) (smallE8CubeMap8 p y) := by field_simp

theorem sphereGaussianDensityFactor8_pow_four {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor8 N)^4 = Real.pi^4*((N:ℝ)/sphereArea8.real univ) := by
  unfold sphereGaussianDensityFactor8
  rw [sphereGaussianScale8_pow_four hN]
  ring

/-- Density-scale separation from a scaled lower distance bound. -/
theorem density_separated_of_scaled_dist {N : ℕ} (hN : 0 < N) {x y : Sphere8} {D : ℝ} (hD : 0 ≤ D)
    (n : ℝ) (hn : 0 ≤ n) (hNn : (N:ℝ) = n^8) (hxy : sphereAreaRoot8*D ≤ n*dist x y) :
    Real.pi*D^2 ≤ sphereGaussianDensityFactor8 N*dist x y^2 := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hc := sphereGaussianDensityFactor8_pos hN
  have hc4 := sphereGaussianDensityFactor8_pow_four hN
  have hr := sphereAreaRoot8_pos
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hlhs : 0 ≤ Real.pi*D^2 := by positivity
  have hrhs : 0 ≤ sphereGaussianDensityFactor8 N*dist x y^2 := by positivity
  apply (pow_le_pow_iff_left₀ hlhs hrhs (by norm_num : (4:ℕ) ≠ 0)).mp
  have h8 : (sphereAreaRoot8*D)^8 ≤ (n*dist x y)^8 :=
    pow_le_pow_left₀ (by positivity) hxy 8
  have hroot := sphereAreaRoot8_pow
  calc (Real.pi*D^2)^4 = Real.pi^4*(sphereAreaRoot8*D)^8/sphereArea8.real univ := by
        rw [show (sphereAreaRoot8*D)^8 = sphereAreaRoot8^8*D^8 by ring, hroot]
        field_simp
    _ ≤ Real.pi^4*(n*dist x y)^8/sphereArea8.real univ := by
        apply div_le_div_of_nonneg_right _ hA.le
        exact mul_le_mul_of_nonneg_left h8 (by positivity)
    _ = (sphereGaussianDensityFactor8 N*dist x y^2)^4 := by
        rw [show (sphereGaussianDensityFactor8 N*dist x y^2)^4 =
          sphereGaussianDensityFactor8 N^4*dist x y^8 by ring, hc4, hNn]
        field_simp

/-- The rational patch nodes are density-scale separated for all large `m`. -/
theorem rationalCubePatchNodes8_density_separated {K : ℕ} (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) {ρ C₀ : ℝ} (hC₀ : 0 < C₀)
    (hlow : ∀ p : SmallE8CubePatch8, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius ≤ ρ →
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
        p.ε*C₀*‖x-y‖ ≤ dist (smallE8CubeMap8 p x) (smallE8CubeMap8 p y))
    (hsmall : ∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ)
    (hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) :
    ∀ᶠ m : ℕ in atTop, ∀ hm : 8 ≤ m, ∀ t t' : Fin K × (Fin 8 → NodeIndex (a*m)), t ≠ t' →
      Real.pi*(C₀/2)^2 ≤ sphereGaussianDensityFactor8 ((d*m)^8)*
        dist (rationalCubePatchNodes8 P a m ha hm t) (rationalCubePatchNodes8 P a m ha hm t')^2 := by
  obtain ⟨δP, hδP, hP⟩ := finite_compact_disjoint_distance8 (fun i => smallE8CubeSet8 (P i))
    (fun i => smallE8CubeSet8_isCompact (P i)) hdis
  have hr := sphereAreaRoot8_pos
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (sphereAreaRoot8*(C₀/2)/δP)
  filter_upwards [eventually_ge_atTop (max 1 M₀)] with m hmM hm t t' htt
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hmM
  have hmM0 : M₀ ≤ m := (le_max_right _ _).trans hmM
  have hdmpos : 0 < d*m := Nat.mul_pos hd hm1
  have hNpos : 0 < (d*m)^8 := pow_pos hdmpos 8
  have hn : (((d*m)^8:ℕ):ℝ) = ((d*m:ℕ):ℝ)^8 := by push_cast; ring
  have hdmR : (0:ℝ) < ((d*m:ℕ):ℝ) := by exact_mod_cast hdmpos
  apply density_separated_of_scaled_dist hNpos (by positivity) ((d*m:ℕ):ℝ) hdmR.le hn
  obtain ⟨i, u⟩ := t
  obtain ⟨j, v⟩ := t'
  by_cases hij : i = j
  · subst hij
    have huv : u ≠ v := fun h => htt (by rw [h])
    have hnm : 8 ≤ a*m := hm.trans (Nat.le_mul_of_pos_left m ha)
    have hsep := cubeNode_norm_separated 8 hnm u v huv
    have hx : cubeNode 8 (a*m) u ∈ UnitCube 8 := originalNode8_mem_cube (a*m) hnm u
    have hy : cubeNode 8 (a*m) v ∈ UnitCube 8 := originalNode8_mem_cube (a*m) hnm v
    have hl := hlow (P i) (hsmall i).1 (hsmall i).2 _ hx _ hy
    have hdist : dist (rationalCubePatchNodes8 P a m ha hm (i, u))
        (rationalCubePatchNodes8 P a m ha hm (i, v)) =
        dist (smallE8CubeMap8 (P i) (cubeNode 8 (a*m) u))
          (smallE8CubeMap8 (P i) (cubeNode 8 (a*m) v)) := rfl
    rw [hdist]
    have hεi : (P i).ε = sphereAreaRoot8*((a:ℝ)/d) := hε i
    have haR : (0:ℝ) < a := by exact_mod_cast ha
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hmR : (0:ℝ) < m := by exact_mod_cast hm1
    have hamR : ((a*m:ℕ):ℝ) = (a:ℝ)*m := by push_cast; ring
    rw [hamR] at hsep
    have h1 : (P i).ε*C₀*(1/(2*((a:ℝ)*m))) ≤ (P i).ε*C₀*‖cubeNode 8 (a*m) u-cubeNode 8 (a*m) v‖ :=
      mul_le_mul_of_nonneg_left hsep.le (by have := (P i).ε_pos; positivity)
    have h2 : sphereAreaRoot8*(C₀/2) = ((d*m:ℕ):ℝ)*((P i).ε*C₀*(1/(2*((a:ℝ)*m)))) := by
      rw [hεi]
      push_cast
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left (h1.trans hl) hdmR.le
  · have hx := rationalCubePatchNodes8_mem P a m ha hm (i, u)
    have hy := rationalCubePatchNodes8_mem P a m ha hm (j, v)
    have hfar := hP i j hij _ hx _ hy
    have hM : sphereAreaRoot8*(C₀/2) ≤ ((d*m:ℕ):ℝ)*δP := by
      have h1 : sphereAreaRoot8*(C₀/2)/δP < M₀ := hM₀
      have h2 : (M₀:ℝ) ≤ ((d*m:ℕ):ℝ) := by
        have : M₀ ≤ d*m := hmM0.trans (Nat.le_mul_of_pos_left m hd)
        exact_mod_cast this
      rw [div_lt_iff₀ hδP] at h1
      nlinarith
    calc sphereAreaRoot8*(C₀/2) ≤ ((d*m:ℕ):ℝ)*δP := hM
      _ ≤ ((d*m:ℕ):ℝ)*dist (rationalCubePatchNodes8 P a m ha hm (i, u))
          (rationalCubePatchNodes8 P a m ha hm (j, v)) :=
        mul_le_mul_of_nonneg_left hfar.le hdmR.le

end SphericalRiesz
