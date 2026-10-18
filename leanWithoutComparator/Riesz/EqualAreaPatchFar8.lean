import Riesz.EqualAreaPatchAnnular8

/-! The actual far row on every checked small sphere patch. A globally
continuous extension is used only to commute finite sums and integrals;
it agrees with the actual kernel at every point of the original cube.
Large annuli vanish on that cube. No far derivative bound is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped ContDiff
namespace SphericalRiesz
open Boundary

structure CurvedAnnularData8 (F : (Fin 8 → ℝ) → Ambient9) : Prop where
  continuous : Continuous F
  derivatives : ∀ y ∈ UnitCube 8, ContDiffAt ℝ ∞ F y ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ 6 → ‖iteratedFDeriv ℝ k F y‖ ≤ equalAreaPatchDerivativeBound8
  distances : ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
    equalAreaPatchLowerDistance8*‖y-x‖ ≤ dist (F x) (F y) ∧
      dist (F x) (F y) ≤ equalAreaPatchDerivativeBound8*‖y-x‖

def curvedAnnularExtension8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ) (x : Fin 8 → ℝ) :
    (Fin 8 → ℝ) → ℝ :=
  if r ≤ 2 then regularizedCurvedAnnular8 F r
    (equalAreaPatchLowerDistance8/4) (4*equalAreaPatchDerivativeBound8)
    (div_pos equalAreaPatchLowerDistance8_pos (by norm_num))
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one equalAreaPatchDerivativeBound8_ge_one)) x
  else fun _ => 0

theorem curvedAnnularExtension8_continuous (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (r : ℝ) (x : Fin 8 → ℝ) : Continuous (curvedAnnularExtension8 F r x) := by
  by_cases h : r ≤ 2
  · simpa only [curvedAnnularExtension8,ite_eq_left h] using
      regularizedCurvedAnnular8_continuous F hF r
        (equalAreaPatchLowerDistance8/4) (4*equalAreaPatchDerivativeBound8)
        (div_pos equalAreaPatchLowerDistance8_pos (by norm_num))
        (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one equalAreaPatchDerivativeBound8_ge_one)) x
  · simp only [curvedAnnularExtension8,ite_eq_right h]
    exact continuous_const

theorem curvedAnnularRieszFour8_zero_large (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (hr : 2 ≤ r) (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    curvedAnnularRieszFour8 F r x y = 0 := by
  have hr0 : 0 < r := by linarith
  have hn : ‖r⁻¹ • (y-x)‖ ≤ 1/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr0),← div_eq_inv_mul]
    apply (div_le_iff₀ hr0).mpr
    linarith [unitCube8_sub_norm y x hy hx]
  rw [curvedAnnularRieszFour8,unitAnnularCutoff_zero_inside 8 _ hn,mul_zero]

theorem curvedAnnularExtension8_eq_actual (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r)
    (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    EqOn (curvedAnnularExtension8 F r x) (curvedAnnularRieszFour8 F r x) (UnitCube 8) := by
  intro y hy
  by_cases h : r ≤ 2
  · simp only [curvedAnnularExtension8,ite_eq_left h]
    exact regularizedCurvedAnnular8_eq_actual F _ _ r equalAreaPatchLowerDistance8_pos
      equalAreaPatchDerivativeBound8_ge_one hr x y
      (hF.distances x hx y hy).1 (hF.distances x hx y hy).2
  · simp only [curvedAnnularExtension8,ite_eq_right h]
    exact (curvedAnnularRieszFour8_zero_large F r (not_le.mp h).le x y hx hy).symm

theorem curvedAnnularExtension8_resolved_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (curvedAnnularExtension8 F r x)-
        cubeIntegral 8 (curvedAnnularExtension8 F r x)| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := regularizedCurvedAnnular8_resolved_bound
    (equalAreaPatchLowerDistance8/4) (4*equalAreaPatchDerivativeBound8) equalAreaPatchDerivativeBound8
    (div_pos equalAreaPatchLowerDistance8_pos (by norm_num))
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one equalAreaPatchDerivativeBound8_ge_one))
    equalAreaPatchDerivativeBound8_ge_one
  refine ⟨C,hC,?_⟩
  intro F hF m hm r hr hmesh x
  by_cases h : r ≤ 2
  · simpa only [curvedAnnularExtension8,ite_eq_left h] using
      hb F hF.continuous hF.derivatives m hm r hr h hmesh x
  · simp only [curvedAnnularExtension8,ite_eq_right h]
    have hq : cubeQuadrature 8 m (fun _ => (0:ℝ)) = 0 := by
      apply abs_nonpos_iff.mp
      exact cubeQuadrature_abs_le 8 m hm _ 0 (by intro _ _; simp)
    have hi : cubeIntegral 8 (fun _ => (0:ℝ)) = 0 := by
      apply abs_nonpos_iff.mp
      exact cubeIntegral_abs_le 8 _ 0 (by intro _ _; simp)
    rw [hq,hi,sub_self,abs_zero]
    positivity

def curvedFarRieszFour8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ) (x y : Fin 8 → ℝ) : ℝ :=
  curvedRieszFour F x y-curvedNearRieszFour F (r/2) x y

theorem curvedFarRieszFour8_eq_kernel (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (x y : Fin 8 → ℝ) : curvedFarRieszFour8 F r x y =
      (dist (F x) (F y))⁻¹^4*(1-outerUnitBump 8 ((r/2)⁻¹ • (y-x))) := by
  unfold curvedFarRieszFour8 curvedNearRieszFour curvedRieszFour
  ring

theorem curvedAnnularRieszFour8_eq_near_sub (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (x y : Fin 8 → ℝ) :
    curvedAnnularRieszFour8 F r x y = curvedNearRieszFour F r x y-curvedNearRieszFour F (r/2) x y := by
  rw [curvedAnnularRieszFour8,unitAnnularCutoff,innerUnitBump_eq_outer_scaled,
    curvedNearRieszFour,curvedNearRieszFour]
  have harg : (2:ℝ) • (r⁻¹ • (y-x)) = (r/2)⁻¹ • (y-x) := by
    rw [smul_smul]
    congr 1
    simp only [div_eq_mul_inv,mul_inv,inv_inv]
    ring
  rw [harg]
  ring

theorem curvedAnnularRieszFour8_partition_sum (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (n : ℕ) (x y : Fin 8 → ℝ) :
    (∑ k ∈ Finset.range n, curvedAnnularRieszFour8 F ((2:ℝ)^k*r) x y) =
      curvedNearRieszFour F (((2:ℝ)^n*r)/2) x y-curvedNearRieszFour F (r/2) x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,curvedAnnularRieszFour8_eq_near_sub]
    rw [show ((2:ℝ)^(n+1)*r)/2 = (2:ℝ)^n*r by rw [pow_succ]; ring]
    ring

theorem curvedNearRieszFour8_eq_kernel_of_norm_le (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (hr : 0 < r) (x y : Fin 8 → ℝ) (hy : ‖y-x‖ ≤ r) :
    curvedNearRieszFour F r x y = curvedRieszFour F x y := by
  have hb : outerUnitBump 8 (r⁻¹ • (y-x)) = 1 := by
    apply (outerUnitBump 8).one_of_mem_closedBall
    rw [Metric.mem_closedBall,dist_zero_right]
    change ‖r⁻¹ • (y-x)‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),← div_eq_inv_mul]
    exact (div_le_one hr).mpr hy
  rw [curvedNearRieszFour,hb,mul_one]

theorem curvedFarRieszFour8_eq_extension_sum_on (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) (n : ℕ)
    (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8)
    (hcover : ∀ y ∈ UnitCube 8, ‖y-x‖ ≤ ((2:ℝ)^n*r)/2) :
    EqOn (curvedFarRieszFour8 F r x)
      (fun y => ∑ k ∈ Finset.range n, curvedAnnularExtension8 F ((2:ℝ)^k*r) x y) (UnitCube 8) := by
  intro y hy
  dsimp only
  have heq : (∑ k ∈ Finset.range n, curvedAnnularExtension8 F ((2:ℝ)^k*r) x y) =
      ∑ k ∈ Finset.range n, curvedAnnularRieszFour8 F ((2:ℝ)^k*r) x y :=
    Finset.sum_congr rfl (fun k _ => curvedAnnularExtension8_eq_actual F hF _ (by positivity) x hx hy)
  rw [heq,curvedAnnularRieszFour8_partition_sum,
    curvedNearRieszFour8_eq_kernel_of_norm_le F _ (by positivity) x y (hcover y hy)]
  rfl

theorem curvedAnnularExtension8_error_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ n : ℕ, ∀ x : Fin 8 → ℝ,
      |∑ k ∈ Finset.range n,
        (cubeQuadrature 8 m (curvedAnnularExtension8 F ((2:ℝ)^k*r) x)-
          cubeIntegral 8 (curvedAnnularExtension8 F ((2:ℝ)^k*r) x))| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := curvedAnnularExtension8_resolved_bound
  refine ⟨(4/3:ℝ)*C,by positivity,?_⟩
  intro F hF m hm r hr hmesh n x
  let e (k : ℕ) := cubeQuadrature 8 m (curvedAnnularExtension8 F ((2:ℝ)^k*r) x)-
    cubeIntegral 8 (curvedAnnularExtension8 F ((2:ℝ)^k*r) x)
  have he (k : ℕ) : |e k| ≤ (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k := by
    have h2 : 0 < (2:ℝ)^k := by positivity
    have hr' : r ≤ (2:ℝ)^k*r := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]
    have h := hb F hF m hm _ (by positivity) (hmesh.trans hr') x
    have hp : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
      rw [← pow_mul,mul_comm k 2,pow_mul]
      norm_num
    calc
      _ ≤ C/((m:ℝ)^6*((2:ℝ)^k*r)^2) := h
      _ = _ := by simp only [div_pow,one_pow,hp,mul_pow]; field_simp [h2.ne',hr.ne']
  calc
    _ ≤ ∑ k ∈ Finset.range n, |e k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k :=
      Finset.sum_le_sum (fun k _ => he k)
    _ = (C/((m:ℝ)^6*r^2))*(∑ k ∈ Finset.range n, (1/4:ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/((m:ℝ)^6*r^2))*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_quarter_sum_le n) (by positivity)
    _ = _ := by ring

theorem curvedFarRieszFour8_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ x ∈ UnitCube 8,
      |cubeQuadrature 8 m (curvedFarRieszFour8 F r x)-cubeIntegral 8 (curvedFarRieszFour8 F r x)| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := curvedAnnularExtension8_error_sum_bound
  refine ⟨C,hC,?_⟩
  intro F hF m hm r hr hmesh x hx
  obtain ⟨n,hn⟩ := exists_annular_cover 8 r hr x
  have heq := curvedFarRieszFour8_eq_extension_sum_on F hF r hr n x hx hn
  rw [cubeQuadrature_congr 8 m hm heq,cubeIntegral_congr 8 heq,
    cubeQuadrature_finset_sum,cubeIntegral_finset_sum 8 _ _
      (fun k _ => curvedAnnularExtension8_continuous F hF.continuous _ x),← Finset.sum_sub_distrib]
  exact hb F hF m hm r hr hmesh n x

theorem equalAreaNormalizedE8Patch_annular_data_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      CurvedAnnularData8 (equalAreaNormalizedE8Patch g v c ε) := by
  obtain ⟨ρ,hρ,hρb,hclass⟩ := equalAreaNormalizedE8Patch_annular_class
  refine ⟨ρ,hρ,hρb,?_⟩
  intro v hv ε hε hs g c hc
  exact ⟨equalAreaNormalizedE8Patch_continuous g v c ε,
    (hclass v hv ε hε hs g c hc).1,(hclass v hv ε hε hs g c hc).2⟩

/-- A proved common far-row constant for actual patches, with no Gaussian
or supplied curved-kernel estimate among the hypotheses. -/
theorem equalAreaPatchFar8_quadrature_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r → ∀ x ∈ UnitCube 8,
      |cubeQuadrature 8 m (curvedFarRieszFour8 (equalAreaNormalizedE8Patch g v c ε) r x)-
        cubeIntegral 8 (curvedFarRieszFour8 (equalAreaNormalizedE8Patch g v c ε) r x)| ≤
          C/((m:ℝ)^6*r^2) := by
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_annular_data_uniform
  obtain ⟨C,hC,hquad⟩ := curvedFarRieszFour8_quadrature_bound
  exact ⟨ρ,hρ,hρb,C,hC,fun v hv ε hε hs g c hc m hm r hr hmesh x hx =>
    hquad _ (hdata v hv ε hε hs g c hc) m hm r hr hmesh x hx⟩

theorem equalAreaPatchFar8_error_small :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ τ : ℝ, 0 < τ → ∃ L : ℝ, 1 ≤ L ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m → ∀ x ∈ UnitCube 8,
      |cubeQuadrature 8 m
          (curvedFarRieszFour8 (equalAreaNormalizedE8Patch g v c ε) (L/(m:ℝ)) x)-
        cubeIntegral 8
          (curvedFarRieszFour8 (equalAreaNormalizedE8Patch g v c ε) (L/(m:ℝ)) x)| ≤ τ/(m:ℝ)^4 := by
  obtain ⟨ρ,hρ,hρb,C,hC,hb⟩ := equalAreaPatchFar8_quadrature_uniform
  refine ⟨ρ,hρ,hρb,?_⟩
  intro τ hτ
  let L := 1+C/τ
  have hL : 1 ≤ L := by dsimp [L]; linarith [div_nonneg hC hτ.le]
  have hL0 : 0 < L := by linarith
  refine ⟨L,hL,?_⟩
  intro v hv ε hε hs g c hc m hm x hx
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : 1/(m:ℝ) ≤ L/(m:ℝ) := div_le_div_of_nonneg_right hL hm0.le
  have hCτ : C ≤ τ*L^2 := by
    have hlin : C ≤ τ*L := by dsimp [L]; field_simp; nlinarith
    have hs : L ≤ L^2 := by nlinarith
    nlinarith
  calc
    _ ≤ C/((m:ℝ)^6*(L/(m:ℝ))^2) := hb v hv ε hε hs g c hc m hm _ (div_pos hL0 hm0) hmesh x hx
    _ = (C/L^2)/(m:ℝ)^4 := by field_simp [hL0.ne',hm0.ne']
    _ ≤ τ/(m:ℝ)^4 := div_le_div_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_pos hL0)).mpr hCτ) (pow_pos hm0 4).le

end SphericalRiesz
