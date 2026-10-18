import Riesz.CurvedNearQuadrature8

/-! Compare the actual full singular rows before taking their original
finite mean. Both far errors are small; only the same near kernels are
compared by relative distances. Large uncancelled full kernels are never
bounded by a relative error at the second-term scale. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def scaledKernelRow8 (K : (Fin 8 → ℝ) → (Fin 8 → ℝ) → ℝ)
    (m : ℕ) (x : Fin 8 → ℝ) : ℝ :=
  (m:ℝ)^4*(cubeQuadrature 8 m (K x)-∫ y in UnitCube 8, K x y)

def curvedFullRowMean8 (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) : ℝ :=
  cubeQuadrature 8 m (scaledKernelRow8 (curvedRieszFour F) m)

theorem flatScaledKernelRow8_eq (m : ℕ) (v : Fin 8 → NodeIndex m) :
    scaledKernelRow8 (obliqueRieszFour 8 e8Map) m (cubeNode 8 m v) = e8FullRow m v := rfl

theorem flatScaledKernelRowMean8_eq (m : ℕ) :
    cubeQuadrature 8 m (scaledKernelRow8 (obliqueRieszFour 8 e8Map) m) = e8FullRowMean m := by
  rw [cubeQuadrature_as_node_sum]
  rfl

theorem curvedScaledKernelRow8_partition (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (hd : CurvedRelativeE8Distance8 F)
    (r : ℝ) (hr : 0 < r) (m : ℕ) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    scaledKernelRow8 (curvedRieszFour F) m x =
      scaledKernelRow8 (curvedFarRieszFour8 F r) m x+
        scaledKernelRow8 (curvedNearRieszFour F (r/2)) m x := by
  have h := cubeQuadrature_sub 8 m (curvedRieszFour F x) (curvedNearRieszFour F (r/2) x)
  change cubeQuadrature 8 m (curvedFarRieszFour8 F r x) = _ at h
  have hq : cubeQuadrature 8 m (curvedRieszFour F x) =
      cubeQuadrature 8 m (curvedFarRieszFour8 F r x)+cubeQuadrature 8 m (curvedNearRieszFour F (r/2) x) := by
    linarith
  have hi := curvedPotential8_partition F hF hd r hr x hx
  unfold curvedPotential8 curvedFarPotential8 curvedNearPotential at hi
  unfold scaledKernelRow8
  rw [hq,hi]
  ring

theorem flatScaledKernelRow8_partition (r : ℝ) (hr : 0 < r) (m : ℕ) (x : Fin 8 → ℝ) :
    scaledKernelRow8 (obliqueRieszFour 8 e8Map) m x =
      scaledKernelRow8 (farObliqueRieszFour 8 e8Map r) m x+
        scaledKernelRow8 (nearObliqueRieszFour 8 e8Map (r/2)) m x := by
  unfold scaledKernelRow8
  rw [e8Kernel_quadrature_partition m r x,e8Kernel_integral_partition r hr x]
  ring

theorem curvedFarScaledKernelRow8_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ R : ℝ, 1 ≤ R → ∀ x ∈ UnitCube 8,
      |scaledKernelRow8 (curvedFarRieszFour8 F (R/(m:ℝ))) m x| ≤ C/R^2 := by
  obtain ⟨C,hC,hb⟩ := curvedFarRieszFour8_quadrature_bound
  refine ⟨C,hC,?_⟩
  intro F hF m hm R hR x hx
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR0 : 0 < R := by linarith
  have hmesh := div_le_div_of_nonneg_right hR hm0.le
  have h := hb F hF m hm _ (div_pos hR0 hm0) hmesh x hx
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (curvedFarRieszFour8_continuousOn F hF _ (div_pos hR0 hm0) x hx)] at h
  rw [scaledKernelRow8,abs_mul,abs_of_nonneg (pow_nonneg hm0.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(C/((m:ℝ)^6*(R/(m:ℝ))^2)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hm0.ne',hR0.ne']

theorem flatFarScaledKernelRow8_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ R : ℝ, 1 ≤ R → ∀ x : Fin 8 → ℝ,
      |scaledKernelRow8 (farObliqueRieszFour 8 e8Map (R/(m:ℝ))) m x| ≤ C/R^2 := by
  obtain ⟨C,hC,hb⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  refine ⟨C,hC,?_⟩
  intro m hm R hR x
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR0 : 0 < R := by linarith
  have h := hb m hm _ (div_pos hR0 hm0) (div_le_div_of_nonneg_right hR hm0.le) x
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective _ (div_pos hR0 hm0) x).continuousOn] at h
  rw [scaledKernelRow8,abs_mul,abs_of_nonneg (pow_nonneg hm0.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(C/((m:ℝ)^6*(R/(m:ℝ))^2)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hm0.ne',hR0.ne']

theorem curvedFullRow8_comparison_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1/2 → CurvedRelativeE8DistanceTolerance8 F η →
      ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, 8 ≤ m → ∀ v : Fin 8 → NodeIndex m,
      |scaledKernelRow8 (curvedRieszFour F) m (cubeNode 8 m v)-e8FullRow m v| ≤
        C/R^2+64*η*curvedNearRowComparisonConstant8 R := by
  obtain ⟨Cg,hCg,hg⟩ := curvedFarScaledKernelRow8_bound
  obtain ⟨Cf,hCf,hf⟩ := flatFarScaledKernelRow8_bound
  refine ⟨Cg+Cf,add_nonneg hCg hCf,?_⟩
  intro F hF η hη hη1 hd R hR m hm v
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR0 : 0 < R := by linarith
  have hr : 0 < 2*R/(m:ℝ) := by positivity
  have hs : (2*R/(m:ℝ))/2 = R/(m:ℝ) := by ring
  have hx := originalNode8_mem_cube m hm v
  have hg' := hg F hF m hm (2*R) (by linarith) _ hx
  have hf' := hf m hm (2*R) (by linarith) (cubeNode 8 m v)
  have hn : |scaledKernelRow8 (curvedNearRieszFour F (R/(m:ℝ))) m (cubeNode 8 m v)-
      scaledKernelRow8 (nearObliqueRieszFour 8 e8Map (R/(m:ℝ))) m (cubeNode 8 m v)| ≤
        64*η*curvedNearRowComparisonConstant8 R := by
    simpa only [scaledKernelRow8,curvedNearPotential,e8NearPotential,mul_sub] using
      curvedNearRow8_relative_bound F hF.continuous η hη hη1 hd R (by linarith) m hm v
  rw [← flatScaledKernelRow8_eq,curvedScaledKernelRow8_partition F hF
      (curvedRelativeE8DistanceTolerance8_half F η hη1 hd) _ hr m _ hx,
    flatScaledKernelRow8_partition _ hr,hs]
  calc
    _ = |(scaledKernelRow8 (curvedFarRieszFour8 F (2*R/(m:ℝ))) m (cubeNode 8 m v)-
        scaledKernelRow8 (farObliqueRieszFour 8 e8Map (2*R/(m:ℝ))) m (cubeNode 8 m v))+
      (scaledKernelRow8 (curvedNearRieszFour F (R/(m:ℝ))) m (cubeNode 8 m v)-
        scaledKernelRow8 (nearObliqueRieszFour 8 e8Map (R/(m:ℝ))) m (cubeNode 8 m v))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (|scaledKernelRow8 (curvedFarRieszFour8 F (2*R/(m:ℝ))) m (cubeNode 8 m v)|+
        |scaledKernelRow8 (farObliqueRieszFour 8 e8Map (2*R/(m:ℝ))) m (cubeNode 8 m v)|)+
      64*η*curvedNearRowComparisonConstant8 R := add_le_add (abs_sub _ _) hn
    _ ≤ (Cg/(2*R)^2+Cf/(2*R)^2)+64*η*curvedNearRowComparisonConstant8 R :=
      add_le_add (add_le_add hg' hf') le_rfl
    _ ≤ _ := by
      rw [← add_div]
      exact add_le_add
        (div_le_div_of_nonneg_left (add_nonneg hCg hCf) (by positivity) (by nlinarith [sq_nonneg R])) le_rfl

theorem curvedFullRowMean8_comparison_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1/2 → CurvedRelativeE8DistanceTolerance8 F η →
      ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, 8 ≤ m →
      |curvedFullRowMean8 F m-e8FullRowMean m| ≤ C/R^2+64*η*curvedNearRowComparisonConstant8 R := by
  obtain ⟨C,hC,hb⟩ := curvedFullRow8_comparison_bound
  refine ⟨C,hC,?_⟩
  intro F hF η hη hη1 hd R hR m hm
  rw [curvedFullRowMean8,← flatScaledKernelRowMean8_eq,← cubeQuadrature_sub]
  exact cubeQuadrature_abs_le_nodes8 m hm _ _ (fun v => hb F hF η hη hη1 hd R hR m hm v)

end SphericalRiesz
