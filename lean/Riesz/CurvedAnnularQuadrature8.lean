import Riesz.CurvedAnnularComposition8
import Riesz.AnnularQuadrature

/-! Local smoothness suffices for the original corrected coordinate nodes.
The regularized kernel is globally continuous and has actual local sixth
derivatives on the cube. Its coordinate support is unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem sixth_coordinate_within_abs_le_of_contDiffAt (d : ℕ)
    {F : (Fin d → ℝ) → ℝ} (i : Fin d) (v : Fin d → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hf : ContDiffAt ℝ 6 F (Function.update v i t)) :
    |iteratedDerivWithin 6 (fun u => F (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤
      ‖iteratedFDeriv ℝ 6 F (Function.update v i t)‖ := by
  let g : ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i
  let a := Function.update v i 0
  let H : (Fin d → ℝ) → ℝ := fun z => F (z+a)
  have hepoint : g t+a = Function.update v i t := (coordinate_update_as_line d i v t).symm
  have hH : ContDiffAt ℝ 6 H (g t) := by
    apply ContDiffAt.comp (g := F) (f := fun z => z+a) (g t)
    · rw [hepoint]; exact hf
    · fun_prop
  have heq : (fun u => F (Function.update v i u)) = H ∘ g := by
    funext u
    rw [coordinate_update_as_line]
    rfl
  obtain ⟨U,hU,hgtU,hHU⟩ := hH.contDiffOn' le_rfl (by simp)
  have hHU' : ContDiffOn ℝ 6 H U := by simpa using hHU
  have hp : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hline := g.iteratedFDerivWithin_comp_right hHU' hU.uniqueDiffOn hp.uniqueDiffOn hgtU
    (i := 6) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 6 hp hgtU,
    iteratedFDerivWithin_of_isOpen 6 hU hgtU] at hline
  rw [heq,iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hH.comp t g.contDiff.contDiffAt) ht,← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,hline]
  have hshift : iteratedFDeriv ℝ 6 H (g t) = iteratedFDeriv ℝ 6 F (Function.update v i t) := by
    dsimp only [H]
    rw [iteratedFDeriv_comp_add_right,hepoint]
  rw [hshift]
  have hnorm : ‖g‖ = 1 := ContinuousLinearMap.norm_single ℝ (fun _ : Fin d => ℝ) i
  simpa only [hnorm,Finset.prod_const_one,mul_one] using
    (iteratedFDeriv ℝ 6 F (Function.update v i t)).norm_compContinuousLinearMap_le (fun _ => g)

theorem regularizedCurvedAnnular8_continuous (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (r δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) (x : Fin 8 → ℝ) :
    Continuous (regularizedCurvedAnnular8 F r δ R hδ hR x) := by
  exact continuous_const.mul ((curvedAnnularAuxiliary8_contDiff δ R hδ hR).continuous.comp
    (((hF.sub continuous_const).const_smul r⁻¹).prodMk
      ((continuous_id.sub continuous_const).const_smul r⁻¹)))

theorem regularizedCurvedAnnular8_zero_outside (F : (Fin 8 → ℝ) → Ambient9)
    (r δ R : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hR : 0 < R) (x y : Fin 8 → ℝ)
    (hn : ¬ ∀ i, |y i-x i| ≤ 2*r) : regularizedCurvedAnnular8 F r δ R hδ hR x y = 0 := by
  unfold regularizedCurvedAnnular8 curvedAnnularAuxiliary8 curvedAnnularPair8
  rw [unitAnnularCutoff_zero_outside 8 _ (scaled_annular_argument_norm 8 r hr x y hn).le,
    mul_zero,mul_zero]

theorem regularizedCurvedAnnular8_sixth_zero_outside (F : (Fin 8 → ℝ) → Ambient9)
    (r δ R : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hR : 0 < R) (x y : Fin 8 → ℝ)
    (hn : ¬ ∀ i, |y i-x i| ≤ 2*r) :
    iteratedFDeriv ℝ 6 (regularizedCurvedAnnular8 F r δ R hδ hR x) y = 0 := by
  have hny := scaled_annular_argument_norm 8 r hr x y hn
  have hc : Continuous (fun z : Fin 8 → ℝ => ‖r⁻¹ • (z-x)‖) := by fun_prop
  have he : regularizedCurvedAnnular8 F r δ R hδ hR x =ᶠ[nhds y] 0 := by
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hny] with z hz
    unfold regularizedCurvedAnnular8 curvedAnnularAuxiliary8 curvedAnnularPair8
    rw [unitAnnularCutoff_zero_outside 8 _ hz.le,mul_zero,mul_zero]
    rfl
  simpa using (he.iteratedFDeriv ℝ 6).eq_of_nhds

theorem regularizedCurvedAnnular8_quadrature_bound (δ R B : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, Continuous F →
      (∀ y ∈ UnitCube 8, ContDiffAt ℝ ∞ F y ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ 6 → ‖iteratedFDeriv ℝ k F y‖ ≤ B) →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (regularizedCurvedAnnular8 F r δ R hδ hR x)-
        cubeIntegral 8 (regularizedCurvedAnnular8 F r δ R hδ hR x)| ≤
        (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := by
  obtain ⟨C,hC,hb⟩ := regularizedCurvedAnnular8_sixth_bounded δ R B hδ hR hB
  refine ⟨C,hC,?_⟩
  intro F hF hFb m hm r hr hr1 x
  let f := regularizedCurvedAnnular8 F r δ R hδ hR x
  have hloc : ∀ y ∈ UnitCube 8, ContDiffAt ℝ 6 f y := by
    intro y hy
    exact (regularizedCurvedAnnular8_contDiffAt F r δ R hδ hR x y (hFb y hy).1).of_le (by simp)
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
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤ C/r^10 := by
    intro i v hv t ht
    exact (sixth_coordinate_within_abs_le_of_contDiffAt 8 i v t ht
      (hloc _ (update_mem_unitCube hv i ht))).trans
        (hb F r hr hr1 x _ (hFb _ (update_mem_unitCube hv i ht)).1
          (hFb _ (update_mem_unitCube hv i ht)).2)
  have hsupport : ∀ y ∈ UnitCube 8, (¬ ∀ i, |y i-x i| ≤ 2*r) → f y = 0 :=
    fun y _ hn => regularizedCurvedAnnular8_zero_outside F r δ R hr hδ hR x y hn
  have hDsupport : ∀ i v, v ∈ UnitCube 8 → ∀ t ∈ Icc (0:ℝ) 1,
      (¬ ∀ j, |Function.update v i t j-x j| ≤ 2*r) →
      iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Icc (0:ℝ) 1) t = 0 := by
    intro i v hv t ht hn
    apply abs_nonpos_iff.mp
    have h := sixth_coordinate_within_abs_le_of_contDiffAt 8 i v t ht
      (hloc _ (update_mem_unitCube hv i ht))
    rw [regularizedCurvedAnnular8_sixth_zero_outside F r δ R hr hδ hR x _ hn,norm_zero] at h
    exact h
  have h := cubeQuadrature_local_sixth_order_bound 8 hm x (2*r) (C/r^10)
    (by positivity) (by positivity) (regularizedCurvedAnnular8_continuous F hF r δ R hδ hR x)
    hs hbound hsupport hDsupport
  simpa only [show 2*(2*r) = 4*r by ring,Nat.cast_ofNat] using h

theorem regularizedCurvedAnnular8_resolved_bound (δ R B : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, Continuous F →
      (∀ y ∈ UnitCube 8, ContDiffAt ℝ ∞ F y ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ 6 → ‖iteratedFDeriv ℝ k F y‖ ≤ B) →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → r ≤ 2 → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (regularizedCurvedAnnular8 F r δ R hδ hR x)-
        cubeIntegral 8 (regularizedCurvedAnnular8 F r δ R hδ hR x)| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := regularizedCurvedAnnular8_quadrature_bound δ R B hδ hR hB
  refine ⟨859963392*C,by positivity,?_⟩
  intro F hF hFb m hm r hr hr1 hmesh x
  have hrad : 4*r+2/(m:ℝ) ≤ 6*r := by
    rw [show 2/(m:ℝ) = 2*(1/(m:ℝ)) by ring]
    linarith
  calc
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := hb F hF hFb m hm r hr hr1 x
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(6*r)^8*(C/r^10) := by gcongr
    _ = (859963392*C)/((m:ℝ)^6*r^2) := by
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp [hr.ne',hm0]
      ring

end SphericalRiesz
