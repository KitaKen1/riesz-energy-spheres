import Riesz.EqualAreaPatchRow8

/-! Actual off-diagonal pair energy, its exact neutralization identity,
and stability of the known flat E8 coefficient on every small equal-area
patch. This is still coordinate Lebesgue background on one patch;
global sphere recovery and probability-density conversion are separate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

def curvedOriginalPairEnergy8 (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) : ℝ :=
  ∑ v : Fin 8 → NodeIndex m, ∑ w ∈ Finset.univ.erase v,
    curvedRieszFour F (cubeNode 8 m v) (cubeNode 8 m w)

theorem curvedOriginalPairEnergy8_eq_full (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) :
    curvedOriginalPairEnergy8 F m = ∑ v : Fin 8 → NodeIndex m, ∑ w : Fin 8 → NodeIndex m,
      curvedRieszFour F (cubeNode 8 m v) (cubeNode 8 m w) := by
  classical
  unfold curvedOriginalPairEnergy8
  apply Finset.sum_congr rfl
  intro v _
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 8 → NodeIndex m))
    (fun w => curvedRieszFour F (cubeNode 8 m v) (cubeNode 8 m w)) (Finset.mem_univ v)
  simpa only [curvedRieszFour,dist_self,inv_zero,zero_pow (by norm_num : (4:ℕ) ≠ 0),add_zero] using h

theorem curvedOriginalPairEnergy8_quadrature (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) :
    cubeQuadrature 8 m (fun x => cubeQuadrature 8 m (curvedRieszFour F x)) =
      curvedOriginalPairEnergy8 F m/(m:ℝ)^16 := by
  simp_rw [cubeQuadrature_as_node_sum]
  rw [← Finset.sum_div,div_div,← pow_add,curvedOriginalPairEnergy8_eq_full]

theorem curvedFullRowMean8_pair_identity (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) :
    curvedFullRowMean8 F m = (m:ℝ)^4*
      (curvedOriginalPairEnergy8 F m/(m:ℝ)^16-cubeQuadrature 8 m (curvedPotential8 F)) := by
  change cubeQuadrature 8 m (fun x => (m:ℝ)^4*(cubeQuadrature 8 m (curvedRieszFour F x)-curvedPotential8 F x)) = _
  rw [cubeQuadrature_const_mul,cubeQuadrature_sub,curvedOriginalPairEnergy8_quadrature]

def curvedNeutralizedEnergy8 (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) : ℝ :=
  (m:ℝ)^4*(curvedOriginalPairEnergy8 F m/(m:ℝ)^16-
    2*cubeQuadrature 8 m (curvedPotential8 F)+∫ x in UnitCube 8, curvedPotential8 F x)

theorem curvedNeutralizedEnergy8_identity (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) :
    curvedNeutralizedEnergy8 F m = curvedFullRowMean8 F m-curvedBackground8 F m := by
  rw [curvedFullRowMean8_pair_identity]
  unfold curvedNeutralizedEnergy8 curvedBackground8
  ring

/-- The known flat answer is reused; no second Epstein computation and
no new optimized near-node count occurs in this proof. -/
theorem equalAreaPatchNeutralized8_uniform_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ M : ℕ, 8 ≤ M ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, M ≤ m →
      |curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch g v c ε) m-(-5*Real.pi^2/6)| < δ := by
  obtain ⟨ρR,hρR,hρRb,MR,hMR,hR⟩ := equalAreaPatchFullRowMean8_uniform_small (δ/2) (half_pos hδ)
  obtain ⟨ρB,hρB,_hρBb,MB,_hMB,hB⟩ := equalAreaPatchBackground8_uniform_small (δ/2) (half_pos hδ)
  refine ⟨min ρR ρB,lt_min hρR hρB,(min_le_left _ _).trans hρRb,
    max MR MB,hMR.trans (le_max_left _ _),?_⟩
  intro v hv ε hε hs g c hc m hm
  have hr := hR v (hv.trans (min_le_left _ _)) ε hε (hs.trans (min_le_left _ _)) g c hc
    m ((le_max_left _ _).trans hm)
  have hb := hB v (hv.trans (min_le_right _ _)) ε hε (hs.trans (min_le_right _ _)) g c hc
    m ((le_max_right _ _).trans hm)
  rw [curvedNeutralizedEnergy8_identity]
  calc
    _ = |(curvedFullRowMean8 (equalAreaNormalizedE8Patch g v c ε) m-(-5*Real.pi^2/6))-
      curvedBackground8 (equalAreaNormalizedE8Patch g v c ε) m| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ < δ := by linarith

theorem equalAreaPatchNeutralized8_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8) :
    Tendsto (fun m : ℕ => curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m)) m)
      atTop (𝓝 (-5*Real.pi^2/6)) := by
  simp_rw [curvedNeutralizedEnergy8_identity]
  simpa only [sub_zero] using (equalAreaPatchFullRowMean8_limit_along g v c e hv he hp hc).sub
    (equalAreaPatchBackground8_limit_along g v c e hv he hp hc)

theorem equalAreaPatchNeutralized8_normalized_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8) :
    Tendsto (fun m : ℕ => curvedNeutralizedEnergy8
      (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m)) m/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact (equalAreaPatchNeutralized8_limit_along g v c e hv he hp hc).div_const _

end SphericalRiesz
