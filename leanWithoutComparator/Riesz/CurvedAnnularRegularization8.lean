import Riesz.EqualAreaPatchClass8
import Riesz.AnnularCutoff
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! A fixed smooth kernel in the product of ambient and coordinate spaces.
The ambient regularization agrees with the inverse fourth power on a fixed
annulus. Compact support bounds all six derivatives simultaneously. -/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SphericalRiesz

def ambientInverseFourth8 (z : Ambient9) : ℝ := ‖z‖⁻¹^4

theorem ambientInverseFourth8_contDiffAt (z : Ambient9) (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ ambientInverseFourth8 z := by
  have heq : ambientInverseFourth8 = fun w : Ambient9 => 1/(‖w‖^2)^2 := by
    funext w
    simp only [ambientInverseFourth8,one_div,inv_pow]
    congr 1
    ring
  rw [heq]
  exact contDiffAt_const.div ((contDiff_id.norm_sq (𝕜 := ℝ)).contDiffAt.pow 2)
    (pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)))

def ambientInnerBump8 (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Ambient9) :=
  ⟨δ/2,δ,by positivity,by linarith⟩

def ambientOuterBump8 (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : Ambient9) :=
  ⟨R,2*R,hR,by linarith⟩

def ambientRegularizedInverseFourth8 (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (z : Ambient9) : ℝ :=
  ambientInverseFourth8 z*(ambientOuterBump8 R hR z-ambientInnerBump8 δ hδ z)

theorem ambientRegularizedInverseFourth8_contDiff (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (ambientRegularizedInverseFourth8 δ R hδ hR) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(ambientOuterBump8 R hR).eventuallyEq_one,
      (ambientInnerBump8 δ hδ).eventuallyEq_one] with z ho hi
    simp [ambientRegularizedInverseFourth8,ho,hi]
  · exact (ambientInverseFourth8_contDiffAt z hz).mul
      ((ambientOuterBump8 R hR).contDiffAt.sub (ambientInnerBump8 δ hδ).contDiffAt)

theorem ambientRegularizedInverseFourth8_hasCompactSupport (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    HasCompactSupport (ambientRegularizedInverseFourth8 δ R hδ hR) :=
  ((ambientOuterBump8 R hR).hasCompactSupport.sub
    (ambientInnerBump8 δ hδ).hasCompactSupport).mul_left

theorem ambientRegularizedInverseFourth8_eq (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (z : Ambient9) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    ambientRegularizedInverseFourth8 δ R hδ hR z = ambientInverseFourth8 z := by
  have ho : ambientOuterBump8 R hR z = 1 :=
    (ambientOuterBump8 R hR).one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right,ambientOuterBump8] using hzR)
  have hi : ambientInnerBump8 δ hδ z = 0 :=
    (ambientInnerBump8 δ hδ).zero_of_le_dist (by
      simpa only [dist_zero_right,ambientInnerBump8] using hzδ)
  simp [ambientRegularizedInverseFourth8,ho,hi]

theorem unitAnnularCutoff_contDiff (d : ℕ) : ContDiff ℝ ∞ (unitAnnularCutoff d) :=
  (outerUnitBump d).contDiff.sub (innerUnitBump d).contDiff

theorem unitAnnularCutoff_hasCompactSupport (d : ℕ) :
    HasCompactSupport (unitAnnularCutoff d) :=
  (outerUnitBump d).hasCompactSupport.sub (innerUnitBump d).hasCompactSupport

def curvedAnnularAuxiliary8 (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (p : Ambient9 × (Fin 8 → ℝ)) : ℝ :=
  ambientRegularizedInverseFourth8 δ R hδ hR p.1*unitAnnularCutoff 8 p.2

theorem curvedAnnularAuxiliary8_contDiff (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (curvedAnnularAuxiliary8 δ R hδ hR) :=
  ((ambientRegularizedInverseFourth8_contDiff δ R hδ hR).comp contDiff_fst).mul
    ((unitAnnularCutoff_contDiff 8).comp contDiff_snd)

theorem curvedAnnularAuxiliary8_hasCompactSupport (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    HasCompactSupport (curvedAnnularAuxiliary8 δ R hδ hR) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((ambientRegularizedInverseFourth8_hasCompactSupport δ R hδ hR).isCompact.prod
      (unitAnnularCutoff_hasCompactSupport 8).isCompact)
  intro p hp
  have hn := mul_ne_zero_iff.mp (Function.mem_support.mp hp)
  exact ⟨subset_tsupport _ (Function.mem_support.mpr hn.1),
    subset_tsupport _ (Function.mem_support.mpr hn.2)⟩

theorem curvedAnnularAuxiliary8_derivatives_bounded (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 6, ∀ p : Ambient9 × (Fin 8 → ℝ),
      ‖iteratedFDeriv ℝ k (curvedAnnularAuxiliary8 δ R hδ hR) p‖ ≤ C :=
  (curvedAnnularAuxiliary8_hasCompactSupport δ R hδ hR).exists_bound_iteratedFDeriv
    (curvedAnnularAuxiliary8_contDiff δ R hδ hR) 6

/-- Local smoothness of the inner map suffices; it need not extend to a
globally smooth sphere chart. -/
theorem norm_iteratedFDeriv_comp_le_of_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {g : F → ℝ} {x : E} {n : ℕ} {C D : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiff ℝ n g)
    (hC : ∀ k ≤ n, ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C)
    (hD : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ D^k) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial*C*D^n := by
  obtain ⟨U,hU,hxU,hfU⟩ := hf.contDiffOn' le_rfl (by simp)
  have hfU' : ContDiffOn ℝ n f U := by simpa using hfU
  have h := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hfU' le_rfl
    uniqueDiffOn_univ hU.uniqueDiffOn (fun _ _ => mem_univ _) hxU
    (C := C) (D := D)
    (fun k hk => by simpa only [iteratedFDerivWithin_univ] using hC k hk)
    (fun k hk hkn => by
      simpa only [iteratedFDerivWithin_of_isOpen k hU hxU] using hD k hk hkn)
  simpa only [iteratedFDerivWithin_of_isOpen n hU hxU] using h

end SphericalRiesz
