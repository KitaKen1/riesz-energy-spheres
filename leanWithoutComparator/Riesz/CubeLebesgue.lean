import Riesz.CubeQuadrature
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The nested cube integral is the actual Lebesgue integral

The recursive interval integral used by the original quadrature is
identified with product Lebesgue measure, not declared as a new measure.
The proof uses the standard finite-coordinate measurable equivalence
and Fubini on actual compact rectangles.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem unitCube_eq_pi (d : ℕ) :
    UnitCube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0:ℝ) 1) := by
  ext v
  simp [UnitCube, Pi.le_def, ← forall_and]

theorem unitCube_isCompact (d : ℕ) : IsCompact (UnitCube d) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem unitCube_measurableSet (d : ℕ) : MeasurableSet (UnitCube d) :=
  (unitCube_isCompact d).measurableSet

theorem unitCube_volume (d : ℕ) : volume (UnitCube d) = 1 := by
  rw [unitCube_eq_pi, volume_pi_pi]
  simp

def cubeConsEquiv (d : ℕ) : (ℝ × (Fin d → ℝ)) ≃ᵐ (Fin (d+1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm

theorem cubeConsEquiv_apply (d : ℕ) (p : ℝ × (Fin d → ℝ)) :
    cubeConsEquiv d p = Fin.cons p.1 p.2 := by
  simp [cubeConsEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv_zero, Fin.consEquiv]

theorem cubeConsEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (cubeConsEquiv d) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm

theorem cubeConsEquiv_image (d : ℕ) :
    cubeConsEquiv d '' ((Set.Icc (0:ℝ) 1).prod (UnitCube d)) = UnitCube (d+1) := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [cubeConsEquiv_apply]
    exact cons_mem_unitCube hp.1 hp.2
  · intro hv
    refine ⟨(v 0, Fin.tail v), ⟨hv 0, fun i => hv i.succ⟩, ?_⟩
    rw [cubeConsEquiv_apply]
    exact Fin.cons_self_tail v

set_option backward.isDefEq.respectTransparency false in
/-- The order agrees with cubeIntegral: first coordinate integrated first. -/
theorem unitCube_setIntegral_succ (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ)
    (hf : Continuous f) :
    (∫ v in UnitCube (d+1), f v) =
      ∫ v in UnitCube d, ∫ t in (0:ℝ)..1, f (Fin.cons t v) := by
  let g : ℝ × (Fin d → ℝ) → ℝ := fun p => f (Fin.cons p.1 p.2)
  have hg : Continuous g := hf.comp (by fun_prop)
  have heq := (cubeConsEquiv_measurePreserving d).setIntegral_image_emb
    (cubeConsEquiv d).measurableEmbedding f ((Set.Icc (0:ℝ) 1).prod (UnitCube d))
  rw [cubeConsEquiv_image] at heq
  simp only [cubeConsEquiv_apply] at heq
  rw [heq]
  change (∫ p in (Set.Icc (0:ℝ) 1).prod (UnitCube d), g p) = _
  rw [Measure.volume_eq_prod]
  refine (setIntegral_prod_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin d → ℝ))) (Set.Icc (0:ℝ) 1) (UnitCube d) g).symm.trans ?_
  have hgswap : Continuous (fun p : (Fin d → ℝ) × ℝ => g p.swap) :=
    hg.comp continuous_swap
  have hiswap : IntegrableOn (fun p : (Fin d → ℝ) × ℝ => g p.swap)
      ((UnitCube d).prod (Set.Icc (0:ℝ) 1)) (volume.prod volume) := by
    exact hgswap.continuousOn.integrableOn_compact ((unitCube_isCompact d).prod isCompact_Icc)
  rw [setIntegral_prod _ hiswap]
  apply setIntegral_congr_fun (unitCube_measurableSet d)
  intro v _
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rfl

theorem cubeIntegral_eq_setIntegral (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    cubeIntegral d f = ∫ v in UnitCube d, f v := by
  induction d with
  | zero =>
    have hcube : UnitCube 0 = Set.univ := by ext v; simp [UnitCube]
    rw [hcube, setIntegral_univ, Measure.volume_pi_eq_dirac Fin.elim0, integral_dirac]
    rfl
  | succ d ih =>
    rw [unitCube_setIntegral_succ d f hf]
    exact ih _ (continuous_unitIntegral_param (hf.comp (by fun_prop)))

/-- The actual far kernels need continuity only on the cube. -/
theorem cubeIntegral_eq_setIntegral_on (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (UnitCube d)) : cubeIntegral d f = ∫ v in UnitCube d, f v := by
  have heq : Set.EqOn (fun v => f (cubeClamp d v)) f (UnitCube d) := fun v hv => by
    dsimp only
    rw [cubeClamp_eq hv]
  calc
    _ = cubeIntegral d (fun v => f (cubeClamp d v)) := cubeIntegral_congr d heq.symm
    _ = ∫ v in UnitCube d, f (cubeClamp d v) :=
      cubeIntegral_eq_setIntegral d _ (continuous_cube_extension hf)
    _ = _ := setIntegral_congr_fun (unitCube_measurableSet d) heq

#print axioms unitCube_volume
#print axioms cubeConsEquiv_measurePreserving
#print axioms unitCube_setIntegral_succ
#print axioms cubeIntegral_eq_setIntegral
#print axioms cubeIntegral_eq_setIntegral_on

end SphericalRiesz.Boundary
