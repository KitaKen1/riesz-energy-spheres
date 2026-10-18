import Riesz.FCLeechModular24
import Riesz.FCLeechMinimum24

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SphericalRiesz

private theorem leechLattice_eq_generator_span : leechLattice = LeechLattice := by
  unfold leechLattice LeechLattice
  congr 1
  congr 1
  funext i
  rw [leechEuclideanBasis_apply, leechGeneratorRows_eq]

def leechShellIndex (x : leechLattice) : ℕ := Classical.choose (leechLattice_even x)

theorem leechShellIndex_norm_sq (x : leechLattice) :
    ‖(x : LeechAmbient)‖ ^ 2 = 2 * (leechShellIndex x : ℝ) :=
  Classical.choose_spec (leechLattice_even x)

theorem leechShellIndex_zero_iff (x : leechLattice) : leechShellIndex x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hn : ‖(x : LeechAmbient)‖ ^ 2 = 0 := by rw [leechShellIndex_norm_sq, h]; norm_num
    apply Subtype.ext
    simpa using hn
  · rintro rfl
    have h := leechShellIndex_norm_sq (0 : leechLattice)
    simpa using h.symm

theorem leechShellIndex_finite (n : ℕ) : (leechShellIndex ⁻¹' {n}).Finite := by
  apply (leechLattice_finite_norm_lt (2 * (n : ℝ) + 1)).subset
  intro x hx
  have hi : leechShellIndex x = n := hx
  have hn := leechShellIndex_norm_sq x
  rw [hi] at hn
  change ‖(x : LeechAmbient)‖ < 2 * (n : ℝ) + 1
  nlinarith [norm_nonneg (x : LeechAmbient), Nat.cast_nonneg (α := ℝ) n]

def leechShellCount (n : ℕ) : ℕ := Nat.card (leechShellIndex ⁻¹' {n})

theorem leechTheta_term_eq_qpow (τ : UpperHalfPlane) (x : leechLattice) :
    leechLatticeThetaTerm τ x = Function.Periodic.qParam 1 τ ^ leechShellIndex x := by
  unfold leechLatticeThetaTerm
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [leechShellIndex_norm_sq]
  push_cast
  ring

theorem leechTheta_shell_hasSum (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (leechShellCount n : ℂ) • Function.Periodic.qParam 1 τ ^ n)
      (leechThetaUpper τ) := by
  have h := (leechLatticeThetaTerm_summable τ.im_pos).hasSum.tsum_fiberwise leechShellIndex
  apply h.congr_fun
  intro n
  letI : Fintype (leechShellIndex ⁻¹' {n}) := (leechShellIndex_finite n).fintype
  have ht : (fun x : leechShellIndex ⁻¹' {n} => leechLatticeThetaTerm τ x) =
      fun _ : leechShellIndex ⁻¹' {n} => Function.Periodic.qParam 1 τ ^ n := by
    funext x
    rw [leechTheta_term_eq_qpow, show leechShellIndex x = n from x.property]
  rw [ht, tsum_const]
  simp [leechShellCount, nsmul_eq_mul]

theorem leechShellCount_eq_qcoeff (n : ℕ) : (leechShellCount n : ℂ) =
    (UpperHalfPlane.qExpansion 1 leechThetaUpper).coeff n :=
  UpperHalfPlane.qExpansion_coeff_unique (h := 1)
    (c := fun m => (leechShellCount m : ℂ)) leechThetaModularForm (by norm_num)
    leechThetaUpper_cusp_analytic leechTheta_shell_hasSum n

theorem leechShellCount_one : leechShellCount 1 = 0 := by
  have he : leechShellIndex ⁻¹' {1} = (∅ : Set leechLattice) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro hi
    have hn := leechShellIndex_norm_sq x
    rw [hi] at hn
    norm_num at hn
    have hx : (x : LeechAmbient) ≠ 0 := by intro h; simp [h] at hn
    have hb := leech_norm_lower_bound x (by rw [← leechLattice_eq_generator_span]; exact x.property) hx
    nlinarith [norm_nonneg (x : LeechAmbient)]
  simp [leechShellCount, he]

theorem leechThetaUpper_qExpansion_one :
    (UpperHalfPlane.qExpansion 1 leechThetaUpper).coeff 1 = 0 := by
  rw [← leechShellCount_eq_qcoeff, leechShellCount_one]
  norm_num

end SphericalRiesz
