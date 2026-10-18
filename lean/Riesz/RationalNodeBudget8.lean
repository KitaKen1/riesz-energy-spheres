import Riesz.RationalScale8

/-! Exact allocation to the original corrected quadrature indices. This
constructs a finite index budget, not a global physical configuration: residual
points and cross-patch energy estimates remain separate. -/

set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz
open Boundary

abbrev rationalCubeNodeIndex8 (K p q m : ℕ) : Type :=
  (Fin K × (Fin 8 → NodeIndex (p*m))) ⊕ Fin ((q^8-K*p^8)*m^8)

theorem rationalCubeNodeBudget8_identity (K p q m : ℕ) (hbudget : K*p^8 ≤ q^8) :
    K*(p*m)^8+(q^8-K*p^8)*m^8 = (q*m)^8 := by
  rw [mul_pow,mul_pow]
  calc
    K*(p^8*m^8)+(q^8-K*p^8)*m^8 = (K*p^8+(q^8-K*p^8))*m^8 := by ring
    _ = q^8*m^8 := by rw [Nat.add_sub_of_le hbudget]

theorem rationalCubeNodeBudget8_positive (K p q m : ℕ)
    (hbudget : K*p^8 < q^8) (hm : 0 < m) : 0 < (q^8-K*p^8)*m^8 := by
  exact mul_pos (Nat.sub_pos_of_lt hbudget) (pow_pos hm _)

theorem rationalCubeNodeBudget8_patch_ratio (p q m : ℕ) (hm : 0 < m) :
    (((p*m)^8 : ℕ) : ℝ)/(((q*m)^8 : ℕ) : ℝ) = ((p : ℝ)/q)^8 := by
  rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_mul,Nat.cast_mul,← div_pow]
  rw [mul_div_mul_right _ _ (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')]

theorem rationalCubeNodeBudget8_residual_ratio (K p q m : ℕ)
    (hq : 0 < q) (hm : 0 < m) (hbudget : K*p^8 ≤ q^8) :
    ((((q^8-K*p^8)*m^8 : ℕ) : ℝ)/(((q*m)^8 : ℕ) : ℝ)) =
      1-(K : ℝ)*((p : ℝ)/q)^8 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm0 : (m : ℝ)^8 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  rw [Nat.cast_mul,Nat.cast_sub hbudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,
    Nat.cast_pow,Nat.cast_pow,Nat.cast_mul,mul_pow,mul_div_mul_right _ _ hm0]
  rw [sub_div,div_self (pow_ne_zero _ hq0),div_pow,mul_div_assoc]

theorem rationalPatchNodeIndex8_card (p m : ℕ) (hp : 0 < p) (hm : 8 ≤ m) :
    Fintype.card (Fin 8 → NodeIndex (p*m)) = (p*m)^8 := by
  have hpm : 8 ≤ p*m := hm.trans (Nat.le_mul_of_pos_left m hp)
  rw [Fintype.card_fun,nodeIndex_card hpm,Fintype.card_fin]

theorem rationalCubeNodeIndex8_card (K p q m : ℕ) (hp : 0 < p) (hm : 8 ≤ m)
    (hbudget : K*p^8 ≤ q^8) :
    Fintype.card (rationalCubeNodeIndex8 K p q m) = (q*m)^8 := by
  change Fintype.card ((Fin K × (Fin 8 → NodeIndex (p*m))) ⊕
    Fin ((q^8-K*p^8)*m^8)) = (q*m)^8
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    rationalPatchNodeIndex8_card p m hp hm,Fintype.card_fin]
  exact rationalCubeNodeBudget8_identity K p q m hbudget

end SphericalRiesz
