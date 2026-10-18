import Riesz.BoundaryTwelveNodes
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Boundary

open Polynomial

def twelvePolynomial : Polynomial ℝ :=
    .X^10 +
    .C ((-16383628163025960173568000 : ℝ)/88580102706155225088000) * .X^9 +
    .C ((1305098710951201031061504000 : ℝ)/88580102706155225088000) * .X^8 +
    .C ((-58595821582661129791025971200 : ℝ)/88580102706155225088000) * .X^7 +
    .C ((1628674182455459972494078771200 : ℝ)/88580102706155225088000) * .X^6 +
    .C ((-28955939893651903339943401881600 : ℝ)/88580102706155225088000) * .X^5 +
    .C ((328054656551266082828093090365440 : ℝ)/88580102706155225088000) * .X^4 +
    .C ((-2278162143669404848060135276093440 : ℝ)/88580102706155225088000) * .X^3 +
    .C ((8842999522732027085544585105582720 : ℝ)/88580102706155225088000) * .X^2 +
    .C ((-15431811328675648799843640757655952 : ℝ)/88580102706155225088000) * .X^1 +
    .C ((5287828609222057732836140870456497 : ℝ)/88580102706155225088000) * .X^0

theorem twelvePolynomial_eval (x : ℝ) :
    twelvePolynomial.eval x = twelveCandidateP x / 88580102706155225088000 := by
  simp [twelvePolynomial, twelveCandidateP]
  ring

theorem twelvePolynomial_node (i : Fin 10) : twelvePolynomial.eval (twelveCandidateNode i) = 0 := by
  rw [twelvePolynomial_eval, (twelveCandidateNode_spec i).2.2]
  norm_num

theorem twelvePolynomial_natDegree : twelvePolynomial.natDegree = 10 := by
  unfold twelvePolynomial
  compute_degree <;> norm_num

theorem twelvePolynomial_monic : twelvePolynomial.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, twelvePolynomial_natDegree]
  norm_num [twelvePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]

def twelveRoots : Multiset ℝ := Finset.univ.val.map twelveCandidateNode

theorem twelvePolynomial_roots : twelvePolynomial.roots = twelveRoots := by
  classical
  let e : Fin 10 ↪ ℝ := ⟨twelveCandidateNode, twelveCandidateNode_injective⟩
  have h := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    (p := twelvePolynomial) (S := Finset.univ.map e) (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact twelvePolynomial_node i) (by simp [twelvePolynomial_natDegree])
    twelvePolynomial_monic.ne_zero
  exact h

theorem twelvePolynomial_factor :
    twelvePolynomial = ∏ i : Fin 10, (.X - .C (twelveCandidateNode i)) := by
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    twelvePolynomial_monic (by rw [twelvePolynomial_roots]; simp [twelveRoots,twelvePolynomial_natDegree])
  rw [twelvePolynomial_roots] at h
  simpa [twelveRoots, Multiset.map_map, Finset.prod] using h.symm

def twelveElementary (k : ℕ) : ℝ := (-1)^k * twelvePolynomial.coeff (10-k)

theorem twelveElementary_eq (k : ℕ) (hk : k ≤ 10) :
    MvPolynomial.aeval twelveCandidateNode (MvPolynomial.esymm (Fin 10) ℝ k) =
      twelveElementary k := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  change twelveRoots.esymm k = twelveElementary k
  have h := Polynomial.coeff_eq_esymm_roots_of_card
    (p := twelvePolynomial) (by rw [twelvePolynomial_roots]; simp [twelveRoots,twelvePolynomial_natDegree])
    (k := 10-k) (by rw [twelvePolynomial_natDegree]; omega)
  rw [twelvePolynomial_monic.leadingCoeff,twelvePolynomial_natDegree,twelvePolynomial_roots] at h
  have hsub : 10-(10-k)=k := by omega
  rw [hsub,one_mul] at h
  unfold twelveElementary
  rw [h]
  simp [← mul_assoc, ← pow_add, Even.neg_one_pow (show Even (k+k) from ⟨k,rfl⟩)]

def twelvePowerSum (k : ℕ) : ℝ := ∑ i : Fin 10, twelveCandidateNode i ^ k

theorem twelvePowerSum_newton (k : ℕ) (hk : 0 < k) (hk10 : k ≤ 10) :
    twelvePowerSum k = (-1)^(k+1) * k * twelveElementary k -
      ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1)^a.1 * twelveElementary a.1 * twelvePowerSum a.2 := by
  have h := congrArg (MvPolynomial.aeval twelveCandidateNode)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin 10) ℝ k hk)
  simp only [map_sub,map_mul,map_pow,map_neg,map_one,map_natCast,map_sum] at h
  simp only [MvPolynomial.psum, map_sum, map_pow,MvPolynomial.aeval_X] at h
  rw [twelveElementary_eq k hk10] at h
  change twelvePowerSum k = _ at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [twelveElementary_eq a.1 (by
    have hmem := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp hmem.1
    omega)]
  rfl

theorem twelvePowerSum_1 : twelvePowerSum 1 = (4439/24 : ℝ) := by
  have h := twelvePowerSum_newton 1 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 1 | a.1 ∈ Set.Ioo 0 1} =
      (∅ : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X] at h
  exact h

theorem twelvePowerSum_2 : twelvePowerSum 2 = (9485/2 : ℝ) := by
  have h := twelvePowerSum_newton 2 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} =
      ({(1,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1] at h
  exact h

theorem twelvePowerSum_3 : twelvePowerSum 3 = (131113207/960 : ℝ) := by
  have h := twelvePowerSum_newton 3 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} =
      ({(1,2),(2,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2] at h
  exact h

theorem twelvePowerSum_4 : twelvePowerSum 4 = (33531029/8 : ℝ) := by
  have h := twelvePowerSum_newton 4 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 4 | a.1 ∈ Set.Ioo 0 4} =
      ({(1,3),(2,2),(3,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3] at h
  exact h

theorem twelvePowerSum_5 : twelvePowerSum 5 = (1079508943769/8064 : ℝ) := by
  have h := twelvePowerSum_newton 5 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 5 | a.1 ∈ Set.Ioo 0 5} =
      ({(1,4),(2,3),(3,2),(4,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4] at h
  exact h

theorem twelvePowerSum_6 : twelvePowerSum 6 = (140600616605/32 : ℝ) := by
  have h := twelvePowerSum_newton 6 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 6 | a.1 ∈ Set.Ioo 0 6} =
      ({(1,5),(2,4),(3,3),(4,2),(5,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4, twelvePowerSum_5] at h
  exact h

theorem twelvePowerSum_7 : twelvePowerSum 7 = (4518393199173727/30720 : ℝ) := by
  have h := twelvePowerSum_newton 7 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 7 | a.1 ∈ Set.Ioo 0 7} =
      ({(1,6),(2,5),(3,4),(4,3),(5,2),(6,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4, twelvePowerSum_5, twelvePowerSum_6] at h
  exact h

theorem twelvePowerSum_8 : twelvePowerSum 8 = (639658966504229/128 : ℝ) := by
  have h := twelvePowerSum_newton 8 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 8 | a.1 ∈ Set.Ioo 0 8} =
      ({(1,7),(2,6),(3,5),(4,4),(5,3),(6,2),(7,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4, twelvePowerSum_5, twelvePowerSum_6, twelvePowerSum_7] at h
  exact h

theorem twelvePowerSum_9 : twelvePowerSum 9 = (11608225489187126729/67584 : ℝ) := by
  have h := twelvePowerSum_newton 9 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 9 | a.1 ∈ Set.Ioo 0 9} =
      ({(1,8),(2,7),(3,6),(4,5),(5,4),(6,3),(7,2),(8,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4, twelvePowerSum_5, twelvePowerSum_6, twelvePowerSum_7, twelvePowerSum_8] at h
  exact h

theorem twelvePowerSum_10 : twelvePowerSum 10 = (3050388693564346925/512 : ℝ) := by
  have h := twelvePowerSum_newton 10 (by norm_num) (by norm_num)
  rw [show {a ∈ Finset.antidiagonal 10 | a.1 ∈ Set.Ioo 0 10} =
      ({(1,9),(2,8),(3,7),(4,6),(5,5),(6,4),(7,3),(8,2),(9,1)} : Finset (ℕ × ℕ)) by decide] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, Finset.sum_singleton, twelveElementary, twelvePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X, twelvePowerSum_1, twelvePowerSum_2, twelvePowerSum_3, twelvePowerSum_4, twelvePowerSum_5, twelvePowerSum_6, twelvePowerSum_7, twelvePowerSum_8, twelvePowerSum_9] at h
  exact h

end SphericalRiesz.Boundary
