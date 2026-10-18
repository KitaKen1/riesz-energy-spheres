/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license; see third_party/SpherePacking/LICENSE.
Authors of the source: Bhavik Mehta, Gareth Ma

The concrete basis and inverse-coordinate formulas are adapted from
Sphere-Packing-Lean, commit 1e98fb493088948ca7bbf47d7faed49cc5b39fc4,
SpherePacking/Dim8/E8/Basic.lean. The proof here specializes to real
coordinates and checks explicit integer witnesses instead of importing
the source's generic submodule and modular-equality infrastructure.
-/
import Riesz.E8Grid

/-!
# Integer basis image equals the usual E8 parity set

Coordinates are either all integers or all integers plus one half, and
their sum is an even integer. The reverse direction supplies eight
explicit integer basis coefficients. No lattice search is required.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz

def e8ParityPoint (w : Fin 8 → ℝ) : Prop :=
  ((∃ n : Fin 8 → ℤ, w = fun i => (n i : ℝ)) ∨
    (∃ n : Fin 8 → ℤ, w = fun i => (n i : ℝ)+1/2)) ∧
      ∃ k : ℤ, (∑ i, w i) = 2*(k:ℝ)

theorem e8Map_eq_vector (v : Fin 8 → ℝ) :
    e8Map v = ![2*v 0-v 1+v 7/2, v 1-v 2+v 7/2,
      v 2-v 3+v 7/2, v 3-v 4+v 7/2, v 4-v 5+v 7/2,
      v 5-v 6+v 7/2, v 6+v 7/2, v 7/2] := by
  rw [e8Map_eq_sum]
  ext i
  fin_cases i <;> norm_num [e8Matrix, Matrix.row, Fin.sum_univ_eight] <;> ring

theorem e8Map_sum (v : Fin 8 → ℝ) : ∑ i, e8Map v i = 2*v 0+4*v 7 := by
  rw [e8Map_eq_vector]
  simp only [Fin.sum_univ_eight]
  simp
  ring

theorem e8IntegerPoint_mem_parity (z : Fin 8 → ℤ) : e8ParityPoint (e8IntegerPoint z) := by
  let q : ℤ := z 7/2
  let e : ℤ := z 7%2
  have he : e = 0 ∨ e = 1 := Int.emod_two_eq_zero_or_one (z 7)
  have hdec : z 7 = 2*q+e := by dsimp [q, e]; omega
  have hdecR : (z 7:ℝ) = 2*(q:ℝ)+(e:ℝ) := by exact_mod_cast hdec
  let n : Fin 8 → ℤ := ![2*z 0-z 1+q, z 1-z 2+q, z 2-z 3+q,
    z 3-z 4+q, z 4-z 5+q, z 5-z 6+q, z 6+q, q]
  have hform : e8IntegerPoint z = fun i => (n i:ℝ)+(e:ℝ)/2 := by
    rw [e8IntegerPoint, e8Map_eq_vector]
    ext i
    fin_cases i <;> simp [n] <;> linarith [hdecR]
  refine ⟨?_, z 0+2*z 7, ?_⟩
  · rcases he with he | he
    · left
      exact ⟨n, by simpa only [he, Int.cast_zero, zero_div, add_zero] using hform⟩
    · right
      exact ⟨n, by simpa only [he, Int.cast_one] using hform⟩
  · rw [e8IntegerPoint, e8Map_sum]
    push_cast
    ring

/-- A known inverse-coordinate witness; its discovery is outside the proof. -/
theorem e8ParityPoint_exists_integer (w : Fin 8 → ℝ) (hw : e8ParityPoint w) :
    ∃ z : Fin 8 → ℤ, e8IntegerPoint z = w := by
  obtain ⟨hn, k, hk⟩ := hw
  obtain ⟨n, e, he, hform⟩ : ∃ n : Fin 8 → ℤ, ∃ e : ℤ,
      (e = 0 ∨ e = 1) ∧ w = (fun i => (n i:ℝ)+(e:ℝ)/2) := by
    rcases hn with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ⟨n, 0, Or.inl rfl, by simpa using hn⟩
    · exact ⟨n, 1, Or.inr rfl, by simpa using hn⟩
  let z : Fin 8 → ℤ := ![k-4*n 7-2*e,
    n 1+n 2+n 3+n 4+n 5+n 6-6*n 7,
    n 2+n 3+n 4+n 5+n 6-5*n 7,
    n 3+n 4+n 5+n 6-4*n 7,
    n 4+n 5+n 6-3*n 7, n 5+n 6-2*n 7, n 6-n 7, 2*n 7+e]
  refine ⟨z, ?_⟩
  rw [hform] at hk ⊢
  simp only [Fin.sum_univ_eight] at hk
  rw [e8IntegerPoint, e8Map_eq_vector]
  ext i
  fin_cases i <;> simp [z] <;> linarith [hk]

theorem e8ParityPoint_iff_integer_image (w : Fin 8 → ℝ) :
    e8ParityPoint w ↔ ∃ z : Fin 8 → ℤ, e8IntegerPoint z = w := by
  constructor
  · exact e8ParityPoint_exists_integer w
  · rintro ⟨z, rfl⟩
    exact e8IntegerPoint_mem_parity z

theorem e8InteriorNode_difference_parity {m : ℕ} (hm : 8 ≤ m)
    (j k : Fin 8 → Fin (m-8)) :
    e8ParityPoint ((m:ℝ) •
      (e8TensorNode m (fun i => interiorNodeIndex (j i))-
        e8TensorNode m (fun i => interiorNodeIndex (k i)))) := by
  have hmne : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [e8InteriorNode_sub, smul_smul, mul_inv_cancel₀ hmne, one_smul]
  exact e8IntegerPoint_mem_parity _

#print axioms e8Map_eq_vector
#print axioms e8Map_sum
#print axioms e8IntegerPoint_mem_parity
#print axioms e8ParityPoint_exists_integer
#print axioms e8ParityPoint_iff_integer_image
#print axioms e8InteriorNode_difference_parity

end SphericalRiesz
