import Riesz.SphereResidualAssembly8
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

/-! Delete a point of maximal row energy. Iterating this exact finite argument
recovers the subset-average coefficient without enumerating all subsets. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

def finiteOrderedPair {n : ℕ} (k : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, k i j

theorem finiteOrderedPair_delete {n : ℕ} (k : Fin (n+1) → Fin (n+1) → ℝ)
    (hs : ∀ i j, k i j = k j i) (hd : ∀ i, k i i = 0) (p : Fin (n+1)) :
    finiteOrderedPair k = 2*(∑ j, k p j) +
      finiteOrderedPair (fun i j : Fin n => k (p.succAbove i) (p.succAbove j)) := by
  have hr : (∑ j : Fin (n+1), k p j) = ∑ j : Fin n, k p (p.succAbove j) := by
    rw [Fin.sum_univ_succAbove _ p, hd p, zero_add]
  have hc : (∑ i : Fin n, k (p.succAbove i) p) = ∑ j : Fin (n+1), k p j := by
    simp_rw [hs (p.succAbove _) p]
    exact hr.symm
  unfold finiteOrderedPair
  rw [Fin.sum_univ_succAbove _ p]
  conv_lhs =>
    arg 2
    arg 2
    ext i
    rw [Fin.sum_univ_succAbove _ p]
  rw [Finset.sum_add_distrib, hc]
  ring

theorem finiteOrderedPair_exists_delete {n : ℕ} (k : Fin (n+1) → Fin (n+1) → ℝ)
    (hs : ∀ i j, k i j = k j i) (hd : ∀ i, k i i = 0) :
    ∃ p : Fin (n+1), (n+1:ℝ)*
      finiteOrderedPair (fun i j : Fin n => k (p.succAbove i) (p.succAbove j)) ≤
      (n-1:ℝ)*finiteOrderedPair k := by
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ j, k i j) Finset.univ_nonempty
  have hmean : finiteOrderedPair k ≤ (n+1:ℝ)*(∑ j, k p j) := by
    calc
      _ ≤ ∑ _i : Fin (n+1), (∑ j, k p j) :=
        Finset.sum_le_sum (fun i hi => hp i hi)
      _ = _ := by simp
  refine ⟨p, ?_⟩
  have he := finiteOrderedPair_delete k hs hd p
  nlinarith

theorem finiteOrderedPair_exists_subembedding (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (k : Fin M → Fin M → ℝ) (hs : ∀ i j, k i j = k j i) (hd : ∀ i, k i i = 0) :
    ∃ e : Fin N ↪ Fin M,
      finiteOrderedPair (fun i j => k (e i) (e j))/((N:ℝ)*(N-1)) ≤
      finiteOrderedPair k/((M:ℝ)*(M-1)) := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases heq : N = M+1
    · subst N
      exact ⟨Function.Embedding.refl _, le_rfl⟩
    have hNM' : N ≤ M := by omega
    obtain ⟨p, hp⟩ := finiteOrderedPair_exists_delete k hs hd
    obtain ⟨e, he⟩ := ih hNM' (fun i j => k (p.succAbove i) (p.succAbove j))
      (fun i j => hs _ _) (fun i => hd _)
    refine ⟨e.trans p.succAboveEmb, he.trans ?_⟩
    have hM : (2:ℝ) ≤ M := by exact_mod_cast hN.trans hNM'
    have h1 : 0 < (M:ℝ)*(M-1) := mul_pos (by linarith) (by linarith)
    have h2 : 0 < ((M+1:ℕ):ℝ)*(((M+1:ℕ):ℝ)-1) := by
      push_cast
      exact mul_pos (by linarith) (by linarith)
    apply (div_le_div_iff₀ h1 h2).mpr
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (M:ℝ) by positivity)
    nlinarith

theorem energy4_exists_subconfiguration (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : Configuration M) :
    ∃ e : Fin N ↪ Fin M, energy4 (e.trans X) ≤
      ((N:ℝ)*(N-1))/((M:ℝ)*(M-1))*energy4 X := by
  obtain ⟨e, he⟩ := finiteOrderedPair_exists_subembedding N M hN hNM
    (fun i j => sphereKernel4 (X i) (X j))
    (fun i j => sphereKernel4_symm _ _) (fun i => by simp [sphereKernel4])
  have h1 : 0 < (N:ℝ)*(N-1) := by
    have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
    exact mul_pos (by linarith) (by linarith)
  have hpair {r : ℕ} (Y : Configuration r) :
      finiteOrderedPair (fun i j => sphereKernel4 (Y i) (Y j)) = energy4 Y :=
    sphereKernel4_pair_offDiagonal Y
  change finiteOrderedPair (fun i j => sphereKernel4 ((e.trans X) i) ((e.trans X) j)) /
    ((N:ℝ)*(N-1)) ≤ finiteOrderedPair (fun i j => sphereKernel4 (X i) (X j)) /
    ((M:ℝ)*(M-1)) at he
  rw [hpair, hpair] at he
  refine ⟨e, ?_⟩
  have hh := (div_le_iff₀ h1).mp he
  calc
    _ ≤ energy4 X/((M:ℝ)*(M-1))*((N:ℝ)*(N-1)) := hh
    _ = _ := by ring

theorem energy4_exists_density_subconfiguration (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : Configuration M) :
    ∃ e : Fin N ↪ Fin M, energy4 (e.trans X) ≤ ((N:ℝ)/(M:ℝ))^2*energy4 X := by
  obtain ⟨e, he⟩ := energy4_exists_subconfiguration N M hN hNM X
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hnm : (N:ℝ) ≤ M := by exact_mod_cast hNM
  have hm : (0:ℝ) < M := by linarith
  have hcoef : ((N:ℝ)*(N-1))/((M:ℝ)*(M-1)) ≤ ((N:ℝ)/(M:ℝ))^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (mul_pos hm (by linarith)) (sq_pos_of_pos hm)).mpr
    have hprod := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ N) hm.le)
      (sub_nonneg.mpr hnm)
    nlinarith
  exact ⟨e, he.trans (mul_le_mul_of_nonneg_right hcoef (energy4_nonneg X))⟩

theorem normalizedEnergy_exists_subconfiguration (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : Configuration M) :
    ∃ e : Fin N ↪ Fin M,
      normalizedEnergy (e.trans X) ≤ Real.sqrt ((N:ℝ)/(M:ℝ))*normalizedEnergy X := by
  obtain ⟨e, he⟩ := energy4_exists_density_subconfiguration N M hN hNM X
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsn : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hsm : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have hcancel : ((N:ℝ)/(M:ℝ))^2*(M:ℝ)^2 = (N:ℝ)^2 := by
    rw [div_pow]
    field_simp [hm.ne']
  have he' : energy4 (e.trans X)-(7/16:ℝ)*(N:ℝ)^2 ≤
      ((N:ℝ)/(M:ℝ))^2*(energy4 X-(7/16:ℝ)*(M:ℝ)^2) := by
    nlinarith [hcancel]
  refine ⟨e, ?_⟩
  unfold normalizedEnergy
  calc
    _ ≤ (((N:ℝ)/(M:ℝ))^2*(energy4 X-(7/16:ℝ)*(M:ℝ)^2))/
        ((N:ℝ)*Real.sqrt (N:ℝ)) :=
      div_le_div_of_nonneg_right he' (mul_pos hn hsn).le
    _ = _ := by
      rw [Real.sqrt_div hn.le]
      field_simp [hn.ne', hm.ne', hsn.ne', hsm.ne']
      rw [Real.sq_sqrt hm.le, Real.sq_sqrt hn.le]
      ring

end SphericalRiesz
