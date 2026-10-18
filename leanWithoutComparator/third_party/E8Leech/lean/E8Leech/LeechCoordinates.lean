import E8Leech.Golay
import E8Leech.StationaryProcess
import Mathlib.Analysis.Real.Sqrt

/-!
# The Golay-congruence coordinate model of the Leech lattice

The integer conditions follow Conway--Goodman-Strauss--Sloane,
Recent Progress in Sphere Packing, p. 32. Scaling by sqrt(8) gives the intended
covolume-one normalization, proved in LeechBasis.lean.
The arbitrary integer parity representative makes subtraction linear; it can
always be normalized to zero or one by adding a constant Golay codeword.
-/

noncomputable section

namespace E8Leech

open Set

theorem golay_minimum_weight {x : Fin 24 → ZMod 2} (hx : x ∈ golayCode) (hne : x ≠ 0) :
    8 ≤ hammingNorm x := by
  have hw := golay_hammingNorm_mem hx
  have hn := hammingNorm_ne_zero_iff.mpr hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  omega

theorem golay_weight_dvd_four {x : Fin 24 → ZMod 2} (hx : x ∈ golayCode) :
    4 ∣ hammingNorm x := by
  have hw := golay_hammingNorm_mem hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with h | h | h | h | h <;> rw [h] <;> norm_num

theorem golayCode_finrank : Module.finrank (ZMod 2) golayCode = 12 := by
  have e : (Fin 12 → ZMod 2) ≃ₗ[ZMod 2] golayCode :=
    LinearEquiv.ofInjective golayEncoderLinear golayEncode_injective
  rw [← e.finrank_eq]
  simp

theorem golayCode_card : Nat.card golayCode = 4096 := by
  have e : (Fin 12 → ZMod 2) ≃ₗ[ZMod 2] golayCode :=
    LinearEquiv.ofInjective golayEncoderLinear golayEncode_injective
  rw [← Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

def leechResidue (z : Fin 24 → ℤ) (m : ℤ) : Fin 24 → ZMod 2 :=
  fun i => ((z i - m) / 2 : ℤ)

def leechNumerators : Set (Fin 24 → ℤ) :=
  {z | ∃ m : ℤ, (∀ i, (2 : ℤ) ∣ z i - m) ∧
    (8 : ℤ) ∣ (∑ i, z i) - 4 * m ∧ leechResidue z m ∈ golayCode}

def leechCoordinates (z : Fin 24 → ℤ) : Ambient 24 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / Real.sqrt 8)

def leechSet : Set (Ambient 24) := leechCoordinates '' leechNumerators

theorem golay_constant_mem (k : ZMod 2) : (fun _ : Fin 24 => k) ∈ golayCode := by
  have h1 : (fun _ : Fin 24 => (1 : ZMod 2)) ∈ golayCode := by
    rw [golay_mem_iff]
    refine ⟨fun _ => 1, ?_⟩
    decide +kernel
  have he : k • (fun _ : Fin 24 => (1 : ZMod 2)) = fun _ => k := by
    ext i
    simp
  rw [← he]
  exact golayCode.smul_mem k h1

theorem leechNumerators_canonical {z : Fin 24 → ℤ} (hz : z ∈ leechNumerators) :
    ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ (∀ i, (2 : ℤ) ∣ z i - m) ∧
      (8 : ℤ) ∣ (∑ i, z i) - 4 * m ∧ leechResidue z m ∈ golayCode := by
  obtain ⟨m, hpar, hsum, hcode⟩ := hz
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hdiv : ∀ i, (2 : ℤ) ∣ z i - m % 2 := by
    intro i
    have hi := hpar i
    omega
  have hsum' : (8 : ℤ) ∣ (∑ i, z i) - 4 * (m % 2) := by omega
  have hres : leechResidue z (m % 2) =
      leechResidue z m + fun _ : Fin 24 => ((m / 2 : ℤ) : ZMod 2) := by
    ext i
    have hi : (z i - m % 2) / 2 = (z i - m) / 2 + m / 2 := by omega
    simp only [leechResidue, Pi.add_apply, hi, Int.cast_add]
  refine ⟨m % 2, hm, hdiv, hsum', ?_⟩
  rw [hres]
  exact golayCode.add_mem hcode (golay_constant_mem _)

theorem leechNumerators_zero : (0 : Fin 24 → ℤ) ∈ leechNumerators := by
  refine ⟨0, ?_, ?_, ?_⟩
  · simp
  · simp
  · have he : leechResidue 0 0 = 0 := by
      ext i
      simp [leechResidue]
    rw [he]
    exact golayCode.zero_mem

theorem leechNumerators_sub {z w : Fin 24 → ℤ}
    (hz : z ∈ leechNumerators) (hw : w ∈ leechNumerators) : z - w ∈ leechNumerators := by
  obtain ⟨m, hm, hsm, hcm⟩ := hz
  obtain ⟨n, hn, hsn, hcn⟩ := hw
  refine ⟨m - n, fun i => ?_, ?_, ?_⟩
  · simpa only [Pi.sub_apply, sub_sub_sub_comm] using dvd_sub (hm i) (hn i)
  · simpa only [Finset.sum_sub_distrib, Pi.sub_apply, mul_sub, sub_sub_sub_comm]
      using dvd_sub hsm hsn
  · have heq : leechResidue (z - w) (m - n) = leechResidue z m - leechResidue w n := by
      ext i
      have hi := hm i
      have hj := hn i
      have he : (z i - w i - (m - n)) / 2 = (z i - m) / 2 - (w i - n) / 2 := by omega
      simp only [leechResidue, Pi.sub_apply, he, Int.cast_sub]
    rw [heq]
    exact golayCode.sub_mem hcm hcn

theorem leechCoordinates_injective : Function.Injective leechCoordinates := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Ambient 24 => x i) h
  change (z i : ℝ) / Real.sqrt 8 = (w i : ℝ) / Real.sqrt 8 at hi
  exact_mod_cast (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))).mp hi

theorem leechCoordinates_sub (z w : Fin 24 → ℤ) :
    leechCoordinates (z - w) = leechCoordinates z - leechCoordinates w := by
  ext i
  simp [leechCoordinates, sub_div]

theorem zero_mem_leechSet : (0 : Ambient 24) ∈ leechSet := by
  refine ⟨0, leechNumerators_zero, ?_⟩
  ext i
  simp [leechCoordinates]

theorem leechSet_sub {x y : Ambient 24} (hx : x ∈ leechSet) (hy : y ∈ leechSet) :
    x - y ∈ leechSet := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨z - w, leechNumerators_sub hz hw, leechCoordinates_sub z w⟩

end E8Leech
