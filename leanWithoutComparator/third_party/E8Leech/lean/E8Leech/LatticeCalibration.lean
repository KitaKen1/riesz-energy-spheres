import E8Leech.GaussianSchwartzCertificates
import Riesz.PoissonLattice

/-!
# Calibration by Poisson summation (P5c)

Let `L` be a covolume-one lattice and `f` a Schwartz function with `f = e^{−α|·|²}` on `L ∖ 0`
and `f̂ = 0` on `L^* ∖ 0`. Then Poisson summation gives the Gaussian lattice energy as
`f̂(0) − f(0)`. This is the `calibration` field of `GaussianSchwartzCertificate`.

For the CKMRV functions both vanishing conditions come from the factor `sin²(π|x|²/2)`, since
`|v|²` is even on `L = L^*` for `E8` and the Leech lattice.
-/

noncomputable section

namespace E8Leech

open MeasureTheory
open scoped ENNReal FourierTransform

/-- **Calibration from Poisson summation.** -/
theorem latticePotentialEnergy_gaussian_toReal_eq {d : ℕ} (L : Submodule ℤ (Ambient d))
    [DiscreteTopology L] [IsZLattice ℝ L] (hcov : ZLattice.covolume L = 1)
    (f : SchwartzMap (Ambient d) ℂ) (α : ℝ)
    (hfin : latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α) ≠ ∞)
    (hf : ∀ v ∈ L, v ≠ 0 → f v = (gaussianKernel α v : ℂ))
    (hfhat : ∀ m ∈ SchwartzMap.dualLattice L, m ≠ 0 → 𝓕 (⇑f) m = 0) :
    (latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α)).toReal =
      (𝓕 (⇑f) 0).re - (f 0).re := by
  -- the real Gaussian sum over `L ∖ 0`
  set e : L → ℝ := fun y => if (y : Ambient d) = 0 then 0 else gaussianKernel α (y : Ambient d)
    with he
  have he0 : ∀ y : L, 0 ≤ e y := fun y => by
    simp only [he]
    split_ifs
    exacts [le_rfl, (gaussianKernel_pos α _).le]
  have hterm : ∀ y : L, (if (y : Ambient d) = 0 then 0 else
      gaussianPotential α (0 : Ambient d) (y : Ambient d)) = ENNReal.ofReal (e y) := by
    intro y
    by_cases hy : (y : Ambient d) = 0
    · rw [if_pos hy]
      simp only [he]
      rw [if_pos hy, ENNReal.ofReal_zero]
    · simp only [he, hy, if_false, gaussianPotential, zero_sub, gaussianKernel, norm_neg]
  have henergy : latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α) =
      ∑' y : L, ENNReal.ofReal (e y) := by
    unfold latticePotentialEnergy
    exact tsum_congr hterm
  have hsumm : Summable e := by
    rw [henergy] at hfin
    exact (ENNReal.summable_toReal hfin).congr fun y => ENNReal.toReal_ofReal (he0 y)
  have htoReal : (latticePotentialEnergy (L : Set (Ambient d)) (gaussianPotential α)).toReal =
      ∑' y : L, e y := by
    rw [henergy, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun y => ENNReal.toReal_ofReal (he0 y)
  -- Poisson summation at `0`
  have hP := SchwartzMap.poissonSummation_lattice (d := d) (L := L) f 0
  simp only [zero_add, hcov, div_one, Complex.ofReal_one, one_mul, WithLp.ofLp_zero,
    RCLike.wInner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hP
  have hL : ∑' ℓ : L, f (ℓ : Ambient d) = f 0 + ((∑' y : L, e y : ℝ) : ℂ) := by
    have hsplit : ∀ ℓ : L, f (ℓ : Ambient d) =
        (if ℓ = 0 then f 0 else 0) + ((e ℓ : ℝ) : ℂ) := by
      intro ℓ
      by_cases hℓ : ℓ = 0
      · subst hℓ
        simp [he]
      · have hℓ' : (ℓ : Ambient d) ≠ 0 := by
          rwa [Ne, Submodule.coe_eq_zero]
        simp only [hℓ, if_false, zero_add, he, hℓ']
        exact hf ℓ ℓ.2 hℓ'
    rw [tsum_congr hsplit, Summable.tsum_add (hasSum_ite_eq 0 (f 0)).summable
      (Complex.summable_ofReal.mpr hsumm), tsum_ite_eq, Complex.ofReal_tsum]
  have hR : ∑' m : SchwartzMap.dualLattice L, 𝓕 (fun x : Ambient d => f x) (m : Ambient d) =
      𝓕 (⇑f) 0 := by
    rw [tsum_eq_single 0 fun (m : SchwartzMap.dualLattice L) hm =>
      hfhat (m : Ambient d) m.2 (by rwa [Ne, Submodule.coe_eq_zero])]
    rfl
  rw [hL, hR] at hP
  have hre := congrArg Complex.re hP
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  rw [htoReal]
  linarith

end E8Leech
