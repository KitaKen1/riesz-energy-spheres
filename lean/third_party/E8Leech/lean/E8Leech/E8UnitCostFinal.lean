import E8Leech.E8KernelLinearGrowth
import E8Leech.CKMRVRegularCoefficients
import E8Leech.SineSquaredSlack

/-!
# The `E8` unit-cost input from the strict kernel inequality alone

The kernels are continuous on the regular locus `j(τ) ≠ j(z)`, which contains the fixed block
`{(iq, iv) : q ∈ [3,4], v ∈ [1,2]}`. Hence the strict inequality `𝒦̂(iq, it) > 0` gives a positive
lower bound on that block, and with the proved linear growth (`e8_kernel_linear_growth`) the
strict (6.4)(1) is the only remaining analytic input of `AnalyticUnitCostInput e8Set s √2`.

On the singular curves `j(iq) = j(it)` (that is, `t = q` or `qt = 1`) the coefficient matrices
contain `0⁻¹ = 0`, so the Lean kernels take the junk value `0` there
(`ckmrvEightHatKernel_eq_zero_of_kleinJ_eq`). The strict hypothesis is therefore only asked off
those curves; this is exactly the form in which (6.4)(1) can be proved.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold

theorem continuousOn_ckmrvEightPlusKernel_regular :
    ContinuousOn (fun p : ℍ × ℍ => ckmrvEightPlusKernel p.1 p.2) ckmrvRegularLocus := by
  simp only [ckmrvEightPlusKernel, ckmrvCoreContraction]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((((mdifferentiable_ckmrvPhiBasis i).continuous.comp continuous_fst).continuousOn).mul
    (continuousOn_ckmrvEightPlusCoefficientMatrix_entry i j)).mul
    (((mdifferentiable_ckmrvTildePhiBasis j).continuous.comp continuous_snd).continuousOn)

theorem continuous_ckmrvTildePsiBasis (j : Fin 3) :
    Continuous (fun z : ℍ => ckmrvTildePsiBasis z j) := by
  fin_cases j
  · exact mdifferentiable_ckmrvL.continuous
  · exact mdifferentiable_thetaW.continuous
  · exact (mdifferentiable_thetaU.continuous.pow 2).sub (mdifferentiable_thetaV.continuous.pow 2)

theorem continuousOn_ckmrvEightMinusKernel_regular :
    ContinuousOn (fun p : ℍ × ℍ => ckmrvEightMinusKernel p.1 p.2) ckmrvRegularLocus := by
  simp only [ckmrvEightMinusKernel, ckmrvCoreContraction]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((((mdifferentiable_ckmrvPsiBasis i).continuous.comp continuous_fst).continuousOn).mul
    (continuousOn_ckmrvEightMinusCoefficientMatrix_entry i j)).mul
    (((continuous_ckmrvTildePsiBasis j).comp continuous_snd).continuousOn)

/-- `K(q, v) = Re 𝒦̂(iq, iv)` is continuous on the block `[3,4] × [1,2]`. -/
theorem continuousOn_e8DualKernel_block :
    ContinuousOn e8DualKernel (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) := by
  have hmaps : MapsTo ckmrvImaginaryPair (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) ckmrvRegularLocus :=
    fun p hp => ckmrvFixedImaginaryRectangle_subset_regular ⟨p, hp, rfl⟩
  have hp := continuousOn_ckmrvEightPlusKernel_regular.comp
    continuousOn_ckmrvImaginaryPair_rectangle hmaps
  have hm := continuousOn_ckmrvEightMinusKernel_regular.comp
    continuousOn_ckmrvImaginaryPair_rectangle hmaps
  have h := (Complex.continuous_re.comp_continuousOn ((hp.sub hm).div_const 2))
  refine h.congr fun p _ => ?_
  simp only [e8DualKernel, ckmrvEightHatKernel, Pi.sub_apply, Function.comp_apply,
    ckmrvImaginaryPair, imagPt]

/-- On the singular set `j(τ) = j(z)` the Lean plus kernel is the junk value `0`. -/
theorem ckmrvEightPlusKernel_eq_zero_of_kleinJ_eq {τ z : ℍ} (h : kleinModularJ τ = kleinModularJ z) :
    ckmrvEightPlusKernel τ z = 0 := by
  simp [ckmrvEightPlusKernel, ckmrvEightPlusCoefficientMatrix, ckmrvCoreContraction, h]

/-- On the singular set `j(τ) = j(z)` the Lean minus kernel is the junk value `0`. -/
theorem ckmrvEightMinusKernel_eq_zero_of_kleinJ_eq {τ z : ℍ} (h : kleinModularJ τ = kleinModularJ z) :
    ckmrvEightMinusKernel τ z = 0 := by
  simp [ckmrvEightMinusKernel, ckmrvEightMinusCoefficientMatrix, ckmrvCoreContraction, h]

theorem ckmrvEightHatKernel_eq_zero_of_kleinJ_eq {τ z : ℍ} (h : kleinModularJ τ = kleinModularJ z) :
    ckmrvEightHatKernel τ z = 0 := by
  rw [ckmrvEightHatKernel, ckmrvEightPlusKernel_eq_zero_of_kleinJ_eq h,
    ckmrvEightMinusKernel_eq_zero_of_kleinJ_eq h, sub_zero, zero_div]

/-- The strict (6.4)(1) off the singular curves gives the weak one everywhere. -/
theorem e8KernelNonneg_of_pos_regular
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t) →
      0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re) : E8KernelNonneg := by
  intro q t hq ht
  by_cases h : kleinModularJ (imagPt q) = kleinModularJ (imagPt t)
  · rw [ckmrvEightHatKernel_eq_zero_of_kleinJ_eq h, Complex.zero_re]
  · exact (hpos q t hq ht h).le

/-- **The `E8` analytic unit-cost input from the strict (6.4)(1).** The hypothesis is asked only
off the singular curves `j(iq) = j(it)`, where the Lean kernel is the junk value `0`. -/
theorem e8_analyticUnitCostInput_of_kernel_pos {s : ℝ} (hs : 0 < s)
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t) →
      0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput e8Set s (Real.sqrt 2) C⁻¹ (1 / 8) := by
  have hP : E8KernelNonneg := e8KernelNonneg_of_pos_regular hpos
  obtain ⟨B, hB, hBlow⟩ := compact_rectangle_positive_lower continuousOn_e8DualKernel_block
    fun p hp => by
      have hmem := ckmrvFixedImaginaryRectangle_subset_regular ⟨p, hp, rfl⟩
      simp only [ckmrvRegularLocus, Set.mem_ofPred_eq] at hmem
      have h1 : (ckmrvImaginaryPair p).1 = imagPt p.1 := rfl
      have h2 : (ckmrvImaginaryPair p).2 = imagPt p.2 := rfl
      rw [h1, h2] at hmem
      exact hpos p.1 p.2 (by linarith [hp.1.1]) (by linarith [hp.2.1]) (sub_ne_zero.mp hmem)
  exact e8_analyticUnitCostInput_of_kernel_bounds hs hP ⟨B, hB, hBlow⟩ e8_kernel_linear_growth

end E8Leech
