import Riesz.RationalLongRangeResidual8
import Riesz.PatchLongRangeBound8
import Riesz.SphereSharpUpperSubsequence8

/-! Sharp `s = 4` subsequences with a uniformly bounded long-range block.

The near-full rational patch family of the `s = 4` upper bound, with the residual chosen jointly
for `sphereKernel4 + w·K⁰`, `w = θ (dm)⁴`, `θ = η/(8 C_L)`.  The patch long-range block is at most
`N (C₁/(p+3) + 1)` for large `m` (`rationalPatch_longRangeBlock_le`), so the `s = 4` normalized
energy gains at most `η/8`; with the sharp `s = 4` lower bound the block gap is at most
`η (dm)¹²`, so the normalized long-range block is at most `9 C_L`, one constant for every
`η ≤ 1`. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

set_option maxHeartbeats 1000000 in
theorem sphere8_joint_sharp_longRange_subsequence
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {p : ℝ} (hp1 : -1 < p) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ Y : Configuration ((d*m)^8),
        (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η ∧
        kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p)
          (fun i => Y i) univ (((d*m)^8:ℕ):ℝ)/(((d*m)^8:ℕ):ℝ) ≤ C := by
  have hp0 : 0 < p+1 := by linarith
  obtain ⟨ρD, hρD, -, C₁, C₂, hC₁, hC₂, hpatchL⟩ := rationalPatch_longRangeBlock_le
  set CL := C₁/(p+3)+1+1/(p+1) with hCL
  have hCL0 : 0 < CL := by
    have : 0 ≤ C₁/(p+3) := div_nonneg hC₁ (by linarith)
    have : 0 < 1/(p+1) := by positivity
    linarith
  refine ⟨9*CL, fun η hη hη1 => ?_⟩
  have hC : predictedCoefficient < 0 := by
    unfold predictedCoefficient
    have h : 0 < Real.sqrt (210:ℝ) := by positivity
    nlinarith
  let A := Real.sqrt (sphereArea8.real univ)
  have hA : 0 < A := by
    apply Real.sqrt_pos.mpr
    rw [sphereArea8_mass_real]
    positivity
  have hAz : Real.sqrt (sphereArea8.real univ) ≠ 0 := hA.ne'
  let δ := η*A/4
  let b := η/(-4*predictedCoefficient)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb : 0 < b := by
    apply div_pos hη
    nlinarith
  set θ := η/(8*CL) with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨N₀, hN₀⟩ := hlow4 (η/4) (by positivity)
  obtain ⟨ρL, hρL, _hρLb, M, hM, hlocal⟩ := equalAreaPatchNeutralized8_uniform_small δ hδ
  obtain ⟨K, P, a, d, ha, hd, hdata, hdis, hl, hu, hmass, hbudget, hcross, _⟩ :=
    sphere8_near_full_rational_energy_upper (min ρL ρD) b (lt_min hρL hρD) hb
  have hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) := fun i => (hdata i).1
  have hρd : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8 := fun i => (hdata i).2.2.2
  have hsmallD : ∀ i, ‖(P i).v‖ ≤ ρD ∧ (P i).ε*equalAreaScaleRadius ≤ ρD := fun i =>
    ⟨(hdata i).2.1.trans (min_le_right _ _), (hdata i).2.2.1.trans (min_le_right _ _)⟩
  have hc : ∀ᶠ m : ℕ in atTop,
      (∑ i, ∑ j ∈ Finset.univ.erase i, smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/
        ((d*m:ℕ):ℝ)^12 < η/4 :=
    hcross.eventually_lt_const (by positivity)
  have hbC : b*predictedCoefficient = -η/4 := by
    dsimp [b]
    field_simp [hC.ne] <;> ring
  have hcoef : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))*(predictedCoefficient+η/4) ≤
      predictedCoefficient+η/2 := by
    have h1 := mul_le_mul_of_nonpos_right hl.le hC.le
    have h2 := mul_le_mul_of_nonneg_right hu.le (show 0 ≤ η/4 by positivity)
    nlinarith
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt (C₂/((p+1)*((a:ℝ)/d)^8))
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max 8 M) (max N₀ m₁)), hc] with m hm hcm
  have hm8 : 8 ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hm
  have hmn : M ≤ a*m :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans hm).trans (Nat.le_mul_of_pos_left m ha)
  have hmN₀ : N₀ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmm₁ : m₁ ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hdm : 0 < d*m := Nat.mul_pos hd (by omega)
  have hdmR : (0:ℝ) < ((d*m:ℕ):ℝ) := by exact_mod_cast hdm
  have hNpos : 0 < (d*m)^8 := pow_pos hdm 8
  have hN₀N : N₀ ≤ (d*m)^8 := by
    have h1 : m ≤ d*m := Nat.le_mul_of_pos_left m hd
    have h2 : d*m ≤ (d*m)^8 := Nat.le_self_pow (by norm_num) _
    omega
  set w := θ*((d*m:ℕ):ℝ)^4 with hw
  have hw0 : 0 < w := by positivity
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  have hc0 : 0 < c := sphereGaussianDensityFactor8_pos hNpos
  obtain ⟨Y, ⟨e, he⟩, hE, hS⟩ := rationalCubeFamily8_exists_joint_longRange P hdis hu a d m ha hd hm8
    hbudget.le hmass hc0.le hp1 hw0
  have hnormY := normalizedEnergy_power_eight (d*m) Y
  have hlowY := hN₀ ((d*m)^8) hN₀N Y
  set N : ℝ := (((d*m)^8:ℕ):ℝ) with hNdef
  have hN : N = ((d*m:ℕ):ℝ)^8 := by rw [hNdef]; push_cast; ring
  have hNR : 0 < N := by rw [hN]; positivity
  set nodes := rationalCubePatchNodes8 P a m ha hm8 with hnodes
  set blk := sphereFiniteBlock4 nodes (⋃ i, smallE8CubeSet8 (P i)) N with hblk
  -- the local plus cross bound on the block
  have hblock : blk/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η/2+η/4 := by
    have hsum : (((a:ℝ)/d)^8/A)*
        (∑ i, curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
          (P i).g (P i).v (P i).c (P i).ε) (a*m)) ≤
        sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))*(predictedCoefficient+η/4) := by
      have hi (i : Fin K) : curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
          (P i).g (P i).v (P i).c (P i).ε) (a*m) ≤ -5*Real.pi^2/6+δ := by
        have h := hlocal (P i).v ((hdata i).2.1.trans (min_le_left _ _)) (P i).ε (P i).ε_pos
          ((hdata i).2.2.1.trans (min_le_left _ _)) (P i).g (P i).c (P i).c_mem (a*m) hmn
        linarith [(abs_lt.mp h).2]
      calc
        _ ≤ (((a:ℝ)/d)^8/A)*(∑ _i : Fin K, (-5*Real.pi^2/6+δ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by positivity)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmass]
          rw [predictedCoefficient_area_normalization]
          dsimp [δ, A]
          field_simp [hAz] <;> ring
    have hsplit : blk/((d*m:ℕ):ℝ)^12 = (((a:ℝ)/d)^8/Real.sqrt (sphereArea8.real univ))*
          (∑ i, curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
            (P i).g (P i).v (P i).c (P i).ε) (a*m))+
        (∑ i, ∑ j ∈ Finset.univ.erase i, smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/
          ((d*m:ℕ):ℝ)^12 := by
      rw [hblk, rationalCubeFamily8_fixed_union_local_cross P hdis a d m ha hd hm8 hρd,
        add_div, Finset.sum_div]
      simp_rw [rationalCubeFamily8_local_normalized P a d m ha hd hm8 hε hρd]
      rw [← Finset.mul_sum]
    have htotal := hsum.trans hcoef
    rw [hsplit]
    dsimp [A] at htotal
    linarith
  -- the patch long-range block
  have hpatch : kernelBlock8 (longRangeKernel8 c p) nodes (⋃ i, smallE8CubeSet8 (P i)) N+N/(p+1) ≤
      N*CL := by
    have h := hpatchL P hdis hsmallD a d m ha hd hm8 hε hρd hp1
    rw [← hcdef, ← hnodes, ← hNdef] at h
    have hsmallterm : C₂/((p+1)*(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8)) ≤ 1 := by
      have hδ8 : (0:ℝ) < ((a:ℝ)/d)^8 := by positivity
      have ham : (m₁:ℝ) ≤ ((a*m:ℕ):ℝ)^4 := by
        have h1 : m₁ ≤ m := hmm₁
        have h2 : m ≤ a*m := Nat.le_mul_of_pos_left m ha
        have h3 : a*m ≤ (a*m)^4 := Nat.le_self_pow (by norm_num) _
        exact_mod_cast (h1.trans (h2.trans h3))
      rw [div_le_one (by positivity)]
      have h4 : C₂ < m₁*((p+1)*((a:ℝ)/d)^8) := by
        rw [div_lt_iff₀ (by positivity)] at hm₁
        linarith
      have h5 : (m₁:ℝ)*((p+1)*((a:ℝ)/d)^8) ≤ ((a*m:ℕ):ℝ)^4*((p+1)*((a:ℝ)/d)^8) :=
        mul_le_mul_of_nonneg_right ham (by positivity)
      nlinarith
    have hNC : N*(C₁/(p+3)+C₂/((p+1)*(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8)))+N/(p+1) ≤ N*CL := by
      rw [hCL]
      have := mul_le_mul_of_nonneg_left hsmallterm hNR.le
      have e1 : N/(p+1) = N*(1/(p+1)) := by ring
      nlinarith
    linarith
  -- the energy
  have hslack : w*(N*CL)/((d*m:ℕ):ℝ)^12 = η/8 := by
    rw [hw, hN, hθ]
    field_simp
  have henergy : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η := by
    have h1 : energy4 Y-(7/16:ℝ)*N^2 ≤ blk+w*(N*CL) := by
      have := mul_le_mul_of_nonneg_left hpatch hw0.le
      linarith
    have h2 : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 ≤
        blk/((d*m:ℕ):ℝ)^12+w*(N*CL)/((d*m:ℕ):ℝ)^12 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    rw [hslack] at h2
    linarith
  refine ⟨Y, henergy, ?_⟩
  -- the block gap is at most η·(dm)^12
  have hgap : (blk-(energy4 Y-(7/16:ℝ)*N^2))/w ≤ N*(8*CL) := by
    have hlowE : (predictedCoefficient-η/4)*((d*m:ℕ):ℝ)^12 ≤ energy4 Y-(7/16:ℝ)*N^2 := by
      have h := hlowY
      rw [hnormY, le_div_iff₀ (by positivity)] at h
      exact h
    have hblk' : blk ≤ (predictedCoefficient+η/2+η/4)*((d*m:ℕ):ℝ)^12 := by
      have h := hblock
      rw [div_lt_iff₀ (by positivity)] at h
      exact h.le
    rw [div_le_iff₀ hw0]
    have he : N*(8*CL)*w = η*((d*m:ℕ):ℝ)^12 := by
      rw [hw, hN, hθ]
      field_simp
    rw [he]
    linarith
  rw [div_le_iff₀ hNR]
  have hfin : kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ N ≤ N*CL+N*(8*CL) := by
    calc kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ N
        ≤ kernelBlock8 (longRangeKernel8 c p) nodes (⋃ i, smallE8CubeSet8 (P i)) N+
            (blk-(energy4 Y-(7/16:ℝ)*N^2))/w+N/(p+1) := hS
      _ ≤ N*CL+N*(8*CL) := by linarith
  linarith

end SphericalRiesz
