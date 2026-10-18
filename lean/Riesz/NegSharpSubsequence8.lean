import Riesz.RationalNegJointCutoff8
import Riesz.SphereJointUpperSubsequence8
import Riesz.SphereRieszUpperFourLt8
import Riesz.SphereRieszNegTransfer8

/-! Sharp `s = 4` subsequences with a small negative-exponent macroscopic end (stage NEG).

The construction is the near-full rational patch family of the `s = 4` upper bound (residual
fraction `b`), with the residual chosen one point per cell of an exact-mass stratification of the
residual region, jointly for `sphereKernel4 + w·k_φ + λ·K'(1)`, `λ = (d m)^4 = √N`.
The stratification is a hypothesis (`NegStratifiable8`): cells of mass `1/N` with
`Σ_j c_N d_j² ≤ B r + ε N`, i.e. at the density scale up to `o(N)`.

* `s = 4`: the energy gains `w·4N/3 + λ Ω ≤ (η/8 + η/16) (d m)^12`, so the normalized energy is
  below `C₄ + η` (the patch block is the HP local plus cross bound).
* macroscopic end: `N ∫_{(0,t]} α^p (F_N + 1) = block_{K'(t)}(Y)` is at most twice the patch block
  (`≤ N (C₁ t^(p+3)/(p+3) + o(1))`) plus `2 (Ω + (dev + w·4N/3)/λ)`, and the deviation
  `dev = block₄(patches) - (E₄ - (7/16) N²)` is at most `η (d m)^12` by the universal `s = 4`
  lower bound (the G8 input). Hence `∫_{(0,t]} α^p (F_N + 1) ≤ 2 C₁ t^(p+3)/(p+3) + 3η` for every
  `0 < t ≤ 1`, with one construction. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

/-- Exact-mass stratifications of a region `A` at the density scale: for every large `N` and every
`r = N σ(A)`, cells of mass `σ(A)/r = 1/N` with diameters `d_j` and `Σ_j c_N d_j² ≤ B r + ε N`. -/
def NegStratifiable8 (A : Set Sphere8) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N r : ℕ, N₀ ≤ N → 0 < r →
    (r:ℝ) = (N:ℝ)*sphereProbability8.real A →
    ∃ C : Fin r → Set Sphere8, ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = A ∧ (∀ j, sphereProbability8 (C j) = sphereProbability8 A/(r:ℝ≥0∞)) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, sphereGaussianDensityFactor8 N*(dm j)^2 ≤ B*r+ε*N

set_option maxHeartbeats 1000000 in
theorem sphere8_neg_sharp_upper_subsequence
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    {p : ℝ} (hp : -2 < p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ Y : Configuration ((d*m)^8),
        (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y+1) ≤
            2*C₁*(t^(p+3)/(p+3))+3*η := by
  have hp2 : 0 < p+2 := by linarith
  obtain ⟨ρN, hρN, _hρN1, C₁, C₄, hC₁, hC₄, hpatch⟩ := rationalPatch_negMacroBlock_le
  refine ⟨C₁, hC₁, fun η hη hη1 => ?_⟩
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
  have hδ : 0 < δ := by dsimp [δ]; positivity
  -- the residual fraction
  set b₀ := η/(-4*predictedCoefficient) with hb₀
  have hb₀0 : 0 < b₀ := by
    apply div_pos hη
    nlinarith
  set b := min b₀ (η*(p+2)/(32*(B+1))) with hbdef
  have hb : 0 < b := lt_min hb₀0 (by positivity)
  have hbb₀ : b ≤ b₀ := min_le_left _ _
  have hbB : B*b ≤ η*(p+2)/32 := by
    have h1 : b ≤ η*(p+2)/(32*(B+1)) := min_le_right _ _
    have h2 : B*b ≤ B*(η*(p+2)/(32*(B+1))) := mul_le_mul_of_nonneg_left h1 hB
    have h3 : B*(η*(p+2)/(32*(B+1))) ≤ η*(p+2)/32 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ η*(p+2) := by positivity
      nlinarith
    linarith
  set θ := η*(3-0)/32 with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨N₀, hN₀⟩ := hlow4 (η/4) (by positivity)
  obtain ⟨ρL, hρL, _hρLb, M, hM, hlocal⟩ := equalAreaPatchNeutralized8_uniform_small δ hδ
  obtain ⟨K, P, a, d, ha, hd, hdata, hdis, hl, hu, hmass, hbudget, hcross, _⟩ :=
    sphere8_near_full_rational_energy_upper (min ρL ρN) b (lt_min hρL hρN) hb
  have hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) := fun i => (hdata i).1
  have hρd : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8 := fun i => (hdata i).2.2.2
  have hsmallN : ∀ i, ‖(P i).v‖ ≤ ρN ∧ (P i).ε*equalAreaScaleRadius ≤ ρN := fun i =>
    ⟨(hdata i).2.1.trans (min_le_right _ _), (hdata i).2.2.1.trans (min_le_right _ _)⟩
  have hc : ∀ᶠ m : ℕ in atTop,
      (∑ i, ∑ j ∈ Finset.univ.erase i, smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/
        ((d*m:ℕ):ℝ)^12 < η/4 :=
    hcross.eventually_lt_const (by positivity)
  have hcoef : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))*(predictedCoefficient+η/4) ≤
      predictedCoefficient+η/2 := by
    have hbC : b₀*predictedCoefficient = -η/4 := by
      rw [hb₀]
      field_simp [hC.ne]
    have h0 : -η/4 ≤ b*predictedCoefficient := by
      rw [← hbC]
      exact mul_le_mul_of_nonpos_right hbb₀ hC.le
    have h1 := mul_le_mul_of_nonpos_right hl.le hC.le
    have h2 := mul_le_mul_of_nonneg_right hu.le (show 0 ≤ η/4 by positivity)
    nlinarith
  -- the stratification of the residual region
  obtain ⟨Ns, hNs⟩ := hstrat P (η*(p+2)/32) (by positivity)
  -- the patch error term becomes small
  set Q := C₄/(((a:ℝ)/d)^8*(p+2)) with hQ
  have hadpos : 0 < ((a:ℝ)/d)^8 := by
    have : (0:ℝ) < a := by exact_mod_cast ha
    have : (0:ℝ) < d := by exact_mod_cast hd
    positivity
  have hQ0 : 0 ≤ Q := div_nonneg hC₄ (by positivity)
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max 8 M) (max N₀ Ns)), hc,
    eventually_ge_atTop (⌈4*Q/η⌉₊+1)] with m hm hcm hmQ
  have hm8 : 8 ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hm
  have hmn : M ≤ a*m :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans hm).trans (Nat.le_mul_of_pos_left m ha)
  have hmN₀ : N₀ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmNs : Ns ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hdm : 0 < d*m := Nat.mul_pos hd (by omega)
  have hdmR : (0:ℝ) < ((d*m:ℕ):ℝ) := by exact_mod_cast hdm
  have hNpos : 0 < (d*m)^8 := pow_pos hdm 8
  have hmle : m ≤ (d*m)^8 := by
    have h1 : m ≤ d*m := Nat.le_mul_of_pos_left m hd
    have h2 : d*m ≤ (d*m)^8 := Nat.le_self_pow (by norm_num) _
    omega
  have hN₀N : N₀ ≤ (d*m)^8 := hmN₀.trans hmle
  have hNsN : Ns ≤ (d*m)^8 := hmNs.trans hmle
  set N : ℝ := (((d*m)^8:ℕ):ℝ) with hNdef
  have hN : N = ((d*m:ℕ):ℝ)^8 := by rw [hNdef]; push_cast; ring
  have hNR : 0 < N := by rw [hN]; positivity
  set lam : ℝ := ((d*m:ℕ):ℝ)^4 with hlamdef
  have hlam0 : 0 < lam := by positivity
  have hd12 : ((d*m:ℕ):ℝ)^12 = N*lam := by rw [hN, hlamdef]; ring
  set w := θ*((d*m:ℕ):ℝ)^4 with hw
  have hw0 : 0 < w := by positivity
  set nodes := rationalCubePatchNodes8 P a m ha hm8 with hnodes
  set S := ⋃ i, smallE8CubeSet8 (P i) with hSdef
  set blk := sphereFiniteBlock4 nodes S N with hblk
  -- the local plus cross bound on the block
  have hblock : blk/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η/2+η/4 := by
    have hsum : (((a:ℝ)/d)^8/A)*
        (∑ i, curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
          (P i).g (P i).v (P i).c (P i).ε) (a*m)) ≤
        sphereProbability8.real S*(predictedCoefficient+η/4) := by
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
  -- the residual count and its cells
  have hr0 : 0 < (d^8-K*a^8)*m^8 := Nat.mul_pos (by omega) (pow_pos (by omega) 8)
  have hrmass := rationalCubeFamily8_residual_mass_matching P a d m hd (by omega) hbudget.le hmass
  obtain ⟨C, dmc, hCm, hdisjC, hunion, hmassC, hdiam, hsumS⟩ :=
    hNs ((d*m)^8) ((d^8-K*a^8)*m^8) hNsN hr0 hrmass
  have hrb : (((d^8-K*a^8)*m^8:ℕ):ℝ) ≤ b*N := by
    rw [hrmass]
    have hS : MeasurableSet S := MeasurableSet.iUnion
      (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
    have hc1 := measureReal_add_measureReal_compl (μ := sphereProbability8) hS
    rw [probReal_univ] at hc1
    have hσ : sphereProbability8.real Sᶜ ≤ b := by linarith
    rw [mul_comm b N]
    exact mul_le_mul_of_nonneg_left hσ hNR.le
  -- the joint construction
  have hc'0 : 0 ≤ sphereGaussianDensityFactor8 ((d*m)^8) :=
    (sphereGaussianDensityFactor8_pos hNpos).le
  obtain ⟨Y, _he, hE, hK⟩ := rationalCubeFamily8_exists_neg_joint_cutoff P hdis hu a d m ha hd hm8
    hbudget.le hmass (p := 0) (by norm_num) (by norm_num) hw0 hc'0 hp zero_le_one hlam0 hr0 C hCm
    hdisjC hunion hmassC dmc hdiam
  -- the cell sum
  set Ω := ∑ j, sphereGaussianDensityFactor8 ((d*m)^8)*(dmc j)^2*((1:ℝ)^(p+2)/(p+2)) with hΩdef
  have hΩ : Ω ≤ η/16*N := by
    have h1 : Ω = (∑ j, sphereGaussianDensityFactor8 ((d*m)^8)*(dmc j)^2)/(p+2) := by
      rw [hΩdef, Real.one_rpow, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, div_le_iff₀ hp2]
    have h2 : (B*(((d^8-K*a^8)*m^8:ℕ):ℝ)) ≤ B*(b*N) := mul_le_mul_of_nonneg_left hrb hB
    have h3 : B*(b*N) ≤ η*(p+2)/32*N := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hbB hNR.le
    have h4 : (η*(p+2)/32)*(((d*m)^8:ℕ):ℝ) = η*(p+2)/32*N := by rw [hNdef]
    have h5 := hsumS
    have h6 : η/16*N*(p+2) = η*(p+2)/32*N+η*(p+2)/32*N := by ring
    rw [h6]
    linarith
  -- the energy
  have hslack : w*(4*N/(3-0))/((d*m:ℕ):ℝ)^12 = η/8 := by
    rw [hw, hN, hθ]
    field_simp
    ring
  have hlamΩ : lam*Ω/((d*m:ℕ):ℝ)^12 ≤ η/16 := by
    rw [hd12, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hΩ hlam0.le
    nlinarith
  have henergy : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η := by
    have h1 : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 ≤
        blk/((d*m:ℕ):ℝ)^12+w*(4*N/(3-0))/((d*m:ℕ):ℝ)^12+lam*Ω/((d*m:ℕ):ℝ)^12 := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right hE (by positivity)
    rw [hslack] at h1
    linarith
  refine ⟨Y, henergy, fun t ht ht1 => ?_⟩
  -- the deviation is at most η (d m)^12
  have hlowY := hN₀ ((d*m)^8) hN₀N Y
  have hlowE : (predictedCoefficient-η/4)*((d*m:ℕ):ℝ)^12 ≤ energy4 Y-(7/16:ℝ)*N^2 := by
    have h := hlowY
    rw [normalizedEnergy_power_eight (d*m) Y, le_div_iff₀ (by positivity)] at h
    exact h
  have hblk' : blk ≤ (predictedCoefficient+η/2+η/4)*((d*m:ℕ):ℝ)^12 := by
    have h := hblock
    rw [div_lt_iff₀ (by positivity)] at h
    exact h.le
  have hdev : (blk-(energy4 Y-(7/16:ℝ)*N^2))+w*(4*N/(3-0)) ≤ (9*η/8)*N*lam := by
    have hwN : w*(4*N/(3-0)) = η/8*((d*m:ℕ):ℝ)^12 := by
      rw [hw, hN, hθ]
      field_simp
      ring
    rw [hwN, show (9*η/8)*N*lam = (9*η/8)*(N*lam) by ring, ← hd12]
    nlinarith
  have hdevl : ((blk-(energy4 Y-(7/16:ℝ)*N^2))+w*(4*N/(3-0)))/lam ≤ (9*η/8)*N := by
    rw [div_le_iff₀ hlam0]
    exact hdev
  -- the patch part
  have hP := hpatch P hdis hsmallN a d m ha hd hm8 hε hρd hmass hp ht ht1
  have htp : t^(p+2)/(p+2) ≤ 1/(p+2) := by
    apply div_le_div_of_nonneg_right _ hp2.le
    exact Real.rpow_le_one ht.le ht1 hp2.le
  have hQm : C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(t^(p+2)/(p+2)) ≤ η/4 := by
    have hmR : 4*Q/η ≤ (m:ℝ) := by
      have h1 : (⌈4*Q/η⌉₊:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmQ
      have h2 : 4*Q/η ≤ (⌈4*Q/η⌉₊:ℝ) := Nat.le_ceil _
      linarith
    have ham : (m:ℝ) ≤ ((a*m:ℕ):ℝ)^2 := by
      have h1 : m ≤ a*m := Nat.le_mul_of_pos_left m ha
      have h2 : a*m ≤ (a*m)^2 := Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1.trans h2
    have hamp : 0 < ((a*m:ℕ):ℝ)^2 := by
      have : 0 < a*m := Nat.mul_pos ha (by omega)
      positivity
    have hC4e : C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(1/(p+2)) = Q/((a*m:ℕ):ℝ)^2 := by
      rw [hQ]
      field_simp
    have h1 : C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(t^(p+2)/(p+2)) ≤
        C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(1/(p+2)) :=
      mul_le_mul_of_nonneg_left htp (div_nonneg hC₄ (by positivity))
    rw [hC4e] at h1
    have h2 : Q/((a*m:ℕ):ℝ)^2 ≤ η/4 := by
      rw [div_le_iff₀ hamp]
      have h3 : 4*Q ≤ η*(m:ℝ) := by
        rw [div_le_iff₀ hη] at hmR
        linarith
      nlinarith
    linarith
  -- the whole configuration
  have hcfg := negMacroBlock8_config hNpos Y hp ht.le
  have hKt := hK t ht.le ht1
  rw [hcfg] at hKt
  have htot : N*∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y+1) ≤
      N*(2*C₁*(t^(p+3)/(p+3))+3*η) := by
    have hP' : kernelBlock8 (negMacroKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p t) nodes S N ≤
        N*(C₁*(t^(p+3)/(p+3))+η/4) := by
      refine hP.trans ?_
      apply mul_le_mul_of_nonneg_left _ hNR.le
      linarith
    have hfin : N*(2*C₁*(t^(p+3)/(p+3))+3*η) =
        2*(N*(C₁*(t^(p+3)/(p+3))+η/4))+2*(η/16*N+(9*η/8)*N)+N*(η/8) := by ring
    rw [hfin]
    have hηN : 0 ≤ N*(η/8) := by positivity
    linarith
  exact le_of_mul_le_mul_left htot hNR


/-- A diagonal sequence: sharp for `s = 4`, with macroscopic ends
`∫_{(0,t]} α^p (F + 1) ≤ 2 C₁ t^(p+3)/(p+3) + 3/(j+1)` for every `0 < t ≤ 1`. -/
theorem sphere8_neg_sharp_sequence (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    {p : ℝ} (hp : -2 < p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ N : ℕ → ℕ, (∀ j, max j 1 ≤ N j) ∧ ∃ X : ∀ j, Configuration (N j),
      (∀ j, normalizedEnergy (X j) < predictedCoefficient+1/((j:ℝ)+1)) ∧
      (∀ j, ∀ t : ℝ, 0 < t → t ≤ 1 →
        ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α (X j)+1) ≤
          2*C₁*(t^(p+3)/(p+3))+3*(1/((j:ℝ)+1))) := by
  obtain ⟨C₁, hC₁, hC⟩ := sphere8_neg_sharp_upper_subsequence
    (sphere8_lower4_of_laplaceSineData D) hB hstrat hp
  have hstep : ∀ j : ℕ, ∃ n : ℕ, max j 1 ≤ n ∧ ∃ Y : Configuration n,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y+1) ≤
          2*C₁*(t^(p+3)/(p+3))+3*(1/((j:ℝ)+1)) := by
    intro j
    have hη : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    have hη1 : 1/((j:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
      linarith
    obtain ⟨d, hd, hev⟩ := hC _ hη hη1
    obtain ⟨m, hm, hmj⟩ := (hev.and (eventually_ge_atTop (max j 1))).exists
    obtain ⟨Y, hE, hS⟩ := hm
    refine ⟨(d*m)^8, ?_, Y, ?_, hS⟩
    · have h2 : m ≤ d*m := Nat.le_mul_of_pos_left m hd
      have h3 : d*m ≤ (d*m)^8 := Nat.le_self_pow (by norm_num) _
      omega
    · rw [normalizedEnergy_power_eight]
      exact hE
  choose N hN X hX using hstep
  exact ⟨C₁, hC₁, N, hN, X, fun j => (hX j).1, fun j => (hX j).2⟩

/-- The sharp lower bound for every `-2 < s < 0` along a sequence `N_j → ∞`, under the CKMRV
contract and the exact-mass stratification hypothesis for the residual regions:
`C_s - η ≤ (Σ_{i≠j} |x_i - x_j|^|s| - I_s N²)/N^(1+s/8)` eventually. -/
theorem sphere8_riesz_neg_lower_sequence (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ (∀ j, 0 < N j) ∧ ∃ X : ∀ j, Configuration (N j),
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        sphereRieszCoefficientNeg8 s-η ≤ normalizedEnergyNeg8 s (X j) := by
  have hp : -2 < s/2-1 := by linarith
  have hp3 : 0 < s/2-1+3 := by linarith
  obtain ⟨C₁, hC₁, N, hNj, X, hE, hM⟩ := sphere8_neg_sharp_sequence D hB hstrat hp
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => (le_max_left _ _).trans (hNj j)) tendsto_id
  have hNpos : ∀ j, 0 < N j := fun j => lt_of_lt_of_le one_pos ((le_max_right _ _).trans (hNj j))
  have hinv : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) ≤ ε := fun ε hε =>
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε)
  refine ⟨N, hNt, hNpos, X, ?_⟩
  apply sphere8_riesz_neg_lower_of_sharp_sequence D hs hs0 hNpos hNt X
  · intro ε hε
    filter_upwards [hinv ε hε] with j hj
    linarith [hE j]
  · intro ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (show 0 < ε*(s/2-1+3)/(4*(C₁+1)) by positivity)
    refine ⟨n₀, ?_⟩
    filter_upwards [hinv (ε/6) (by positivity)] with j hj
    set x : ℝ := 1/((n₀:ℝ)+1) with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one (by positivity)]
      have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
      linarith
    have hb := hM j x hx0 hx1
    have hxq : x^(s/2-1+3) ≤ x := by
      have h := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (show (1:ℝ) ≤ s/2-1+3 by linarith)
      rwa [Real.rpow_one] at h
    have hterm : 2*C₁*(x^(s/2-1+3)/(s/2-1+3)) ≤ ε/2 := by
      have h1 : 2*C₁*(x^(s/2-1+3)/(s/2-1+3)) ≤ 2*C₁*(x/(s/2-1+3)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxq hp3.le) (by positivity)
      have h2 : x < ε*(s/2-1+3)/(4*(C₁+1)) := hn₀
      have h3 : 2*C₁*(x/(s/2-1+3)) ≤ ε/2 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hp3]
        have h4 : x*(4*(C₁+1)) < ε*(s/2-1+3) := by
          rwa [lt_div_iff₀ (by positivity)] at h2
        nlinarith
      linarith
    linarith

#print axioms sphere8_neg_sharp_upper_subsequence
#print axioms sphere8_neg_sharp_sequence
#print axioms sphere8_riesz_neg_lower_sequence

end SphericalRiesz
