import Riesz.RationalJointResidual8
import Riesz.SphereSharpUpperSubsequence8

/-! Sharp `s = 4` subsequences with a uniformly bounded weighted short-range energy.

The construction is the near-full rational patch family of the `s = 4` upper bound, with the
residual chosen jointly for `sphereKernel4 + w·k_φ`, `w = θ·(dm)^4`, `θ = η(3-p)/32`.  The `s = 4`
normalized energy gains at most `η/8`.  With the sharp `s = 4` lower bound (the G8 input) the
block gap is at most `η·(dm)^12`, so the normalized short-range energy is at most
`K_δ·K_g + 32/(3-p) + 4/(3-p)`, one constant for every `η ≤ 1`. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

set_option maxHeartbeats 1000000 in
theorem sphere8_joint_sharp_upper_subsequence
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {p : ℝ} (hp1 : -1 < p) (hp : p < 3) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ Y : Configuration ((d*m)^8),
        (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η ∧
        finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p)
          (fun i => Y i)/(((d*m)^8:ℕ):ℝ) ≤ C := by
  have h3p : 0 < 3-p := by linarith
  obtain ⟨ρS, hρS, C₀, hC₀, hlow⟩ := smallE8CubeMap8_dist_lower
  set δs := Real.sqrt Real.pi*(C₀/2) with hδs
  have hδs0 : 0 < δs := by positivity
  have hδs2 : δs^2 = Real.pi*(C₀/2)^2 := by
    rw [hδs, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  set E₁ := predictedCoefficient+1 with hE₁
  set Kg := Real.sqrt 2^9+Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₁+1))*4+16 with hKg
  set Kδ := separatedShortRangeConst8 p δs with hKδ
  have hKδ0 : 0 ≤ Kδ := separatedShortRangeConst8_nonneg p δs
  refine ⟨Kδ*max Kg 0+36/(3-p), fun η hη hη1 => ?_⟩
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
  set θ := η*(3-p)/32 with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨N₀, hN₀⟩ := hlow4 (η/4) (by positivity)
  obtain ⟨ρL, hρL, _hρLb, M, hM, hlocal⟩ := equalAreaPatchNeutralized8_uniform_small δ hδ
  obtain ⟨K, P, a, d, ha, hd, hdata, hdis, hl, hu, hmass, hbudget, hcross, _⟩ :=
    sphere8_near_full_rational_energy_upper (min ρL ρS) b (lt_min hρL hρS) hb
  have hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) := fun i => (hdata i).1
  have hρd : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8 := fun i => (hdata i).2.2.2
  have hsmallS : ∀ i, ‖(P i).v‖ ≤ ρS ∧ (P i).ε*equalAreaScaleRadius ≤ ρS := fun i =>
    ⟨(hdata i).2.1.trans (min_le_right _ _), (hdata i).2.2.1.trans (min_le_right _ _)⟩
  have hsep := rationalCubePatchNodes8_density_separated P hdis a d ha hd hC₀ hlow hsmallS hε
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
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max 8 M) N₀), hc, hsep] with m hm hcm hsepm
  have hm8 : 8 ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hm
  have hmn : M ≤ a*m :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans hm).trans (Nat.le_mul_of_pos_left m ha)
  have hmN₀ : N₀ ≤ m := (le_max_right _ _).trans hm
  have hdm : 0 < d*m := Nat.mul_pos hd (by omega)
  have hdmR : (0:ℝ) < ((d*m:ℕ):ℝ) := by exact_mod_cast hdm
  have hNpos : 0 < (d*m)^8 := pow_pos hdm 8
  have hN₀N : N₀ ≤ (d*m)^8 := by
    have h1 : m ≤ d*m := Nat.le_mul_of_pos_left m hd
    have h2 : d*m ≤ (d*m)^8 := Nat.le_self_pow (by norm_num) _
    omega
  set w := θ*((d*m:ℕ):ℝ)^4 with hw
  have hw0 : 0 < w := by positivity
  obtain ⟨Y, ⟨e, he⟩, hE, hS⟩ := rationalCubeFamily8_exists_joint_shortRange P hdis hu a d m ha hd hm8
    hbudget.le hmass hp1.le hp hw0
  have hnormY := normalizedEnergy_power_eight (d*m) Y
  have hlowY := hN₀ ((d*m)^8) hN₀N Y
  have hgY0 := fun E (hE : normalizedEnergy Y ≤ E) => finitePairSum_gaussian_half_le hNpos Y hE
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
  -- the energy
  have hslack : w*(4*N/(3-p))/((d*m:ℕ):ℝ)^12 = η/8 := by
    rw [hw, hN, hθ]
    field_simp
    ring
  have henergy : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η := by
    have h1 : (energy4 Y-(7/16:ℝ)*N^2)/((d*m:ℕ):ℝ)^12 ≤
        blk/((d*m:ℕ):ℝ)^12+w*(4*N/(3-p))/((d*m:ℕ):ℝ)^12 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hE (by positivity)
    rw [hslack] at h1
    linarith
  have hnorm : normalizedEnergy Y ≤ E₁ := by
    rw [hnormY, hE₁]
    linarith
  refine ⟨Y, henergy, ?_⟩
  have hgY := hgY0 E₁ hnorm
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  have hc0 : 0 < c := sphereGaussianDensityFactor8_pos hNpos
  -- the patch part of the short-range energy
  have hYe : (fun i => Y i) ∘ e = Sum.elim nodes (fun j => Y (e (Sum.inr j))) := by
    funext u
    cases u with
    | inl t => exact he t
    | inr j => rfl
  have hsubg := finitePairSum_gaussian_sub_le (c/2) nodes (fun j => Y (e (Sum.inr j)))
  rw [← hYe, finitePairSum_reindex] at hsubg
  have hcardsum : (Fintype.card (Fin K × (Fin 8 → NodeIndex (a*m))):ℝ)+
      Fintype.card (Fin ((d^8-K*a^8)*m^8)) = N := by
    have h := rationalCubeNodeIndex8_card K a d m ha hm8 hbudget.le
    change Fintype.card ((Fin K × (Fin 8 → NodeIndex (a*m))) ⊕ Fin ((d^8-K*a^8)*m^8)) = _ at h
    rw [Fintype.card_sum] at h
    rw [hNdef]
    exact_mod_cast h
  rw [hcardsum] at hsubg
  have hnodesep := finitePairSum_shortRange_le_of_separated (c := c) (p := p) (δ := δs) hc0 hp1 hδs0
    nodes (fun t t' htt => by rw [hδs2]; exact hsepm hm8 t t' htt)
  have hpatch : finitePairSum (shortRangeKernel8 c p) nodes ≤ Kδ*(N*max Kg 0) := by
    calc finitePairSum (shortRangeKernel8 c p) nodes
        ≤ Kδ*(finitePairSum (sphereGaussianKernel8 (c/2)) nodes-
            Fintype.card (Fin K × (Fin 8 → NodeIndex (a*m)))) := hnodesep
      _ ≤ Kδ*(N*max Kg 0) := by
          apply mul_le_mul_of_nonneg_left _ hKδ0
          have h1 : finitePairSum (sphereGaussianKernel8 (c/2)) (fun i => Y i)-N ≤ N*Kg := hgY
          have h2 : N*Kg ≤ N*max Kg 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hNR.le
          linarith
  -- the residual part: the block gap is at most η·(dm)^12
  have hgap : (blk-(energy4 Y-(7/16:ℝ)*N^2))/w ≤ N*(32/(3-p)) := by
    have hlowE : (predictedCoefficient-η/4)*((d*m:ℕ):ℝ)^12 ≤ energy4 Y-(7/16:ℝ)*N^2 := by
      have h := hlowY
      rw [hnormY, le_div_iff₀ (by positivity)] at h
      exact h
    have hblk' : blk ≤ (predictedCoefficient+η/2+η/4)*((d*m:ℕ):ℝ)^12 := by
      have h := hblock
      rw [div_lt_iff₀ (by positivity)] at h
      exact h.le
    rw [div_le_iff₀ hw0]
    have he : N*(32/(3-p))*w = η*((d*m:ℕ):ℝ)^12 := by
      rw [hw, hN, hθ]
      field_simp
    rw [he]
    linarith
  have hfinal : finitePairSum (shortRangeKernel8 c p) (fun i => Y i) ≤
      N*(Kδ*max Kg 0+36/(3-p)) := by
    have h4 : 4*N/(3-p) = N*(4/(3-p)) := by ring
    have h36 : N*(Kδ*max Kg 0+36/(3-p)) = Kδ*(N*max Kg 0)+N*(32/(3-p))+N*(4/(3-p)) := by
      field_simp
      ring
    rw [h36]
    calc finitePairSum (shortRangeKernel8 c p) (fun i => Y i)
        ≤ finitePairSum (shortRangeKernel8 c p) nodes+(blk-(energy4 Y-(7/16:ℝ)*N^2))/w+
            4*N/(3-p) := hS
      _ ≤ Kδ*(N*max Kg 0)+N*(32/(3-p))+N*(4/(3-p)) := by
          rw [h4]
          linarith
  rw [div_le_iff₀ hNR]
  linarith

end SphericalRiesz
