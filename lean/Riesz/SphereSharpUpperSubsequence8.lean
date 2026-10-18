import Riesz.SmallE8PhysicalAssembly4

/-! A sharp physical upper coefficient along a fixed rational-size sequence.
Choose the local tolerance, then one near-full small patch family, and only
then let its original node count grow. Thus the fixed-family cross limit
requires no estimate uniform in shrinking patch gaps. All-N transfer and
the sharp Gaussian lower bound remain separate obligations. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem sphere8_exists_original_nodes_sharp_upper_subsequence
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∃ P : Fin K → SmallE8CubePatch8, ∃ a d : ℕ,
      ∃ ha : 0 < a, 0 < d ∧
      ∀ᶠ m : ℕ in atTop, ∃ hm : 8 ≤ m, ∃ Y : Configuration ((d*m)^8),
        (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
          ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
        (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 <
          predictedCoefficient+η := by
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
  obtain ⟨ρ,hρ,_hρb,M,hM,hlocal⟩ := equalAreaPatchNeutralized8_uniform_small δ hδ
  obtain ⟨K,P,a,d,ha,hd,hdata,hdis,hl,hu,hmass,hbudget,hcross,_⟩ :=
    sphere8_near_full_rational_energy_upper ρ b hρ hb
  have hε : ∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) :=
    fun i => (hdata i).1
  have hρd : ∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8 :=
    fun i => (hdata i).2.2.2
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
  refine ⟨K,P,a,d,ha,hd,?_⟩
  filter_upwards [eventually_ge_atTop (max 8 M),hc] with m hm hc
  have hm8 : 8 ≤ m := (le_max_left _ _).trans hm
  have hmn : M ≤ a*m := ((le_max_right _ _).trans hm).trans (Nat.le_mul_of_pos_left m ha)
  obtain ⟨Y,hY,hE⟩ := rationalCubeFamily8_exists_normalized_energy_upper
    P hdis hu a d m ha hd hm8 hbudget.le hmass hε hρd
  have hsum : (((a:ℝ)/d)^8/A)*
      (∑ i, curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
        (P i).g (P i).v (P i).c (P i).ε) (a*m)) ≤
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))*(predictedCoefficient+η/4) := by
    have hi (i : Fin K) : curvedNeutralizedEnergy8 (equalAreaNormalizedE8Patch
        (P i).g (P i).v (P i).c (P i).ε) (a*m) ≤ -5*Real.pi^2/6+δ := by
      have h := hlocal (P i).v (hdata i).2.1 (P i).ε (P i).ε_pos
        (hdata i).2.2.1 (P i).g (P i).c (P i).c_mem (a*m) hmn
      linarith [(abs_lt.mp h).2]
    calc
      _ ≤ (((a:ℝ)/d)^8/A)*(∑ _i : Fin K, (-5*Real.pi^2/6+δ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hmass]
        rw [predictedCoefficient_area_normalization]
        dsimp [δ,A]
        field_simp [hAz] <;> ring
  refine ⟨hm8,Y,hY,?_⟩
  change _ ≤ _ at hE
  change _ < _
  have htotal := hsum.trans hcoef
  dsimp [A] at htotal
  linarith

theorem sphere8_inverse_fourth_sharp_upper_subsequence (η : ℝ) (hη : 0 < η) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ Y : Configuration ((d*m)^8),
      (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2)/((d*m:ℕ):ℝ)^12 < predictedCoefficient+η := by
  obtain ⟨K,P,a,d,ha,hd,h⟩ := sphere8_exists_original_nodes_sharp_upper_subsequence η hη
  refine ⟨d,hd,?_⟩
  filter_upwards [h] with m hm
  obtain ⟨hm8,Y,_hY,hE⟩ := hm
  exact ⟨Y,hE⟩

theorem normalizedEnergy_power_eight (k : ℕ) (Y : Configuration (k^8)) :
    normalizedEnergy Y = (energy4 Y-(7/16:ℝ)*((k^8:ℕ):ℝ)^2)/(k:ℝ)^12 := by
  have hs : Real.sqrt ((k^8:ℕ):ℝ) = (k:ℝ)^4 := by
    rw [Nat.cast_pow,show (k:ℝ)^8 = ((k:ℝ)^4)^2 by ring,
      Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg k) 4)]
  unfold normalizedEnergy
  rw [hs]
  congr 1
  rw [Nat.cast_pow]
  ring

theorem sphere8_inverse_fourth_sharp_normalized_upper_subsequence (η : ℝ) (hη : 0 < η) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ Y : Configuration ((d*m)^8),
      normalizedEnergy Y < predictedCoefficient+η := by
  obtain ⟨d,hd,h⟩ := sphere8_inverse_fourth_sharp_upper_subsequence η hη
  refine ⟨d,hd,?_⟩
  filter_upwards [h] with m hm
  obtain ⟨Y,hY⟩ := hm
  exact ⟨Y,by rw [normalizedEnergy_power_eight]; exact hY⟩

end SphericalRiesz
