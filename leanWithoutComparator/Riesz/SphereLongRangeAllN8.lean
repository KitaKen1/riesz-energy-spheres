import Riesz.SphereLongRangeSubsequence8
import Riesz.LongRangeRescale8
import Riesz.RationalSizeFloor8

/-! Sharp `s = 4` configurations with a bounded long-range block for every large `N`.

For `N` take the rational size `M = (dm)⁸ ≤ N` just below it, a configuration `Y_M` with sharp
`s = 4` energy and long-range block `O(M)` (density factor `c_M`), raise the density factor to
`c_N` (`longRangeBlock8_rescale_le`, cost `M K_E/(p+1)`), and add the `N - M` missing points by
the joint first-moment choice (`sphere8_joint_longRange_addition`) with weight `w = θ √N`.  Since
`M/N → 1`, the `s = 4` normalized energy stays below the sharp coefficient plus `η`, and the
block gap is at most `η N^{3/2}`, so the normalized long-range block is bounded by one constant
for every `η ≤ 1`. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem energy4_sub_eq_normalized {N : ℕ} (hN : 0 < N) (Y : Configuration N) :
    energy4 Y-(7/16:ℝ)*(N:ℝ)^2 = normalizedEnergy Y*((N:ℝ)*Real.sqrt N) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNR
  unfold normalizedEnergy
  field_simp

/-- The profile constant is bounded on bounded energies. -/
theorem profileConstE_le {E R : ℝ} (hE : |E| ≤ R) :
    profileConstE E ≤ Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*R+1)) := by
  unfold profileConstE
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h8 : 0 ≤ 8/Real.sqrt 210 := by positivity
  have h1 : |(2/3)*((8/Real.sqrt 210)*E+1)| ≤ (2/3)*((8/Real.sqrt 210)*R+1) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2/3)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc |(8/Real.sqrt 210)*E+1| ≤ |(8/Real.sqrt 210)*E|+|(1:ℝ)| := abs_add_le _ _
      _ = (8/Real.sqrt 210)*|E|+1 := by rw [abs_mul, abs_of_nonneg h8, abs_one]
      _ ≤ (8/Real.sqrt 210)*R+1 := by
          have := mul_le_mul_of_nonneg_left hE h8
          linarith
  linarith

/-- Adding `r` points to a configuration with the joint first-moment choice. -/
theorem configuration_add_points {M N r : ℕ} (hMN : M+r = N) (Y : Configuration M) {c p w : ℝ}
    (hc : 0 ≤ c) (hp : -1 < p) (hw : 0 < w) :
    ∃ Y' : Configuration N,
      energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 ≤ (energy4 Y-(7/16:ℝ)*(M:ℝ)^2)+
        w*(kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ M+(r:ℝ)/(p+1)) ∧
      kernelBlock8 (longRangeKernel8 c p) (fun i => Y' i) univ (N:ℝ) ≤
        kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ M+
          ((energy4 Y-(7/16:ℝ)*(M:ℝ)^2)-(energy4 Y'-(7/16:ℝ)*(N:ℝ)^2))/w+(r:ℝ)/(p+1) := by
  classical
  subst hMN
  obtain ⟨Z, hZ, havoid, hblock, hlong⟩ := sphere8_joint_longRange_addition (r := r)
    (fun i => Y i) (M:ℝ) hc hp hw
  have hinj : Function.Injective (Sum.elim (fun i => Y i) Z) := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Y.2 huv)
      | inr v => exact False.elim (havoid v ⟨u, huv⟩)
    | inr u =>
      cases v with
      | inl v => exact False.elim (havoid u ⟨v, huv.symm⟩)
      | inr v => exact congrArg Sum.inr (hZ huv)
  let e : Fin M ⊕ Fin r ≃ Fin (M+r) := finSumFinEquiv
  let Y' : Configuration (M+r) := ⟨(Sum.elim (fun i => Y i) Z) ∘ e.symm, hinj.comp e.symm.injective⟩
  have hYfun : (fun i => Y' i) ∘ e = Sum.elim (fun i => Y i) Z := by
    funext u
    simp [Y']
  have hcast : ((M+r:ℕ):ℝ) = (M:ℝ)+r := by push_cast; ring
  have hE' : energy4 Y'-(7/16:ℝ)*((M+r:ℕ):ℝ)^2 =
      sphereFiniteBlock4 (Sum.elim (fun i => Y i) Z) univ ((M:ℝ)+r) := by
    rw [← sphereFiniteBlock4_eq_energy4 Y', ← hcast]
    have h := sphereFiniteBlock4_reindex e (fun i => Y' i) univ ((M+r:ℕ):ℝ)
    rw [hYfun] at h
    exact h.symm
  have hE : energy4 Y-(7/16:ℝ)*(M:ℝ)^2 = sphereFiniteBlock4 (fun i => Y i) univ (M:ℝ) :=
    (sphereFiniteBlock4_eq_energy4 Y).symm
  have hL' : kernelBlock8 (longRangeKernel8 c p) (fun i => Y' i) univ ((M+r:ℕ):ℝ) =
      kernelBlock8 (longRangeKernel8 c p) (Sum.elim (fun i => Y i) Z) univ ((M:ℝ)+r) := by
    rw [← hcast]
    have h := kernelBlock8_reindex (longRangeKernel8 c p) e (fun i => Y' i) univ ((M+r:ℕ):ℝ)
    rw [hYfun] at h
    exact h.symm
  refine ⟨Y', ?_, ?_⟩
  · rw [hE', hE]
    exact hblock
  · rw [hL', hE', hE]
    exact hlong

/-- The constant of the all-`N` long-range bound. -/
def allNLongRangeConst (C p : ℝ) : ℝ :=
  (max C 0+Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*(|predictedCoefficient|+1)+1))/(p+1))+
    4*(max C 0+Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*(|predictedCoefficient|+1)+1))/(p+1)+
      1/(p+1))+1/(p+1)

set_option maxHeartbeats 1000000 in
/-- One step of the all-`N` construction: from `M ≤ N` points to `N` points. -/
theorem longRange_allN_step {p C η : ℝ} (hp1 : -1 < p) (hη : 0 < η) (hη1 : η ≤ 1)
    {M N : ℕ} (hM0 : 0 < M) (hMN : M ≤ N) (YM : Configuration M)
    (hYE : normalizedEnergy YM < predictedCoefficient+η/4)
    (hYlow : predictedCoefficient-1 ≤ normalizedEnergy YM)
    (hYL : kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 M) p) (fun i => YM i)
      univ M/(M:ℝ) ≤ C)
    (hlowN : ∀ X : Configuration N, predictedCoefficient-η/4 ≤ normalizedEnergy X)
    (hq : 1-η/(4*(|predictedCoefficient|+1)) ≤ ((M:ℝ)/N)*Real.sqrt ((M:ℝ)/N)) :
    ∃ Y : Configuration N, normalizedEnergy Y < predictedCoefficient+η ∧
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y i) univ N/
        (N:ℝ) ≤ allNLongRangeConst C p := by
  have hp0 : 0 < p+1 := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R, R = |predictedCoefficient|+1 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hRabs : |predictedCoefficient| ≤ R := by rw [hRdef]; linarith
  obtain ⟨KE, hKEdef⟩ : ∃ KE, KE = Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*R+1)) := ⟨_, rfl⟩
  have hKE0 : 0 ≤ KE := by rw [hKEdef]; positivity
  obtain ⟨CA, hCAdef⟩ : ∃ CA, CA = max C 0+KE/(p+1)+1/(p+1) := ⟨_, rfl⟩
  have hCA0 : 0 < CA := by
    have : 0 < 1/(p+1) := by positivity
    have : 0 ≤ KE/(p+1) := by positivity
    have : 0 ≤ max C 0 := le_max_right _ _
    rw [hCAdef]; linarith
  have hconst : allNLongRangeConst C p = max C 0+KE/(p+1)+4*CA+1/(p+1) := by
    rw [allNLongRangeConst, hCAdef, hKEdef, hRdef]
  rw [hconst]
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = η/(4*CA) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = η/(4*R) := ⟨_, rfl⟩
  have hN0 : 0 < N := lt_of_lt_of_le hM0 hMN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hMN' : (M:ℝ) ≤ N := by exact_mod_cast hMN
  obtain ⟨r, hr⟩ : ∃ r, M+r = N := ⟨N-M, by omega⟩
  have hrN : (r:ℝ) ≤ N := by
    have : r ≤ N := by omega
    exact_mod_cast this
  -- the profile constant of Y_M
  have hYabs : |normalizedEnergy YM| ≤ R := by
    rw [abs_le]
    constructor
    · have := neg_abs_le predictedCoefficient
      rw [hRdef]; linarith
    · have := le_abs_self predictedCoefficient
      rw [hRdef]; linarith
  have hKY : profileConstE (normalizedEnergy YM) ≤ KE := by
    rw [hKEdef]; exact profileConstE_le hYabs
  -- raise the density factor from `c_M` to `c_N`
  have hcM := sphereGaussianDensityFactor8_pos hM0
  obtain ⟨l, hldef⟩ : ∃ l, l = sphereGaussianDensityFactor8 N/sphereGaussianDensityFactor8 M :=
    ⟨_, rfl⟩
  have hl1 : 1 ≤ l := by
    rw [hldef, le_div_iff₀ hcM, one_mul]
    unfold sphereGaussianDensityFactor8 sphereGaussianScale8
    have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
    have hle : (M:ℝ)/sphereArea8.real univ ≤ (N:ℝ)/sphereArea8.real univ :=
      div_le_div_of_nonneg_right hMN' hA.le
    have := Real.rpow_le_rpow (by positivity) hle (by norm_num : (0:ℝ) ≤ 1/4)
    nlinarith [Real.pi_pos]
  have hlc : l*sphereGaussianDensityFactor8 M = sphereGaussianDensityFactor8 N := by
    rw [hldef]; field_simp
  have hresc := longRangeBlock8_rescale_le hM0 YM hl1 hp1
  rw [hlc] at hresc
  have hYL' : kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 M) p) (fun i => YM i)
      univ M ≤ M*max C 0 := by
    have h := hYL
    rw [div_le_iff₀ hMR] at h
    have : C*(M:ℝ) ≤ M*max C 0 := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hMR.le
    linarith
  have hXL : kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => YM i)
      univ M ≤ M*(max C 0+KE/(p+1)) := by
    have h2 : (M:ℝ)*profileConstE (normalizedEnergy YM)/(p+1) ≤ M*(KE/(p+1)) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hMR.le
      exact div_le_div_of_nonneg_right hKY hp0.le
    have h3 : (M:ℝ)*(max C 0+KE/(p+1)) = M*max C 0+M*(KE/(p+1)) := by ring
    linarith
  -- add the missing points
  obtain ⟨w, hwdef⟩ : ∃ w, w = θ*Real.sqrt N := ⟨_, rfl⟩
  have hsN : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNR
  have hw0 : 0 < w := by rw [hwdef]; positivity
  obtain ⟨Y', hYE', hYL''⟩ := configuration_add_points hr YM
    (c := sphereGaussianDensityFactor8 N) (p := p) (sphereGaussianDensityFactor8_pos hN0).le
    hp1 hw0
  have hEM := energy4_sub_eq_normalized hM0 YM
  have hEN := energy4_sub_eq_normalized hN0 Y'
  obtain ⟨q, hqdef⟩ : ∃ q, q = ((M:ℝ)/N)*Real.sqrt ((M:ℝ)/N) := ⟨_, rfl⟩
  have hq' : 1-κ ≤ q := by rw [hκdef, hqdef, hRdef]; exact hq
  have hq0' : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have h1 : (M:ℝ)/N ≤ 1 := (div_le_one hNR).mpr hMN'
    have h2 : Real.sqrt ((M:ℝ)/N) ≤ 1 := Real.sqrt_le_one.mpr h1
    calc (M:ℝ)/N*Real.sqrt ((M:ℝ)/N) ≤ 1*1 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hqM : (M:ℝ)*Real.sqrt M = q*((N:ℝ)*Real.sqrt N) := by
    rw [hqdef, Real.sqrt_div hMR.le]
    field_simp
  have hNsN : 0 < (N:ℝ)*Real.sqrt N := by positivity
  have hκq : 1-q ≤ κ := by linarith
  have hRκ : R*κ = η/4 := by rw [hκdef]; field_simp
  -- the cost of the added points
  have hcost : w*(kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p)
      (fun i => YM i) univ M+(r:ℝ)/(p+1)) ≤ η/4*((N:ℝ)*Real.sqrt N) := by
    have h1 : kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p)
        (fun i => YM i) univ M+(r:ℝ)/(p+1) ≤ N*CA := by
      have h2 : (M:ℝ)*(max C 0+KE/(p+1)) ≤ N*(max C 0+KE/(p+1)) :=
        mul_le_mul_of_nonneg_right hMN' (by positivity)
      have h3 : (r:ℝ)/(p+1) ≤ N/(p+1) := div_le_div_of_nonneg_right hrN hp0.le
      have h4 : (N:ℝ)*CA = N*(max C 0+KE/(p+1))+N/(p+1) := by rw [hCAdef]; ring
      linarith
    calc w*(kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p)
          (fun i => YM i) univ M+(r:ℝ)/(p+1)) ≤ w*(N*CA) := mul_le_mul_of_nonneg_left h1 hw0.le
      _ = η/4*((N:ℝ)*Real.sqrt N) := by rw [hwdef, hθdef]; field_simp
  -- the energy of the enlarged configuration
  have hdev : |predictedCoefficient+η/4| * (1-q) ≤ η/4 := by
    have h1 : |predictedCoefficient+η/4| ≤ R := by
      have h2 : |predictedCoefficient+η/4| ≤ |predictedCoefficient|+|η/4| := abs_add_le _ _
      rw [abs_of_pos (by positivity : 0 < η/4)] at h2
      rw [hRdef]; linarith
    calc |predictedCoefficient+η/4| * (1-q) ≤ R*κ :=
          mul_le_mul h1 hκq (by linarith) hR0.le
      _ = η/4 := hRκ
  have hx : (predictedCoefficient+η/4)*q ≤ predictedCoefficient+η/4+η/4 := by
    have hneg : -((predictedCoefficient+η/4)*(1-q)) ≤ |predictedCoefficient+η/4| * (1-q) := by
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    have hsplit : (predictedCoefficient+η/4)*q =
        (predictedCoefficient+η/4)-(predictedCoefficient+η/4)*(1-q) := by ring
    linarith
  have henergy : normalizedEnergy Y' < predictedCoefficient+η := by
    have h1 : energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 ≤
        (energy4 YM-(7/16:ℝ)*(M:ℝ)^2)+η/4*((N:ℝ)*Real.sqrt N) := by linarith
    rw [hEN, hEM, hqM] at h1
    have h2 : normalizedEnergy YM*(q*((N:ℝ)*Real.sqrt N)) ≤
        (predictedCoefficient+η/4)*(q*((N:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_right hYE.le (by positivity)
    have h3 : normalizedEnergy Y'*((N:ℝ)*Real.sqrt N) ≤
        ((predictedCoefficient+η/4)*q+η/4)*((N:ℝ)*Real.sqrt N) := by
      calc normalizedEnergy Y'*((N:ℝ)*Real.sqrt N)
          ≤ normalizedEnergy YM*(q*((N:ℝ)*Real.sqrt N))+η/4*((N:ℝ)*Real.sqrt N) := h1
        _ ≤ (predictedCoefficient+η/4)*(q*((N:ℝ)*Real.sqrt N))+η/4*((N:ℝ)*Real.sqrt N) :=
            add_le_add h2 le_rfl
        _ = ((predictedCoefficient+η/4)*q+η/4)*((N:ℝ)*Real.sqrt N) := by ring
    have h4 := le_of_mul_le_mul_right h3 hNsN
    linarith
  refine ⟨Y', henergy, ?_⟩
  -- the long-range block of the enlarged configuration
  have hgap : ((energy4 YM-(7/16:ℝ)*(M:ℝ)^2)-(energy4 Y'-(7/16:ℝ)*(N:ℝ)^2))/w ≤ N*(4*CA) := by
    have hupM : energy4 YM-(7/16:ℝ)*(M:ℝ)^2 ≤ (predictedCoefficient+η/4)*q*((N:ℝ)*Real.sqrt N) := by
      rw [hEM, hqM, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hNsN.le
      exact mul_le_mul_of_nonneg_right hYE.le hq0'
    have hlowY : (predictedCoefficient-η/4)*((N:ℝ)*Real.sqrt N) ≤ energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 := by
      rw [hEN]
      exact mul_le_mul_of_nonneg_right (hlowN Y') hNsN.le
    have hdiff : (predictedCoefficient+η/4)*q-(predictedCoefficient-η/4) ≤ η := by
      have h1 : |predictedCoefficient| * (1-q) ≤ η/4 := by
        calc |predictedCoefficient| * (1-q) ≤ R*κ := mul_le_mul hRabs hκq (by linarith) hR0.le
          _ = η/4 := hRκ
      have h4 : predictedCoefficient*(q-1) ≤ |predictedCoefficient| * (1-q) := by
        have h5 : predictedCoefficient*(q-1) = (-predictedCoefficient)*(1-q) := by ring
        rw [h5]
        exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
      have h6 : (predictedCoefficient+η/4)*q-(predictedCoefficient-η/4) =
          predictedCoefficient*(q-1)+η/4*q+η/4 := by ring
      have h7 : η/4*q ≤ η/4 := by
        have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0:ℝ) ≤ η/4)
        linarith
      rw [h6]
      linarith
    rw [div_le_iff₀ hw0]
    have hwN : N*(4*CA)*w = η*((N:ℝ)*Real.sqrt N) := by
      rw [hwdef, hθdef]; field_simp
    rw [hwN]
    have := mul_le_mul_of_nonneg_right hdiff hNsN.le
    have e1 : ((predictedCoefficient+η/4)*q-(predictedCoefficient-η/4))*((N:ℝ)*Real.sqrt N) =
        (predictedCoefficient+η/4)*q*((N:ℝ)*Real.sqrt N)-
          (predictedCoefficient-η/4)*((N:ℝ)*Real.sqrt N) := by ring
    linarith
  rw [div_le_iff₀ hNR]
  have h1 : kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y' i)
      univ N ≤ M*(max C 0+KE/(p+1))+N*(4*CA)+(r:ℝ)/(p+1) := by
    linarith
  have h2 : (M:ℝ)*(max C 0+KE/(p+1)) ≤ N*(max C 0+KE/(p+1)) :=
    mul_le_mul_of_nonneg_right hMN' (by positivity)
  have h3 : (r:ℝ)/(p+1) ≤ N*(1/(p+1)) := by
    rw [← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right hrN hp0.le
  have e2 : (max C 0+KE/(p+1)+4*CA+1/(p+1))*(N:ℝ) =
      N*(max C 0+KE/(p+1))+N*(4*CA)+N*(1/(p+1)) := by ring
  linarith

theorem sphere8_joint_sharp_longRange_allN
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {p : ℝ} (hp1 : -1 < p) :
    ∃ C' : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+η ∧
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y i) univ N/
        (N:ℝ) ≤ C' := by
  obtain ⟨C, hC⟩ := sphere8_joint_sharp_longRange_subsequence hlow4 hp1
  refine ⟨allNLongRangeConst C p, fun η hη hη1 => ?_⟩
  obtain ⟨d, hd, hev⟩ := hC (η/4) (by positivity) (by linarith)
  obtain ⟨N₀, hN₀⟩ := hlow4 (η/4) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hlow4 1 one_pos
  have hq : Tendsto (fun N : ℕ => ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))*
      Real.sqrt ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))) atTop (𝓝 1) := by
    have h := rationalSizeFloor8_ratio_tendsto d hd
    simpa only [Real.sqrt_one, mul_one] using h.mul h.sqrt
  have hκ0 : 0 < η/(4*(|predictedCoefficient|+1)) := by positivity
  have hqev : ∀ᶠ N : ℕ in atTop, 1-η/(4*(|predictedCoefficient|+1)) ≤
      ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))*Real.sqrt ((rationalSizeFloor8 d N:ℝ)/(N:ℝ)) :=
    hq.eventually (Ici_mem_nhds (by linarith))
  have hmev := (rationalSizeFloorIndex8_tendsto d hd).eventually hev
  have hMlarge : ∀ᶠ N : ℕ in atTop, max N₁ 1 ≤ rationalSizeFloor8 d N := by
    have h := (rationalSizeFloorIndex8_tendsto d hd).eventually (eventually_ge_atTop (max N₁ 1))
    filter_upwards [h] with N hN
    unfold rationalSizeFloor8
    have h1 : rationalSizeFloorIndex8 d N ≤ d*rationalSizeFloorIndex8 d N :=
      Nat.le_mul_of_pos_left _ hd
    have h2 : d*rationalSizeFloorIndex8 d N ≤ (d*rationalSizeFloorIndex8 d N)^8 :=
      Nat.le_self_pow (by norm_num) _
    omega
  filter_upwards [hqev, hmev, hMlarge, eventually_ge_atTop N₀] with N hqN hmN hMbig hNN₀
  obtain ⟨YM, hYE, hYL⟩ := hmN
  have hMN : rationalSizeFloor8 d N ≤ N := rationalSizeFloor8_le d N hd
  have hM0 : 0 < rationalSizeFloor8 d N := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hMbig)
  have hYnorm : normalizedEnergy YM < predictedCoefficient+η/4 := by
    rw [normalizedEnergy_power_eight (d*rationalSizeFloorIndex8 d N) YM]
    exact hYE
  have hYlow := hN₁ (rationalSizeFloor8 d N) ((le_max_left _ _).trans hMbig) YM
  exact longRange_allN_step hp1 hη hη1 hM0 hMN YM hYnorm hYlow hYL (hN₀ N hNN₀) hqN

end SphericalRiesz
