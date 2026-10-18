import Riesz.E8InteriorFullRow
import Riesz.E8PotentialApprox

/-!
# All original flat E8 rows, including boundary corrections

A fixed padded interior box has cardinality (m-8-2k)^8. Its fraction
tends to one for each fixed k. Combining the sharp C/k^2 interior
estimate with the already proved uniform bound on every original row
proves the full row mean limit. The stronger O(1/m) rate is unnecessary
here: first let m grow, then k grow. The neutralized energy still needs
the separately unproved potential quadrature estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SphericalRiesz
open Boundary

def paddedInteriorIndex (m k : ℕ) (w : Fin (m-8-2*k)) : Fin (m-8) :=
  ⟨w.val+k, by have hw := w.isLt; omega⟩

def paddedCubeIndex (d m k : ℕ) (w : Fin d → Fin (m-8-2*k)) : Fin d → NodeIndex m :=
  fun i => interiorNodeIndex (paddedInteriorIndex m k (w i))

def paddedCubeSet (d m k : ℕ) : Finset (Fin d → NodeIndex m) := by
  classical
  exact Finset.univ.image (paddedCubeIndex d m k)

theorem paddedCubeIndex_injective (d m k : ℕ) : Function.Injective (paddedCubeIndex d m k) := by
  intro w v h
  funext i
  apply Fin.ext
  have hi := interiorNodeIndex_injective m (congrFun h i)
  have hi' := congrArg Fin.val hi
  change (w i).val+k = (v i).val+k at hi'
  omega

theorem paddedCubeSet_card (d m k : ℕ) : (paddedCubeSet d m k).card = (m-8-2*k)^d := by
  classical
  rw [paddedCubeSet, Finset.card_image_of_injective _ (paddedCubeIndex_injective d m k)]
  simp only [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]

theorem paddedInteriorIndex_padding (d m k : ℕ) (w : Fin d → Fin (m-8-2*k)) :
    InteriorPadding d m (fun i => paddedInteriorIndex m k (w i)) (k:ℝ) := by
  intro i
  have hw := (w i).isLt
  have hi : k ≤ (paddedInteriorIndex m k (w i)).val := by
    dsimp only [paddedInteriorIndex]
    omega
  have hj : (paddedInteriorIndex m k (w i)).val+k+9 ≤ m := by
    dsimp only [paddedInteriorIndex]
    omega
  constructor
  · exact_mod_cast hi
  · have hj' : (paddedInteriorIndex m k (w i) : ℝ)+(k:ℝ)+9 ≤ m := by exact_mod_cast hj
    linarith

def paddedCubeFraction (d m k : ℕ) : ℝ := ((m-8-2*k:ℕ):ℝ)^d/(m:ℝ)^d

theorem paddedCubeFraction_limit (d k : ℕ) :
    Tendsto (fun m : ℕ => paddedCubeFraction d m k) atTop (𝓝 1) := by
  have hr : Tendsto (fun m : ℕ => ((m-8-2*k:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (8+2*k:ℝ)).const_sub 1
    apply (show Tendsto (fun m : ℕ => 1-(8+2*k:ℝ)/(m:ℝ)) atTop (𝓝 1) from by simpa using h).congr'
    filter_upwards [eventually_ge_atTop (8+2*k+1)] with m hm
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have he : ((m-8-2*k:ℕ):ℝ) = (m:ℝ)-(8+2*k:ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [he]
    field_simp
  simpa only [paddedCubeFraction, div_pow, one_pow] using hr.pow d

/-- A generic finite mean estimate; no geometry or asymptotic assumptions. -/
theorem finite_mean_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (good : Finset ι) (f : ι → ℝ) (c a b : ℝ) (ha0 : 0 ≤ a)
    (hn : 0 < Fintype.card ι)
    (ha : ∀ v ∈ good, |f v-c| ≤ a)
    (hb : ∀ v ∉ good, |f v-c| ≤ b) :
    |(∑ v, f v)/(Fintype.card ι:ℝ)-c| ≤
      a+((Finset.univ \ good).card:ℝ)/(Fintype.card ι:ℝ)*b := by
  have hnr : (0:ℝ) < Fintype.card ι := by exact_mod_cast hn
  have heq : (∑ v, f v)/(Fintype.card ι:ℝ)-c =
      (∑ v, (f v-c))/(Fintype.card ι:ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hsum : (∑ v, |f v-c|) ≤
      (good.card:ℝ)*a+((Finset.univ \ good).card:ℝ)*b := by
    rw [← Finset.sum_sdiff (Finset.subset_univ good)]
    have hg := Finset.sum_le_sum (fun v hv => ha v hv)
    have hd := Finset.sum_le_sum (s := Finset.univ \ good)
      (fun v hv => hb v (Finset.mem_sdiff.1 hv).2)
    simpa [add_comm] using add_le_add hd hg
  have hcard : (good.card:ℝ) ≤ (Fintype.card ι:ℝ) := by
    exact_mod_cast (show good.card ≤ Fintype.card ι from Finset.card_le_card (Finset.subset_univ good))
  rw [heq, abs_div, abs_of_pos hnr]
  calc
    _ ≤ ((good.card:ℝ)*a+((Finset.univ \ good).card:ℝ)*b)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans hsum) hnr.le
    _ ≤ ((Fintype.card ι:ℝ)*a+((Finset.univ \ good).card:ℝ)*b)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hcard ha0) le_rfl) hnr.le
    _ = _ := by field_simp

def e8FullRow (m : ℕ) (v : Fin 8 → NodeIndex m) : ℝ :=
  (m:ℝ)^4 * (cubeQuadrature 8 m (obliqueRieszFour 8 e8Map (cubeNode 8 m v)) -
    ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map (cubeNode 8 m v) y)

def e8FullRowMean (m : ℕ) : ℝ := (∑ v : Fin 8 → NodeIndex m, e8FullRow m v)/(m:ℝ)^8

theorem e8FullRow_interior (m : ℕ) (j : Fin 8 → Fin (m-8)) :
    e8FullRow m (e8InteriorIndex m j) = e8InteriorFullRow m j := rfl

theorem e8FullRow_uniform_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, 8 ≤ m → ∀ v : Fin 8 → NodeIndex m,
      |e8FullRow m v-(-5*Real.pi^2/6)| ≤ B := by
  obtain ⟨C, hC, hb⟩ := e8FlatRow_error_bound
  refine ⟨C+|-5*Real.pi^2/6|, by positivity, ?_⟩
  intro m hm v
  have hmr : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrow : |e8FullRow m v| ≤ C := by
    rw [e8FullRow, abs_mul, abs_of_nonneg (pow_nonneg hmr.le 4)]
    calc
      _ ≤ (m:ℝ)^4*(C/(m:ℝ)^4) := mul_le_mul_of_nonneg_left (hb m hm v) (by positivity)
      _ = C := by field_simp
  exact (abs_sub _ _).trans (add_le_add hrow le_rfl)

theorem e8FullRowMean_padding_bound :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ k : ℕ, 2 ≤ k → ∀ m : ℕ, 9 ≤ m →
      |e8FullRowMean m-(-5*Real.pi^2/6)| ≤
        C/(k:ℝ)^2+B*(1-paddedCubeFraction 8 m k) := by
  classical
  obtain ⟨C, hC, hc⟩ := e8InteriorFullRow_padding_bound
  obtain ⟨B, hB, hb⟩ := e8FullRow_uniform_bound
  refine ⟨C, B, hC, hB, ?_⟩
  intro k hk m hm
  have hcard : Fintype.card (Fin 8 → NodeIndex m) = m^8 := cubeNode_card 8 m (by omega)
  have hn : 0 < Fintype.card (Fin 8 → NodeIndex m) := by rw [hcard]; positivity
  have hg (v : Fin 8 → NodeIndex m) (hv : v ∈ paddedCubeSet 8 m k) :
      |e8FullRow m v-(-5*Real.pi^2/6)| ≤ C/(k:ℝ)^2 := by
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    change |e8InteriorFullRow m (fun i => paddedInteriorIndex m k (w i))-(-5*Real.pi^2/6)| ≤ _
    exact hc m hm _ (k:ℝ) (by exact_mod_cast hk) (paddedInteriorIndex_padding 8 m k w)
  have h := finite_mean_error_bound (paddedCubeSet 8 m k) (e8FullRow m) (-5*Real.pi^2/6)
    (C/(k:ℝ)^2) B (by positivity) hn hg (fun v _ => hb m (by omega) v)
  have hbad : ((Finset.univ \ paddedCubeSet 8 m k).card:ℝ) =
      (m:ℝ)^8-((m-8-2*k:ℕ):ℝ)^8 := by
    have ht := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (paddedCubeSet 8 m k))
    rw [paddedCubeSet_card, Finset.card_univ, hcard] at ht
    have ht' : ((Finset.univ \ paddedCubeSet 8 m k).card:ℝ)+((m-8-2*k:ℕ):ℝ)^8 = (m:ℝ)^8 := by exact_mod_cast ht
    linarith
  have hmr : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  simp only [hcard, Nat.cast_pow] at h
  change |e8FullRowMean m-(-5*Real.pi^2/6)| ≤ _ at h
  rw [hbad] at h
  convert h using 1
  unfold paddedCubeFraction
  field_simp

theorem e8FullRowMean_limit : Tendsto e8FullRowMean atTop (𝓝 (-5*Real.pi^2/6)) := by
  obtain ⟨C, B, hC, hB, hb⟩ := e8FullRowMean_padding_bound
  have hk : Tendsto (fun k : ℕ => C/(k:ℝ)^2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk2, hka⟩ := ((eventually_ge_atTop (2:ℕ)).and
    (hk.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2)))).exists
  have hf : Tendsto (fun m : ℕ => B*(1-paddedCubeFraction 8 m k)) atTop (𝓝 0) := by
    simpa using ((paddedCubeFraction_limit 8 k).const_sub 1).const_mul B
  filter_upwards [eventually_ge_atTop (9:ℕ),
    hf.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))] with m hm he
  rw [Real.dist_eq]
  have h := hb k hk2 m hm
  linarith

theorem e8FullRowMean_normalized_limit :
    Tendsto (fun m : ℕ => e8FullRowMean m/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact e8FullRowMean_limit.div_const _

def e8FlatPairEnergy (m : ℕ) : ℝ :=
  ∑ v : Fin 8 → NodeIndex m, ∑ w ∈ Finset.univ.erase v,
    (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4

theorem e8FlatPairEnergy_eq_full (m : ℕ) :
    e8FlatPairEnergy m = ∑ v : Fin 8 → NodeIndex m, ∑ w : Fin 8 → NodeIndex m,
      (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4 := by
  classical
  unfold e8FlatPairEnergy
  apply Finset.sum_congr rfl
  intro v _
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 8 → NodeIndex m))
    (fun w => (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4) (Finset.mem_univ v)
  simpa only [dist_self, inv_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0), add_zero] using h

/-- Actual off-diagonal pair energy minus one actual background. -/
theorem e8FullRowMean_eq_pair_background (m : ℕ) (hm : 0 < m) :
    e8FullRowMean m = (m:ℝ)^4 *
      (e8FlatPairEnergy m/(m:ℝ)^16-cubeQuadrature 8 m e8Potential) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum : (∑ v : Fin 8 → NodeIndex m,
      cubeQuadrature 8 m (obliqueRieszFour 8 e8Map (cubeNode 8 m v))) =
      e8FlatPairEnergy m/(m:ℝ)^8 := by
    simp_rw [cubeQuadrature_as_node_sum, obliqueRieszFour_eq_dist]
    change (∑ v : Fin 8 → NodeIndex m, (∑ w : Fin 8 → NodeIndex m,
      (dist (WithLp.toLp 2 (e8TensorNode m v) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4)/(m:ℝ)^8) = _
    rw [← Finset.sum_div, e8FlatPairEnergy_eq_full]
  unfold e8FullRowMean
  simp only [e8FullRow, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum, cubeQuadrature_as_node_sum]
  simp only [e8Potential]
  field_simp

def e8FlatBackgroundError (m : ℕ) : ℝ := (m:ℝ)^4 *
  (cubeQuadrature 8 m e8Potential-∫ x in UnitCube 8, e8Potential x)

/-- The actual neutralized finite energy at the second-term scale m^-12. -/
def e8FlatNeutralizedEnergy (m : ℕ) : ℝ := (m:ℝ)^4 *
  (e8FlatPairEnergy m/(m:ℝ)^16-2*cubeQuadrature 8 m e8Potential+
    ∫ x in UnitCube 8, e8Potential x)

theorem e8FlatNeutralizedEnergy_eq (m : ℕ) (hm : 0 < m) :
    e8FlatNeutralizedEnergy m = e8FullRowMean m-e8FlatBackgroundError m := by
  rw [e8FullRowMean_eq_pair_background m hm]
  unfold e8FlatNeutralizedEnergy e8FlatBackgroundError
  ring

/-- Conditional assembly only: the background error limit remains a separate obligation. -/
theorem e8FlatNeutralizedEnergy_limit_of_background
    (hb : Tendsto e8FlatBackgroundError atTop (𝓝 0)) :
    Tendsto e8FlatNeutralizedEnergy atTop (𝓝 (-5*Real.pi^2/6)) := by
  apply (show Tendsto (fun m => e8FullRowMean m-e8FlatBackgroundError m)
    atTop (𝓝 (-5*Real.pi^2/6)) from by simpa using e8FullRowMean_limit.sub hb).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  exact (e8FlatNeutralizedEnergy_eq m (by omega)).symm

theorem e8FlatBackgroundError_limit_of_bound
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 9 ≤ m →
      |cubeQuadrature 8 m e8Potential-∫ x in UnitCube 8, e8Potential x| ≤ C/(m:ℝ)^5) :
    Tendsto e8FlatBackgroundError atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := hb
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun m => abs_nonneg (e8FlatBackgroundError m)))
    (show ∀ᶠ m : ℕ in atTop, |e8FlatBackgroundError m| ≤ C/(m:ℝ) from by
      filter_upwards [eventually_ge_atTop (9:ℕ)] with m hm
      have hmr : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      rw [e8FlatBackgroundError, abs_mul, abs_of_nonneg (pow_nonneg hmr.le 4)]
      calc
        _ ≤ (m:ℝ)^4*(C/(m:ℝ)^5) := mul_le_mul_of_nonneg_left (hc m hm) (by positivity)
        _ = C/(m:ℝ) := by field_simp)
    (tendsto_const_div_atTop_nhds_zero_nat C)

#print axioms paddedCubeIndex_injective
#print axioms paddedCubeSet_card
#print axioms paddedInteriorIndex_padding
#print axioms paddedCubeFraction_limit
#print axioms finite_mean_error_bound
#print axioms e8FullRow_interior
#print axioms e8FullRow_uniform_bound
#print axioms e8FullRowMean_padding_bound
#print axioms e8FullRowMean_limit
#print axioms e8FullRowMean_normalized_limit
#print axioms e8FlatPairEnergy_eq_full
#print axioms e8FullRowMean_eq_pair_background
#print axioms e8FlatNeutralizedEnergy_eq
#print axioms e8FlatNeutralizedEnergy_limit_of_background
#print axioms e8FlatBackgroundError_limit_of_bound

end SphericalRiesz
