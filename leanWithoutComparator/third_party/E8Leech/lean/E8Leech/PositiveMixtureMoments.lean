import E8Leech.GaussianPotentialMixtures
import E8Leech.LocalSecondMoments

/-!
# Local second moments from positive Gaussian mixture energy

One compact positive-parameter block supplies a positive pair-cost on every
bounded window. A single nonzero lattice vector makes that block's mass finite.
Neither a density for the mixing measure nor finite Riesz energy is needed.
These are moment prerequisites, not the actual CKMRV certificates or the
arbitrary-mixture stationary LP theorem.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem exists_positive_parameter_interval (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ν (Icc a b) ≠ 0 := by
  let A : ℕ → Set ℝ := fun n => Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hcover : Ioi (0 : ℝ) ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
    have hn0 : 0 < (n : ℝ) + 1 := by positivity
    have hupper : x ≤ (n : ℝ) + 1 := by
      have := (le_max_left x (1 / x)).trans_lt hn
      linarith
    have hinv : 1 / x < (n : ℝ) + 1 := by
      have := (le_max_right x (1 / x)).trans_lt hn
      linarith
    have hprod : 1 < ((n : ℝ) + 1) * x := by
      simpa only [mul_comm] using (div_lt_iff₀ hx).mp hinv
    exact mem_iUnion.mpr ⟨n, (div_le_iff₀ hn0).mpr (by nlinarith [hprod]), hupper⟩
  have hmass : ν (⋃ n, A n) ≠ 0 := by
    intro hz
    apply hν
    exact le_zero_iff.mp ((measure_mono hcover).trans (le_of_eq hz))
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  have hn0 : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, one_div_pos.mpr hn0, ?_, hn.ne'⟩
  apply (div_le_iff₀ hn0).mpr
  nlinarith [show 0 ≤ (n : ℝ) by positivity]

theorem gaussianPotential_lower_on_bounded_pairs {d : ℕ} {α b D : ℝ}
    (hb : 0 ≤ b) (hα : α ≤ b) (hD : 0 ≤ D)
    (x y : Ambient d) (hxy : dist x y ≤ D) :
    ENNReal.ofReal (Real.exp (-b * D ^ 2)) ≤ gaussianPotential α x y := by
  unfold gaussianPotential gaussianKernel
  rw [← dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hsquare : dist x y ^ 2 ≤ D ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
  nlinarith [sq_nonneg (dist x y), mul_nonneg hb (sub_nonneg.mpr hsquare),
    mul_nonneg (sub_nonneg.mpr hα) (sq_nonneg (dist x y))]

theorem positiveGaussianMixture_lower_on_parameter_interval {d : ℕ}
    (ν : Measure ℝ) {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D)
    (x y : Ambient d) (hxy : dist x y ≤ D) :
    ENNReal.ofReal (Real.exp (-b * D ^ 2)) * ν (Icc a b) ≤
      positiveGaussianMixturePotential ν x y := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun _ h => ha.trans_le h.1
  have hmass : (ν.restrict (Ioi 0)) (Icc a b) = ν (Icc a b) := by
    rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub]
  simpa only [hmass, positiveGaussianMixturePotential] using
    potentialMixture_lower_on_parameter_set (ν.restrict (Ioi 0)) gaussianPotential
      (A := Icc a b)
      measurableSet_Icc (ENNReal.ofReal (Real.exp (-b * D ^ 2))) x y
      (fun α hα => gaussianPotential_lower_on_bounded_pairs (ha.trans_le hab).le hα.2 hD x y hxy)

theorem positive_parameter_interval_mass_ne_top_of_pair {d : ℕ}
    (ν : Measure ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x y : Ambient d)
    (hfinite : positiveGaussianMixturePotential ν x y ≠ ∞) : ν (Icc a b) ≠ ∞ := by
  have hc : ENNReal.ofReal (Real.exp (-b * dist x y ^ 2)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  apply (ENNReal.lt_top_of_mul_ne_top_right (b := ν (Icc a b)) ?_ hc).ne
  exact ne_of_lt ((positiveGaussianMixture_lower_on_parameter_interval ν ha hab
    (dist_nonneg (x := x) (y := y)) x y le_rfl).trans_lt hfinite.lt_top)

theorem latticePotentialEnergy_single_vector_lower {d : ℕ}
    {Λ : Set (Ambient d)} (P : Ambient d → Ambient d → ℝ≥0∞)
    {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0) : P 0 z ≤ latticePotentialEnergy Λ P := by
  have h := ENNReal.le_tsum (f := fun y : Λ =>
    if (y : Ambient d) = 0 then 0 else P 0 y) ⟨z, hz⟩
  simpa only [hne, if_false, latticePotentialEnergy] using h

theorem positive_parameter_interval_mass_ne_top_of_lattice {d : ℕ}
    (ν : Measure ℝ) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ν (Icc a b) ≠ ∞ := by
  exact positive_parameter_interval_mass_ne_top_of_pair ν ha hab 0 z
    (ne_of_lt ((latticePotentialEnergy_single_vector_lower _ hz hne).trans_lt hfinite.lt_top))

theorem exists_finite_positive_parameter_interval_of_lattice {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ν (Icc a b) ≠ 0 ∧ ν (Icc a b) ≠ ∞ := by
  obtain ⟨a, b, ha, hab, hm⟩ := exists_positive_parameter_interval ν hν
  exact ⟨a, b, ha, hab, hm,
    positive_parameter_interval_mass_ne_top_of_lattice ν hz hne hfinite ha hab⟩

theorem exists_positiveGaussianMixture_bounded_pair_cost {d : ℕ}
    (ν : Measure ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hm0 : ν (Icc a b) ≠ 0) (hmtop : ν (Icc a b) ≠ ∞)
    {W : Set (Ambient d)} (hW : Bornology.IsBounded W) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧
      ∀ x ∈ W, ∀ y ∈ W, κ ≤ positiveGaussianMixturePotential ν x y := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hW
  let D := max R 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  let κ := ENNReal.ofReal (Real.exp (-b * D ^ 2)) * ν (Icc a b)
  refine ⟨κ, mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) hm0,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop, ?_⟩
  exact fun x hx y hy => positiveGaussianMixture_lower_on_parameter_interval ν ha hab hD.le
    x y ((hR hx hy).trans (le_max_left R 1))

theorem expected_unit_count_sq_ne_top_of_positiveGaussianMixture {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c
      (unitWindow d) ∂μ) ≠ ∞) :
    (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞ := by
  obtain ⟨a, b, ha, hab, hm0, hmtop⟩ :=
    exists_finite_positive_parameter_interval_of_lattice ν hν hz hne hfinite
  obtain ⟨κ, hκ0, hκtop, hκ⟩ := exists_positiveGaussianMixture_bounded_pair_cost ν ha hab
    hm0 hmtop (isBounded_unitWindow d)
  apply expected_window_count_sq_ne_top_of_cost μ (measurable_unitWindow d) κ hκ0 hκtop
    (positiveGaussianMixturePotential ν) (fun x hx y hy _ => hκ x hx y hy)
  · rwa [expected_count_unitWindow μ ρ hρ]
  · exact henergy

theorem exists_uniform_unit_second_moment_bound_of_positiveGaussianMixture {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (Δ : ℝ≥0∞) (hΔtop : Δ ≠ ∞)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ μ : Measure (Configuration (Ambient d)), HasIntensity μ 1 →
      (∫⁻ c, orderedWindowEnergy (positiveGaussianMixturePotential ν) c (unitWindow d) ∂μ) ≤
        latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) + Δ →
      (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≤ M := by
  obtain ⟨a, b, ha, hab, hm0, hmtop⟩ :=
    exists_finite_positive_parameter_interval_of_lattice ν hν hz hne hfinite
  obtain ⟨κ, hκ0, hκtop, hκ⟩ := exists_positiveGaussianMixture_bounded_pair_cost ν ha hab
    hm0 hmtop (isBounded_unitWindow d)
  refine ⟨1 + (latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) + Δ) / κ,
    ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.div_ne_top
      (ENNReal.add_ne_top.mpr ⟨hfinite, hΔtop⟩) hκ0⟩, ?_⟩
  intro μ hρ henergy
  have h := expected_window_count_sq_le_of_pair_cost μ (measurable_unitWindow d) κ hκ0 hκtop
    (positiveGaussianMixturePotential ν) (fun x hx y hy _ => hκ x hx y hy)
  rw [expected_count_unitWindow μ 1 hρ] at h
  exact h.trans (add_le_add le_rfl (ENNReal.div_le_div_right henergy κ))


theorem sigmaFinite_positive_parameter_restrict_of_pair {d : ℕ}
    (ν : Measure ℝ) (x y : Ambient d)
    (hfinite : positiveGaussianMixturePotential ν x y ≠ ∞) :
    SigmaFinite (ν.restrict (Ioi (0 : ℝ))) := by
  let A : ℕ → Set ℝ := fun n => Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hcover : Ioi (0 : ℝ) ⊆ ⋃ n, A n := by
    intro u hu
    obtain ⟨n, hn⟩ := exists_nat_gt (max u (1 / u))
    have hn0 : 0 < (n : ℝ) + 1 := by positivity
    have hup : u ≤ (n : ℝ) + 1 := by
      have := (le_max_left u (1 / u)).trans_lt hn
      linarith
    have hinv : 1 / u < (n : ℝ) + 1 := by
      have := (le_max_right u (1 / u)).trans_lt hn
      linarith
    have hprod := (div_lt_iff₀ hu).mp hinv
    exact mem_iUnion.mpr ⟨n, (div_le_iff₀ hn0).mpr (by nlinarith [hprod]), hup⟩
  apply sigmaFinite_iff.mpr
  refine ⟨{ set := fun n => A n ∪ Iic 0
            set_mem := fun _ => mem_univ _
            finite := ?_
            spanning := ?_ }⟩
  · intro n
    have hn0 : 0 < (n : ℝ) + 1 := by positivity
    have ha : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn0
    have hab : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith [show 0 ≤ (n : ℝ) by positivity]
    have hsub : A n ⊆ Ioi (0 : ℝ) := fun _ h => ha.trans_le h.1
    have he : (A n ∪ Iic 0) ∩ Ioi (0 : ℝ) = A n := by
      ext u
      constructor
      · rintro ⟨hleft, hpos⟩
        rcases hleft with hA | hneg
        · exact hA
        · exact False.elim (not_lt_of_ge (show u ≤ 0 from hneg) (show 0 < u from hpos))
      · intro hA
        exact ⟨Or.inl hA, hsub hA⟩
    rw [Measure.restrict_apply (measurableSet_Icc.union measurableSet_Iic), he]
    exact (positive_parameter_interval_mass_ne_top_of_pair ν ha hab x y hfinite).lt_top
  · apply eq_univ_of_forall
    intro u
    by_cases hu : 0 < u
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hu)
      exact mem_iUnion.mpr ⟨n, Or.inl hn⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr (not_lt.mp hu)⟩

theorem sigmaFinite_positive_parameter_restrict_of_lattice {d : ℕ}
    (ν : Measure ℝ) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞) :
    SigmaFinite (ν.restrict (Ioi (0 : ℝ))) :=
  sigmaFinite_positive_parameter_restrict_of_pair ν 0 z
    (ne_of_lt ((latticePotentialEnergy_single_vector_lower _ hz hne).trans_lt hfinite.lt_top))

theorem measurable_positiveGaussianMixturePotential_of_lattice {d : ℕ}
    (ν : Measure ℝ) {Λ : Set (Ambient d)} {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞) :
    Measurable (Function.uncurry (positiveGaussianMixturePotential (d := d) ν)) := by
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hfinite
  exact measurable_potentialMixture (ν.restrict (Ioi 0)) gaussianPotential
    (measurable_gaussianPotential_joint d)

end E8Leech
