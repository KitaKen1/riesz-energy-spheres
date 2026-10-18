import E8Leech.UniformCellTails
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Summable integer-cell envelopes from polynomial decay

The coordinate sup norm gives a deliberately coarse envelope. Its summability
is transferred from the standard real-coordinate integer lattice, avoiding a
new shell-counting proof and avoiding conversion of lattice norms to Euclidean
norms. The original kernel still uses Euclidean distance.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def integerCellCoordinates {d : ℕ} (z : IntegerCellIndex d) : Fin d → ℝ :=
  fun i => (z i : ℝ)

def integerCoordinateLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

instance integerCoordinateLattice_discrete (d : ℕ) :
    DiscreteTopology (integerCoordinateLattice d) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))))

instance integerCoordinateLattice_isZLattice (d : ℕ) :
    IsZLattice ℝ (integerCoordinateLattice d) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))))

theorem integerCoordinateLattice_rank (d : ℕ) :
    Module.finrank ℤ (integerCoordinateLattice d) = d := by
  rw [ZLattice.rank ℝ]
  simp

theorem integerCellCoordinates_mem_lattice {d : ℕ} (z : IntegerCellIndex d) :
    integerCellCoordinates z ∈ integerCoordinateLattice d := by
  apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨z i, rfl⟩

def integerCellLatticePoint {d : ℕ} (z : IntegerCellIndex d) : integerCoordinateLattice d :=
  ⟨integerCellCoordinates z, integerCellCoordinates_mem_lattice z⟩

theorem integerCellLatticePoint_injective {d : ℕ} :
    Function.Injective (@integerCellLatticePoint d) := by
  intro z w h
  have hc := congrArg Subtype.val h
  funext i
  exact Int.cast_injective (congrFun hc i)

/-- Pad the origin by one before taking a negative power. -/
theorem summable_lattice_one_add_norm_rpow {d : ℕ}
    {p : ℝ} (hp : (d : ℝ) < p) :
    Summable (fun z : integerCoordinateLattice d => (1 + ‖z‖) ^ (-p)) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hsum := ZLattice.summable_norm_rpow (integerCoordinateLattice d) (-p)
    (by simpa only [integerCoordinateLattice_rank] using neg_lt_neg hp)
  have hsingle : Summable (fun z : integerCoordinateLattice d => if z = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : integerCoordinateLattice d) (1 : ℝ)).summable
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun z => ?_) (hsum.add hsingle)
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (neg_ne_zero.mpr hp0.ne')]
  · simpa only [hz, if_false, add_zero] using
      (Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz)
        (show ‖z‖ ≤ 1 + ‖z‖ by linarith) (neg_nonpos.mpr hp0.le))

theorem summable_integerCell_weight {d : ℕ} {p : ℝ} (hp : (d : ℝ) < p) :
    Summable (fun z : IntegerCellIndex d => (1 + ‖integerCellCoordinates z‖) ^ (-p)) := by
  have hnorm (z : IntegerCellIndex d) : ‖integerCellLatticePoint z‖ = ‖integerCellCoordinates z‖ := rfl
  simpa only [Function.comp_def, hnorm] using
    (summable_lattice_one_add_norm_rpow hp).comp_injective integerCellLatticePoint_injective

def integerCellCenter {d : ℕ} (z : IntegerCellIndex d) : Ambient d :=
  -integerCellShift z

@[simp] theorem integerCellCenter_apply {d : ℕ} (z : IntegerCellIndex d) (i : Fin d) :
    integerCellCenter z i = (z i : ℝ) := by
  simp [integerCellCenter, integerCellShift]

theorem sub_integerCellCenter_mem_unitWindow {d : ℕ} {z : IntegerCellIndex d}
    {y : Ambient d} (hy : y ∈ integerCell z) :
    y - integerCellCenter z ∈ unitWindow d := by
  simpa only [integerCell, mem_preimage, integerCellCenter, sub_neg_eq_add, add_comm] using hy

/-- A coarse bound is enough; no square root of the dimension is needed. -/
theorem integerCellCoordinates_norm_le {d : ℕ} (D : ℝ) (hD : 0 ≤ D)
    (hwindow : ∀ x ∈ unitWindow d, ‖x‖ ≤ D)
    (a : Ambient d) {z : IntegerCellIndex d} {x y : Ambient d}
    (hx : x ∈ (fun x => a + x) ⁻¹' unitWindow d) (hy : y ∈ integerCell z) :
    ‖integerCellCoordinates z‖ ≤ ‖x - y‖ + 2 * D + ‖a‖ := by
  have hax : ‖x‖ ≤ D + ‖a‖ := by
    calc
      ‖x‖ = ‖(a + x) - a‖ := by congr 1; abel
      _ ≤ ‖a + x‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ D + ‖a‖ := add_le_add (hwindow _ hx) le_rfl
  have hyz : ‖y - integerCellCenter z‖ ≤ D :=
    hwindow _ (sub_integerCellCenter_mem_unitWindow hy)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hid : (z i : ℝ) = x i - (x - y) i - (y - integerCellCenter z) i := by
    simp only [PiLp.sub_apply, integerCellCenter_apply]
    ring
  change ‖(z i : ℝ)‖ ≤ _
  rw [hid]
  calc
    _ ≤ (‖x i‖ + ‖(x - y) i‖) + ‖(y - integerCellCenter z) i‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (‖x‖ + ‖x - y‖) + ‖y - integerCellCenter z‖ :=
      add_le_add (add_le_add (PiLp.norm_apply_le x i) (PiLp.norm_apply_le (x - y) i))
        (PiLp.norm_apply_le (y - integerCellCenter z) i)
    _ ≤ ‖x - y‖ + 2 * D + ‖a‖ := by linarith

theorem polynomial_decay_rescale_le {p B t r : ℝ} (hp : 0 ≤ p)
    (hB : 0 < B) (ht : 0 < t) (hr : 0 < r) (htr : t ≤ B * r) :
    r ^ (-p) ≤ B ^ p * t ^ (-p) := by
  calc
    r ^ (-p) = B ^ p * (B * r) ^ (-p) := by
      rw [Real.mul_rpow hB.le hr.le, ← mul_assoc, ← Real.rpow_add hB]
      simp
    _ ≤ B ^ p * t ^ (-p) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht htr (neg_nonpos.mpr hp))
      (Real.rpow_nonneg hB.le _)

def polynomialCellEnvelope {d : ℕ} (C D p : ℝ) (a : Ambient d)
    (z : IntegerCellIndex d) : ℝ :=
  (C * (1 + 2 * D + ‖a‖) ^ p) * (1 + ‖integerCellCoordinates z‖) ^ (-p)

theorem summable_polynomialCellEnvelope {d : ℕ} (C D : ℝ) {p : ℝ}
    (hp : (d : ℝ) < p) (a : Ambient d) :
    Summable (polynomialCellEnvelope C D p a) :=
  (summable_integerCell_weight hp).mul_left _

theorem polynomialCellEnvelope_tsum_ofReal_ne_top {d : ℕ} (C D : ℝ) {p : ℝ}
    (hp : (d : ℝ) < p) (a : Ambient d) :
    (∑' z : IntegerCellIndex d, ENNReal.ofReal (polynomialCellEnvelope C D p a z)) ≠ ∞ :=
  (summable_polynomialCellEnvelope C D hp a).tsum_ofReal_ne_top

theorem difference_kernel_le_polynomialCellEnvelope {d : ℕ}
    (h : Ambient d → ℝ) (C D p : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hwindow : ∀ x ∈ unitWindow d, ‖x‖ ≤ D)
    (hdecay : ∀ v, |h v| ≤ C * (1 + ‖v‖) ^ (-p))
    (a : Ambient d) {z : IntegerCellIndex d} {x y : Ambient d}
    (hx : x ∈ (fun x => a + x) ⁻¹' unitWindow d) (hy : y ∈ integerCell z) :
    |h (x - y)| ≤ polynomialCellEnvelope C D p a z := by
  have hB : 0 < 1 + 2 * D + ‖a‖ := by positivity
  have hscale : 1 + ‖integerCellCoordinates z‖ ≤
      (1 + 2 * D + ‖a‖) * (1 + ‖x - y‖) := by
    have hgeom := integerCellCoordinates_norm_le D hD hwindow a hx hy
    have hnonneg : 0 ≤ (2 * D + ‖a‖) * ‖x - y‖ := by positivity
    nlinarith
  exact (hdecay (x - y)).trans (by
    simpa only [polynomialCellEnvelope, mul_assoc] using
      mul_le_mul_of_nonneg_left (polynomial_decay_rescale_le hp hB
        (by positivity) (by positivity) hscale) hC)

theorem exists_summable_difference_cell_envelope {d : ℕ}
    (h : Ambient d → ℝ) (C : ℝ) (hC : 0 ≤ C) {p : ℝ} (hp : (d : ℝ) < p)
    (hdecay : ∀ v, |h v| ≤ C * (1 + ‖v‖) ^ (-p)) (a : Ambient d) :
    ∃ M : IntegerCellIndex d → ℝ, (∑' z, ENNReal.ofReal (M z)) ≠ ∞ ∧
      ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
        ∀ y ∈ integerCell z, |h (x - y)| ≤ M z := by
  obtain ⟨D, hD, hwindow⟩ := (isBounded_unitWindow d).exists_pos_norm_le
  refine ⟨polynomialCellEnvelope C D p a,
    polynomialCellEnvelope_tsum_ofReal_ne_top C D hp a, ?_⟩
  intro z x hx y hy
  exact difference_kernel_le_polynomialCellEnvelope h C D p hC hD.le
    (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hp)) hwindow hdecay a hx hy

end E8Leech
