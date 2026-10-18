import E8Leech.Configuration
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# Deletion with neighbours outside the observation window

Every point having a close neighbour anywhere in the configuration is deleted. The cardinal
bound uses extended cardinalities, so it applies to infinite configurations as well.
-/

noncomputable section

namespace E8Leech

open Set

variable {X : Type*} [PseudoMetricSpace X]

def globalBadPoints (s : Set X) (r : ℝ) : Set X :=
  {x | x ∈ s ∧ ∃ y ∈ s, x ≠ y ∧ dist x y < r}

def globalKeptPoints (s : Set X) (r : ℝ) : Set X :=
  s \ globalBadPoints s r

/-- The first endpoint is in the window; the second is allowed to lie outside it. -/
def anchoredClosePairs (s W : Set X) (r : ℝ) : Set (X × X) :=
  {p | p.1 ∈ s ∩ W ∧ p.2 ∈ s ∧ p.1 ≠ p.2 ∧ dist p.1 p.2 < r}

theorem badPoints_inter_eq_image (s W : Set X) (r : ℝ) :
    globalBadPoints s r ∩ W = Prod.fst '' anchoredClosePairs s W r := by
  ext x
  constructor
  · rintro ⟨⟨hxs, y, hys, hxy, hd⟩, hxW⟩
    exact ⟨(x, y), ⟨⟨hxs, hxW⟩, hys, hxy, hd⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨⟨hxs, hxW⟩, hys, hxy, hd⟩, rfl⟩
    exact ⟨⟨hxs, y, hys, hxy, hd⟩, hxW⟩

theorem badPoints_encard_le_pairs (s W : Set X) (r : ℝ) :
    (globalBadPoints s r ∩ W).encard ≤ (anchoredClosePairs s W r).encard := by
  rw [badPoints_inter_eq_image]
  exact Set.encard_image_le _ _

theorem globalKeptPoints_separated {s : Set X} {r : ℝ} {x y : X}
    (hx : x ∈ globalKeptPoints s r) (hy : y ∈ globalKeptPoints s r)
    (hne : x ≠ y) : r ≤ dist x y := by
  by_contra h
  exact hx.2 ⟨hx.1, y, hy.1, hne, lt_of_not_ge h⟩

/-- If no deleted point lies in the window, the window is exactly unchanged. -/
theorem restore_window {s W : Set X} {r : ℝ}
    (h : globalBadPoints s r ∩ W = ∅) :
    globalKeptPoints s r ∩ W = s ∩ W := by
  ext x
  constructor
  · exact fun hx => ⟨hx.1.1, hx.2⟩
  · intro hx
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    intro hb
    have : x ∈ (∅ : Set X) := h ▸ ⟨hb, hx.2⟩
    exact this.elim

def Configuration.deleteClose (c : Configuration X) (r : ℝ) : Configuration X :=
  c.restrict (globalBadPoints c.support r)ᶜ

@[simp] theorem Configuration.deleteClose_support (c : Configuration X) (r : ℝ) :
    (c.deleteClose r).support = globalKeptPoints c.support r := rfl

theorem badPoints_image_isometry {Y : Type*} [PseudoMetricSpace Y]
    (e : X → Y) (he : Isometry e) (hinj : Function.Injective e) (s : Set X) (r : ℝ) :
    globalBadPoints (e '' s) r = e '' globalBadPoints s r := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, w, ⟨y, hy, rfl⟩, hne, hd⟩
    exact ⟨x, ⟨hx, y, hy, fun h => hne (congrArg e h), by simpa [he.dist_eq] using hd⟩, rfl⟩
  · rintro ⟨x, ⟨hx, y, hy, hne, hd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, fun h => hne (hinj h), by
      simpa [he.dist_eq] using hd⟩

end E8Leech
