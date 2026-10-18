import Mathlib.Data.List.Basic

/-!
# Boolean checks of a list given in chunks

A long list of certificate rows is stored as a list of chunks, and each chunk is checked by the
kernel in its own declaration. These lemmas collect the chunk checks without any computation.

* `forall_mem_cons_of`, `forall_mem_nil'`: a statement about every chunk from the single ones.
* `forall_mem_flatten_of_all`: a Boolean check of every chunk holds on the concatenation.
* `all_map_flatten_of_all`: the same for a Boolean check of the images under a map.
-/

namespace E8Leech.Kron

theorem forall_mem_nil' {α : Type*} (p : α → Prop) : ∀ x ∈ ([] : List α), p x :=
  fun _ h => absurd h List.not_mem_nil

theorem forall_mem_cons_of {α : Type*} {p : α → Prop} {a : α} {l : List α} (ha : p a)
    (hl : ∀ x ∈ l, p x) : ∀ x ∈ a :: l, p x := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · rw [h]
    exact ha
  · exact hl x h

theorem forall_mem_flatten_of_all {α : Type*} {P : α → Bool} {cs : List (List α)}
    (h : ∀ c ∈ cs, c.all P = true) : ∀ g ∈ cs.flatten, P g = true := by
  intro g hg
  obtain ⟨c, hc, hgc⟩ := List.mem_flatten.mp hg
  exact List.all_eq_true.mp (h c hc) g hgc

theorem all_map_flatten_of_all {α β : Type*} {f : α → β} {Q : β → Bool} {cs : List (List α)}
    (h : ∀ c ∈ cs, (c.map f).all Q = true) : (cs.flatten.map f).all Q = true := by
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨g, hg, hgb⟩ := List.mem_map.mp hb
  obtain ⟨c, hc, hgc⟩ := List.mem_flatten.mp hg
  exact List.all_eq_true.mp (h c hc) b (List.mem_map.mpr ⟨g, hgc, hgb⟩)

end E8Leech.Kron
