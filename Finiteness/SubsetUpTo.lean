import Mathlib.Order.Defs.Unbundled

/-!
# Definitions of up-to relations

Includes the definitions of `mem_up_to`, `subset_up_to` and `equality_up_to`, as well as
their basic properties.

-/

/-- Defines membership of an element in a list, modulo a relation R. -/
@[simp]
def mem_up_to (R : α → α → Prop) : α → List α → Prop :=
  fun x ys => ∃ y, R x y ∧ y ∈ ys

notation x " ∈[ " R " ] " ys => mem_up_to R x ys

/-- Lifts the notion of set inclusion to lists, modulo a relation R. -/
@[simp]
def subset_up_to (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => ∀ x ∈ xs, x ∈[ R ] ys

notation xs " ⊆[ " R " ] " ys => subset_up_to R xs ys

/-- Two lists are equivalent up to R if both are subsets of each other under R. -/
@[simp]
def equality_up_to (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => (xs ⊆[ R ] ys) ∧ (ys ⊆[ R ] xs)

notation xs " =[ " R " ] " ys => equality_up_to R xs ys

theorem subset_up_to_refl {xs : List α} (hr : Reflexive R) :
  xs ⊆[ R ] xs := fun x h => ⟨x,hr x,h⟩

theorem subset_up_to_trans {xs ys zs : List α} (ht : Transitive R)
  (h1 : xs ⊆[ R ] ys) (h2 : ys ⊆[ R ] zs) :
  xs ⊆[ R ] zs :=
  fun r hr =>
  have ⟨g1,g2,g3⟩ := h1 r hr
  have ⟨i1,i2,i3⟩ := h2 g1 g3
  ⟨i1,ht g2 i2,i3⟩

theorem subset_to_subset_up_to {xs ys : List α} (hr : Reflexive R) (h : xs ⊆ ys) :
  xs ⊆[ R ] ys := fun g g1 => ⟨g,hr g,h g1⟩
