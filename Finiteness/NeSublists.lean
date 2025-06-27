import Mathlib.Data.List.Sublists

open List

/-!
# neSublists

This file contains the definition of `neSublists` and all of its related theorems.

-/

/-- Non-empty sublists. -/
@[simp]
def neSublists : List α → List (List α)
  | []    => []
  | x::xs => [[x]] ++ map (x :: ·) (neSublists xs)
                   ++ neSublists xs

theorem neSublists_completeness :
  xs <+ ys ∧ xs ≠ [] → xs ∈ neSublists ys := fun ⟨h,ne⟩ =>
  match h with
  | Sublist.slnil => False.elim (ne rfl)
  | Sublist.cons a h1 => by
    simp only [neSublists, singleton_append, cons_append, mem_cons, mem_append, mem_map]
    exact Or.inr $ Or.inr (neSublists_completeness ⟨h1, ne⟩)
  | @Sublist.cons₂ _ l1 l2 a h1 => by
    match l1 with
    | [] => exact mem_of_mem_head? rfl
    | l::ls =>
      simp only [neSublists, cons_append, nil_append, mem_cons, cons.injEq, reduceCtorEq, and_false,
        mem_append, cons_injective, mem_map_of_injective, false_or]
      exact Or.inl $ neSublists_completeness ⟨h1,cons_ne_nil l ls⟩

@[simp]
theorem neSublists_correctness :
  xs ∈ neSublists ys → xs <+ ys ∧ xs ≠ [] :=
  fun h => by
  match ys with
  | [] => simp only [neSublists, not_mem_nil] at h
  | y::ys =>
    simp only [neSublists, singleton_append] at h
    simp only [cons_append, mem_cons, mem_append, mem_map] at h
    match h with
    | Or.inl h1 =>
      subst h1
      simp only [cons_sublist_cons, nil_sublist, ne_eq, cons_ne_self, not_false_eq_true, and_self]
    | Or.inr h1 =>
      match h1 with
      | Or.inl ⟨g1,g2,g3⟩ =>
        subst g3
        simp only [cons_sublist_cons, ne_eq, not_false_eq_true, and_true]
        exact ⟨(neSublists_correctness g2).1, cons_ne_nil y g1⟩
      | Or.inr h2 =>
        exact ⟨Sublist.cons y (neSublists_correctness h2).1,(neSublists_correctness h2).2⟩

theorem neSublists_characterization {xs ys : List α} : xs ∈ neSublists ys ↔ xs <+ ys ∧ xs ≠ [] :=
  ⟨neSublists_correctness, neSublists_completeness⟩

theorem neSub_ne (h : xs ∈ neSublists ys) : xs ≠ [] := (neSublists_correctness h).2
theorem neSub_ne_perm (h : pxs ∈ neSublists ys) (hp : xs ~ pxs) : xs ≠ [] := fun h => by
  subst h
  exact (neSub_ne h) (nil_perm.mp hp)

theorem neSublists_append (h : x ∈ neSublists xs) (h1 : y ∈ neSublists ys) :
  (x++y) ∈ neSublists (xs++ys) :=
  have ⟨y_sub,y_ne⟩ := neSublists_characterization.mp h1
  have := Sublist.append (neSublists_characterization.mp h).1 y_sub
  neSublists_characterization.mpr ⟨this,append_ne_nil_of_right_ne_nil x y_ne⟩

@[simp]
theorem neSublists_unitality (ne : xs ≠ []) : xs ∈ neSublists xs :=
  neSublists_characterization.mpr ⟨Sublist.refl xs,ne⟩

@[simp]
theorem neSublists_singleton (h : x ∈ xs) : [x] ∈ neSublists xs :=
  match xs with
  | [] => False.elim ((mem_nil_iff x).mp h)
  | _::_ => neSublists_characterization.mpr ⟨singleton_sublist.mpr h,cons_ne_nil x []⟩

@[simp]
theorem neSublists_extend (h : xs ∈ neSublists ys) :
  xs ∈ neSublists (x::ys) :=
  have ⟨h1,h2⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨Sublist.cons x h1,h2⟩

theorem neSublists_appendL (h : x ∈ neSublists xs) :
  x ∈ neSublists (xs ++ ys) :=
  let ⟨x_sub,x_ne⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨sublist_append_of_sublist_left x_sub,x_ne⟩

theorem neSublists_appendR (h : x ∈ neSublists ys) :
  x ∈ neSublists (xs ++ ys) :=
  let ⟨x_sub,x_ne⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨sublist_append_of_sublist_right x_sub,x_ne⟩
