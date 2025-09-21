import Finiteness.NeSublists
import Finiteness.Similarity
import Mathlib.Data.List.Permutation

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Permute

This file contains the definitions of `toSum`, `neSubsets`, and `toSumSubsets` functions.
These functions are needed in order to define the overapproximation for the set of
all derivatives.

-/

/-- Folds a given list of regexes into a sum. -/
def toSum : List (RE α) → RE α
  | []  => Pred ⊥
  | [a] => a
  | a::b::bs => a ⋓ toSum (b::bs)

@[simp]
def neSubsets (xs : List α) : List (List α) := neSublists xs |> map permutations' |> flatten

def toSumSubsets (xs : List (RE α)) : List (RE α) := xs |> neSubsets |> map toSum
prefix:max "⊕" => toSumSubsets

theorem neSubsets_ne (h : xs ∈ neSubsets ys) : xs ≠ [] := fun xs_empty => by
  subst xs_empty
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and] at h
  let ⟨xs,xs_sub,xs_perm⟩ := h
  exact (neSub_ne xs_sub) (nil_perm.mp $ mem_permutations'.mp xs_perm)

theorem neSubsets_refl (ne : xs ≠ []) :
  xs ∈ neSubsets xs := by
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and]
  exact ⟨xs,neSublists_characterization.mpr ⟨Sublist.refl xs,ne⟩,mem_permutations'.mpr (Perm.refl xs)⟩

@[simp]
theorem neSubsets_characterization :
  xs ∈ neSubsets ys ↔ ∃ zs, zs ∈ neSublists ys ∧ xs ~ zs := by
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and, mem_permutations']

theorem neSublist_neSubset (h : xs ∈ neSublists ys) : xs ∈ neSubsets ys :=
  neSubsets_characterization.mpr ⟨xs,h,Perm.refl _⟩

theorem neSubsets_map {ys : List (RE α)} (h : ys ∈ neSubsets xs) :
  toSum ys ∈ map toSum (neSubsets xs) := mem_map.mpr ⟨ys,h,rfl⟩

theorem neSubsets_appendL (h : x ∈ neSubsets xs) :
  x ∈ neSubsets (xs ++ ys) :=
  let ⟨as,as_sub,as_perm⟩ := neSubsets_characterization.mp h
  neSubsets_characterization.mpr ⟨as,neSublists_appendL as_sub,as_perm⟩

theorem neSubsets_appendR (h : x ∈ neSubsets ys) :
  x ∈ neSubsets (xs ++ ys) := by
  let ⟨as,as_sub,as_perm⟩ := neSubsets_characterization.mp h
  exact neSubsets_characterization.mpr ⟨as,neSublists_appendR as_sub,as_perm⟩

theorem neSubsets_append (hl : x ∈ neSubsets xs) (hr : y ∈ neSubsets ys) :
  x ++ y ∈ neSubsets (xs ++ ys) :=
  let ⟨as,as_sub,as_perm⟩ := neSubsets_characterization.mp hl
  let ⟨bs,bs_sub,bs_perm⟩ := neSubsets_characterization.mp hr
  neSubsets_characterization.mpr ⟨as ++ bs,neSublists_append as_sub bs_sub,Perm.append as_perm bs_perm⟩

theorem neSubsets_extend (h : xs ∈ neSubsets ys) :
  xs ∈ neSubsets (x::ys) :=
  let ⟨as,as_sub,as_perm⟩ := neSubsets_characterization.mp h
  neSubsets_characterization.mpr ⟨as,neSublists_extend as_sub,as_perm⟩

theorem neSubsets_singleton (h : x ∈ xs) : [x] ∈ neSubsets xs :=
  match xs with
  | [] => False.elim ((mem_nil_iff x).mp h)
  | _::_ =>
   match mem_cons.mp h with
   | Or.inl h1 => mem_of_mem_head? (by subst h1; rfl)
   | Or.inr h1 => neSubsets_extend (neSubsets_singleton h1)

theorem toSum_append {xs ys : List (RE α)} (_ : xs ≠ []) (h1 : ys ≠ []) :
  toSum (xs ++ ys) ≅ (toSum xs ⋓ toSum ys) :=
  match xs with
  | x::[]    => by
    cases ys; simp only [ne_eq, not_true_eq_false] at h1; exact Rfl
  | _::a::as => Trans (AltCong Rfl (toSum_append (cons_ne_nil a as) h1)) (Sym Assoc)

theorem toSum_alt_cong {xs : List (RE α)} (_ : xs ≠ []) (_ : ys ≠ []) (eqv : x ≅ y) (eqv_fs : toSum xs ≅ toSum ys) :
  toSum (x :: xs) ≅ toSum (y :: ys) :=
  match xs, ys with
  | _::_, _::_ => AltCong eqv eqv_fs

theorem toSum_appendL {xs : List (RE α)} (h : x ∈ ⊕xs) : x ∈ ⊕(xs ++ ys) := by
  unfold toSumSubsets neSubsets at h
  unfold toSumSubsets neSubsets
  simp_all only [map_flatten, map_map, mem_flatten, mem_map, Function.comp_apply, exists_exists_and_eq_and, mem_permutations']
  let ⟨a1,a2,a3,a4,a5⟩ := h
  subst a5
  exact ⟨a1,neSublists_appendL a2,⟨a3,a4,rfl⟩⟩

theorem toSum_appendR {xs : List (RE α)} (h : x ∈ ⊕ys) : x ∈ ⊕(xs ++ ys) := by
  unfold toSumSubsets neSubsets at h
  unfold toSumSubsets neSubsets
  simp_all only [map_flatten, map_map, mem_flatten, mem_map, Function.comp_apply, exists_exists_and_eq_and, mem_permutations']
  let ⟨a1,a2,a3,a4,a5⟩ := h
  subst a5
  exact ⟨a1,neSublists_appendR a2,⟨a3,a4,rfl⟩⟩

theorem deconstruct (h1 : x ∈ ys) :
  ∃ ys1 ys2, ys = ys1 ++ x::ys2 :=
  match ys with
  | [] => mem_iff_append.mp h1
  | y::ys =>
    match mem_cons.mp h1 with
    | Or.inl g1 => ⟨[],ys,congrFun (congrArg cons (id (Eq.symm g1))) ys⟩
    | Or.inr g1 =>
      have ⟨i1,i2,i3⟩ := deconstruct g1
      ⟨y::i1,i2,congrArg (cons y) i3⟩

theorem perms_erase_helper [DecidableEq α] {y : α}
  (h1 : y ∈ xs) : xs ∈ permutations'Aux y ((xs).erase y) :=
  match xs with
  | [] => False.elim (not_mem_nil h1)
  | x::[] => by
    simp only [mem_singleton] at h1
    subst h1
    simp only [erase_cons_head, permutations'Aux, mem_singleton]
  | x1::x2::xs => by
    match mem_cons.mp h1 with
    | Or.inl h2 =>
      subst h2
      simp only [erase_cons_head, permutations'Aux, mem_cons, mem_map, true_or]
    | Or.inr h2 =>
      unfold List.erase
      by_cases g : x1 == y
      . simp only [g, permutations'Aux, mem_cons, cons.injEq, and_true, mem_map, exists_eq_right_right]
        simp only [beq_iff_eq.mp g,true_or]
      . simp only [g, permutations'Aux, mem_cons, cons.injEq, cons_injective, mem_map_of_injective]
        simp only [beq_iff_eq] at g
        simp only [g, false_and, false_or]
        exact perms_erase_helper (xs:=(x2::xs)) h2

theorem erase_nodup [DecidableEq α] {xs : List α} (h : Nodup xs) : Nodup (xs.erase y) :=
  match xs with
  | [] => h
  | x::xs => by
    by_cases g : x == y
    . simp only [beq_iff_eq] at g; subst g; exact Nodup.erase x h
    . simp only [g, Bool.false_eq_true, not_false_eq_true, erase_cons_tail, nodup_cons]
      simp only [beq_iff_eq] at g
      rw[nodup_cons] at h
      exact ⟨(iff_false_right h.left).mp (mem_erase_of_ne g),erase_nodup (y:=y) h.2⟩

theorem subset_cons (h : xs ⊆ x1 :: ys) (not_in : x1 ∉ xs) : xs ⊆ ys := fun e he =>
  match mem_cons.mp (h he) with
  | Or.inl h1 => by subst h1; contradiction
  | Or.inr h1 => h1

theorem erase_cons1 [DecidableEq α] {xs : List α}
  (hh1 : y ∈ (x1::xs))
  (hh : (x1 :: xs).Nodup)
  (h : (x1 :: xs).erase y ⊆ y :: ys)
  : (x1 :: xs).erase y ⊆ ys := by
  match xs with
  | [] =>
    simp only [mem_singleton] at hh1
    subst hh1
    rw[erase_cons_head y []]
    exact nil_subset ys
  | x2::xs =>
    unfold List.erase at h
    by_cases g : x1 == y
    . simp only [g, cons_subset, mem_cons] at h
      unfold List.erase; simp only [g, cons_subset]
      let ⟨k1,k2⟩ := h
      match k1 with
      | Or.inl k =>
        subst k; simp only [beq_iff_eq] at g; subst g
        simp_all only [nodup_cons, mem_cons, true_or, not_true_eq_false, false_and]
      | Or.inr k =>
        simp only [k, true_and]
        simp only [beq_iff_eq] at g
        subst g
        simp only [nodup_cons, mem_cons, not_or] at hh
        apply subset_cons k2 hh.1.2
    . simp only [g, cons_subset, mem_cons] at h
      unfold List.erase
      simp only [g, cons_subset]
      simp only [beq_iff_eq] at g
      simp only [mem_cons] at hh1
      let ⟨k1,k2⟩ := h
      match hh1 with
      | Or.inl j => subst j; simp only [not_true_eq_false] at g
      | Or.inr j =>
        match k1 with
        | Or.inl k => subst k; exact False.elim (g rfl)
        | Or.inr k => exact ⟨k,erase_cons1 (ys:=ys) (mem_cons.mpr j) (Nodup.of_cons hh) k2⟩

theorem nodup_subset_to_neSubsets [DecidableEq α] {xs ys : List α}
  (h : xs ≠ [])
  (sb : xs ⊆ ys)
  (nd : Nodup xs)
  : xs ∈ neSubsets ys := by
  match ys with
  | [] => simp only [subset_nil] at sb; contradiction
  | y::ys =>
    by_cases g : y ∈ xs
    . match xs with
      | [] => simp only [not_mem_nil] at g
      | x::[] =>
        simp only [mem_cons, not_mem_nil, or_false] at g
        subst g
        exact mem_of_mem_head? rfl
      | x1::x2::xs =>
        have f := Subset.trans (diff_subset (x1::x2::xs) [y]) sb
        have f' : (x1::x2::xs).diff [y] ⊆ ys := by
          simp only [diff_cons, diff_nil]
          simp only [diff_cons, diff_nil] at f
          exact erase_cons1 g nd f
        have f₁ : Nodup ((x1::x2::xs).diff [y]) := Nodup.diff nd
        have f₂ : (x1::x2::xs).diff [y] ≠ [] := by
          by_cases g1 : x1 = y
          . subst g1
            simp only [diff_cons, erase_cons_head, diff_nil, ne_eq, reduceCtorEq,
            not_false_eq_true]
          . simp only [diff_cons, diff_nil, ne_eq, erase_eq_nil_iff, reduceCtorEq, cons.injEq,
            and_false, or_self, not_false_eq_true]
        have ih := nodup_subset_to_neSubsets f₂ f' f₁
        simp only [neSubsets, diff_cons, diff_nil, mem_flatten, mem_map,
          exists_exists_and_eq_and] at ih
        let ⟨i1,i2,i3⟩ := ih
        simp only [neSubsets, neSublists, cons_append, nil_append, map_cons, permutations',
          flatMap_cons, permutations'Aux, flatMap_nil, append_nil, map_append, map_map,
          flatten_cons, flatten_append, mem_cons, cons.injEq, reduceCtorEq, and_false, mem_append,
          mem_flatten, mem_map, Function.comp_apply, exists_exists_and_eq_and, mem_flatMap,
          false_or]
        exact Or.inl ⟨i1,i2,(x1::x2::xs).erase y,i3,perms_erase_helper g⟩
    . exact neSubsets_extend (nodup_subset_to_neSubsets h (subset_cons sb g) nd)

theorem nodup_subset_to_neSubset [DecidableEq α] {xs : List (RE α)}
  (h : xs ≠ []) (sb : xs ⊆ ys) (nd : Nodup xs) : toSum xs ∈ ⊕ ys :=
  mem_map_of_mem (nodup_subset_to_neSubsets h sb nd)

theorem subset_sim_toSum {xs ys : List (RE α)}
  (ne : xs ≠ [])
  (h : xs ⊆[ (· ≅ ·) ] ys)
  : ∃ (us : List (RE α)),
        us ⊆ ys
      ∧ us ≠ []
      ∧ toSum xs ≅ toSum us := by
  match xs with
  | [] => contradiction
  | [x] =>
    simp only [subset_up_to, mem_singleton, mem_up_to, forall_eq] at h
    have ⟨y,eq,mem⟩ := h
    exact ⟨[y],by simp only [subset_def, mem_singleton, forall_eq]; exact mem,cons_ne_nil y [],eq⟩
  | x :: x' :: xs =>
    have ⟨hx, h'⟩ := forall_mem_cons.mp h
    have ⟨us, sb, eq1,eq2⟩ := subset_sim_toSum (cons_ne_nil x' xs) h'
    have ⟨y, p1, p2⟩ := hx
    exact ⟨y::us,by simp only [subset_def, mem_cons, forall_eq_or_imp]
                    exact ⟨p2,sb⟩,cons_ne_nil y us,toSum_alt_cong (cons_ne_nil x' xs) eq1 p1 eq2⟩

theorem nodup_swap (h : (z1 ++ x :: z2).Nodup) : (x :: z1 ++ z2).Nodup := by
  have ⟨h1,h2,h3⟩ := List.nodup_append.mp h
  apply List.nodup_append.mpr
  simp_all
  let ⟨h2a,h2b⟩ := h2
  exact ⟨fun eq => by have ⟨a1,a2⟩ := h3 _ eq; contradiction,
         fun b hb eq => by subst eq; contradiction⟩

theorem nodup_equiv (xs : List (RE α)) (ne : xs ≠ [])
  : ∃ (zs : List (RE α)),
        Nodup zs
      ∧ zs ≠ []
      ∧ zs ⊆ xs
      ∧ toSum xs ≅ toSum zs := by
  match xs with
  | []      => simp only [ne_eq, not_true_eq_false] at ne
  | x :: [] =>
    simp only [ne_eq]
    exact ⟨[x],nodup_singleton x,ne,fun _ ha => ha,Rfl⟩
  | x :: x1 :: xs =>
    have ⟨zs,nd,sb,fs1,fs2⟩ := nodup_equiv (x1::xs) (cons_ne_nil x1 xs)
    by_cases h : x ∈ zs
    . have ⟨z1,z2,z3⟩ := deconstruct h
      subst z3
      exists (x::z1++z2)
      have t1 : z1 ⊆ x :: x1 :: xs := by
        simp only [subset_def, mem_cons]
        intro a ha; simp only [subset_def, mem_append, mem_cons] at fs1
        have t := fs1 (Or.inl ha); exact Or.inr t
      have t2 : z2 ⊆ x :: x1 :: xs := by
        simp only [subset_def, mem_cons]; intro a ha
        simp only [subset_def, mem_append, mem_cons] at fs1
        have t := fs1 (Or.inr $ Or.inr ha); exact Or.inr t
      exists nodup_swap nd; exists (ne_nil_of_length_eq_add_one rfl)
      exists (by simp only [cons_append, cons_subset, mem_cons, true_or, append_subset, true_and]
                 exact ⟨t1, t2⟩)
      simp only [toSum, cons_append]
      apply Trans (AltCong Rfl fs2)
      match z2 with
      | [] =>
        match z1 with
        | [] => exact Idem
        | z1a::z1b =>
          apply Trans (AltCong Rfl (toSum_append (cons_ne_nil z1a z1b) (cons_ne_nil x [])))
          simp only [append_nil]
          exact DeDup
      | _::_ =>
        match z1 with
        | [] => exact Trans (Sym Assoc) $ Trans (AltCong Idem Rfl) Rfl
        | z1a::z1b =>
          apply Trans (AltCong Rfl (toSum_append (cons_ne_nil z1a z1b)
                      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])))
          apply Trans (Sym Assoc)
          apply Trans (Sym Assoc)
          apply Trans (AltCong Assoc Rfl)
          apply Trans (AltCong DeDup Rfl)
          exact Trans Assoc $ Trans (AltCong Rfl (Sym (toSum_append (cons_ne_nil z1a z1b) (by simp only [ne_eq,
            reduceCtorEq, not_false_eq_true])))) Rfl
    . exact ⟨x :: zs,by simp only [nodup_cons]; exact ⟨h,nd⟩,by simp only [ne_eq, reduceCtorEq, not_false_eq_true],
             by simp only [cons_subset, mem_cons, true_or, true_and]; apply subset_cons_of_subset x fs1,
             toSum_alt_cong (cons_ne_nil x1 xs) sb Rfl fs2⟩

theorem toSumnodup_equiv {xs ys : List (RE α)}
  (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys)
  : ∃ (us : List (RE α)),
        Nodup us
      ∧ us ≠ []
      ∧ us ⊆ ys
      ∧ toSum xs ≅ toSum us :=
  have ⟨xs', xs'_ys, xs'_ne ,xs_xs'⟩ := subset_sim_toSum ne h
  have ⟨us, nd, us_xs', p, xs'_us⟩ := nodup_equiv xs' xs'_ne
  ⟨us, nd, us_xs', subset_trans p xs'_ys, Trans xs_xs' xs'_us⟩

@[simp]
theorem subset_sim_perm [DecidableEq α] {xs ys : List (RE α)}
  (ne : xs ≠ [])
  (h : xs ⊆[ (· ≅ ·) ] ys)
  : toSum xs ∈[ (· ≅ ·) ] ⊕ ys :=
  have ⟨us, ndup, ne, us_ys, ftoSum⟩ := toSumnodup_equiv ne h
  ⟨toSum us,ftoSum,nodup_subset_to_neSubset ne us_ys ndup⟩

theorem neSublist_to_subset {xs ys : List (RE α)}
  (h : xs ∈ neSublists ys) : xs ⊆ ys :=
  Sublist.subset (neSublists_characterization.mp h).1

@[simp]
theorem neSubset_to_sublist {xs ys : List (RE α)}
  (h : xs ∈ neSubsets ys)
  : xs ⊆ ys := by
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and] at h
  let ⟨a,ha,pa⟩ := h
  simp only [subset_def]; intro x hx
  exact neSublist_to_subset ha ((Perm.mem_iff (mem_permutations'.mp pa)).mp hx)

@[simp]
theorem toSumSubsets_to_neSubset {x : RE α} {xs : List (RE α)}
  (h : x ∈ ⊕xs)
  : ∃ zs, zs ≠ [] ∧ x = toSum zs ∧ zs ⊆ xs := by
  have ⟨zs, zs_mem, zs_eq⟩ := mem_map.mp h
  match zs with
  | [] => have := neSubsets_ne zs_mem; simp only [ne_eq, not_true_eq_false] at this
  | z::zs => exact ⟨z::zs,cons_ne_nil z zs,symm zs_eq,neSubset_to_sublist zs_mem⟩

@[simp]
theorem toSumSubsets_monotone [DecidableEq α] {xs : List (RE α)}
  (h : xs ⊆[ (· ≅ ·) ] ys)
  : ⊕xs ⊆[ (· ≅ ·) ] ⊕ys := fun x x_mem => by
  have ⟨zs, p1, p2, p3⟩ := toSumSubsets_to_neSubset x_mem; subst p2
  have zsxs := subset_to_subset_up_to_sim p3
  exact subset_sim_perm p1 (subset_up_to_trans_sim zsxs h)

@[simp]
theorem subset_to_neSubset [DecidableEq α] {xs ys : List (RE α)}
  (h : xs ⊆ ys) (ne : xs ≠ []) (nodup : xs.Nodup)
  : ∃ ys', ys' ∈ neSubsets ys
          ∧ toSum xs ≅ toSum ys' := by
  match xs with
  | x::[] =>
    simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and]
    simp only [cons_subset, nil_subset, and_true] at h
    exact ⟨[x],⟨[x],neSublists_singleton h,mem_of_mem_head? rfl⟩,Rfl⟩
  | x1::x2::xs =>
    have ⟨i1,i2,i3⟩ := mem_map.mp $ nodup_subset_to_neSubset (xs:=x1::x2::xs) (ys:=ys) ne h nodup
    exact ⟨i1,i2,by rw[i3]; exact Rfl⟩
