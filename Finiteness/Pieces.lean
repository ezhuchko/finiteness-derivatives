import Finiteness.Permute
import Finiteness.Similarity

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Pieces

This file contains the definitions of `pieces` which is the key component of the overapproximation for the set of
all derivatives.

-/

/-- This is an overapproximation of the set of pieces of all possible derivatives. -/
def pieces : RE α → List (RE α)
  | ε         => [ε, Pred ⊥]
  | ?= r      => [?= r, ε, Pred ⊥]
  | ?! r      => [?! r, ε, Pred ⊥]
  | ?<= r     => [?<= r, ε, Pred ⊥]
  | ?<! r     => [?<! r, ε, Pred ⊥]
  | Pred φ    => [Pred φ, ε, Pred ⊥]
  | l ⋓ r     => pieces l ++ pieces r
  | l ⋒ r     => productWith (· ⋒ ·) ⊕(pieces l) ⊕(pieces r)
  | l ⬝ r     => map (· ⬝ r) ⊕(pieces l) ++ pieces r
  | .Star r   => r* :: map (· ⬝ r*) ⊕(pieces r)
  | ~ r       => map (~ ·) ⊕(pieces r)

theorem topmost_not_union {r x y : RE α} : ¬ ((x ⋓ y) ∈ pieces r) := fun h =>
  match r with
  | ε | ?=_ | ?!_ | ?<=_ | ?<!_ => by
    simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | Pred φ    => by simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | l ⋓ r     =>
    match mem_append.mp h with
    | Or.inl h1 => topmost_not_union h1
    | Or.inr h1 => topmost_not_union h1
  | l ⋒ r     => by
    simp only [pieces, productWith, product] at h
    simp only [mem_map, mem_flatMap, exists_exists_and_exists_and_eq_and] at h
    let ⟨a,b,c,d,e⟩ := h
    simp only [Function.uncurry_apply_pair, reduceCtorEq] at e
  | l ⬝ r     => by
    simp only [pieces, mem_append, mem_map, reduceCtorEq, and_false, exists_false, false_or] at h
    exact topmost_not_union h
  | .Star r   => by simp only [pieces, mem_cons, reduceCtorEq, mem_map, and_false, exists_false, or_self] at h
  | ~ r       => by simp only [pieces, mem_map, reduceCtorEq, and_false, exists_false] at h

theorem pieces_refl {r : RE α} :
  ∃ xs, xs ∈ neSublists (pieces r) ∧ toSum xs ≅ r :=
  match r with
  | ε         => ⟨[ε],mem_of_mem_head? rfl,Rfl⟩
  | ?= r      => ⟨[?= r],mem_of_mem_head? rfl,Rfl⟩
  | ?! r      => ⟨[?! r],mem_of_mem_head? rfl,Rfl⟩
  | ?<= r     => ⟨[?<= r],mem_of_mem_head? rfl,Rfl⟩
  | ?<! r     => ⟨[?<! r],mem_of_mem_head? rfl,Rfl⟩
  | Pred φ    => ⟨[Pred φ],mem_of_mem_head? rfl,Rfl⟩
  | l ⋓ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    have ⟨j1,j2,j3⟩ := pieces_refl (r:=r)
    ⟨i1 ++ j1,neSublists_append i2 j2,Trans (toSum_append (neSub_ne i2) (neSub_ne j2)) (AltCong i3 j3)⟩
  | l ⋒ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    have ⟨j1,j2,j3⟩ := pieces_refl (r:=r)
    ⟨[toSum i1 ⋒ toSum j1], neSublists_singleton
                            (by unfold pieces productWith product
                                simp only [mem_map, mem_flatMap, exists_exists_and_exists_and_eq_and,
                                  Function.uncurry_apply_pair, Intersection.injEq, exists_eq_right_right]
                                unfold toSumSubsets
                                exact ⟨mem_map.mpr ⟨i1,neSubsets_characterization.mpr ⟨i1,i2,Perm.refl _⟩,rfl⟩,
                                       mem_map.mpr ⟨j1,neSubsets_characterization.mpr ⟨j1,j2,Perm.refl _⟩,rfl⟩⟩),
                            InterCong i3 j3⟩
  | .Star r   => ⟨[r*],mem_of_mem_head? rfl,Rfl⟩
  | ~ r       => by
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=r)
    simp only [pieces, toSumSubsets, neSubsets, map_flatten, map_map]
    exact ⟨[~(toSum i1)],
           neSublists_singleton (mem_flatten.mpr $ ⟨(map (~·) ∘ map toSum ∘ permutations') i1,
           mem_map.mpr ⟨i1,i2,rfl⟩,
           by simp only [Function.comp_apply, map_map, mem_map, mem_permutations']; exact ⟨i1,Perm.refl _,rfl⟩⟩),
           NegCong i3⟩
  | l ⬝ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    ⟨[toSum i1 ⬝ r],
     neSublists_singleton (mem_append_left _ $ mem_map.mpr ⟨toSum i1,mem_map.mpr ⟨i1,neSublist_neSubset i2,rfl⟩,rfl⟩),
     CatCong i3⟩

theorem pieces_equiv' [DecidableEq α] {f f' : RE α} (eqv : f ≅ f') :
  pieces f =[(· ≅ ·)] pieces f' := by
  simp only [equality_up_to, subset_up_to, mem_up_to]
  induction eqv with
  | Rfl => simp only [and_self]; intro r hr; exact ⟨r,Rfl,hr⟩
  | Sym _ ph => exact ⟨fun r hr => ph.2 r hr, fun r hr => ph.1 r hr⟩
  | Trans _ _ ph qh =>
    exact ⟨fun e h1 =>
           have ⟨e1,e1_eq,e1_in⟩ := ph.1 e h1
           have ⟨e2,e2_eq,e2_in⟩ := qh.1 e1 e1_in
           ⟨e2, Trans e1_eq e2_eq, e2_in⟩,
           fun e h1 =>
           have ⟨e1,e1_eq,e1_in⟩ := qh.2 e h1
           have ⟨e2,e2_eq,e2_in⟩ := ph.2 e1 e1_in
           ⟨e2, Trans e1_eq e2_eq, e2_in⟩⟩
  | Assoc =>
    exact ⟨fun e h1 => by
           simp_all only [pieces, append_assoc, mem_append]
           match h1 with
           | Or.inl h2 => exact ⟨e,Rfl,Or.inl h2⟩
           | Or.inr h2 => exact ⟨e,Rfl,Or.inr h2⟩,
           fun e h1 => by
           simp_all only [pieces, append_assoc, mem_append]
           match h1 with
           | Or.inl h2 => exact ⟨e,Rfl,Or.inl h2⟩
           | Or.inr h2 => exact ⟨e,Rfl,Or.inr h2⟩⟩
  | Idem =>
    exact ⟨fun e h1 => by simp only [pieces, mem_append, or_self] at h1; exact ⟨e,Rfl,h1⟩,
           fun e h1 => ⟨e,Rfl,mem_append.mpr $ Or.inl h1⟩⟩
  | DeDup =>
    exact ⟨fun e h1 => ⟨e,Rfl,by simp only [pieces, mem_append] at h1; rw[or_comm,or_assoc,or_self] at h1; exact mem_append.mpr $ Or.symm h1⟩,
           fun e h1 => by simp only [pieces, mem_append] at h1; simp only [pieces, mem_append]; exact ⟨e,Rfl,Or.inr $ Or.symm h1⟩⟩
  | NegCong _ ih =>
    exact ⟨fun x hx => by
      simp_all only [pieces, mem_map]
      let ⟨zs,hz1,hz2⟩ := hx
      subst hz2
      have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih.1 zs hz1
      exact ⟨~i1,NegCong i2,i1,i3,rfl⟩,
     fun x hx => by
      simp_all only [pieces, mem_map]
      let ⟨zs,hz1,hz2⟩ := hx
      subst hz2
      have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih.2 _ hz1
      exact ⟨~i1,NegCong i2,i1,i3,rfl⟩⟩
   | AltCong _ _ ph qh =>
     exact ⟨fun e h1 => by
            simp_all only [pieces, mem_append]
            match h1 with
            | Or.inl h2 =>
              have ⟨i1,i2,i3⟩ := ph.1 _ h2
              exact ⟨i1,i2,Or.inl i3⟩
            | Or.inr h2 =>
              have ⟨i1,i2,i3⟩ := qh.1 _ h2
              exact ⟨i1,i2,Or.inr i3⟩,
            fun e h1 => by
            simp_all only [pieces, mem_append]
            match h1 with
            | Or.inl h2 =>
              have ⟨i1,i2,i3⟩ := ph.2 _ h2
              exact ⟨i1,i2,Or.inl i3⟩
            | Or.inr h2 =>
              have ⟨i1,i2,i3⟩ := qh.2 _ h2
              exact ⟨i1,i2,Or.inr i3⟩⟩
   | CatCong h ih =>
     exact ⟨fun e h1 => by
            simp only [pieces, mem_append, mem_map] at h1
            match h1 with
            | Or.inl ⟨xs,g1,g2⟩ =>
              subst g2; rename_i r1 r2
              have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih.1 _ g1
              exact ⟨i1 ⬝ r2,CatCong i2,by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨i1,i3,rfl⟩⟩
            | Or.inr g =>  exact ⟨e,Rfl,mem_append.mpr $ Or.inr g⟩,
            fun e h1 => by
            simp only [pieces, mem_append, mem_map] at h1
            match h1 with
            | Or.inl ⟨xs,g1,g2⟩ =>
              subst g2; rename_i r1 g _ r2
              have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih.2 _ g1
              exact ⟨i1 ⬝ r2,CatCong i2,by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨i1,i3,rfl⟩⟩
            | Or.inr g => exact ⟨e,Rfl,mem_append.mpr $ Or.inr g⟩⟩
  | InterCong _ _ ih1 ih2 =>
     exact ⟨fun e h1 => by
            simp only [pieces, productWith, mem_map, Prod.exists, pair_mem_product,
              Function.uncurry_apply_pair] at h1
            have ⟨a,b,⟨c,d⟩,e⟩ := h1; subst e
            have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih1.1 _ c
            have ⟨j1,j2,j3⟩ := toSumSubsets_monotone ih2.1 _ d
            exact ⟨i1 ⋒ j1,InterCong i2 j2,by simp only [pieces, productWith, mem_map,
              Prod.exists, pair_mem_product]; exact ⟨i1,j1,⟨i3,j3⟩,rfl⟩⟩,
            fun e h1 => by
            simp only [pieces, productWith, mem_map, Prod.exists, pair_mem_product] at h1
            have ⟨a,b,⟨c,d⟩,e⟩ := h1; subst e
            have ⟨i1,i2,i3⟩ := toSumSubsets_monotone ih1.2 _ c
            have ⟨j1,j2,j3⟩ := toSumSubsets_monotone ih2.2 _ d
            exact ⟨i1 ⋒ j1,InterCong i2 j2,by simp only [pieces, productWith, mem_map,
              Prod.exists, pair_mem_product]; exact ⟨i1,j1,⟨i3,j3⟩,rfl⟩⟩⟩

/- The set of pieces respects equivalence (up to). -/
theorem pieces_sim [DecidableEq α] {f : RE α}
  (sim : f ≅ f') : pieces f ⊆[ (· ≅ ·) ] pieces f' := fun _ h => (pieces_equiv' sim).1 _ h

theorem pieces_toSum {e : RE α} (ne : xs ≠ []) (h : e ∈ pieces (toSum xs)) :
  ∃ g ∈ xs, e ∈ pieces g :=
  match xs with
  | e::[] => exists_mem_cons_of [] h
  | e1::e2::es =>
    match mem_append.mp h with
    | Or.inl h1 => ⟨e1,mem_cons_self,h1⟩
    | Or.inr h1 =>
      have ⟨i1,i2,ih⟩ := pieces_toSum (cons_ne_nil e2 es) h1
      match mem_cons.mp i2 with
      | Or.inl g => by subst g; exact ⟨i1,mem_cons_of_mem e1 i2,ih⟩
      | Or.inr g => by exact ⟨i1,mem_cons_of_mem e1 i2,ih⟩

theorem pieces_bot_eps [DecidableEq α] {e : RE α}
  (h1 : e ∈ pieces f)
  (h2 : f = ε ∨ f = Pred ⊥) :
  e = ε ∨ e = Pred ⊥ := by
  match h2 with
  | Or.inl g =>
    subst g
    simp only [pieces, mem_cons, not_mem_nil, or_false] at h1
    exact h1
  | Or.inr g =>
    subst g
    simp only [pieces, mem_cons, not_mem_nil, or_false] at h1
    exact or_self_right.mp (Or.symm h1)

theorem pieces_trans' [DecidableEq α] {e : RE α}
  (h1 : e ∈ pieces f)
  (h2 : f ∈ pieces g) :
  e ∈[ (· ≅ ·) ] pieces g := by
  match g with
  | ?<=_ | ?<!_ | ?!_ | ?=_  =>
    simp_all only [pieces, mem_cons, not_mem_nil, or_false, mem_up_to]
    match h2 with
    | Or.inl g => subst g; simp only [pieces, mem_cons, not_mem_nil, or_false] at h1; exact ⟨e,Rfl,h1⟩
    | Or.inr g =>
      match pieces_bot_eps h1 g with
      | Or.inl g1 => subst g1; exact ⟨ε,Rfl,Or.inr $ Or.inl rfl⟩
      | Or.inr g1 => subst g1; exact ⟨Pred ⊥,Rfl,Or.inr $ Or.inr rfl⟩
  | ε =>
    simp_all only [pieces, mem_cons, not_mem_nil, or_false, mem_up_to]
    match pieces_bot_eps h1 h2 with
    | Or.inl g1 => subst g1; exact ⟨ε,Rfl,Or.inl rfl⟩
    | Or.inr g1 => subst g1; exact ⟨Pred ⊥,Rfl,Or.inr rfl⟩
  | Pred φ =>
    simp_all only [pieces, mem_cons, not_mem_nil, or_false, mem_up_to]
    match h2 with
    | Or.inl g => subst g; exact ⟨e,Rfl,by simp only [pieces, mem_cons, not_mem_nil, or_false] at h1; exact h1⟩
    | Or.inr g =>
      match pieces_bot_eps h1 g with
      | Or.inl g1 => subst g1; exact ⟨ε,Rfl,Or.inr $ Or.inl rfl⟩
      | Or.inr g1 => subst g1; exact ⟨Pred ⊥,Rfl,Or.inr $ Or.inr rfl⟩
  | g1 ⋓ g2 =>
    simp_all only [pieces, mem_append, mem_up_to]
    match h2 with
    | Or.inl g => have ⟨i1,i2,i3⟩ := pieces_trans' h1 g; exact ⟨i1,i2,Or.inl i3⟩
    | Or.inr g => have ⟨i1,i2,i3⟩ := pieces_trans' h1 g; exact ⟨i1,i2,Or.inr i3⟩
  | l ⋒ r =>
    simp_all only [pieces, productWith, mem_map, Prod.exists, pair_mem_product, Function.uncurry_apply_pair, mem_up_to]
    let ⟨a,b,⟨ha,hb⟩,eq⟩ := h2; subst eq
    simp only [pieces, productWith, mem_map, Prod.exists, pair_mem_product, Function.uncurry_apply_pair] at h1
    let ⟨c,d,⟨hc,hd⟩,eq⟩ := h1; subst eq
    have ⟨zs,ne_zs,m1,m2⟩ := toSumSubsets_to_neSubset ha
    have ⟨as,ne_as,k1,k2⟩ := toSumSubsets_to_neSubset hc
    subst m1 k1
    have : as ⊆[ (· ≅ ·) ] pieces l := fun x hx =>
      have ⟨pi,pi_in,pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
      pieces_trans' pi_piece (m2 pi_in)
    have mon := toSumSubsets_monotone this
    have ⟨m1,m2,m3⟩ := mon (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as,rfl⟩)
    have ⟨zs',ne_zs',m1',m2'⟩ := toSumSubsets_to_neSubset hb
    have ⟨as',ne_as',k1',k2'⟩ := toSumSubsets_to_neSubset hd
    subst m1' k1'
    have t : as' ⊆[ (· ≅ ·) ] pieces r := fun x hx =>
      have ⟨pi,pi_in,pi_piece⟩ := pieces_toSum ne_zs' (k2' hx)
      pieces_trans' pi_piece (m2' pi_in)
    have mon' := toSumSubsets_monotone t
    have ⟨m1',m2',m3'⟩ := mon' (toSum as') (mem_map.mpr ⟨as', neSubsets_refl ne_as',rfl⟩)
    exact ⟨m1 ⋒ m1',InterCong m2 m2',m1,⟨m1',⟨m3,m3'⟩,rfl⟩⟩
  | l ⬝ r =>
    simp_all only [mem_up_to, pieces, mem_append, mem_map]
    match h2 with
    | Or.inl ⟨a,ha,ha1⟩ =>
      subst ha1
      simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨b,hb,hb1⟩ =>
        subst hb1
        have ⟨zs,ne_zs,m1,m2⟩ := toSumSubsets_to_neSubset ha
        have ⟨as,ne_as,k1,k2⟩ := toSumSubsets_to_neSubset hb
        subst m1 k1
        have : as ⊆[ (· ≅ ·) ] pieces l := fun x hx =>
          have ⟨pi,pi_in,pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
          pieces_trans' pi_piece (m2 pi_in)
        have mon := toSumSubsets_monotone this
        have ⟨m1,m2,m3⟩ := mon (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as,rfl⟩)
        exact ⟨m1 ⬝ r,CatCong m2,Or.inl ⟨m1,m3,rfl⟩⟩
      | Or.inr g => exact ⟨e,Rfl,Or.inr g⟩
    | Or.inr g =>
      have ⟨i1,i2,ih⟩ := pieces_trans' h1 g
      exact ⟨i1,i2,Or.inr ih⟩
  | ~ g =>
    simp only [pieces, mem_map] at h2
    let ⟨a,ha,ha1⟩ := h2; subst ha1
    simp only [pieces, mem_map] at h1
    let ⟨b,bh,bh1⟩ := h1; subst bh1
    simp only [mem_up_to, pieces, mem_map]
    have ⟨zs,ne_zs,m1,m2⟩ := toSumSubsets_to_neSubset ha
    have ⟨as,ne_as,k1,k2⟩ := toSumSubsets_to_neSubset bh; subst m1 k1
    have : as ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
      have ⟨pi,pi_in,pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
      pieces_trans' pi_piece (m2 pi_in)
    have mon := toSumSubsets_monotone this
    have ⟨m1,m2,m3⟩ := mon (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as,rfl⟩)
    exact ⟨~m1,NegCong m2,⟨m1,m3,rfl⟩⟩
  | .Star r  =>
    simp only [pieces, mem_cons, mem_map] at h2
    match h2 with
    | Or.inl g =>
      subst g
      simp_all only [pieces, mem_cons, mem_map, true_or, mem_up_to]
      match h1 with
      | Or.inl g => subst g; exact ⟨r*,Rfl,Or.inl rfl⟩
      | Or.inr ⟨a,_,ha1⟩ => subst ha1; exact ⟨a ⬝ r*,Rfl,h1⟩
    | Or.inr ⟨a,ha,ha1⟩ =>
      subst ha1
      simp_all only [pieces, mem_append, mem_map, mem_cons, Concatenation.injEq, and_true, exists_eq_right, or_true, mem_up_to]
      match h1 with
      | Or.inl ⟨b,hb,hb1⟩ =>
        subst hb1
        have ⟨zs,ne_zs,m1,m2⟩ := toSumSubsets_to_neSubset ha
        have ⟨as,ne_as,k1,k2⟩ := toSumSubsets_to_neSubset hb
        subst m1 k1
        have : as ⊆[ (· ≅ ·) ] pieces r := fun x hx =>
          have ⟨pi,pi_in,pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
          pieces_trans' pi_piece (m2 pi_in)
        have mon := toSumSubsets_monotone this
        have ⟨m1,m2,m3⟩ := mon (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as,rfl⟩)
        exact ⟨m1 ⬝ r*,CatCong m2,Or.inr ⟨m1,m3,rfl⟩⟩
      | Or.inr g =>
        match g with
        | Or.inl g1 => subst g1; exact ⟨r*,Rfl,Or.inl rfl⟩
        | Or.inr ⟨a,_,ha1⟩ => subst ha1; exact ⟨a ⬝ r*,Rfl,g⟩

theorem toSumSubsets_pieces_refl {r : RE α} : r ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  have ⟨xs,xs_in,xs_eqv⟩ := pieces_refl (r:=r)
  ⟨toSum xs,Sym xs_eqv, mem_map.mpr ⟨xs,neSubsets_characterization.mpr ⟨xs,xs_in,Perm.refl _⟩,rfl⟩⟩

theorem toSumSubsets_pieces_trans [DecidableEq α] {e : RE α}
  (h1 : e ∈[ (· ≅ ·) ] ⊕(pieces f))
  (h2 : f ∈[ (· ≅ ·) ] ⊕(pieces g)) :
        e ∈[ (· ≅ ·) ] ⊕(pieces g) := by
  simp_all only [mem_up_to, toSumSubsets, mem_map]
  -- reason about neSubsets of pieces
  let ⟨ff,f1,⟨sub_ps_f,hbs,hbs1⟩⟩ := h1
  let ⟨gg,g1,⟨sub_ps_g,has,has1⟩⟩ := h2
  subst has1 hbs1
  -- use properties of pieces (pieces_sim and pieces_trans)
  have sub : sub_ps_f ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
    have ⟨i1,i2,i3⟩ := (pieces_sim g1) _ ((neSubset_to_sublist hbs) hx)
    have ⟨gi,hgi1,hgi2⟩ := pieces_toSum (neSubsets_ne has) i3
    have : pieces gi ⊆[ (· ≅ ·) ] pieces g := fun p hp => pieces_trans' hp ((neSubset_to_sublist has) hgi1)
    have ⟨f1,f2,f3⟩ := this _ hgi2
    ⟨f1,Trans i2 f2,f3⟩
  have ⟨ys',nodup_ys',ne_ys',sub_ys',fs_ys'⟩ := toSumnodup_equiv (neSubsets_ne hbs) sub
  have ⟨i1,i2,i3⟩ := subset_to_neSubset sub_ys' ne_ys' nodup_ys'
  exact ⟨toSum i1,Trans (Trans f1 fs_ys') i3,⟨i1,i2,rfl⟩⟩

/-- `pieces` as a closure operator. -/
@[simp]
def piecesS (xs : List (RE α)) : List (RE α) :=
  map ((⊕ ·) ∘ (pieces ·)) xs |> flatten

theorem piecesS_extensive [DecidableEq α] {xs : List (RE α)} :
  xs ⊆[(· ≅ ·)] piecesS xs := fun x hx =>
  have ⟨x', x'_eq, x'_mem⟩ := toSumSubsets_pieces_refl (r := x)
  ⟨x',x'_eq,by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists x⟩

theorem piecesS_monotone [DecidableEq α] {xs ys : List (RE α)} (h : xs ⊆[(· ≅ ·)] ys) :
  piecesS xs ⊆[(· ≅ ·)] piecesS ys := fun px hpx => by
  simp only [subset_up_to] at h
  simp only [piecesS] at hpx
  have ⟨l, l_in, px_in⟩ := mem_flatten.mp hpx
  have ⟨x', x'_in, x'_pcs⟩ := mem_map.mp l_in
  subst x'_pcs
  have ⟨y', y'_eq, y'_in⟩ := h x' x'_in
  have pcs_x'_y' := pieces_sim y'_eq
  have ⟨py, py_eq, py_in⟩ := toSumSubsets_monotone pcs_x'_y' px px_in
  exact ⟨py,py_eq,by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists y'⟩

theorem piecesS_idem [DecidableEq α] (xs : List (RE α)) :
  piecesS (piecesS xs) ⊆[(· ≅ ·)] piecesS xs := fun px hpx => by
  have ⟨l, l_in, px_l⟩ := mem_flatten.mp hpx
  have ⟨m, m_in, pcs_m_l⟩ := mem_map.mp l_in
  have ⟨n, n_in, m_n⟩ := mem_flatten.mp m_in
  have ⟨x, x_in, pcs_x_n⟩ := mem_map.mp n_in
  subst pcs_m_l pcs_x_n
  have r1 : px ∈[(· ≅ ·)] ⊕(pieces m) := ⟨px, Rfl, px_l⟩
  have r2 : m ∈[(· ≅ ·)] ⊕(pieces x) := ⟨m, Rfl, m_n⟩
  have ⟨px', px'_eq, px'_in⟩ := toSumSubsets_pieces_trans r1 r2
  exact ⟨px', px'_eq, by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists x⟩
