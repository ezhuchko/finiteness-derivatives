import Finiteness.Pieces
import Finiteness.Similarity

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Finiteness of the state space

Contains the proof of finiteness for symbolic derivatives.

The main approach here is to relate the `step` function to the `pieces` function, which
is the overapproximation of the state space.

-/

theorem step_to_pieces {e : RE α} (e_in : e ∈ step f) :
  ∃ xs, toSum xs ≅ e ∧ xs ∈ neSubsets (pieces f) := by
  match f with
  | ε | ?=_ | ?!_ | ?<=_ | ?<! _ =>
    simp only [step, derivative, leaves, mem_cons, not_mem_nil, or_false] at e_in
    subst e_in
    exact ⟨[Pred ⊥], Rfl, mem_of_getLast? rfl⟩
  | Pred φ    =>
    simp only [step, derivative, leaves, cons_append, nil_append, mem_cons, not_mem_nil, or_false] at e_in
    match e_in with
    | Or.inl h2 =>
      subst h2
      let eps_in_pieces := neSublists_singleton (xs:=(pieces (Pred φ))) (mem_cons.mpr $ Or.inr $ mem_cons.mpr $ Or.inl rfl)
      let eps_in_neSubsets := neSubsets_characterization.mpr ⟨[ε], eps_in_pieces, singleton_perm_singleton.mpr rfl⟩
      exact ⟨[ε],Rfl,eps_in_neSubsets⟩
    | Or.inr h2 =>
      subst h2
      let bot_in_pieces := neSublists_singleton (xs:=(pieces (Pred φ))) (mem_cons.mpr $ Or.inr $ mem_cons.mpr $ Or.inr $ mem_singleton.mpr rfl)
      let bot_in_neSubsets := neSubsets_characterization.mpr ⟨[Pred ⊥], bot_in_pieces, singleton_perm_singleton.mpr rfl⟩
      exact ⟨[Pred ⊥],Rfl,bot_in_neSubsets⟩
  | l ⬝ r     =>
    rw[step_concatenation] at e_in
    simp only [productWith, product, step, leaves_unary, mem_append, mem_map, mem_flatMap] at e_in
    simp only [exists_exists_and_eq_and, exists_exists_and_exists_and_eq_and] at e_in
    match e_in with
    | Or.inl ⟨a1,a2,⟨a3,a4,a5⟩⟩ =>
      subst a5
      have ⟨i1,i2,i3⟩ := step_to_pieces a2
      have ⟨j1,j2,j3⟩ := step_to_pieces a4
      let ⟨b,hb,hb1⟩ := neSubsets_characterization.mp j3
      let ⟨a,ha,ha1⟩ := neSubsets_characterization.mp i3
      have equiv := Trans (toSum_append (cons_ne_nil (toSum i1 ⬝ r) []) (neSub_ne_perm hb hb1)) (AltCong (CatCong i2) j2)
      exact ⟨(toSum i1 ⬝ r) :: j1, equiv, neSubsets_append (neSubsets_singleton $ mem_map.mpr ⟨toSum i1,mem_map.mpr ⟨i1,i3,rfl⟩,rfl⟩) j3⟩
    | Or.inr ⟨a1,a2,a4⟩ =>
      subst a4
      have ⟨i1,i2,i3⟩ := step_to_pieces a2
      let ⟨a,ha,ha1⟩ := neSubsets_characterization.mp i3
      exact ⟨[(toSum i1) ⬝ r],CatCong i2, neSubsets_singleton $ mem_append.mpr $ Or.inl $ mem_map.mpr ⟨toSum i1,mem_map.mpr ⟨i1,i3,rfl⟩,rfl⟩⟩
  | r* =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    let ⟨a1,a2,a4⟩ := e_in
    subst a4
    have ⟨i1,i2,i3⟩ := step_to_pieces a2
    let ⟨a,ha,ha1⟩ := neSubsets_characterization.mp i3
    exact ⟨[(toSum i1) ⬝ r*],CatCong i2,neSubsets_singleton $ mem_cons.mpr $ Or.inr $ mem_map.mpr ⟨toSum i1,mem_map.mpr ⟨i1,i3,rfl⟩,rfl⟩⟩
  | l ⋓ r =>
    simp only [step, derivative, leaves_binary, productWith, product, mem_map, mem_flatMap,
      exists_exists_and_exists_and_eq_and] at e_in
    let ⟨a1,a2,⟨a3,a4,a5⟩⟩ := e_in; subst a5
    have ⟨i1,i2,i3⟩ := step_to_pieces a2
    have ⟨j1,j2,j3⟩ := step_to_pieces a4
    exact ⟨i1 ++ j1,Trans (toSum_append (neSubsets_ne i3) (neSubsets_ne j3)) (AltCong i2 j2),neSubsets_append i3 j3⟩
  | l ⋒ r =>
    simp only [step, derivative, leaves_binary, productWith, product, mem_map, mem_flatMap, exists_exists_and_exists_and_eq_and] at e_in
    let ⟨a1,a2,⟨a3,a4,a5⟩⟩ := e_in
    subst a5
    have ⟨i1,i2,i3⟩ := step_to_pieces a2
    have ⟨j1,j2,j3⟩ := step_to_pieces a4
    exact ⟨[toSum i1 ⋒ toSum j1],InterCong i2 j2,
            neSubsets_singleton (by unfold pieces productWith product
                                    simp only [mem_map, mem_flatMap, exists_exists_and_exists_and_eq_and,
                                      Function.uncurry_apply_pair, Intersection.injEq, exists_eq_right_right];
                                    unfold toSumSubsets
                                    exact ⟨mem_map.mpr ⟨i1,i3,rfl⟩,mem_map.mpr ⟨j1,j3,rfl⟩⟩)⟩
  | ~ r =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    let ⟨a1,a2,a3⟩ := e_in
    subst a3
    have ⟨i1,i2,i3⟩ := step_to_pieces a2
    exact ⟨[~(toSum i1)],NegCong i2,neSubsets_singleton (mem_map.mpr ⟨toSum i1,mem_map.mpr ⟨i1,i3,rfl⟩,rfl⟩)⟩

theorem step_to_toSumSubsets {r : RE α} :
  step r ⊆[ (· ≅ ·) ] ⊕(pieces r) :=
  fun _ in_step =>
  have ⟨a1,a2,a3⟩ := step_to_pieces in_step
  ⟨toSum a1,Sym a2,mem_map.mpr ⟨a1,a3,rfl⟩⟩

theorem steps_to_toSumSubsets [DecidableEq α] {r : RE α} :
  steps r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 h =>
  match n with
  | 0 => by
    simp only [steps, mem_cons, not_mem_nil, or_false] at h
    subst h
    exact toSumSubsets_pieces_refl -- reflexivity
  | Nat.succ n => by
    simp only [steps, mem_flatten, mem_map, step, exists_exists_and_eq_and] at h
    let ⟨e2,e2_steps_n,e1_step_e2⟩ := h
    have ⟨q1,q1_eqv,ih⟩  := steps_to_toSumSubsets e2 e2_steps_n -- inductive hypothesis
    have ⟨xs,xs_eqv,hxs⟩ := step_to_toSumSubsets _ e1_step_e2   -- single-step closure
    have e2_in : e2 ∈[ (· ≅ ·) ] ⊕(pieces r) := ⟨q1,q1_eqv,ih⟩
    have e_in  : e1 ∈[ (· ≅ ·) ] ⊕(pieces e2) := ⟨xs,xs_eqv,hxs⟩
    exact toSumSubsets_pieces_trans e_in e2_in -- transitivity

theorem finiteness [DecidableEq α] {r : RE α} :
  ∃ (xs : List (RE α)), ∀ {n : ℕ}, steps r n ⊆[ (· ≅ ·) ] xs :=
  ⟨⊕(pieces r),steps_to_toSumSubsets⟩

/-- Alternative way to state finiteness with the closure operator. -/
theorem finiteness_piecesS [DecidableEq α] {r : RE α}:
  steps r n ⊆[(· ≅ ·)] piecesS [r] :=
  match n with
  | 0 => piecesS_extensive
  | n + 1 => fun re re_in => by
    simp only [steps, mem_flatten, mem_map, exists_exists_and_eq_and] at re_in
    let ⟨e,_,e_step⟩ := re_in
    have ⟨f,f_equiv,_⟩ : re ∈[(· ≅ ·)] ⊕(pieces e) :=
      have ⟨xs,h1,h2⟩ := step_to_pieces (f:=e) e_step
      ⟨toSum xs,Sym h1,mem_map.mpr ⟨xs,h2,rfl⟩⟩
    have ⟨_,g_equiv,g_piece⟩ : re ∈[(· ≅ ·)] piecesS (steps r n) :=
      ⟨f,f_equiv,
       by simp only [piecesS, map_flatten, map_map, mem_flatten, mem_map, exists_exists_and_eq_and]
          exists e⟩
    have step1 := piecesS_monotone (finiteness_piecesS (r:=r) (n:=n))
    have step2 := piecesS_idem (xs:= [r])
    have ⟨h,h_equiv,h_piece⟩ := subset_up_to_trans_sim step1 step2 _ g_piece
    exact ⟨h,Sim.Trans g_equiv h_equiv,h_piece⟩
