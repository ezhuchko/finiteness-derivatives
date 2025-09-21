import Finiteness.Finite

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Simplifications

This file contains the simplifications which preserve the finiteness result.
This gives rise to the following criterion: a simplification function `f : RE α → RE α` is admissible
if it is `NonIncreasing`.
-/

@[simp]
def simplify (f : RE α → RE α) : RE α → RE α
  | l ⋒ r  => simplify f l ⋒ simplify f r
  | ~r     => ~(simplify f r)
  | l ⬝ r  => f (simplify f l ⬝ r)
  | l ⋓ r  => f (simplify f l ⋓ simplify f r)
  | r      => r

-- define a type for nonincreasing fs
@[simp]
def NonIncreasing (f : RE α → RE α) := ∀ ⦃r⦄, pieces (f r) ⊆ pieces r

theorem NonIncreasing_comp {f g : RE α → RE α} (ni_f : NonIncreasing f) (ni_g : NonIncreasing g):
  NonIncreasing (g ∘ f) := fun _ _ h => ni_f (ni_g h)

theorem NonIncreasing_pieces [DecidableEq α] {r : RE α} (ni_f : NonIncreasing f) :
  pieces (simplify f r) ⊆[ (· ≅ ·) ] pieces r := fun re h =>
  match r with
  | ε | Pred φ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ => ⟨re,Rfl,h⟩
  | l ⬝ r  => by
    have := ni_f h
    simp only [simplify, pieces, mem_append, mem_map] at h this
    match this with
    | Or.inl ⟨g1,g2,g3⟩ =>
      have ⟨a1,a2,a3⟩ := toSumSubsets_monotone (NonIncreasing_pieces ni_f (r:=l)) _ g2
      subst g3
      exact ⟨a1 ⬝ r,Sim.Trans Rfl (CatCong a2),
             by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨a1,a3,rfl⟩⟩
    | Or.inr g1 => exact ⟨re,Rfl,by simp only [pieces, mem_append, mem_map]; exact Or.inr g1⟩
  | l ⋓ r  => by
    have := ni_f h
    simp[pieces] at h this
    match this with
    | Or.inl g1 =>
      have ⟨a1,a2,a3⟩ := (NonIncreasing_pieces ni_f (r:=l)) _ g1
      exact ⟨a1,Sim.Trans Rfl a2,mem_append.mpr $ Or.inl a3⟩
    | Or.inr g1 =>
      have ⟨a1,a2,a3⟩ := (NonIncreasing_pieces ni_f (r:=r)) _ g1
      exact ⟨a1,Sim.Trans Rfl a2,mem_append.mpr $ Or.inr a3⟩
  | l ⋒ r  => by
    simp[pieces] at h
    let ⟨r1,r2,⟨hr1,hr2⟩,eq⟩ := h
    subst eq
    have ⟨a1,a2,a3⟩ := toSumSubsets_monotone (NonIncreasing_pieces ni_f (r:=l)) _ hr1
    have ⟨b1,b2,b3⟩ := toSumSubsets_monotone (NonIncreasing_pieces ni_f (r:=r)) _ hr2
    exact ⟨a1 ⋒ b1,InterCong a2 b2,
           by simp only [pieces, productWith, mem_map, Prod.exists, pair_mem_product];
              exact ⟨a1,b1,⟨a3,b3⟩,rfl⟩⟩
  | ~r     => by
    simp[pieces] at h
    let ⟨r1,hr1,eq⟩ := h
    subst eq
    have ⟨a1,a2,a3⟩ := toSumSubsets_monotone (NonIncreasing_pieces ni_f (r:=r)) _ hr1
    exact ⟨~a1,NegCong a2,by simp only [pieces, mem_map, Negation.injEq, exists_eq_right]; exact a3⟩

@[simp]
def plus_bot_l [DecidableEq α] : RE α → RE α
  | Pred ψ ⋓ r => if ψ = ⊥ then r else Pred ψ ⋓ r
  | r => r

@[simp]
def plus_bot_r [DecidableEq α] : RE α → RE α
  | l ⋓ Pred ψ => if ψ = ⊥ then l else l ⋓ Pred ψ
  | r => r

@[simp]
def mult_eps : RE α → RE α
  | ε ⬝ r => r
  | r => r

@[simp]
def mult_bot [DecidableEq α] : RE α → RE α
  | r ⬝ Pred ψ => if ψ = ⊥ then Pred ⊥ else r ⬝ Pred ψ
  | r => r

@[simp]
def distr : RE α → RE α
  | (l ⋓ r) ⬝ p => l ⬝ p ⋓ r ⬝ p
  | r => r

-- ~⊥ + r → ~⊥
@[simp]
def plus_not_bot [DecidableEq α] : RE α → RE α
  | ~(Pred ψ) ⋓ r => if ψ = ⊥ then ~(Pred ψ) else ~(Pred ψ) ⋓ r
  | r => r

-- e ⬝ ⊥ -> ⊥ less useful than ⊥ ⬝ f -> ⊥
-- this would allow to stop the derivative early

theorem plus_bot_l_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_bot_l := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | ~_ => h
  | l ⋓ r  =>
    match l with
    | Pred φ => by
      by_cases g : φ = ⊥
      . subst g; simp only [plus_bot_l] at h; exact mem_append.mpr (Or.inr h)
      . simp_all only [plus_bot_l, ↓reduceIte, pieces, cons_append, nil_append, mem_cons]
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem plus_bot_r_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_bot_r := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | ~_  => h
  | l ⋓ r  =>
    match r with
    | Pred φ => by
      by_cases g : φ = ⊥
      . subst g; simp only [plus_bot_r] at h; exact mem_append.mpr (Or.inl h)
      . simp_all only [plus_bot_r, ↓reduceIte, pieces, mem_append, mem_cons, not_mem_nil, or_false]
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem mult_eps_ni :
  NonIncreasing (α := α) mult_eps := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
  | l ⬝ r  =>
    match l with
    | ε      => by simp_all only [mult_eps, pieces, mem_append, mem_map, or_true]
    | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem mult_bot_ni [DecidableEq α] :
  NonIncreasing (α := α) mult_bot := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
  | l ⬝ r  =>
    match r with
    | Pred ψ => by
      by_cases g : ψ = ⊥
      . subst g
        simp_all only [mult_bot, ↓reduceIte, pieces, mem_cons, not_mem_nil, or_false, mem_append, mem_map, or_true]
      . simp only [mult_bot, g] at h; exact h
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem distr_ni :
  NonIncreasing (α := α) distr := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
  | (l ⋓ r) ⬝ g  => by
    simp[pieces] at h
    match h with
    | Or.inl ⟨a1,a2,eq⟩ =>
      subst eq
      unfold pieces; simp only [mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
      exact Or.inl (toSum_appendL a2)
    | Or.inr g' =>
      rw[Or.comm, or_self_right] at g'
      match g' with
      | Or.inl ⟨a1,a2,eq⟩ =>
        subst eq
        unfold pieces; simp only [mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
        exact Or.inl $ toSum_appendR a2
      | Or.inr g1 => simp only [pieces, mem_append, mem_map]; exact Or.inr g1
  | l ⬝ g =>
    match l with
    | l1 ⋓ l2 => by
      simp only [distr, pieces, append_assoc, mem_append, mem_map] at h
      match h with
      | Or.inl ⟨a1,a2,a3⟩ =>
        subst a3
        unfold pieces; simp only [mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
        exact Or.inl $ toSum_appendL a2
      | Or.inr g1 =>
        rw[Or.comm, or_self_right] at g1
        match g1 with
        | Or.inl ⟨a1,a2,a3⟩ =>
          subst a3; unfold pieces
          simp only [mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
          exact Or.inl $ toSum_appendR a2
        | Or.inr g2 =>
          unfold pieces; simp only [mem_append, mem_map]
          exact Or.inr g2
    | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | ~_ => h

theorem plus_not_bot_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_not_bot := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⬝_ | ~_ => h
  | l ⋓ r =>
    match l with
    | ~l =>
      match l with
      | Pred ψ => by
        by_cases g : ψ = ⊥
        . subst g; simp only [plus_not_bot, ↓reduceIte] at h; exact mem_append.mpr $ Or.inl h
        . simp only [plus_not_bot, g, ↓reduceIte] at h; exact h
      | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h
    | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ => h

-- define as a fold
def NonIncreasing_simps [DecidableEq α] : RE α → RE α :=
  plus_not_bot ∘ plus_bot_l ∘ plus_bot_r ∘ mult_eps ∘ mult_bot ∘ distr

def NonIncreasing_simps_proof [DecidableEq α] :
  NonIncreasing (α := α) NonIncreasing_simps := fun r _ h =>
  have step0 : NonIncreasing (α:=α) (plus_not_bot ∘ plus_bot_l ∘ plus_bot_r ∘ mult_eps ∘ mult_bot) :=
    NonIncreasing_comp (NonIncreasing_comp (NonIncreasing_comp (NonIncreasing_comp mult_bot_ni mult_eps_ni) plus_bot_r_ni) plus_bot_l_ni) plus_not_bot_ni
  have step := NonIncreasing_comp (g:= plus_not_bot ∘ plus_bot_l ∘ plus_bot_r ∘ mult_eps ∘ mult_bot) (r:=r) distr_ni step0
  step h

def step_with_simp [DecidableEq α] (r : RE α) : List (RE α) :=
  map (simplify NonIncreasing_simps) (step r)

@[simp]
def steps_with_simp [DecidableEq α] (r : RE α) : ℕ → List (RE α)
  | 0 => [r]
  | Nat.succ n => map step_with_simp (steps_with_simp r n) |> flatten

theorem fin_step_with_simp [DecidableEq α] {r : RE α} :
  step_with_simp r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 in_step => by
  simp only [step_with_simp, mem_map] at in_step
  let ⟨a1,a2,a3⟩ := in_step
  subst a3
  have ⟨p1,p2,p3⟩ := pieces_refl (r:=simplify NonIncreasing_simps a1)
  have ⟨m1,m2,m3⟩ : toSum p1 ∈[ (· ≅ ·) ] ⊕((pieces (simplify NonIncreasing_simps a1))) :=
    ⟨toSum p1, Rfl, by simp[toSumSubsets]; exact ⟨p1,p2,⟨p1,Perm.refl _,rfl⟩⟩⟩
  have inter_step := toSumSubsets_monotone $ NonIncreasing_pieces (r:=a1) NonIncreasing_simps_proof
  have ⟨o1,o2,o3⟩ := toSumSubsets_pieces_trans (inter_step _ m3) (step_to_toSumSubsets _ a2)
  exists o1; exists Sim.Trans (Sim.Trans (Sym p3) m2 ) o2

theorem finiteness_simp [DecidableEq α] {r : RE α} :
  steps_with_simp r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 h =>
  match n with
  | 0 => by
    simp only [steps_with_simp, mem_cons, not_mem_nil, or_false] at h
    subst h; exact toSumSubsets_pieces_refl
  | Nat.succ n => by
    simp at h
    let ⟨e2,e2_steps_n,e1_step_e2⟩ := h
    have ⟨q1,q1_eqv,ih⟩ := finiteness_simp _ e2_steps_n
    have ⟨xs,xs_eqv,hxs⟩ := fin_step_with_simp _ e1_step_e2
    have e2_in : e2 ∈[ (· ≅ ·) ] ⊕(pieces r) := ⟨q1,q1_eqv,ih⟩
    have e_in  : e1 ∈[ (· ≅ ·) ] ⊕(pieces e2) := ⟨xs,xs_eqv,hxs⟩
    exact toSumSubsets_pieces_trans e_in e2_in

/-- An alternative definition of pieces which allows more simplifications.
    Added `⊥` to inter, star and neg cases to make pieces `⊥`-closed. Also added
    `pieces' l` and `pieces' r` in the intersection case to allow more simplifications.
    Finally, add `pieces' l` to concat case to allows `mult_eps_r`. -/
def pieces' : RE α → List (RE α)
  | ε         => [ε, Pred ⊥]
  | ?= r      => [?= r, ε, Pred ⊥]
  | ?! r      => [?! r, ε, Pred ⊥]
  | ?<= r     => [?<= r, ε, Pred ⊥]
  | ?<! r     => [?<! r, ε, Pred ⊥]
  | Pred φ    => [Pred φ, ε, Pred ⊥]
  | l ⋓ r     => pieces' l ++ pieces' r
  | l ⋒ r     => Pred ⊥ :: productWith (· ⋒ ·) ⊕(pieces' l) ⊕(pieces' r) ++ pieces' l ++ pieces' r
  | l ⬝ r     => map (· ⬝ r) ⊕(pieces' l) ++ pieces' r ++ pieces' l
  | .Star r   => Pred ⊥ :: r* :: map (· ⬝ r*) ⊕(pieces' r) ++ pieces' r
  | ~ r       => Pred ⊥ :: map (~ ·) ⊕(pieces' r) ++ pieces' r

theorem bot_in_pieces' {r : RE α} : Pred ⊥ ∈ pieces' r := by
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | ~r | l ⋒ r | .Star r => simp[pieces']
  | l ⋓ r => simp[pieces']; exact Or.inl bot_in_pieces'
  | l ⬝ r => simp[pieces']; exact Or.inl bot_in_pieces'

theorem eps_in_pieces' {r : RE α} : ε ∈ pieces' r := by
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ => simp[pieces']
  | .Star r | ~r => simp[pieces']; exact eps_in_pieces'
  | l ⬝ r | l ⋓ r | l ⋒ r => simp[pieces']; exact Or.inl eps_in_pieces'

-- ⊥ ⬝ r → ⊥
@[simp]
def mult_bot_l [DecidableEq α] : RE α → RE α
  | Pred ψ ⬝ r => if ψ = ⊥ then Pred ⊥ else Pred ψ ⬝ r
  | r => r

-- ⊥ ⋒ r → ⊥
@[simp]
def inter_bot_l [DecidableEq α] : RE α → RE α
  | Pred ψ ⋒ r => if ψ = ⊥ then Pred ⊥ else Pred ψ ⋒ r
  | r => r

-- r ⋒ ⊥ → ⊥
@[simp]
def inter_bot_r [DecidableEq α] : RE α → RE α
  | r ⋒ Pred ψ => if ψ = ⊥ then Pred ⊥ else r ⋒ Pred ψ
  | r => r

-- ~~r → r
@[simp]
def double_neg [DecidableEq α] : RE α → RE α
  | ~~r => r
  | r => r

-- r ⋒ ~⊥ → r
@[simp]
def inter_not_bot_r [DecidableEq α] : RE α → RE α
  | r ⋒ ~(Pred ψ) => if ψ = ⊥ then r else r ⋒ ~(Pred ψ)
  | r => r

-- ~⊥ ⋒ r → r
@[simp]
def inter_not_bot_l [DecidableEq α] : RE α → RE α
  | ~(Pred ψ) ⋒ r => if ψ = ⊥ then r else ~(Pred ψ) ⋒ r
  | r => r

-- r ⬝ ε → r
@[simp]
def mult_eps_r : RE α → RE α
  | r ⬝ ε => r
  | r => r

def Nonincreasing' (f : RE α → RE α) := ∀ ⦃r⦄, pieces' (f r) ⊆ pieces' r

theorem Nonincreasing'_comp {f g : RE α → RE α} (ni_f : Nonincreasing' f) (ni_g : Nonincreasing' g):
  Nonincreasing' (g ∘ f) := fun _ _ h => ni_f (ni_g h)

theorem mult_bot_l_ni [DecidableEq α] :
  Nonincreasing' (α := α) mult_bot_l := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
  | l ⬝ r  =>
    match l with
    | Pred ψ => by
      by_cases g : ψ = ⊥
      . subst g
        simp only [mult_bot_l, ↓reduceIte, pieces', mem_cons, not_mem_nil, or_false] at h
        rw[Or.comm, or_self_right] at h
        match h with
        | Or.inl h1 => subst h1; exact eps_in_pieces'
        | Or.inr h1 => subst h1; exact bot_in_pieces'
      . simp only [mult_bot_l, g] at h; exact h
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem inter_bot_l_ni [DecidableEq α] :
  Nonincreasing' (α := α) inter_bot_l := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | ~_ => h
  | l ⋒ r  =>
    match l with
    | Pred ψ => by
      by_cases g : ψ = ⊥
      . subst g
        simp only [inter_bot_l] at h
        unfold pieces'
        simp only [productWith, cons_append, append_assoc, mem_cons, mem_append, mem_map,
          Prod.exists, pair_mem_product]
        exact Or.inr $ Or.inr $ Or.inl h
      . simp only [inter_bot_l, g] at h; exact h
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem inter_bot_r_ni [DecidableEq α] :
  Nonincreasing' (α := α) inter_bot_r := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | ~_ => h
  | l ⋒ r  =>
    match r with
    | Pred ψ => by
      by_cases g : ψ = ⊥
      . subst g; simp only [inter_bot_r] at h
        unfold pieces'
        simp only [productWith, cons_append, append_assoc, mem_cons, mem_append, mem_map,
          Prod.exists, pair_mem_product]
        exact Or.inr $ Or.inr $ Or.inr h
      . simp only [inter_bot_r, g] at h; exact h
    | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

theorem double_neg_ni [DecidableEq α] :
  Nonincreasing' (α := α) double_neg := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_  => h
  | ~r =>
    match r with
    | ~r => by
      unfold pieces'
      simp only [cons_append, mem_cons, mem_append, mem_map]
      simp only [double_neg] at h
      unfold pieces'
      simp only [cons_append, mem_cons, mem_append, mem_map]
      exact Or.inr $ Or.inr $ Or.inr $ Or.inr h
    | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_  => h

theorem inter_not_bot_r_ni [DecidableEq α] :
  Nonincreasing' (α := α) inter_not_bot_r := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | ~_  => h
  | l ⋒ r =>
    match r with
    | ~r =>
      match r with
      | Pred ψ => by
        by_cases g : ψ = ⊥
        . subst g; simp only [inter_not_bot_r] at h
          unfold pieces'
          simp only [productWith, cons_append, append_assoc, mem_cons, mem_append, mem_map, Prod.exists, pair_mem_product]
          exact Or.inr $ Or.inr $ Or.inl h
        . simp[g] at h; exact h
      | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_ | ~_ => h
    | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_ => h

theorem inter_not_bot_l_ni [DecidableEq α] :
  Nonincreasing' (α := α) inter_not_bot_l := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | ~_  => h
  | l ⋒ r =>
    match l with
    | ~r =>
      match r with
      | Pred ψ => by
        by_cases g : ψ = ⊥
        . subst g; simp only [inter_not_bot_l] at h
          unfold pieces'
          simp only [productWith, cons_append, append_assoc, mem_cons, mem_append, mem_map, Prod.exists, pair_mem_product]
          exact Or.inr $ Or.inr $ Or.inr h
        . simp only [inter_not_bot_l, g] at h; exact h
      | ε | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_ | ~_ => h
    | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋓_ | _⋒_ => h

theorem mult_eps_r_ni :
  Nonincreasing' (α := α) mult_eps_r := fun r r1 h =>
  match r with
  | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
  | l ⬝ r  =>
    match r with
    | ε      => by
      simp only [mult_eps_r] at h; unfold pieces'
      simp only [append_assoc, mem_append, mem_map]
      exact Or.inr $ Or.inr h
    | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | _⋓_ | ~_ => h

def NonIncreasing_simps' [DecidableEq α] : RE α → RE α :=
  mult_eps_r ∘ inter_not_bot_l ∘ inter_not_bot_r ∘ double_neg ∘ NonIncreasing_simps ∘ mult_bot_l ∘ inter_bot_l ∘ inter_bot_r

-- theorem distr'_ni :
--   Nonincreasing' (α := α) distr := fun r r1 h =>
--   match r with
--   | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⋒_ | _⋓_ | ~_ => h
--   | (l ⋓ r) ⬝ g  => by
--     simp[pieces'] at h
--     match h with
--     | Or.inl ⟨a1,a2,eq⟩ =>
--       subst eq
--       simp only [pieces', mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
--       exact Or.inl (Or.inl (toSum_appendL a2))
--     | Or.inr g' =>
--       match g' with
--       | Or.inl a1 => unfold pieces'; simp; exact Or.inr $ Or.inl a1
--       | Or.inr g1 =>
--         simp[pieces']
--         match g1 with
--         | Or.inl g2 => exact Or.inr $ Or.inr $ Or.inl g2
--         | Or.inr g2 =>
--           match g2 with
--           | Or.inl ⟨a1,a2,eq⟩ => subst eq; exact Or.inl ⟨a1,toSum_appendR a2,rfl⟩
--           | Or.inr g3 => exact Or.inr (by aesop)
--   | l ⬝ g =>
--     match l with
--     | l1 ⋓ l2 => by
--       simp only [distr, pieces', append_assoc, mem_append, mem_map] at h
--       match h with
--       | Or.inl ⟨a1,a2,a3⟩ =>
--         subst a3
--         simp only [pieces', mem_append, mem_map, Concatenation.injEq, and_true, exists_eq_right]
--         exact Or.inl $ Or.inl (toSum_appendL a2)
--       | Or.inr g1 =>
--         match g1 with
--         | Or.inl g2 =>
--           unfold pieces'
--           simp only [mem_append, mem_map]
--           exact Or.inl $ Or.inr g2
--         | Or.inr g2 =>
--           simp only [pieces', mem_append, mem_map]
--           sorry
--     | ε | Pred ψ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ | _⬝_ | _⋒_ | ~_ => h

-- def NonIncreasing_simps'_proof [DecidableEq α] :
--   NonIncreasing (α := α) NonIncreasing_simps' := fun r _ h =>
--   have step0 : Nonincreasing' (α:=α) (mult_eps_r ∘ inter_not_bot_l ∘ inter_not_bot_r ∘ double_neg ∘ NonIncreasing_simps' ∘ mult_bot_l ∘ inter_bot_l) :=
--     Nonincreasing'_comp (Nonincreasing'_comp (Nonincreasing'_comp (Nonincreasing'_comp (Nonincreasing'_comp (Nonincreasing'_comp inter_bot_l_ni mult_bot_l_ni) sorry) double_neg_ni) inter_not_bot_r_ni) inter_not_bot_l_ni) mult_eps_r_ni
--   have step := Nonincreasing'_comp (g:= mult_eps_r ∘ inter_not_bot_l ∘ inter_not_bot_r ∘ double_neg ∘ NonIncreasing_simps' ∘ mult_bot_l ∘ inter_bot_l ∘ inter_bot_r) (r:=r) distr'_ni step0
--   step h

def step_with_simp' [DecidableEq α] (r : RE α) : List (RE α) :=
  map (simplify NonIncreasing_simps') (step r)

@[simp]
def steps_with_simp' [DecidableEq α] (r : RE α) : ℕ → List (RE α)
  | 0 => [r]
  | Nat.succ n => map step_with_simp' (steps_with_simp' r n) |> flatten

-- theorem fin_step_with_simp' [DecidableEq α] {r : RE α} :
--   step_with_simp' r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 in_step => by
--   simp only [step_with_simp', mem_map] at in_step
--   let ⟨a1,a2,a3⟩ := in_step
--   subst a3
--   have ⟨p1,p2,p3⟩ := pieces_refl (r:=simplify NonIncreasing_simps' a1)
--   have ⟨m1,m2,m3⟩ : toSum p1 ∈[ (· ≅ ·) ] ⊕((pieces (simplify NonIncreasing_simps' a1))) :=
--     ⟨toSum p1, Rfl, by simp[toSumSubsets]; exact ⟨p1,p2,⟨p1,Perm.refl _,rfl⟩⟩⟩
--   -- have inter_step := toSumSubsets_monotone $ NonIncreasing_pieces (r:=a1) sorry -- NonIncreasing_simps'_proof
--   -- have ⟨o1,o2,o3⟩ := toSumSubsets_pieces_trans (inter_step _ m3) (step_to_toSumSubsets _ a2)
--   -- exists o1; exists Sim.Trans (Sim.Trans (Sym p3) m2) o2
--   sorry

-- theorem finiteness_simp' [DecidableEq α] {r : RE α} :
--   steps_with_simp' r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 h =>
--   match n with
--   | 0 => by
--     simp only [steps_with_simp', mem_cons, not_mem_nil, or_false] at h
--     subst h; exact toSumSubsets_pieces_refl
--   | Nat.succ n => by
--     simp at h
--     let ⟨e2,e2_steps_n,e1_step_e2⟩ := h
--     have ⟨q1,q1_eqv,ih⟩ := finiteness_simp' _ e2_steps_n
--     have ⟨xs,xs_eqv,hxs⟩ := fin_step_with_simp' _ e1_step_e2
--     have e2_in : e2 ∈[ (· ≅ ·) ] ⊕(pieces r) := ⟨q1,q1_eqv,ih⟩
--     have e_in  : e1 ∈[ (· ≅ ·) ] ⊕(pieces e2) := ⟨xs,xs_eqv,hxs⟩
--     exact toSumSubsets_pieces_trans e_in e2_in
