import Finiteness.SymbolicDerivative
import Finiteness.SubsetUpTo

open RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Similarity relation

This file contains the definition of similarity. It is necessary to quotient the
alternation operator under similarity in order to obtain
finiteness of the state space.

-/

/-- Similarity relation contains the following laws :
    associativity, right deduplication and idempotence. -/
inductive Sim : RE α → RE α → Prop where
  | Assoc     : Sim ((R₁ ⋓ R₂) ⋓ R₃) (R₁ ⋓ (R₂ ⋓ R₃))
  | DeDup     : Sim (R₁ ⋓ R₂ ⋓ R₁) (R₁ ⋓ R₂)
  | Idem      : Sim (R ⋓ R) R
  | Rfl       : Sim R R
  | Sym       : Sim R₁ R₂ → Sim R₂ R₁
  | Trans     : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  | NegCong   : Sim R₁ R₂ → Sim ~R₁ ~R₂
  | AltCong   : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋓ S₁) (R₂ ⋓ S₂)
  | InterCong : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋒ S₁) (R₂ ⋒ S₂)
  | CatCong   : Sim R₁ R₂ → Sim (R₁ ⬝ S) (R₂ ⬝ S)
infix:37 " ≅ " => Sim
open Sim

theorem subset_up_to_refl_sim {xs : List (RE α)} :
  xs ⊆[ (· ≅ ·) ] xs := subset_up_to_refl (fun _ => Rfl)

theorem subset_up_to_trans_sim {xs ys zs : List (RE α)}
  (h : xs ⊆[ (· ≅ ·) ] ys) (h1 : ys ⊆[ (· ≅ ·) ] zs) :
  xs ⊆[ (· ≅ ·) ] zs := subset_up_to_trans (fun _ _ _ g1 g2 => Trans g1 g2) h h1

theorem subset_to_subset_up_to_sim {xs ys : List (RE α)} (h : xs ⊆ ys) :
  xs ⊆[ (· ≅ ·) ] ys := subset_to_subset_up_to (fun _ => Rfl) h

theorem subset_up_to_sim_cons (xs : List (RE α)) :
  xs ⊆[ (· ≅ ·) ] (x::xs) :=
  match xs with
  | [] => subset_to_subset_up_to_sim (List.nil_subset [x])
  | y::ys => fun a ha =>
    match List.mem_cons.mp ha with
    | Or.inl _ => ⟨a,Rfl,List.mem_cons_of_mem x ha⟩
    | Or.inr g1 =>
      have ⟨i1,i2,i3⟩ := (subset_up_to_sim_cons (x:=y) ys) a g1
      ⟨i1,i2,List.mem_cons_of_mem x i3⟩

theorem subset_up_to_sim_of_cons_subset {c : RE α} (h : (c :: cs) ⊆[ (· ≅ ·) ] ys) :
  cs ⊆[ (· ≅ ·) ] ys := subset_up_to_trans_sim (subset_up_to_sim_cons cs) h

theorem step_assoc {r s t : RE α} :
  step ((r ⋓ s) ⋓ t) ⊆[ (· ≅ ·) ] step (r ⋓ (s ⋓ t)) := fun x h => by
  rw[step_alternation] at h
  simp only [List.productWith, step, derivative, leaves_binary, List.mem_map, Prod.exists,
    List.pair_mem_product, Function.uncurry_apply_pair] at h
  let ⟨y,h1,⟨⟨⟨a,⟨b1,b2,b3⟩⟩,c⟩,h2⟩⟩ := h
  subst h2 b3
  exact ⟨a ⋓ b1 ⋓ h1,Assoc,
         by rw[step_alternation]
            simp only [List.productWith, step, derivative, leaves_binary, List.mem_map, Prod.exists,
              List.pair_mem_product, Function.uncurry_apply_pair, Alternation.injEq, exists_eq_right_right,
              exists_eq_right]
            exact ⟨b2.1,b2.2,c⟩⟩
