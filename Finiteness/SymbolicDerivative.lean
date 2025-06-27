import Regex.Definitions
import Finiteness.TTerm

open RE TTerm List

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Symbolic derivatives

This file contains the definition of symbolic derivatives and the `step` function
which collects the leaves (states) of a transition tree.

-/

/-- The symbolic derivative operation on regexes. -/
@[simp]
def derivative : RE α → TTerm (RE α) (RE α)
  | ε         => Leaf (Pred ⊥)
  | ?= _      => Leaf (Pred ⊥)
  | ?! _      => Leaf (Pred ⊥)
  | ?<= _     => Leaf (Pred ⊥)
  | ?<! _     => Leaf (Pred ⊥)
  | Pred φ    => Node (?= (Pred φ)) (Leaf ε) (Leaf (Pred ⊥))
  | l ⋓ r     => lift_binary (· ⋓ ·) (derivative l) (derivative r)
  | l ⋒ r     => lift_binary (· ⋒ ·) (derivative l) (derivative r)
  | r *       => lift_unary (· ⬝ r*) (derivative r)
  | ~ r       => lift_unary (~ ·) (derivative r)
  | l ⬝ r     =>
    Node l
    (lift_binary (· ⋓ ·) (lift_unary (· ⬝ r) (derivative l)) (derivative r))
    (lift_unary (· ⬝ r) (derivative l))
prefix:max "𝜕 " => derivative

/-- Take a single step in r with the symbolic derivative and return the list of leaves (regex states). -/
@[simp]
def step (r : RE α) : List (RE α) := leaves (𝜕 r)

@[simp]
theorem step_negation (r : RE α) :
  step (~ r) = map (~ ·) (step r) := by simp only [step, derivative, lift_unary, leaves_fmap]

@[simp]
theorem step_star (r : RE α) :
  step r* = map (· ⬝ r*) (step r) := leaves_unary (· ⬝ r*) (𝜕 r)

@[simp]
theorem step_alternation (r s : RE α) :
  step (r ⋓ s) = productWith (· ⋓ ·) (step r) (step s) := leaves_binary (· ⋓ ·) (𝜕 r) (𝜕 s)

@[simp]
theorem step_intersection (r s : RE α) :
  step (r ⋒ s) = productWith (· ⋒ ·) (step r) (step s) := leaves_binary (· ⋒ ·) (𝜕 r) (𝜕 s)

@[simp]
theorem step_concatenation (r s : RE α) :
  step (r ⬝ s) =
     productWith (· ⋓ ·) (leaves $ lift_unary (· ⬝ s) (𝜕 r)) (step s)
  ++ leaves (lift_unary (· ⬝ s) (𝜕 r)) := by
  simp only [step, derivative, leaves, leaves_binary, productWith, leaves_unary]

/-- Take n steps in r (iterate the symbolic derivative and collect the leaves). -/
@[simp]
def steps (r : RE α) : ℕ → List (RE α)
  | 0 => [r]
  | Nat.succ n => map step (steps r n) |> flatten
