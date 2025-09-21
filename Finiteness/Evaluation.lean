import Regex.Derives
import Regex.Correctness
import Finiteness.SymbolicDerivative

open TTerm RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Evaluation

This file contains the definition of the `evaluation` function to evaluate
transition regexes with concrete locations.

We then prove the equivalence between the symbolic and classical definitions.

-/

/- The evaluation of a transition regex r for a given location x. -/
@[simp]
def evaluation (x : Loc σ) (r : TTerm (RE α) β) : β :=
  match r with
  | Leaf r => r
  | Node cond f g =>
    if null cond x then
      evaluation x f
    else
      evaluation x g
notation f "[" l "]" => evaluation l f

-- useful properties of evaluation
theorem liftU (op : β → β) (f : TTerm (RE α) β) (x : Loc σ) :
  (lift_unary op f) [x] = op (f [x]) :=
  match f with
  | Leaf r => rfl
  | Node p ff g => by
    match g1:null p x with
    | true  =>
      simp only [evaluation, g1, lift_unary, fmap]
      exact liftU op ff x -- inductive hypothesis
    | false =>
      simp only [evaluation, g1, lift_unary, fmap]
      exact liftU op g x  -- inductive hypothesis

-- evaluation is a homomorphism
theorem liftB (op : β → β → β) (f g : TTerm (RE α) β) (x : Loc σ) :
  (lift_binary op f g) [x] = (op (f [x]) (g [x])) :=
  match f, g with
  | Leaf f1, Leaf g1 => rfl
  | Node p ff gg, Leaf g1 => by
    match g2:null p x with
    | true  =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, join]
      exact liftB op ff (Leaf g1) x -- inductive hypothesis
    | false =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, join]
      exact liftB op gg (Leaf g1) x -- inductive hypothesis
  | Leaf f1, Node p ff gg => by
    match g2:null p x with
    | true  =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, TTerm.pure, lift_unary, join]
      exact liftU (op f1) ff x
    | false =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, TTerm.pure, lift_unary, join]
      exact liftU (op f1) gg x
  | Node p ff gg, Node p1 ff1 gg1 => by
    match g2:null p x with
    | true  =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, lift_unary, join]
      exact liftB op ff (Node p1 ff1 gg1) x -- inductive hypothesis
    | false =>
      simp only [evaluation, g2, lift_binary, fmap, TTerm.bind, lift_unary, join]
      exact liftB op gg (Node p1 ff1 gg1) x -- inductive hypothesis

/- The equivalence between the classical definition of location based derivatives
   and the symbolic definition. -/
theorem equivalence (r : RE α) (x : Loc σ) :
  der r x = (𝜕 r) [x] :=
  match r with
  | ε | ?=_ | ?!_ | ?<=_ | ?<!_ => by simp only [lookaround_height, der, derivative, evaluation]
  | Pred φ    => by
    match x with
    | (_, []) => simp only [lookaround_height, der, derivative, evaluation, existsMatch, null]; rfl
    | (a, y::ys) =>
      simp
      by_cases h1 : y ⊨ φ
      . simp only [modelsEBA] at h1; simp only [h1, ↓reduceIte]
        split_ifs with h2
        . rfl
        . cases ys; simp only [existsMatch, null, not_true_eq_false] at h2
          simp only [existsMatch, null, lookaround_height, der, Bool.true_or, not_true_eq_false] at h2
      . simp at h1; simp_rw[h1]
        simp only [Bool.false_eq_true, ↓reduceIte, right_eq_ite_iff,
        reduceCtorEq, imp_false]
        rw[derives_to_existsMatch]
        simp; intro ⟨s,u,v⟩ h2 eq eq1
        subst eq eq1; rw[derives_Bot] at h2; contradiction
  | l ⋓ r     => by
    simp only [lookaround_height, der]
    simp only [equivalence l x, equivalence r x, derivative] -- inductive hypothesis
    exact Eq.symm $ liftB Alternation (derivative l) (derivative r) x
  | l ⋒ r     => by
    simp only [lookaround_height, der]
    simp only [equivalence l x, equivalence r x, derivative] -- inductive hypothesis
    exact Eq.symm $ liftB Intersection (derivative l) (derivative r) x
  | .Star r   => by
    simp only [lookaround_height, der, derivative]
    rw[equivalence r x] -- inductive hypothesis
    exact Eq.symm $ liftU (· ⬝ r*) (derivative r) x
  | ~ r       => by
    simp only [lookaround_height, der, derivative]
    rw[equivalence r x] -- inductive hypothesis
    exact Eq.symm $ liftU Negation (derivative r) x
  | l ⬝ r     => by
    unfold der
    by_cases h : null l x
    . simp only [lookaround_height, derivative, evaluation]
      simp only [h, ↓reduceIte, equivalence l x, equivalence r x] -- inductive hypothesis
      rw[←(liftU (· ⬝ r) (derivative l) x),
         ←(liftB Alternation ((lift_unary (· ⬝ r) (derivative l))) (derivative r) x)]
    . simp only [lookaround_height, derivative, evaluation, h]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw[equivalence l x] -- inductive hypothesis
      exact (liftU (· ⬝ r) (derivative l) x).symm
