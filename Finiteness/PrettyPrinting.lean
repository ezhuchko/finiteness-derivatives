import Regex.Definitions
import Finiteness.Simplifications

open TTerm String RE BA List

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

instance : ToString (BA Char) where
  toString := toStringBA where
    toStringBA : BA Char → String
    | atom a   => a.repr
    | top      => "⊤"
    | bot      => "⊥"
    | .and a b => toStringBA a ++ " ⋓ " ++ toStringBA b
    | .or a b  => toStringBA a ++ " ⋒ " ++ toStringBA b
    | .not a   => "¬ " ++ toStringBA a

instance [ToString α] : ToString (RE α) where
  toString := toStringRE where
    toStringRE : RE α → String
    | ?= r    => "(?= " ++ toStringRE r ++ ")"
    | ?! r    => "(?! " ++ toStringRE r ++ ")"
    | ?<= r   => "(?<=" ++ toStringRE r ++ ")"
    | ?<! r   => "(?<!" ++ toStringRE r ++ ")"
    | ε       => "ε"
    | Pred a  => toString a
    | r1 ⋓ r2 => "(" ++ toStringRE r1 ++ " + " ++ toStringRE r2 ++ ")"
    | r1 ⋒ r2 => "(" ++ toStringRE r1 ++ " & " ++ toStringRE r2 ++ ")"
    | r1 ⬝ r2 => "(" ++ toStringRE r1 ++ "⬝" ++ toStringRE r2 ++ ")"
    | ~ r     => "~" ++ toStringRE r
    | r *     => toStringRE r ++ "*"

def addBranch (empty : Bool) (l : (String × List String)) : List String :=
  match l with
  | (_,[]) => []
  | (n,x::xs) =>
    let header := s!"+--{n}--";
    (header ++ x) :: xs.map ((if empty then " " else "|") ++ String.replicate (header.length - 1) ' ' ++ ·)

def ppTree (head : String) (l : List (String × List String)) : List String :=
  match l with
  | [] => [head]
  | x::xs => head :: "|" :: List.flatten ((x::xs).dropLast.map (addBranch false)) ++ addBranch true (x::xs).getLast!

def ppTreeNameless (head : String) (l : List (List String)) : List String :=
  ppTree head (l.map ("", ·))

def ppRE (r : RE (BA Char)) : List String :=
  match r with
  | ?= r    => ppTreeNameless "?= " [ppRE r]
  | ?! r    => ppTreeNameless "?! " [ppRE r]
  | ?<= r   => ppTreeNameless "?<=" [ppRE r]
  | ?<! r   => ppTreeNameless "?<!" [ppRE r]
  | ε       => ppTreeNameless "ε" []
  | Pred a  => ppTreeNameless (toString a) []
  | r1 ⋓ r2 => ppTree "+" [("l",ppRE r1), ("r",ppRE r2)]
  | r1 ⋒ r2 => ppTree "&" [("l",ppRE r1), ("r",ppRE r2)]
  | r1 ⬝ r2 => ppTreeNameless "·" [ppRE r1, ppRE r2]
  | ~ r     => ppTreeNameless "~" [ppRE r]
  | r *     => ppTreeNameless "*" [ppRE r]

def ppTR' : TTerm (RE (BA Char)) (RE (BA Char)) → List String
  | Leaf r     => [toString r]
  | Node c f g => ppTree ("ite(" ++ toString c ++ ")") [("fst", ppTR' f), ("snd", ppTR' g)]

-- Just concat the result
def ppTR (r : TTerm (RE (BA Char)) (RE (BA Char))) : IO Unit :=
  -- "\n" is the separator string
  IO.print $ intercalate "\n" $ ppTR' r

-- for printing lists of leaves
def ppLeaves [ToString A] (rs : List A) : IO Unit :=
  IO.print $ intercalate "\n" $ map toString rs

def ppLeavesL [ToString A] (rs : List (List A)) : IO Unit :=
  IO.print $ intercalate "\n" $ map (intercalate ", " ∘ map toString) rs

def a := Pred (atom 'a')
def b := Pred (atom 'b')
def aba := a ⬝ b ⬝ a
def aOrb := (a ⋓ (b ⋓ (Pred ⊥)))
def lka := ?= (Pred (atom 'a'))

#eval toString $ step aba
#eval toString $ step_with_simp aba
#eval toString $ step_with_simp' aba

-- #eval ppLeaves $ pieces (Pred (atom 'a') ⬝ Pred ⊥)
#eval ppTR $ derivative (a ⬝ b)

-- example: global state space of (a ⋓ b)
-- symbolic derivative of (a ⋓ b)
#eval ppTR $ derivative (a ⋓ b)
-- overaprox of the state space of (a ⋓ b) at lk height = 0
#eval ppLeaves $ ⊕ (pieces (a ⋓ b))

#eval ppTR $ derivative ((?=a)⬝a)

#eval ppTR $ derivative (?=a⬝(?=b))

#eval ppTR $ derivative (ε ⋓ ε)
#eval ppTR $ derivative (ε ⋓ Pred ⊥)
#eval ppTR $ derivative (Pred ⊥ ⋓ ε )
#eval ppTR $ derivative (Pred ⊥ ⋓ Pred ⊥)
-- #eval allPaths (𝜕 (a ⋓ b))

#eval ppLeaves $ steps (a* ⬝ b) 2
