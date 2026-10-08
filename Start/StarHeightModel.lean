import Mathlib

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/StarHeight/Model.lean`, family 134,
paper "Finite monoid computations and a uniform generalized star height bound".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.StarHeight*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace GeneralizedStarHeight

universe u

inductive Expression (Alphabet : Type u) : Type u
  | zero : Expression Alphabet
  | one : Expression Alphabet
  | letter : Alphabet → Expression Alphabet
  | union : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | concat : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | compl : Expression Alphabet → Expression Alphabet
  | star : Expression Alphabet → Expression Alphabet

namespace Expression

open scoped Computability

def language {Alphabet : Type u} : Expression Alphabet → Language Alphabet
  | .zero => 0
  | .one => 1
  | .letter a => {[a]}
  | .union P Q => P.language + Q.language
  | .concat P Q => P.language * Q.language
  | .compl P => P.languageᶜ
  | .star P => P.language∗

def height {Alphabet : Type u} : Expression Alphabet → ℕ
  | .zero | .one | .letter _ => 0
  | .union P Q | .concat P Q => max P.height Q.height
  | .compl P => P.height
  | .star P => 1 + P.height

end Expression

def HasHeightAtMost {Alphabet : Type u} (L : Language Alphabet) (n : ℕ) : Prop :=
  ∃ P : Expression Alphabet, P.language = L ∧ P.height ≤ n

end GeneralizedStarHeight

