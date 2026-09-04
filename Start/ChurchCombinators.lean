/-
Church numerals, the standard combinators, and λ-computability of a partial function.

These are the *terms* the rest of the library computes with; they were previously mixed into
`Start/Reduction.lean`, which is now exclusively the confluence development (single-step,
parallel and multi-step reduction, the diamond property, the strip lemma and Church–Rosser).
Splitting them apart keeps the confluence proof free of any datatype encoding, and gives the
encodings a module of their own that other tracks can import.
-/

import Start.Reduction
import Mathlib.Computability.Partrec

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

------------------------------------------------------------------------
-- Church numerals
------------------------------------------------------------------------

/-- Church numeral for n -/
def Lambda.church (n : ℕ) : Lambda :=
  let f := Lambda.var 1
  let x := Lambda.var 0
  let body := (List.range n).foldl (fun t _ => Lambda.app f t) x
  Lambda.lam (Lambda.lam body)

------------------------------------------------------------------------
-- Computability definition
------------------------------------------------------------------------

/-- A partial function f : ℕ →. ℕ is Lambda-computable if there exists a term F such that
    for all n, if f(n) is defined and equals m, then F (church n) reduces to (church m). -/
def LambdaComputable (f : ℕ →. ℕ) : Prop :=
  ∃ F : Lambda, ∀ n m, f n = Part.some m ↔ Lambda.reduces (Lambda.app F (Lambda.church n))
      (Lambda.church m)

------------------------------------------------------------------------
-- Standard combinators
------------------------------------------------------------------------

def Lambda.I : Lambda := Lambda.lam (Lambda.var 0)
def Lambda.K : Lambda := Lambda.lam (Lambda.lam (Lambda.var 1))
def Lambda.S : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 0))
      (Lambda.app (Lambda.var 1) (Lambda.var 0)))))

def Lambda.pair : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.var 2))
      (Lambda.var 1))))
def Lambda.fst : Lambda :=
  Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.lam (Lambda.var 1))))
def Lambda.snd : Lambda :=
  Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.lam (Lambda.var 0))))

def Lambda.succ : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.app (Lambda.var
      2) (Lambda.var 1)) (Lambda.var 0)))))

/-- Y combinator: λ f. (λ x. f (x x)) (λ x. f (x x)) -/
def Lambda.fix : Lambda :=
  let omega := Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 0) (Lambda.var 0)))
  Lambda.lam (Lambda.app omega omega)

end
