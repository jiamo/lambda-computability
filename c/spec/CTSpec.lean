/-
**Reference semantics for the C implementation in `c/`.**

The definitions below are copied from the church-turing Lean development, which uses Lean v4.33
and Mathlib.  Only the namespace `CT` is added, so that this file is self-contained and type-checks
on its own with `import Mathlib`.  The C code in `c/` must agree with these definitions.

Sources in the repository:
* `CT.Lambda`, `CT.Lambda.lift`, `CT.Lambda.subst` — `Start/Syntax.lean`;
* `CT.Lambda.step` — `Start/Reduction.lean` (full β-reduction, one step);
* `CT.Lambda.size` — `Start/TermSize.lean` (there `size`);
* `CT.Lambda.church` — `Start/ChurchCombinators.lean`;
* `CT.Word`, `CT.Cob`, `CT.Cob.eval` — `Start/ComplexityClasses.lean`;
* `CT.QBF`, `CT.QBF.eval` — `Start/Qbf.lean`.
-/

import Mathlib

namespace CT

/-! ### The untyped λ-calculus, with de Bruijn indices -/

inductive Lambda
  | var : ℕ → Lambda
  | app : Lambda → Lambda → Lambda
  | lam : Lambda → Lambda
  deriving DecidableEq, Repr

/-- Lifting: `lift n k t` increments all free variables in `t` that are >= `k` by `n`. -/
def Lambda.lift (n : ℕ) (k : ℕ) : Lambda → Lambda
  | Lambda.var y => if y < k then Lambda.var y else Lambda.var (y + n)
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.lift n k t₁) (Lambda.lift n k t₂)
  | Lambda.lam t => Lambda.lam (Lambda.lift n (k + 1) t)

/-- Proper substitution: `subst s x t` replaces variable `x` in `t` with `s`.
    When entering a lambda, the indices in `s` must be lifted. -/
def Lambda.subst (s : Lambda) (x : ℕ) : Lambda → Lambda
  | Lambda.var y =>
    if y = x then s
    else if y > x then Lambda.var (y - 1)
    else Lambda.var y
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.subst s x t₁) (Lambda.subst s x t₂)
  | Lambda.lam t => Lambda.lam (Lambda.subst (Lambda.lift 1 0 s) (x + 1) t)

/-- Single-step beta reduction -/
inductive Lambda.step : Lambda → Lambda → Prop
  | beta (t₁ t₂ : Lambda) : Lambda.step (Lambda.app (Lambda.lam t₁) t₂) (Lambda.subst t₂ 0 t₁)
  | app_left (t₁ t₁' t₂ : Lambda) :
      Lambda.step t₁ t₁' → Lambda.step (Lambda.app t₁ t₂) (Lambda.app t₁' t₂)
  | app_right (t₁ t₂ t₂' : Lambda) :
      Lambda.step t₂ t₂' → Lambda.step (Lambda.app t₁ t₂) (Lambda.app t₁ t₂')
  | lam (t t' : Lambda) : Lambda.step t t' → Lambda.step (Lambda.lam t) (Lambda.lam t')

/-- Syntactic size of a term: the number of syntax nodes, where a de Bruijn index `i` counts as
`i + 1`. -/
def Lambda.size : Lambda → ℕ
  | Lambda.var i => i + 1
  | Lambda.app a b => Lambda.size a + Lambda.size b + 1
  | Lambda.lam t => Lambda.size t + 1

/-- Church numeral for n -/
def Lambda.church (n : ℕ) : Lambda :=
  let f := Lambda.var 1
  let x := Lambda.var 0
  let body := (List.range n).foldl (fun t _ => Lambda.app f t) x
  Lambda.lam (Lambda.lam body)

/-! ### Cobham's class of polynomial-time functions on binary words -/

abbrev Word := List Bool

/-- Syntax for Cobham's class.  A term denotes a function `List Word → Word`; arguments are
addressed by position, and a missing argument reads as the empty word. -/
inductive Cob : Type
  | proj (i : ℕ)
  | empty
  | app (b : Bool)
  | smash
  | comp (f : Cob) (gs : List Cob)
  | bRec (g h₀ h₁ bd : Cob)
  deriving Inhabited

/-- The function denoted by a Cobham term.  In the `bRec` case the recursion runs on the first
argument, the step functions receive `(tail of the recursion argument, recursive value, other
arguments)`, and the result is truncated to the length of the bound. -/
def Cob.eval : Cob → List Word → Word
  | .proj i, args => args.getD i []
  | .empty, _ => []
  | .app b, args => b :: args.getD 0 []
  | .smash, args =>
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true
  | .comp f gs, args => f.eval (gs.attach.map (fun g => g.1.eval args))
  | .bRec g h₀ h₁ bd, args =>
      List.rec (g.eval args.tail)
        (fun b x' ih =>
          (if b then h₁.eval (x' :: ih :: args.tail) else h₀.eval (x' :: ih :: args.tail)).take
            ((bd.eval ((b :: x') :: args.tail)).length))
        (args.headD [])
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

/-! ### Quantified Boolean formulas -/

inductive QBF where
  | var (i : ℕ)
  | neg (p : QBF)
  | conj (p q : QBF)
  | disj (p q : QBF)
  | all (i : ℕ) (p : QBF)
  | ex (i : ℕ) (p : QBF)
  deriving DecidableEq, Repr, Inhabited

/-- The value of a formula under an assignment. -/
def QBF.eval (σ : ℕ → Bool) : QBF → Bool
  | .var i => σ i
  | .neg p => !QBF.eval σ p
  | .conj p q => QBF.eval σ p && QBF.eval σ q
  | .disj p q => QBF.eval σ p || QBF.eval σ q
  | .all i p => QBF.eval (Function.update σ i false) p && QBF.eval (Function.update σ i true) p
  | .ex i p => QBF.eval (Function.update σ i false) p || QBF.eval (Function.update σ i true) p

end CT
