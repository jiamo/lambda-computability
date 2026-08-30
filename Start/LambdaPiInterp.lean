/-
The **interpretation of `λΠ` in a model**: semantic contexts, and the relation that assigns to a
raw expression of the calculus a type, resp. a term, of a category with attributes with a universe.

`Start/LambdaPiUniv.lean` shows that the syntax of `λΠ` *is* a model: a category with attributes
whose universe is the sort `∗`, with products over the small types and codes for them.  What is
still missing for initiality is the interpretation in the other direction, into an arbitrary such
model.  This module defines it.

* `LambdaPi.Model C` — the structure a category of contexts must carry to interpret `λΠ`: a
  category with attributes `T`, coherent substitution of terms (`Cwa.ExtCoherent`), a universe
  `Un` of small types, dependent products over the small types (`Cwa.Universe.SmallPi`) with
  abstraction and application natural in the context, codes for the products
  (`Cwa.Universe.NaturalPiClosed`) and a terminal object to interpret the empty context;
* `LambdaPi.SemCtx M Γ` — a *semantic context* over the object `Γ`: the list of the types by which
  `Γ` was built, which is what reading the de Bruijn variables requires;
* `LambdaPi.SemCtx.varVal` — the term a de Bruijn index denotes in a semantic context;
* `LambdaPi.TyI`, `LambdaPi.TmI` — the interpretation relations, defined by mutual induction on the
  raw syntax: `TyI s t A` says that the expression `t` denotes the type `A` of the model, and
  `TmI s t A x` that `t` denotes the term `x` of type `A`.  Both are relations rather than
  functions because a raw expression need not denote anything; that they are nevertheless
  *functional* is proved in `Start/LambdaPiInterpFun.lean`.

The rules mirror the typing rules of `Start/LambdaPiTyping.lean`: the sort `∗` denotes the type of
codes, a term of `∗` denotes the type it names, a product denotes the dependent product over the
small type its domain names, and — this is the rule `(∗,∗)` — a product of two small types also
denotes a *code*, namely the code the universe is closed under.
-/

import Start.LambdaPiTyping
import Start.CwaSmall
import Start.CwaVar

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace LambdaPi

variable {C : Type u} [Category.{v} C]

/-- **A model of `λΠ`**: a category with attributes with a universe of small types, products over
the small types with natural abstraction and application, codes for those products, and a terminal
object.  These are exactly the pieces the rules of the calculus ask for: `(∗,∗)` needs the codes,
`(∗,□)` needs the products over the small types with an arbitrary body, and the empty context needs
the terminal object.  The naturality laws are what a *substitution* calculus needs; the syntax
satisfies them (`Start/LambdaPiUniv.lean`). -/
structure Model (C : Type u) [Category.{v} C] where
  /-- The underlying category with attributes. -/
  T : Cwa.{u, v, w} C
  /-- Substitution of terms is functorial. -/
  co : Cwa.ExtCoherent T
  /-- The universe of small types, interpreting the sort `∗`. -/
  Un : Cwa.Universe T
  /-- Dependent products over the small types, interpreting the rule `(∗,□)`. -/
  SP : Cwa.Universe.SmallPi Un
  /-- Codes for the products of two small types, interpreting the rule `(∗,∗)`. -/
  PC : Cwa.Universe.NaturalPiClosed Un SP
  /-- The object interpreting the empty context. -/
  emp : C
  /-- It is terminal, so that a substitution into the empty context is unique. -/
  empIsTerminal : IsTerminal emp
  /-- Abstraction is natural in the context. -/
  lam_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) (B : T.Ty (T.ext Γ (Un.El a)))
      (b : T.Tm (T.ext Γ (Un.El a)) B),
      Cwa.tmCast (SP.Pi_sub σ a B) (T.tmSub σ (SP.lam b))
        = SP.lam (T.tmSub (Un.extHom σ a) b)
  /-- Application is natural in the context. -/
  app_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ)) (B : T.Ty (T.ext Γ (Un.El a)))
      (f : T.Tm Γ (SP.Pi a B)),
      T.tmSub (Un.extHom σ a) (SP.app f)
        = SP.app (Cwa.tmCast (SP.Pi_sub σ a B) (T.tmSub σ f))

namespace Model

variable (M : Model.{u, v, w} C)

/-- The type of codes of the model, in a context. -/
abbrev U (Γ : C) : M.T.Ty Γ := M.Un.U Γ

/-- The decoding of a code as a type of the model. -/
abbrev El {Γ : C} (a : Cwa.Tm M.T Γ (M.U Γ)) : M.T.Ty Γ := M.Un.El a

/-- The dependent product over a small type. -/
abbrev Pi {Γ : C} (a : Cwa.Tm M.T Γ (M.U Γ)) (B : M.T.Ty (M.T.ext Γ (M.El a))) : M.T.Ty Γ :=
  M.SP.Pi a B

end Model

/-- A **semantic context** over the object `Γ`: the list of types out of which `Γ` was built by
context extension.  An object of the category carries no such list, and reading a de Bruijn
variable needs one. -/
inductive SemCtx (M : Model.{u, v, w} C) : C → Type (max u w) where
  /-- The empty semantic context, over the terminal object. -/
  | nil : SemCtx M M.emp
  /-- Extension of a semantic context by a type. -/
  | cons {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) : SemCtx M (M.T.ext Γ A)

variable {M : Model.{u, v, w} C}

/-- The pair of a type of the model and a term of it: the value of the interpretation of a term. -/
abbrev TmVal (M : Model.{u, v, w} C) (Γ : C) : Type max v w := Cwa.Val M.T Γ

/-- **What a de Bruijn variable denotes** in a semantic context: the generic term of the last type
for `0`, and the weakening of what it denotes in the shorter context for a later variable.  This
mirrors `LambdaPi.Lookup`, weakening replacing the syntactic `shift`. -/
noncomputable def SemCtx.varVal : {Γ : C} → SemCtx M Γ → ℕ → Option (TmVal M Γ)
  | _, .nil, _ => none
  | _, .cons _ A, 0 => some ⟨M.T.tySub (M.T.disp A) A, Cwa.var A⟩
  | _, .cons s A, n + 1 => (s.varVal n).map (Cwa.Val.sub (M.T.disp A))

mutual

/-- `TyI s t A` : in the semantic context `s`, the raw expression `t` denotes the type `A` of the
model.  The sort `∗` denotes the type of codes, a term of `∗` denotes the type it names, and a
product denotes the dependent product over the small type its domain names. -/
inductive TyI : {Γ : C} → SemCtx M Γ → Tm → M.T.Ty Γ → Prop where
  /-- The sort `∗` denotes the universe. -/
  | star {Γ : C} (s : SemCtx M Γ) : TyI s (Tm.sort Srt.star) (M.Un.U Γ)
  /-- A code denotes the type it names. -/
  | el {Γ : C} {s : SemCtx M Γ} {t : Tm} {c : Cwa.Tm M.T Γ (M.Un.U Γ)} :
      TmI s t (M.Un.U Γ) c → TyI s t (M.Un.El c)
  /-- The rule `(∗,□)`: a product over a small type denotes the dependent product. -/
  | pi {Γ : C} {s : SemCtx M Γ} {A B : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
      {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} :
      TmI s A (M.Un.U Γ) a → TyI (s.cons (M.Un.El a)) B B' →
      TyI s (Tm.pi A B) (M.SP.Pi a B')

/-- `TmI s t A x` : in the semantic context `s`, the raw expression `t` denotes the term `x` of
type `A` of the model. -/
inductive TmI : {Γ : C} → SemCtx M Γ → Tm → (A : M.T.Ty Γ) → Cwa.Tm M.T Γ A → Prop where
  /-- A variable denotes what the semantic context says. -/
  | var {Γ : C} {s : SemCtx M Γ} {n : ℕ} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A} :
      s.varVal n = some ⟨A, x⟩ → TmI s (Tm.var n) A x
  /-- The rule `(∗,∗)`: a product of two small types denotes the code of the product. -/
  | pi {Γ : C} {s : SemCtx M Γ} {A B : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
      {b : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) (M.Un.U (M.T.ext Γ (M.Un.El a)))} :
      TmI s A (M.Un.U Γ) a → TmI (s.cons (M.Un.El a)) B (M.Un.U _) b →
      TmI s (Tm.pi A B) (M.Un.U Γ) (M.PC.code a b)
  /-- An abstraction denotes the abstraction of the model. -/
  | lam {Γ : C} {s : SemCtx M Γ} {A b : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
      {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} {x : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) B'} :
      TmI s A (M.Un.U Γ) a → TmI (s.cons (M.Un.El a)) b B' x →
      TmI s (Tm.lam A b) (M.SP.Pi a B') (M.SP.lam x)
  /-- An application denotes the generic application substituted along the argument. -/
  | app {Γ : C} {s : SemCtx M Γ} {f g : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
      {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} {f' : Cwa.Tm M.T Γ (M.SP.Pi a B')}
      {g' : Cwa.Tm M.T Γ (M.Un.El a)} :
      TmI s f (M.SP.Pi a B') f' → TmI s g (M.Un.El a) g' →
      TmI s (Tm.app f g) (M.T.tySub g'.1 B') (M.T.tmSub g'.1 (M.SP.app f'))

end

/-- `CtxI Γ s` : the semantic context `s` interprets the syntactic context `Γ`. -/
inductive CtxI : (Γ : Ctx) → {Γ' : C} → SemCtx M Γ' → Prop where
  /-- The empty context is interpreted by the terminal object. -/
  | nil : CtxI [] SemCtx.nil
  /-- An extended context is interpreted by the extension by the interpretation of the new type. -/
  | cons {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} {A : Tm} {A' : M.T.Ty Γ'} :
      CtxI Γ s → TyI s A A' → CtxI (A :: Γ) (s.cons A')

end LambdaPi
