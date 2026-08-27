# M9-LAMBDAPI-SN

**Status:** DONE_STRONG

Modules `Start/LambdaPiUnique.lean`, `Start/LambdaPiSkeleton.lean`, `Start/LambdaPiSimple.lean`,
`Start/LambdaPiSN.lean`, `Start/LambdaPiConsistent.lean`, `Start/LambdaPiNormalize.lean` and
`Start/LambdaPiInfer.lean`, all imported by `Start.lean`.  They
build without `sorry`, and the headline theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`.

`Start/LambdaPi.lean` and `Start/LambdaPiTyping.lean` develop the syntax of the dependently typed
calculus `λΠ`, the Church–Rosser theorem and the metatheory of the typing judgement up to subject
reduction.  This task adds what those files stop short of: the normalization theorem for the
calculus and its logical consequence.

The proof is the one of Harper, Honsell and Plotkin: the *dependency* of a `λΠ` type is forgotten
by mapping it to a **simple type**, its skeleton, in which `Π x:A. B` becomes `A° → B°`; a
dependent derivation erases to a simply typed derivation of the same raw term; and the simply
typed calculus is normalized by Tait's method of reducibility.

## Uniqueness of types and the stratification

`Start/LambdaPiUnique.lean`:

* `LambdaPi.Lookup.det` — a variable has at most one type in a context;
* `LambdaPi.Typing.unique` — **uniqueness of types**: two types of one term in one context are
  convertible;
* `LambdaPi.not_typing_box` — the top sort `□` is not a term of the calculus;
* `LambdaPi.IsKind`, `IsType`, `IsObject` — the three levels of `λΠ`, with
  `LambdaPi.not_isType_isKind`, `not_isObject_isKind`, `not_isObject_isType` showing that they are
  mutually exclusive, and `LambdaPi.Typing.level` that every typable term lies on one of them.

## The skeleton of a type

`Start/LambdaPiSkeleton.lean`:

* `LambdaPi.STy`, `LambdaPi.skel` — simple types and the skeleton of a term, with its behaviour
  under renaming and substitution (`skel_rename`, `skel_shift`, `skel_subst`, `skel_inst`);
* `LambdaPi.IsKindSyn` — the syntactic shape of a kind, with `isKindSyn_of_isKind` and
  `not_isKindSyn_of_typing_star`: a kind has that shape and a type never does;
* `LambdaPi.TypeLevel` and its inversion lemmas — the subterms in type position of a type-level
  term are again type-level;
* `LambdaPi.skel_irrel` — **the skeleton only sees the type variables**: two skeleton contexts
  agreeing at the positions that declare a kind give a type-level term the same skeleton.  This is
  the formal content of the stratification, and it is what makes the skeleton invariant under
  reduction: `LambdaPi.skel_step`, `skel_red` and **`LambdaPi.skel_conv`**.

## Erasure to a simply typed derivation

`Start/LambdaPiSimple.lean`:

* `LambdaPi.STyping` — simple typing of the *raw* terms of `λΠ`, in which the sorts and the
  products are constants of the base type and the annotation of an abstraction is itself typed, so
  that a derivation bounds the whole term;
* `LambdaPi.skelCtx`, `LambdaPi.Lookup.skel_eq` — the skeleton of a context;
* **`LambdaPi.Typing.styping`** — erasure: `Γ ⊢ t : A` implies `Γ° ⊢ t : A°`.  The application
  case is where `skel_irrel` is needed (the skeleton of `B[a]` must not depend on `a`), and the
  conversion case is where `skel_conv` is.

## Reducibility and strong normalization

`Start/LambdaPiSN.lean`:

* `LambdaPi.SN` — strong normalization, `Acc` of the converse of `LambdaPi.Step`; the reduction of
  `λΠ` also reduces inside abstraction annotations and inside products, so `sn_pi` and `sn_lam`
  are proved by a double `Acc` induction;
* `LambdaPi.step_rename_inv` — **a renaming reflects reduction**: every step out of `rename ρ t`
  is the renaming of a step out of `t`.  No injectivity of `ρ` is needed, and `LambdaPi.sn_rename`
  follows;
* `LambdaPi.Reducible` — Tait's predicate in **Kripke form**, quantifying at an arrow type over
  all renamings of the function; this is what makes `LambdaPi.Reducible.rename` provable, and that
  stability is needed because substituting under a binder shifts the substituted terms;
* `LambdaPi.cr` — the three candidate conditions CR1, CR2, CR3, proved simultaneously by induction
  on the simple type;
* `LambdaPi.red_lam_app` — the abstraction lemma, by a threefold induction on the strong
  normalization of the annotation, of the body and of the argument;
* `LambdaPi.STyping.reducible` — the fundamental lemma, and `LambdaPi.sn_of_styping`;
* **`LambdaPi.Typing.sn`** — *in a well-formed context every term typable in `λΠ` is strongly
  normalizing*, with `LambdaPi.Typing.hasNormalForm`: every typable term reduces to a normal form.

## Consistency

`Start/LambdaPiConsistent.lean`:

* `LambdaPi.SortCtx` — a context all of whose declarations are sorts;
* `LambdaPi.not_typing_normal_app` — in such a context no normal application is typable: the head
  would be a variable declared with a sort, and a sort is not a product;
* **`LambdaPi.not_typing_var_zero`** — *consistency*: in the context declaring `α : ∗` no term has
  type `α`.  The inhabitant would reduce to a normal form of the same type, and none of the five
  shapes of a normal term can have an atomic type;
* `LambdaPi.not_typing_pi_star_var` — for comparison, `Π α:∗. α` is not a type of `λΠ` at all: the
  product rule only allows `∗`-typed domains, so the calculus has no quantification over types.
  This is why consistency is stated for a type variable rather than for the polymorphic empty
  type, as it would be in System F.

## Normal forms and decidability

`Start/LambdaPiNormalize.lean` turns termination and confluence into an algorithm:

* `LambdaPi.nf_unique` — a term has at most one normal form, and
  `LambdaPi.conv_iff_normalForm_eq` — two terms with normal forms are convertible exactly when
  those normal forms are equal;
* `LambdaPi.stepFn` — a computable reduction strategy, sound (`LambdaPi.stepFn_sound`) and stuck
  only at a normal term (`LambdaPi.normal_of_stepFn_none`);
* `LambdaPi.nf` — the normal form of a strongly normalizing term, computed by iterating the
  strategy the number of times extracted from strong normalization, with `LambdaPi.nf_spec`;
* **`LambdaPi.decidableConv`** — conversion of strongly normalizing terms is decidable, hence
  `LambdaPi.Typing.decidableConv` for terms typable in a well-formed context.

`Start/LambdaPiInfer.lean` decides the judgement itself.  The algorithm is written as a Lean
function that is *correct by construction*: it does not return a type but a type **together with a
derivation**, so soundness is its type rather than a theorem.

* `LambdaPi.lookupTy`, `LambdaPi.checkSort`, `LambdaPi.inferApp`, `LambdaPi.inferAppOf` — the
  steps of the algorithm: the declared type of a variable, the check that a term is a type or a
  kind, and the application rule, which normalizes the type of the function part to expose a
  product and compares the type of the argument with its domain;
* **`LambdaPi.infer`** — type inference, `Γ ⊢ t : ?`;
* **`LambdaPi.infer_isSome`** — completeness: a typable term is always inferred;
* **`LambdaPi.decidableTypable`** and **`LambdaPi.decidableTyping`** — typability and type
  checking are decidable.
* **`LambdaPi.checkWf`** and **`LambdaPi.decidableWf`** — the same algorithm run down a context
  decides whether that context is well formed, so no hypothesis has to be assumed to run the
  type checker.
