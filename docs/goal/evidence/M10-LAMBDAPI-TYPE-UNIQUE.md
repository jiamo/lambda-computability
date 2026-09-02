# M10-LAMBDAPI-TYPE-UNIQUE

**Status:** DONE_STRONG

Module `Start/LambdaPiTypeUnique.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

`Start/LambdaPiFull.lean` records, in the comment on its `tySetoid`, that "uniqueness of sorts is
not part of the metatheory developed in the project": a type of the syntactic model is a raw term
*together with* the sort typing it, and two types are identified only when they are convertible
**and** carry the same sort.  This module supplies the missing metatheorem and removes the caveat.

## Uniqueness of types

* `LambdaPi.Lookup.det` — a de Bruijn index has at most one type in a context;
* **`LambdaPi.Typing.conv_type`** — two types of the same term are convertible, i.e. `λΠ` is a
  *functional* pure type system;
* `LambdaPi.Typing.srt_unique` — hence a term is typed by at most one sort;
* `LambdaPi.Typing.not_star_box` — no term is both a type and a kind.

The proof is a structural induction on the raw term.  Each case applies to both derivations the
inversion lemma of `Start/LambdaPiTyping.lean` for that construct, which delivers the canonical
type together with a conversion to the given one, and then compares the two canonical types:
sorts are compared outright, variables by the determinism of lookup, products and abstractions by
the induction hypothesis for the body, and applications by the injectivity of the product former
(`LambdaPi.pi_inj_left`, `LambdaPi.pi_inj_right`), itself a consequence of the Church–Rosser
theorem.

## The consequence for the syntactic model

* `LambdaPiFull.srt_eq_of_conv` — convertible types of the syntactic model carry the same sort:
  both reduce to a common term, which subject reduction (`LambdaPi.Typing.red`) types by each of
  the two sorts;
* **`LambdaPiFull.tyMk_eq_of_conv`** — hence convertible types of the syntactic model are equal.

So the sort recorded by `LambdaPiFull.TyOf` is redundant data, and an equality of types of the
syntactic model may be proved by a conversion alone.

## Gates

* `lake build` — zero errors and zero warnings.
* `python3 scripts/goal_state.py validate`.
* `python3 scripts/check_closure.py` — all modules in the import closure and registered.
* No `sorry` and no `admit` anywhere under `Start/`.
