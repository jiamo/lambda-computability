# M7-STLC-SN

**Status:** DONE_STRONG

Module `Start/SimpleTypes.lean`, imported by `Start.lean`.  It puts a type discipline on the very
same de Bruijn syntax `Lambda` that carries the untyped metatheory, so confluence, the reduction
relation and the normal-form vocabulary of the rest of the development apply verbatim.

## Definitions

* `Lambda.Ty` — simple types over one base type.
* `Lambda.Typing Γ t A` — the typing relation, the context listing the types of the free de
  Bruijn indices.
* `Lambda.SN t` — strong normalization as well-foundedness of `Lambda.step` above `t`.
* `Lambda.Red A t` — Tait's reducibility predicate, defined by recursion on the type.

## Theorems

* `Lambda.cr`, `Lambda.cr1`, `Lambda.cr2`, `Lambda.cr3` — the three reducibility candidate
  conditions.
* `Lambda.red_lam` — abstraction preserves reducibility.
* `Lambda.red_substEnv` — the fundamental lemma: a typed term is reducible under every reducible
  substitution.
* `Lambda.sn_of_typing` — **strong normalization**: every typable term is strongly normalizing.
* `Lambda.hasNormalForm_of_typing` — hence every typable term has a normal form.
* `Lambda.not_typing_omega` — the looping term `omega = (λx. x x)(λx. x x)` is untypable, which
  is the expected boundary: typing buys termination at the price of losing the fixed point
  combinators, so the simply typed calculus is *not* Turing complete.
* `Lambda.typing_I` — non-vacuity: the identity is typable at every type `A → A`.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` reports only the standard axioms.
