# M9-REPRESENTATION-BRIDGE

**Status:** DONE_STRONG

Module `Start/Representation.lean`, imported by `Start.lean`.  It builds without `sorry`, and its
results depend only on `propext`, `Classical.choice`, `Quot.sound`.

The file connects the de Bruijn representation of the untyped λ-calculus used throughout this
development (`Lambda`, `Start/Syntax.lean`) with the *locally nameless* representation of
[`cslib`](https://github.com/leanprover/cslib)
(`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`), where bound variables are de Bruijn indices
and free variables are atoms.  `cslib` is now a Lake dependency of this project, pinned at its
`v4.33.0` tag.

## The translation (first exit criterion)

The translation is *canonical*: no environment of names is threaded through it.  A term is read
inside an ambient context of `D` binders, and its free de Bruijn indices are interpreted as de
Bruijn **levels**, i.e. as the atoms `0, …, D-1`, with the innermost ambient binder the atom
`D-1`.

* `Lambda.toLN D d t` — de Bruijn to locally nameless, for `t` sitting under `d` binders of its
  own inside the ambient context of size `D`.
* `Lambda.ofLN D d M` — the converse translation.
* `Lambda.ofLN_toLN` and `Lambda.toLN_ofLN` — the two are mutually inverse, on de Bruijn terms
  whose free indices fit (`freeMax t ≤ d + D`) and on locally nameless terms that are locally
  closed at `d` with atoms below `D`.
* `Lambda.lcAt_toLN`, `Lambda.lc_toLN`, `Lambda.fv_toLN`, `Lambda.freeMax_ofLN` — the translations
  respect `cslib`'s local closure predicate and the free-variable bounds on both sides.
* `Lambda.closedEquiv : {t : Lambda // freeMax t = 0} ≃ {M : LNTerm // M.LC ∧ M.fv = ∅}` — the
  bijection between closed terms of the two representations.

Choosing levels rather than names is what makes the atom `D` *canonically fresh* for a term read
in a context of size `D`, and that is what makes `cslib`'s cofinitely quantified `ξ`-rule for
abstractions usable in both directions.

## Substitution and reduction (second exit criterion)

* `Lambda.toLN_lift`, `Lambda.toLN_subst`, `Lambda.toLN_subst_zero` — the translation intertwines
  this library's `lift`/`subst` with `cslib`'s opening and substitution; in particular
  `toLN D 0 (t.subst 0 s) = (toLN D 1 t) ^ toLN D 0 s`.
* `Lambda.toLN_openRec_fvar`, `Lambda.toLN_open_fvar` — opening a translated body with the fresh
  atom `D` is the translation in the enlarged context: `(toLN D 1 u) ^ fvar D = toLN (D+1) 0 u`.
* `Lambda.step_toLN` — **forward simulation**: `t ⟶β t'` implies
  `toLN D 0 t ⭢βᶠ toLN D 0 t'` (for `freeMax t ≤ D`).
* `Lambda.reflect_step` — **reflection**: every `cslib` step out of a translated term is itself a
  translation, `toLN D 0 t ⭢βᶠ N → ∃ t', toLN D 0 t' = N ∧ t ⟶β t'`.  The abstraction case picks
  a fresh atom, renames it to `D` with `Term.FullBeta.redex_subst_cong`, and concludes with
  `Term.open_injective`.
* `Lambda.reduces_toLN` and `Lambda.reflect_reduces` — the multi-step versions, for
  `Lambda.reduces` and `↠βᶠ`.

Together these say the two reduction relations are *the same relation* read through the
bijection, not merely that each simulates the other.

## Confluence, both ways (third exit criterion)

* `Lambda.confluence_of_cslib : Lambda.Confluence` — this library's Church–Rosser theorem obtained
  from `cslib`'s `Term.confluent_fullBeta` across the bridge.  It is an *independent* proof of
  `Lambda.confluence_theorem` (which is proved here directly, by parallel reduction).
* `Lambda.cslib_confluence_of_lambda` — the transport in the other direction: confluence of
  `cslib`'s `↠βᶠ` on locally closed terms, derived from `Lambda.confluence_theorem`.

So the two formalizations corroborate each other on their headline theorem.

## Three representations (fourth exit criterion)

`Start/BLC.lean` already provides `Lambda.bitsEquiv : Lambda ≃ {bs // isBLC bs}`, the binary
λ-calculus leg.  Composing it with `closedEquiv` gives

```
Lambda.closedBitsEquiv :
  {M : LNTerm // M.LC ∧ M.fv = ∅} ≃ {bs : {bs // isBLC bs} // freeMax (bitsEquiv.symm bs) = 0}
```

so the de Bruijn, locally nameless and BLC representations of closed terms are all in bijection.
The prose account is `docs/representations.md`.

## Boundary

* The bridge is stated for `Term ℕ`, i.e. natural-number atoms.  `cslib`'s development is generic
  in the atom type (subject to `HasFresh`); nothing here depends on ℕ beyond the arithmetic of
  levels, but the generic version is not stated.
* `cslib_confluence_of_lambda` is restricted to locally closed terms with atoms bounded by some
  `D` — the second restriction is harmless (`fv` is finite) but is carried explicitly rather than
  eliminated.
* Only β is treated.  `cslib`'s η and typed developments are not bridged.
