# Three representations of the untyped λ-calculus, and why they agree

This note accompanies `Start/Representation.lean`.  It explains, informally, how the three
syntactic representations of the untyped λ-calculus that appear in or around this development are
related, and exactly which statements in the Lean sources justify each link.

The three representations are:

1. **De Bruijn** — `Lambda` in `Start/Syntax.lean`, the representation used everywhere in this
   library.  A term is `var i`, `app s t` or `lam u`; *every* variable is a numeric index, and an
   index `i` under `d` binders is free when `i ≥ d`.
2. **Locally nameless** — `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var` from
   [`cslib`](https://github.com/leanprover/cslib).  *Bound* variables are de Bruijn indices
   (`bvar i`) but *free* variables are atoms (`fvar a`).  A term with no dangling `bvar` is
   *locally closed* (`LC`); reduction is only defined on locally closed terms, and abstraction
   rules are quantified cofinitely over fresh atoms.
3. **Binary λ-calculus (BLC)** — Tromp's bit encoding, `Lambda.bits` and `Lambda.isBLC` in
   `Start/BLC.lean`, where `lam u ↦ 00 · u`, `app s t ↦ 01 · s · t` and `var i ↦ 1^{i+1} 0`.

## 1 → 3: BLC (already in the library)

`Start/BLC.lean` proves that `Lambda.bits` is injective with decidable image, packaged as

```lean
Lambda.bitsEquiv : Lambda ≃ {bs : List Bool // isBLC bs = true}
```

This leg is a plain bijection of syntax: BLC is a *serialisation* of the de Bruijn syntax tree, so
nothing about substitution or reduction has to be checked — reduction on bit strings is *defined*
by transport.

## 1 ↔ 2: de Bruijn ↔ locally nameless

This is the substance of `Start/Representation.lean`, and the only genuinely non-trivial link,
because the two representations disagree about what a *free* variable is.

### The idea: free indices are de Bruijn *levels*

The usual way to translate is to carry an environment mapping each free index to a name.  We avoid
that.  Fix an ambient context of `D` binders and agree that the free index `j` (counted from the
innermost ambient binder outwards) denotes the atom `D - 1 - j`.  That is: free indices are read
as de Bruijn **levels** rather than indices.  Thus

```lean
toLN D d (var i) = if i < d then bvar i else fvar (D - 1 - (i - d))
toLN D d (app a b) = app (toLN D d a) (toLN D d b)
toLN D d (lam u)   = abs (toLN D (d+1) u)
```

where `d` counts the binders of the term itself, and `ofLN` inverts this.  Two things make levels
the right choice:

* the translation of a term is **stable under going under a binder** — a level does not shift, so
  no renaming is needed when `d` increases; and
* the atom `D` is **canonically fresh** for every term read in a context of size `D`
  (`Lambda.fv_toLN`).  This matters because `cslib`'s abstraction rules are of the form "for all
  atoms outside some finite set `xs`", and to *use* such a rule one must produce a fresh atom and
  then rename.  Having a distinguished fresh atom makes the renaming a one-liner.

`Lambda.ofLN_toLN` and `Lambda.toLN_ofLN` prove the two directions inverse — the first for terms
with `freeMax t ≤ d + D`, the second for terms locally closed at `d` with all atoms `< D`.
Specialised to `D = 0` this is a bijection of closed terms,

```lean
Lambda.closedEquiv : {t : Lambda // freeMax t = 0} ≃ {M : LNTerm // M.LC ∧ M.fv = ∅}
```

### Substitution commutes with the translation

The key computational lemma is

```lean
Lambda.toLN_subst_zero : toLN D 0 (Lambda.subst s 0 t) = (toLN D 1 t) ^ (toLN D 0 s)
```

i.e. de Bruijn substitution of `s` for index `0` is exactly `cslib`'s *opening* of the body with
the translation of `s`.  It is proved from a general form `Lambda.toLN_subst`, which in turn needs
`Lambda.toLN_lift`: the de Bruijn `lift` is invisible on the locally nameless side, because levels
do not move when a binder is added.  This is precisely the "substitution commutation" that makes
the whole bridge work, and it is where the level-based translation pays off — with an index-based
translation the lifting lemma would need a renaming of atoms.

### The two reduction relations are the same relation

* **Forward** (`Lambda.step_toLN`): if `t ⟶β t'` then `toLN D 0 t ⭢βᶠ toLN D 0 t'`.  The β-case is
  the substitution lemma above plus the local-closure side conditions
  (`Lambda.lc_toLN`); the `lam` case must produce a `cslib` `ξ`-derivation, which quantifies over
  cofinitely many atoms — we prove it for the canonical atom `D` and rename with
  `Term.FullBeta.redex_subst_cong`.
* **Backward** (`Lambda.reflect_step`): if `toLN D 0 t ⭢βᶠ N` then `N = toLN D 0 t'` for some
  `t'` with `t ⟶β t'`.  Here the induction is on the *de Bruijn* term, with inversion on the
  `cslib` derivation; under an abstraction one instantiates the cofinite quantifier at a fresh
  atom, renames it to `D`, applies the induction hypothesis in context `D+1`, and recovers the
  body with `Term.open_injective`.

Both extend to the reflexive-transitive closures (`Lambda.reduces_toLN`,
`Lambda.reflect_reduces`).  Note that reflection is what makes this an equivalence rather than a
mere simulation: the image of the translation is *closed under `cslib` reduction*, so no `cslib`
term reachable from a translated term falls outside the correspondence.

### Confluence, corroborated in both directions

Because the correspondence is an isomorphism of reduction systems, confluence transfers both ways,
and we prove both transports:

```lean
Lambda.confluence_of_cslib      : Lambda.Confluence          -- from cslib's confluent_fullBeta
Lambda.cslib_confluence_of_lambda                            -- from our confluence_theorem
```

This library already proves `Lambda.confluence_theorem` directly, by the Tait–Martin-Löf parallel
reduction argument.  `cslib` proves `Term.confluent_fullBeta` by its own route.  The two proofs are
independent, and after the bridge each one implies the other, so the two formalizations check each
other on their headline theorem.

## Putting the three together

Composing the closed-term bijection with the BLC bijection gives

```lean
Lambda.closedBitsEquiv :
  {M : LNTerm // M.LC ∧ M.fv = ∅} ≃ {bs : {bs // isBLC bs} // freeMax (bitsEquiv.symm bs) = 0}
```

so the closed terms of the three representations are in bijection, and — by the reduction lemmas
above — that bijection carries β-reduction to β-reduction.  Concretely this means the
Kolmogorov-complexity and randomness development of this library, which is stated over BLC bit
strings and de Bruijn terms, could equally have been stated over `cslib`'s locally nameless terms.

## What is *not* claimed

* The bridge is for `Term ℕ` (natural numbers as atoms); `cslib`'s theory is generic in the atom
  type and the generic statement is not given here.
* Only β-reduction is bridged: η, the typed calculi, and `cslib`'s other languages are untouched.
* `cslib_confluence_of_lambda` assumes local closure and an explicit bound `D` on the atoms; the
  bound is not a real restriction (free-variable sets are finite) but it is carried in the
  statement rather than eliminated.
