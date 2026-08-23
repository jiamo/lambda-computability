# M9-SYSTEMT-ADEQUACY

**Status:** DONE_STRONG

Modules `Start/SystemTConfluence.lean` and `Start/SystemTDenot.lean`, both imported by
`Start.lean`.  They build without `sorry`; `#print axioms` on the headline theorems reports only
`propext`, `Classical.choice`, `Quot.sound`.

Together with the strong normalization and canonicity results already in the repository, these
files close the converse direction of the denotational semantics of Gödel's System T: not only
does convertibility imply equality of denotations (soundness), but at the base type equality of
denotations implies convertibility and observational equivalence (adequacy).

## Confluence — `Start/SystemTConfluence.lean`

Congruence lemmas for the reflexive–transitive closure `reduces` (`reduces_appL`, `reduces_appR`,
`reduces_app`, `reduces_lam`, `reduces_recL/M/R`, `reduces_natrec`), the substitution lemmas
`lift_subst_le`, `step_lift` and `reduces_subst_arg`, then

* `local_confluence` — one-step diamond up to `reduces`;
* `confluence` — Newman's lemma for strongly normalizing terms;
* `confluence_of_typing` — hence for every typable term;
* `isNormal_num`, `num_injective`, `eq_of_reduces_num`, `eq_of_reduces_num_of_typing` — a typable
  term reduces to at most one numeral.

## Denotational semantics — `Start/SystemTDenot.lean`

`tyDen` interprets types as sets (`nat` as `ℕ`, `arrow` as the full function space), `Env Γ` is the
recursive product of the interpretations of a context, `Der` records typing derivations as data,
and `eval` interprets a derivation.  Because the calculus is Curry-style, typing derivations are
not unique; `denot` therefore evaluates the canonically chosen derivation `derOf h`, and
`eval_irrel_nat` proves that at the base type the choice does not matter.

The logical relation `LR` (with `LR.expand`, `lr_natrec`, `lr_substEnv`, `lr_closed`) gives

* **`adequacy`** — a closed term of type `nat` reduces to the numeral of its denotation;
* `reduces_num_iff_denot`, `denot_eq_iff_joins` — equality of denotations at base type is exactly
  reduction to a common numeral;
* `ObsEq`, **`obsEq_of_denot_eq`** — equal denotations imply observational equivalence at every
  type;
* `denot_eq_of_obsEq_nat`, **`denot_eq_iff_obsEq_nat`** — at base type the three notions coincide.

## Boundary

Full abstraction at higher types is not claimed, and neither is invariance of the higher-type
denotation under reduction; both are documented in the module docstring of
`Start/SystemTDenot.lean`.
