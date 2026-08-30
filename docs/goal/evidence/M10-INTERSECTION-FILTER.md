# M10-INTERSECTION-FILTER

**Status:** DONE_STRONG

Intersection types and the filter model: the third model of the untyped calculus, and the one
that identifies "syntactically typable" with "semantically nonempty".

## The type assignment system — `Start/IntersectionTypes.lean`

The strict (van Bakel) presentation of the BCD/Coppo–Dezani system `λ∩`:

* `Inter.Sty := GraphModel.Tok` — a strict type is an atom or an arrow `a → σ` whose source is a
  finite intersection; these are *literally* the tokens of the graph model;
* `Inter.Ty := List Inter.Sty` — intersections, the empty list being the universal type `ω`;
* `Inter.Basis := ℕ → Inter.Ty`, `Inter.push` — bases and their extension under a binder;
* `Inter.Deriv Γ M σ` — the three rules: variable (intersection elimination built in),
  application (intersection introduction built in), abstraction;
* generation lemmas `Inter.deriv_var_iff`, `deriv_app_iff`, `deriv_lam_iff`,
  `not_deriv_lam_atom`, weakening `Inter.Deriv.weaken`, and `Inter.Typable`.

## The filter model — `Start/FilterModel.lean`

* **`Inter.deriv_iff_mem_denot`** — `Γ ⊢ M : σ ↔ σ ∈ GraphModel.denot M (basisEnv Γ)`.  The set
  of types of a term *is* its denotation: the graph model is the filter model of `λ∩`
  (`Inter.typeSet_eq_denot`).
* `Inter.deriv_reduces`, `Inter.deriv_expansion`, `Inter.deriv_conv`, `Inter.typeSet_conv` —
  subject reduction, subject expansion, invariance of the type set under β-conversion.
* **`Inter.typable_iff_hasHnf`** — a term is typable iff it has a head normal form;
  `Inter.typable_iff_denot_ne_empty` and `Inter.typable_iff_exists_denot_ne_empty` restate this
  semantically, and `Inter.typable_iff_solvable` restates it as solvability.
* `Inter.not_typable_omega`, `Inter.typable_I`, `Inter.deriv_I` — the extreme cases.

## The normalisation theorem — `Start/IntersectionNormalization.lean`

* `Inter.Proper`, `Inter.ProperBasis` — `ω`-free strict types and bases;
* `Inter.proper_of_mem_denot_neutral`, `Inter.isNormal_of_mem_denot_direct` — the two facts about
  proper types that force a direct approximant to be `Ω`-free;
* **`Inter.hasNormalForm_of_properDeriv`** — `ω`-free typability implies normalisation, proved
  through the approximation theorem `GraphModel.exists_reduct_mem_denot_direct` rather than a
  reducibility argument;
* `Inter.properDeriv_of_hasNormalForm` — the converse, by induction on normal forms;
* **`Inter.properTypable_iff_hasNormalForm`** — the Coppo–Dezani normalisation theorem;
* `Inter.exists_typable_not_properTypable` — the inclusion is strict: `x Ω` is typable but has no
  normal form.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.IntersectionTypes Start.FilterModel Start.IntersectionNormalization`
* Axioms of `Inter.deriv_iff_mem_denot`, `Inter.typable_iff_hasHnf`,
  `Inter.properTypable_iff_hasNormalForm`, `Inter.exists_typable_not_properTypable`:
  `propext, Classical.choice, Quot.sound`.
