# M11-MULTI-TYPES

**Status:** DONE_STRONG

`Start/MultiTypes.lean` builds the **non-idempotent** intersection type system — de Carvalho's
*multi types* — on top of the λ-terms and head reduction of this development, and proves that a
derivation is not merely a certificate of head normalisation but a *measurement* of it.  The
module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds without `sorry`
and without linter warning, and the headline results depend only on `propext`,
`Classical.choice`, `Quot.sound`.

`Start/IntersectionTypes.lean` and `Start/FilterModel.lean` already gave the *idempotent* system,
where `σ ∧ σ = σ` and typability characterises head normalisation qualitatively
(`Inter.typable_iff_hasHnf`).  Idempotence is exactly what destroys the quantitative content: a
premise may be reused for free, so the derivation forgets how many times an argument was needed.

## The system (first and second exit criteria)

* `Multi.Sty` — strict types: an atom, or an arrow `a → σ` whose source `a : Multi.MTy` is a
  finite multiset of strict types, presented as a list;
* `Multi.Ctx := ℕ → Multiset Sty` — a context assigns a *multiset* of strict types to each de
  Bruijn index.  Using multisets rather than lists removes all permutation bookkeeping; lists
  survive only inside arrow sources, where the derivation needs to line the premises up.
* `Multi.Deriv Γ M σ n` and `Multi.DerivList Γ M a n`, a mutual inductive family carrying the
  **size** `n` of the derivation as an index (`var` = 1, `lam` = n+1, `app` = n+m+1,
  `cons` = n+m).  There is **no weakening**: the context is an output.  The variable rule produces
  the singleton context `single x σ`; the application rule produces the *sum* `add Γ Δ` of the
  contexts of its two premises.

The supporting context algebra (`add_comm`, `add_assoc`, `add_rearrange`, `push_add`, `del_add`,
`del_single_*`, `ins_*`, …) is proved pointwise.  `Multi.DerivList.split`, `.append` and `.perm`
let a list of derivations be cut and reassembled along a splitting of its multi type.

## The quantitative substitution lemma (third exit criterion)

`Multi.substitution` is the engine.  Given a derivation of `M` of size `n` in a context using the
multi type `a` at the index `x`, and a `DerivList` deriving `a` for `N` of total size `m`, it
produces a derivation of `M[N/x]` of size `p` satisfying

    p + a.length = n + m

— every element of `a` consumes exactly one `var` node of size 1, so the sizes add up and the
`|a|` variable occurrences are paid for.  Proved by mutual induction together with `lifting`,
which transports a derivation along an index shift.

## Quantitative subject reduction (fourth exit criterion)

`Multi.subject_reduction_wstep` and `Multi.subject_reduction_hstep`: if `M` head-reduces to `M'`
and `M` has a derivation of size `n`, then `M'` has a derivation of size `p` with `p < n`.  The
strictness is what idempotent intersection types cannot deliver.

## The bound (fifth exit criterion)

* `Multi.hnIn_of_deriv` — by strong induction on the size: a term with a derivation of size `n`
  reaches a head normal form within `n` head steps (`Lambda.HNIn n M`).  The type system bounds
  the running time, not just the fact of termination.
* `Multi.hasHeadEval_of_deriv`, `Multi.hasHnf_of_typable` — the qualitative corollary.
* `Multi.exists_deriv_of_neutral`, `Multi.typable_of_isHnf` — the converse half: every head normal
  form is typable, so the system is not vacuous and typability *characterises* head normalisation.
* `Multi.no_deriv_of_hstep_self`, `Multi.hstep_omega_omega`, `Multi.not_typable_omega` — a term
  that head-reduces to itself has no derivation at all, so `Ω` is untypable.

## Boundary

Subject **expansion** is not proved.  Consequently de Carvalho's exact equality — the size of a
derivation equals the number of head steps to the head normal form plus the size of a derivation
for that head normal form — is *not* claimed here.  What is proved is the upper bound
`hnIn_of_deriv` in one direction and typability of head normal forms in the other.  Likewise the
relational/denotational side of multi types (the multiset relational model, and the theorem that
the interpretation of a term is the set of its derivable judgements) is not developed.
