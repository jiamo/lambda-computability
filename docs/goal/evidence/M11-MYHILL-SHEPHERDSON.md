# M11-MYHILL-SHEPHERDSON

**Status:** DONE_STRONG

`Start/EffectiveOperation.lean` proves that an *effective operation* — a partial computable
`Ψ : ℕ →. ℕ` on indices whose value depends only on the partial function `φ_e` named by the index
(`Lambda.Post.ExtensionalOp`) — is monotone and compact, hence Scott continuous.  Nothing in the
definition restricts the algorithm to reading finitely much of its argument: it is handed a
program, a finite object determining the whole infinite graph.  The theorem says it makes no
difference.  The module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds
without `sorry` and without linter warning, and `Lambda.Post.effop_continuous` depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## The s-m-n theorem with values (first exit criterion)

`Start/PostIncomplete.lean` had `exists_index_fun`, which names a partial computable family but
records only the *domains* of its members.  `Lambda.Post.exists_index_eval` strengthens it: the
index `h n` produced by currying a code for the uncurried family satisfies `φ (h n) = F n` as
partial functions, values included.  That is what an extensionality hypothesis can be applied to.

## Effective operations, and the class of a value (second exit criterion)

* `Lambda.Post.phi` — the partial function named by an index;
* `Lambda.Post.ExtensionalOp`, `Lambda.Post.SubFun`, `Lambda.Post.FiniteDom`;
* `Lambda.Post.rePred_value` — `{e | v ∈ Ψ e}` is r.e., by running a code for `Ψ` stage by stage.

## Monotonicity (third exit criterion)

`Lambda.Post.effop_mono`.  Suppose `v ∈ Ψ e`, `φ e ⊆ φ d`, but `v ∉ Ψ d`.  The family
`φ (h n) = φ e ∪ (φ d guarded by "n has entered the halting set")` is partial computable — the two
branches agree where both are defined, so `Partrec.merge` applies — and it names `φ e` when `n`
does not halt and `φ d` when it does.  Extensionality then gives `¬ HaltK n ↔ v ∈ Ψ (h n)`, so the
complement of the halting set would be r.e.: `Lambda.Post.false_of_compl_haltK_iff`.

## Compactness (fourth exit criterion)

`Lambda.Post.effop_finite_witness`.  Suppose `v ∈ Ψ e` but no finite restriction of `φ e` has that
value.  `Lambda.Post.cutFun e n` runs `φ e x` and accepts its value only if the computation
converged strictly before `n` entered the halting set (`Lambda.Post.cutTest`,
`Lambda.Post.mem_cutFun_iff`).  If `n` never enters, this is the whole of `φ e`; if it enters at
stage `s₀`, the domain is contained in `Iio s₀`, since a computation converging in `s` steps has
input below `s` — a finite restriction.  Again `¬ HaltK n ↔ v ∈ Ψ (h n)`.

## Scott continuity and a consequence (fifth exit criterion)

`Lambda.Post.effop_continuous` combines the two, and `Lambda.Post.effop_const_of_empty` records
that an operation with a value at the nowhere-defined function has that value everywhere: an
effective operation cannot test its argument for divergence.

## Boundary

The counterpart for *total* computable functions — the Kreisel–Lacombe–Shoenfield theorem — is not
proved here and is not claimed.  The argument above does not transfer: an operation defined only on
indices of total functions cannot be applied to the cut-off function, which is no longer total.
The type-two form of continuity, for functions computed from names rather than from indices, is
`Start/ComputableReal.lean` (M11-COMPUTABLE-REAL-CONTINUITY).
