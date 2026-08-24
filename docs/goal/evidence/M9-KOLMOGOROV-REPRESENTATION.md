# M9-KOLMOGOROV-REPRESENTATION

**Status:** DONE_STRONG

Module `Start/KolmogorovRepresentation.lean`, imported by `Start.lean`.  It builds without `sorry`
and without linter warnings.

The module asks how much of Kolmogorov complexity depends on the representation of programs.  The
library has three representations of λ-terms — de Bruijn terms (`Lambda`), the locally nameless
terms of `cslib` (`LNTerm`), and BLC bit strings (`bits`) — and the answer turns out to be
different for a change of *syntax* and for a change of *cost measure*.

## Changing the syntax costs nothing

* `sizeLN` is the size of a locally nameless term, and `sizeLN_toLN` proves that the translation
  `toLN` of `Start/Representation.lean` preserves size exactly.
* `IsProgramForLN`, `kolmLN` define Kolmogorov complexity in the locally nameless representation:
  the least size of a closed locally nameless term reducing to the Church numeral of `s`.
* **`kolmLN_eq_kolm`** — `kolmLN s = kolm s` for every `s`, with no additive constant at all.  The
  proof transports programs in both directions along the bijection of `M9-REPRESENTATION-BRIDGE`:
  `toLN` sends a de Bruijn program to a locally nameless one of the same size (`lc_toLN`,
  `fv_toLN_closed`, `reduces_toLN`), and `ofLN` comes back (`toLN_ofLN`, `reflect_reduces`,
  `freeMax_ofLN`), so the two sets of achievable sizes coincide.

## Changing the cost measure costs a factor, and not only a constant

* `nodes` counts the nodes of a term and **`bits_length_eq_size_add_nodes`** proves
  `|bits t| = size t + nodes t`: the BLC code length is the size measure plus the node count.
* `Start/PlainVsPrefix.lean` already had the two-sided bound `kolm s ≤ kolmP s ≤ 2 * kolm s`.
* **`not_exists_const_kolmP_le_kolm_add`** shows that this factor two cannot be improved to an
  additive constant: there is no `c` with `kolmP s ≤ kolm s + c` for all `s`.  The proof uses
  `finite_closed_nodes_le` (only finitely many closed terms have a bounded node count) to produce,
  for each bound, a numeral whose shortest program has many nodes (`exists_nodes_gt`), and hence a
  gap `exists_kolm_add_lt_kolmP` larger than any prescribed constant.

So Kolmogorov complexity is *exactly* invariant under a change of term syntax, while a change of
cost measure is invariant only up to a multiplicative constant — the additive invariance one might
expect is false.

## Boundary

* Invariance is proved for the two syntaxes of terms and for the size/bit-length measures of this
  library; no claim is made about arbitrary universal machines beyond the invariance theorem
  already in `Start/Kolmogorov.lean`.
