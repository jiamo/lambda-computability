# M6-KOLMOGOROV-CORE

**Status:** DONE_STRONG

New module `Start/Kolmogorov.lean` (imported by `Start.lean`).

* `Lambda.size` — syntactic size of a term (number of nodes, a de Bruijn index `i` costing
  `i + 1`); `Lambda.size_church : size (church n) = 3 * n + 3`.
* `Lambda.IsProgramFor t s` — `t` is closed and reduces to `church s`.
* `Lambda.kolm` — Kolmogorov complexity: `sInf {size t | IsProgramFor t s}`.  Well defined:
  `church s` is always a program (`Lambda.isProgramFor_church`), so the set is non-empty and
  `Lambda.exists_program_of_kolm` produces a shortest program.
* `Lambda.finite_setOf_size_le` — only finitely many terms have size at most `n` (explicit
  covering of the size-`≤ n` terms by variables, abstractions and applications of smaller terms).
* `Lambda.valOf`, `Lambda.valOf_eq` — the numeral a term reduces to, well defined by confluence
  (`Lambda.unique_church_reduct`).
* `Lambda.finite_setOf_kolm_le` — `{s | kolm s ≤ n}` is finite.
* `Lambda.exists_incompressible` — **for every `n` there is an `s` with `n ≤ kolm s`.**

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on
`Lambda.exists_incompressible` reports only `propext, Classical.choice, Quot.sound`.
