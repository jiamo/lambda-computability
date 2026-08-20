# M5-ALGORITHM-REPRESENTATION

**Status:** DONE_STRONG

New module `Start/AlgorithmRepresentation.lean` (imported by `Start.lean`).

Axiomatization (bounded exploration, in concrete form):

* states have finitely many locations holding naturals (`Fin size → ℕ`);
* the transition is a finite list of guarded update rules (`SeqAlgorithm.Rule`): each guard tests
  finitely many equalities and disequalities between terms over the locations
  (`SeqAlgorithm.Expr`, `SeqAlgorithm.Guard`), and each rule updates finitely many locations
  simultaneously (`SeqAlgorithm.applyUpdates`);
* the first rule whose guard holds fires (`SeqAlgorithm.stepProg`).

Results:

* `SeqAlgorithm.primrec_stepProg` — the induced state transition is primitive recursive.  This is
  *derived* from the axioms; computability is not part of the hypotheses.
* `SeqAlgorithm.Algorithm.partrec_run` — the input-output partial function is partial recursive;
  `lambdaComputable_run` and `tm2Computable_run` transport it to the lambda calculus and to
  Turing machines using the existing capstones.
* `SeqAlgorithm.doubling`, `SeqAlgorithm.run_doubling`, `SeqAlgorithm.lambdaComputable_doubling` —
  a genuinely looping algorithm (count the input down, add two each step) whose function is
  computed exactly: `doubling.run n = Part.some (2 * n)`.

Scope note: this is a representation theorem for the stated axioms, not a proof of the
Church–Turing thesis, which is not a formalizable statement.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on the headline
results reports only `propext, Classical.choice, Quot.sound`.
