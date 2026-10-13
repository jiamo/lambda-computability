# M27-POLYTIME-TO-COBHAM — polynomial-time multi-tape machines decide languages in Cobham's P

Status: DONE_STRONG.

## Terminal statement

```lean
theorem Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn (M : FiniteMultiTapeMachine)
    (L : Language) (p : ℕ → ℕ) (hp : PolyBound p)
    (hM : ∀ x, ∃ b, MultiTapeHaltsIn M x b (p x.length) ∧ (L x ↔ b = true)) : InP L
```

(`Start/MultiTapeCobham.lean`).  `FiniteMultiTapeMachine` and `MultiTapeHaltsIn` are upstream's
definitions (`Start/DepthThreeModel.lean`), unchanged; `InP` is the library's Cobham class.

## The construction

* Encoding (`Start/MultiTapeMacro.lean`): a configuration is a word over the finite alphabet
  `Sym M` — the state, then for every tape a delimited segment with the head position marked —
  related to the configuration by `Rep M u c`; then in binary by `Macro.enc`.
* One step (`MultiTapeCobham.stepTerm`, `eval_stepTerm`): a left-to-right finite-state transducer
  reads the state and the scanned symbols (`Start/MacroTransducer.lean`); its final state selects
  the edit transducer of the transition (`Macro.selectTerm`, `Start/CobhamMacro.lean`), which
  rewrites the word into a word of the next configuration, at most `2 |K|` symbols longer.  On a
  halted configuration the step term is the identity.
* Iteration (`MultiTapeCobham.decider`, `eval_decider`): starting from the encoded initial
  configuration (`initTerm`), the step term is iterated exactly `a · (n + 1)^k` times with
  `Cob.iterT` (`Start/CobhamTimeIter.lean`), where `p n ≤ a · (n + 1)^k` is the polynomial bound
  of `PolyBound p`; the accepting bit of the final state is read off (`accTerm`).  The length of
  every intermediate word is at most `|x| + c + 2|K| · a (n + 1)^k`, which is the polynomial bound
  that `iterT` needs.

## Axioms

`#print axioms Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn`:
`[propext, Classical.choice, Quot.sound]`.  Same for `eval_stepTerm` and `eval_decider`.
