# M25-CBV-STEP-PROG — the tape program for one CEK transition

## Big round 2, run 1 (item W3)

First exit criterion ("A binary encoding of CEK states (codes, nested environments of closures,
frames) as words") — done, `Start/CbvStateWord.lean`:

* `CEK.closBits`, `CEK.envBits` (mutual on the nested type `Krivine.Clos`): a closure is the
  prefix-free code `Lambda.sizeBits` of its term followed by its environment; an environment is
  `1 · closure` per entry and a final `0`;
* `CEK.frameBits` (`0 · term · env` for an argument frame, `1 · closure` for a function frame),
  `CEK.stackBits`, `CEK.stateBits` (`0 · term · env · stack` for `eval`, `1 · closure · stack`
  for `ret`);
* unique decoding: `closBits_append_inj`, `envBits_append_inj`, `frameBits_append_inj`,
  `stackBits_append_inj`; **`CEK.stateBits_injective`**.

Second exit criterion (a tape program performing one transition, specified through
`Complexity.Space.Realizes` of `Start/SpaceCompile.lean`, with a polynomial time bound) — open.
First missing lemma: the machine and its realization,

    theorem CEK.realizes_trans : ∃ (M : Complexity.Space.Machine) (code : List Bool → CEK.State → Complexity.Space.Config)
      (B : List Bool → ℕ), Complexity.Space.Realizes M CEK.absMachine code B ∧
      ∀ x s, (code x s).tape = CEK.stateBits s

for an abstract machine `CEK.absMachine` running `CEK.Trans` from `State.init` of the decoded
input (to be defined), followed by the per-transition time bound.

Also this run, `Start/CbvStepFn.lean`: the step function the abstract machine needs, `CEK.stepFn`,
with `CEK.stepFn_eq_some_iff` (`stepFn s = some s'` iff `Trans l s s'` for some `l`) and
`CEK.stepFn_eq_none_iff` (`none` exactly on final states).  So `CEK.absMachine` can be defined with
`step := CEK.stepFn`.

Also this run, `Start/CbvAbsMachine.lean`: the abstract machine is now defined,
`CEK.absMachine dec acc` (start `State.init (dec x)`, step `CEK.stepFn`, accept `acc`), with
`CEK.absMachine_reaches_iff` (its reachable states are exactly the CEK run states from the initial
state).  The first missing lemma is therefore `CEK.realizes_trans` with `CEK.absMachine dec acc` in
place of `CEK.absMachine` (for a fixed decoder `dec` and acceptance test `acc`).

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").
