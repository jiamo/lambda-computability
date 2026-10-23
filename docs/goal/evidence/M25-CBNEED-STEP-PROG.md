# M25-CBNEED-STEP-PROG — the tape program for one transition of the lazy machine

## Big round 2, run 1 (item W3)

First exit criterion ("A binary encoding of lazy machine states (codes, environments of heap
addresses, the heap of thunk, hole and value cells, argument and update frames) as words") — done,
`Start/LazyStateWord.lean`:

* `Lazy.natBits` (unary, `Lambda.sizeBits (var n)`), `Lazy.listBits` (a `1` before each entry and a
  final `0`) with `Lazy.listBits_append_inj` for any prefix-free entry code;
* `Lazy.lclosBits` (term, then environment of addresses), `Lazy.cellBits` (`00`/`01` + closure for
  thunk/hole, `1` + two closures for a value cell), `Lazy.lframeBits` (`0`/`1` + address);
* `Lazy.lstateBits` (code, environment, stack, heap) and **`Lazy.lstateBits_injective`**.

Second exit criterion (a tape program performing one `LTrans` transition, specified through
`Complexity.Space.Realizes`, with a polynomial time bound) — open.  First missing lemma:

    theorem Lazy.realizes_trans : ∃ (M : Complexity.Space.Machine) (code : List Bool → Lazy.LState → Complexity.Space.Config)
      (B : List Bool → ℕ), Complexity.Space.Realizes M Lazy.absMachine code B ∧
      ∀ x s, (code x s).tape = Lazy.lstateBits s

for an abstract machine `Lazy.absMachine` running `LTrans` from `LState.init` (to be defined).

Also this run, `Start/LazyStepFn.lean`: the step function the abstract machine needs,
`Lazy.lstepFn`, with `Lazy.lstepFn_eq_some_iff` (`lstepFn s = some s'` iff `LStep s s'`) and
`Lazy.lstepFn_eq_none_iff` (`none` exactly on final states).

Also this run, `Start/LazyAbsMachine.lean`: the abstract machine is now defined,
`Lazy.labsMachine dec acc` (start `LState.init (dec x)`, step `Lazy.lstepFn`, accept `acc`), with
`Lazy.labsMachine_reaches_iff` (its reachable states are exactly the lazy run states from the
initial state).  The first missing lemma is therefore `Lazy.realizes_trans` with
`Lazy.labsMachine dec acc` in place of `Lazy.absMachine`.

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").
