# Delivery instruction

Paste the block below as the instruction for a delivery.  Unlike the previous version, the
objective is a *theorem* rather than a single row: the five rows it needs are all
`TODO_READY`, share one substrate, and are worth doing in one delivery.

---

```
Work to this instruction for this delivery.

THE OBJECTIVE

Close the relativization barrier: prove that neither side of P vs NP relativizes,
unconditionally. That is one theorem, and it needs these five rows, all of which are
already TODO_READY -- none needs a design step:

  M15-ORACLE-PROG      query-tape instructions for Complexity.Space.Prog, the
                       compiler of Start/CobhamSpace.lean extended to Complexity.CobQ,
                       and the witness loop giving NP^A subseteq PSPACE^A.
  M15-ORACLE-CLASSES   closes (DONE_WEAK) as soon as the above lands.
  M14-QBF-STEP-PROG    a tape program performing one step of the Start/Qbf.lean
                       evaluator, with the realizes_loop bridge.
  M14-TQBF-IN-PSPACE   follows from it and M14-SPACE-COMPILE; with the hardness
                       already proved, M14-TQBF-PSPACE-HARD then closes and TQBF is
                       PSPACE-complete.
  M15-BGS-EQUAL        P^A = NP^A for that A, from the two above.
  M15-NO-RELATIVIZING-PROOF  closes (DONE_WEAK), and with it

      Complexity.no_relativizing_resolution

  becomes unconditional. BakerGillSolovay.lean already supplies the other oracle.

DO THEM IN ONE DELIVERY

The one-objective-per-delivery rule is about not wandering between milestones. It is
not a rule against finishing a chain: when every row of the objective is TODO_READY
and they depend only on each other, carry them all. Stop only when the theorem is
closed or when a row defeats you.

M15-ORACLE-PROG and M14-QBF-STEP-PROG are the same kind of work -- writing a tape
program on top of the combinators you factored out in Start/SpaceProgLib.lean,
Start/SpaceProgTracks.lean and Start/SpaceProgDecide.lean. Do them together, and if
the combinator library turns out to be missing something both need, extend it there
rather than twice.

WHAT COUNTS AS DONE

Complexity.no_relativizing_resolution with no hypothesis about an oracle, and
M15-NO-RELATIVIZING-PROOF, M15-ORACLE-CLASSES and M14-TQBF-PSPACE-HARD all
DONE_STRONG with empty open_boundary. If a row defeats you, the DONE_WEAK rule of
docs/goal/goal-prompt.md applies: name the missing lemma precisely, open it as a row
at the head of the queue, and leave the rest of the chain unstarted rather than
substituting other work.

ONE QUESTION TO ANSWER IN THE REPORT

AGENTS.md now says a delivery is produced by exactly

    scripts/pack_gate.sh HEAD && git archive --format=tar.gz HEAD -o delivery.tar.gz

Thirteen consecutive deliveries, including the one that introduced that rule, have
arrived with a lake-manifest.json naming package 'start', pinning Mathlib v4.28.0 and
omitting cslib. That manifest fails scripts/check_manifest.py, so the command above
cannot have produced those archives: pack_gate.sh would have exited first and no
tarball would exist. Something else is packing them.

So, in the report: what command or process actually produces the file that is handed
over, and from which directory? Do not guess -- check, and quote what you find. If the
packaging is outside your control, say that; it is a more useful answer than another
promise to run the gate.

AFTER THE OBJECTIVE, IF THERE IS ROOM

docs/related-work.md lists claims you could not verify. Two are cheap to settle from
sources you already have, and both affect how the library describes itself:

  - the Coq L development (Forster et al., POPL 2020 / ITP 2021): exactly which
    invariance results does it prove, and in which direction? The document now says
    it proves more of the programme than this library does; confirm or correct that
    with a citation.
  - Cubical Agda's realizability topos: does it construct the effective topos itself,
    or assemblies and modest sets only?

Nothing else from that list. Do not start a new milestone.

REPORT

Four short paragraphs: whether the barrier theorem is closed and the verbatim
statement of what was proved; which rows closed and which did not; the answer to the
packaging question; and anything from related-work.md you settled.
```

---

## Why this shape

* **The objective is a theorem, not a row.**  Fifteen deliveries have shown that one row per
  delivery is the right granularity when rows need designing, and the wrong one when a chain
  of `TODO_READY` rows is all that stands between the library and a quotable result.  Five
  rows, no design, one theorem.
* **The two tape-program rows are siblings.**  `Start/SpaceProgLib.lean` was factored out
  last delivery precisely so that writing the next tape program would be cheap; this is the
  delivery that tests whether it was.
* **The packaging item is a question, not a reminder.**  Thirteen reminders have not worked,
  and the delivered artifact is now provably not the output of the documented command.  Asking
  where the file comes from is the only step that can move it.
