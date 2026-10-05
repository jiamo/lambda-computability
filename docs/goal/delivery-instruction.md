# Delivery instruction

The objective is a theorem, and the rows it needs are all `TODO_READY`.  This is the same
shape as the delivery that closed the relativization barrier.

---

```
Work to this instruction for this delivery.

THE OBJECTIVE

IP = PSPACE.

Every row it needs is TODO_READY, and both prerequisites outside M21 are now
DONE_STRONG (M14-TQBF-PSPACE-HARD and M21-COBHAM-TO-SPACE). Nothing here needs a
design step. Nine rows, in dependency order:

  M21-QBF-SIMPLE-FORM    the simple form of a QBF the protocol runs on
  M21-LINEARIZE          Shen's linearization operator, so a quantifier cannot double
                         the degree and the verifier stays polynomial
  M21-IP-DEF             verifiers in Cobham's class, provers arbitrary, acceptance
                         probability by counting over random words: completeness 2/3,
                         soundness 1/3
  M21-FIELD-COBHAM       field arithmetic as Cobham terms
  M21-SUMCHECK-GAME      the protocol itself, on top of M21-SUMCHECK-ROUND
  M21-VERIFIER-POLY      the verifier is a Cobham term
  M21-TQBF-IN-IP         TQBF has an interactive proof
  M21-PSPACE-SUBSET-IP   with TQBF PSPACE-complete, PSPACE subseteq IP
  M21-IP-SUBSET-PSPACE   the converse, from M21-COBHAM-TO-SPACE
  M21-IP-EQ-PSPACE       Complexity.ip_eq_pspace

CARRY THE CHAIN, AND STOP WHERE IT STOPS

Take the rows in order and carry as many as hold. Nine is more than the five of the
last delivery, and finishing all of them in one go is not expected. What is expected
is that you stop at the first row that defeats you rather than moving sideways: name
the missing lemma in its open_boundary, open it as a row if it is a new construction,
and leave the rest of the chain unstarted.

If a row turns out to be reachable by a different route than the one its exit criteria
describe -- as the collapsing oracle was last time, where the self-referential
construction of Start/CollapsingOracle.lean replaced the PSPACE-complete oracle -- take
the better route, prove the theorem, and leave the superseded row TODO_READY with its
own gap named. That was the right call and it is the right call again.

GOING BEYOND THE OBJECTIVE

Last time the instruction said not to start a new milestone and Start/Resolution.lean
and Start/AbstractLob.lean were started anyway. The rule was too blunt, so here it is
properly: when the objective is closed and there is room left, continue with rows that
are already on the board, say in the report which ones and why, and do not add a
milestone that is not there. Do not do this before the objective is closed.

THE PACKAGING QUESTION, AGAIN

The previous instruction asked what command actually produces the delivered archive.
The report did not answer it. The delivered manifest has now named package 'start',
pinned Mathlib v4.28.0 and omitted cslib fourteen times running, including in the two
deliveries that added scripts/pack_gate.sh, .githooks/pre-commit and the AGENTS.md
rule fixing the delivery to one command. Those archives therefore cannot have come
from that command.

Answer in the report, in three lines:
  - the exact command or script that writes the file handed over;
  - the directory it runs in, and whether that directory is a git clone of this
    repository at the delivered commit;
  - whether scripts/check_manifest.py passes in that directory right now, quoting its
    output.

If you cannot determine any of the three, say which and why. An honest "the packaging
step is outside the tree I work in" ends fourteen deliveries of guessing.

REPORT

Four short paragraphs: which rows closed, with the verbatim terminal statement of the
furthest one reached; where the chain stopped and what defeated it; the three lines on
packaging; and anything done after the objective, with the row ids.
```

---

## Notes

* **Nine rows, one theorem.**  The pattern that closed the barrier is reused deliberately: an
  objective stated as a theorem, a chain of `TODO_READY` rows under it, and permission to
  carry them all.  Nine will probably not fit in one delivery; the instruction says so, and
  says what to do instead of substituting other work.
* **The re-routing clause is new.**  Last delivery proved `bgs_equal` by a construction the
  row did not call for, and left the row open with its gap named.  That is better behaviour
  than following the written route into a wall, so it is now explicitly sanctioned.
* **The overshoot rule is loosened rather than repeated.**  "Do not start a new milestone"
  was ignored; the version here allows continuing on existing rows after the objective and
  asks for them to be named.
* **The packaging question is now three specific questions.**  The open-ended version went
  unanswered.
