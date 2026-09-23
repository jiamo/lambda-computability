# Delivery instruction

Paste the block below as the instruction for a delivery.  It is written to close one theorem
per delivery instead of opening several lines at once; the queue at the end is followed in
order, and the first item that is not `DONE_STRONG` is the objective.

---

```
Work to this instruction for this delivery.

THE OBJECTIVE

Your objective is the first task in the QUEUE below whose status is not DONE_STRONG.
That task, and nothing else, is what this delivery is for. Do not choose a different
task because it looks cheaper, and do not open a new milestone while the objective
is open.

WHAT COUNTS AS DONE

The delivery is acceptable only if the objective ends the delivery as DONE_STRONG with
an empty open_boundary. DONE_WEAK is not an acceptable outcome for the objective. If
you cannot close it, deliver the partial work but say so in one sentence at the top of
your report, name the single lemma that defeated you, and leave the objective as the
first queue item so that the next delivery resumes it. Do not fill the delivery with
unrelated tasks to compensate.

IF THE OBJECTIVE IS TODO_NEEDS_DESIGN

Design first, in writing, before any Lean. Split it into TODO_READY rows on the task
board, each with a terminal_statement you could check against, and each small enough
that its proof is a single module. Then execute those rows in the same delivery. The
split itself is part of the delivery, not a substitute for it: a delivery that only
adds rows has not met the objective.

WHAT MAY BE DONE BESIDES

Only what the objective needs. If a prerequisite turns out to be missing, add it and
say so. Incidental cleanups are fine when they are forced by the objective; they are
not a reason to grow the delivery. A DONE_WEAK task from an earlier delivery may be
closed if the objective passes through it.

STANDING PRECONDITIONS

Run scripts/install_hooks.sh once in your clone; the pre-commit hook it installs calls
scripts/pack_gate.sh, which is the gate that catches a lake-manifest.json disagreeing
with lakefile.toml. Nine consecutive deliveries have shipped a manifest naming package
'start' while lakefile.toml declares 'lambda_computability': that manifest cannot be
built from a fresh clone, so every one of those deliveries was unbuildable as shipped,
whatever your working tree did. Run scripts/pack_gate.sh before packing, and do not
deliver a tree that fails it.

This repository is pinned to leanprover/lean4:v4.33.0 with Mathlib v4.33.0 (db584cd6)
and cslib 3951377e. If your environment cannot supply that pair, say so in the report
rather than repinning the tree downwards: a v4.28 tree cannot be merged here, and the
adaptation diffs it produces are discarded on arrival.

REPORT

Three short paragraphs: what the objective was and whether it is closed; the terminal
statement, verbatim, of what was proved; what is honestly still open, if anything.

QUEUE

 1. M14-TQBF-PSPACE-HARD   — TQBF is PSPACE-complete. All the machinery exists
                              (M14-QBF-*, M13-SAVITCH-SPACE); what is missing is the
                              reduction itself and Complexity.Qbf.pspaceComplete_TQBF.
 2. M15-BGS-EQUAL          — P^A = NP^A for A PSPACE-complete. Unblocked by 1.
 3. M15-NO-RELATIVIZING-PROOF — currently DONE_WEAK; closes with 2, and with it the
                              whole statement that neither side of P vs NP relativizes.
 4. M16-FRIEDBERG-MUCHNIK  — the framework is in place (M16-FINITE-INJURY); this is the
                              construction itself, and Post's problem with it.
 5. M17-EXREG-PROJ-REGULAR and M17-EXREG-UNIVERSAL — both TODO_READY, both short.
 6. M18-KLS                — TODO_READY.
 7. M19-SYMMETRY-HARD-HALF — the oldest outstanding item in the library.
 8. M20-GANDY              — the physical Church-Turing thesis; the task this library is
                              named for, and never formalized anywhere.

Items 1 to 3 are one theorem split across three rows: until they are all DONE_STRONG the
barrier result cannot be stated, and the fourteen QBF modules of the last two deliveries
are load-bearing for nothing.
```

---

## Why it is shaped this way

Fourteen deliveries of evidence say the failure is not capacity, it is selection:

* **It builds machinery and does not close the theorem.**  The last two deliveries added
  fourteen modules encoding a space-bounded run as a QBF, and `M14-TQBF-PSPACE-HARD` is
  still `TODO_NEEDS_DESIGN`.  Hence: one named objective, and `DONE_WEAK` disallowed for it.
* **It will not start a `TODO_NEEDS_DESIGN` task.**  Seventeen of the thirty-one open tasks
  carry that status and none has been picked up; the two flagships it *did* finish
  (Accattoli's time invariance, the space cost model) were both handed to it pre-split into
  three rows.  Hence: the split is mandatory and is part of the delivery, not the delivery.
* **It compensates for a hard objective with easy breadth.**  Hence the explicit ban on
  filling the delivery with unrelated tasks, and the requirement to name the lemma that
  defeated it.
* **The queue is ordered so that consecutive deliveries continue the same line** rather
  than each opening a new one.
