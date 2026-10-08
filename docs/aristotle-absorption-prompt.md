Work to this instruction for this delivery.

WHAT YOU ARE GIVEN

oai-math-relevant.tar.gz, extracted from github.com/openai/math (Apache-2.0, commit
adc7f1241): 1275 Lean files from their lean/OAI/Computability tree, 12 papers, and a
README.md mapping directories to results. Read that README first -- it was written from
greps, not from reading proofs, so correct whatever does not survive checking.

Their build is leanprover/lean4:v4.34.1 with Mathlib d13f23b7. Ours is v4.33.0 with
Mathlib v4.33.0 (db584cd6). Nothing compiles against our pin unmodified.

THE OBJECTIVE

Absorb their work into Start/ as ordinary modules of this library: adapted to our pin,
imported from Start.lean, registered in Start/Capstones.lean, sorry-free, passing
check_closure.py and goal_state.py validate. Not a vendored subtree, not a dependency --
our modules, under our naming conventions, in our namespaces.

ATTRIBUTION IS NOT OPTIONAL

Apache-2.0 requires it even when the code is rewritten. Every absorbed module carries a
header naming the source (github.com/openai/math, the directory, the family number and
the paper title), and the repository gains a NOTICE file listing what came from there.
A module whose proof you reconstructed rather than adapted says that instead. Do not
present absorbed results as this library's own in README.md or Capstones.lean prose.

ORDER, BY COST AND BY WHAT IT BUYS US

Do them in this order and stop where the delivery stops. Do not start a later one before
an earlier one is DONE_STRONG.

  1. TypeSystem (33 files, family 245): weak normalization implies strong normalization
     for every pure type system. This is the one with real leverage: lambda-Pi is a PTS,
     and Start/LambdaPiSN.lean proves strong normalization for that single system. Once
     their theorem is ours, say explicitly whether Start/LambdaPiSN.lean becomes an
     instance of it or stays independent, and if it becomes an instance, make it one.
  2. Logspace (1 file, family 103: L = RL = BPL) and SolenoidalRecorder (5 files,
     family 376). Small, and both sit next to Start/SpaceMachine.lean. Check first
     whether one file really carries L = RL = BPL or only a fragment of it.
  3. StarHeight (37, family 134: every regular language has generalized star height at
     most three) and WeisfeilerLeman (43, family 133). Self-contained, and we have no
     regular-language development at all, so these arrive with their own foundations.
  4. DepthThree (179, family 112): a language in P whose n-bit membership needs
     2^omega(sqrt n)-size depth-three circuits. Our first circuit lower bound; it meets
     Start/PolyCircuit.lean and Start/UniformCircuit.lean.
  5. DegreeRigidity (975, family 241) last, and only if the four above are closed.
     Roughly 674 of those files are set theory -- SetModels 273, CohenForcing 108,
     OrdinalCodes 105, Constructibility 101, Syntax 87 -- and the recursion-theory part
     imports it (25 imports of SetModels, 20 of CohenForcing, 13 of Constructibility),
     so it does not detach. Absorbing it means absorbing a forcing and ZFSet development
     into this library. Before writing any of it, say in one paragraph whether that is
     worth it, and what it would cost; the answer may be no.

BEFORE ANY PORTING, SETTLE ONE FACT

DegreeRigidity/SetModels/Degrees.lean imports Mathlib.Computability.TuringDegree and
defines Degree := Antisymmetrization Oracle Reduces. Start/OracleSim.lean imports the
same Mathlib module. Are our Lambda.Oracle development and their Degree the same object
up to unfolding, or is one a wrapper of the other? Put the two definitions side by side
and answer. This decides how much of anything is portable, so do it first and report it
whatever else happens.

WHAT THE BOARD GETS

Open a milestone M26 for this, with one row per absorbed directory, each with
exit_criteria naming the theorem that must end up provable in our namespace. Rows for
directories you have not reached stay TODO_READY; the DegreeRigidity row stays
TODO_NEEDS_DESIGN until you have answered whether it is worth doing.

WHAT NOT TO DO

Do not change lean-toolchain or the Mathlib pin to make their code compile. Adapting
their proofs to our pin is the work; moving our pin to theirs would invalidate 510
modules to import 1275, and the archive is a snapshot, not a dependency we can track.

REPORT

Four paragraphs: the answer to the Degree question, with both definitions quoted; which
directories were absorbed and under what names, with the verbatim terminal statement of
each; what you had to reconstruct rather than adapt, and why; and your paragraph on
whether DegreeRigidity is worth absorbing at all.
