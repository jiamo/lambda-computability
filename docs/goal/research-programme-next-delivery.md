Work in this SAME project, continuing from the completed M26 absorption.

THE NEXT OBJECTIVE: BUILD NEW FORMAL THEORY

You have already done substantial absorption work. The next stage is original
formalization work inside this library: new constructions, machine compilers,
normalization arguments, semantic models and priority proofs. Use the imported
results as foundations and connect them to the library's existing theory.

Give type theory and computational cost models equal priority. Independent
tracks below may advance together; a difficult machine compiler must not stop
all type-theoretic work. Within each track, respect actual dependencies. Carry
substantive proofs as far as they hold, recording precisely where each stops.

"Original" here means new definitions, constructions and checked proofs for
this project. Distinguish classical mathematical results from new interfaces,
quantitative refinements and consequences established by combining them here.

PRESERVE THE FOUNDATION

- Keep Lean v4.33.0, Mathlib v4.33.0 and the existing dependency pins unchanged.
- Keep absorbed results attributed to openai/math and preserve NOTICE.
- Reuse existing syntax, typing, substitution, machine and category interfaces.
- Preserve public statements; provide proved compatibility maps for necessary
  refactors. Keep every new ordinary module in Start.lean's closure and register
  its terminal result in Start/Capstones.lean.
- No sorry, admit, new axioms, or a structure field containing the theorem that
  the construction is supposed to establish.

TRACK A — TYPE THEORY: THE CUBE, NORMALIZATION, AND INTENSIONAL IDENTITY

A1. Finish M23-PTS using the absorbed PureTypeSystem framework.

Define all eight corners of the lambda cube through one parameterized family
of specifications. Prove the typing/substitution facts needed for its instances
and the inclusions induced by adding product rules. Relate the existing lambda-Pi
and System F developments to their corners by actual derivation translations.

SystemF.lean is Curry-style: its terms have erased type abstractions and type
annotations. Build a derivation-directed elaboration into annotated PTS terms,
with typing preservation and an erasure theorem. A type-name correspondence or
syntax-only map does not discharge this obligation. Preserve LambdaPiSN as an
independent result unless a genuinely independent normalization route replaces it.

A2. Close M23-FOMEGA and M23-COC-SN.

Construct System F-omega's kinds, type operators and their substitution/kinding
theory, or their equivalent presentation in the cube. Prove the normalization
facts needed for type-level computation and for typable terms. Then prove strong
normalization for the Calculus of Constructions corner of the same framework.

The generic weak_implies_strong theorem does not supply its own hypothesis.
Develop the missing logical-relations/candidate interpretation, fundamental
lemma or an independent weak-normalization proof. The final SN theorem must be
unconditional for well-typed terms; assuming system-wide WN is not completion.

A3. Close M23-HURKENS.

Give the actual sorts, axioms and product rules of System U-, build Hurkens'
term, and check its typing as a closed inhabitant of the internal type
"forall A : *, A". This is an object-theory inconsistency theorem, not a claim
of False in Lean's metatheory. The target type cannot be added as an axiom.
Use it to state precisely which normalization/consistency guarantees fail.

A4. Carry M23-ID-TYPES -> M23-GROUPOID-MODEL -> M23-UIP-INDEPENDENT.

Add an identity-type structure to the existing CwA interface: formation,
reflexivity, J, its computation rule, and stability under substitution. Construct
the Hofmann-Streicher groupoid model with the dependent products and coherence
needed to validate those rules. Reuse the existing categorical machinery.
Exercise the same identity-type interface on a set-based model as well, so
the UIP and non-UIP cases are validated through one formal contract.

Exhibit a concrete nontrivial loop, for example in a one-object groupoid with
the automorphisms of Bool, and prove failure of internal UIP. Prove the semantic
soundness needed to conclude non-derivability from the stated object-theory
rules. Two distinct groupoid arrows alone are not a completed type-theoretic
countermodel. Do not confuse internal identity with Lean's proof-irrelevant Eq.

TRACK B — SPACE: CONCRETE COMPILERS AND A REASONABLE LAMBDA COST MODEL

B1. Build concrete translations between ExactDerandomization.Machine and
Complexity.Space.Machine.

Account for multiple two-sided work tapes, multiple read-only input heads,
end markers, control states, acceptance and rejection. Prove a source-step
simulation by finite target runs with a space bound on EVERY intermediate
configuration, including initialization, scans, counters and scratch storage.

Aim for a uniform compiler on finite transition descriptions with a bound
C_M * (s + log2(n + 2) + 1), making every parameter explicit. Reuse SpaceCompile
and SpaceProg for run-level reasoning. Realizes already exists: the missing
contribution is concrete finite control discharging its obligations, not another
record assuming that a simulator exists. Do not evaluate an arbitrary source
transition for free inside one target step.

B2. Handle the reverse direction and its halting mismatch.

The host DSPACE definition is bounded-space acceptance by a possibly looping
recognizer. Upstream L requires a decider. Implement the configuration bound
and clock/cycle argument needed to turn the former into the latter at logarithmic
space, with correctness and counter-storage bounds. Use a computable explicit
logarithmic budget rather than silently consulting an arbitrary space oracle.

B3. Prove the exact host-model transfer theorems, for every binary language A:

  A in ExactDerandomization.L <-> Complexity.Space.LOGSPACE A
  A in ExactDerandomization.RL <-> Complexity.Space.LOGSPACE A
  A in ExactDerandomization.BPL <-> Complexity.Space.LOGSPACE A

The first equivalence must come from simulations of the existing definitions;
the next two may use the absorbed equality. Do not redefine LOGSPACE or alias it
to the upstream class. Expose the machine-level witnesses and quantitative
bounds, so this interface can be reused beyond this single equality.

B4. Close M14-KRIVINE-SPACE-CLASS with an actual tape implementation.

Implement all transitions of the shared Krivine machine and its garbage
collection on the binary encoding, including allocation, address lookup,
environment traversal, stack updates and relocation of live pointers.
KrivineCobBin currently supplies only a width/stack-indexed stack-pop pass;
it is not a uniform implementation of the entire collected machine.

Give one finite program that handles varying widths and stack lengths, prove
its execution on reachable encodings, and instantiate the existing Realizes
or Prog.realizes_loop theorem. Account for GC workspace as well as checkpoint
states. The existing encoding estimate budgets code-table size, stack and live
heap cells; do not replace that whole budget by heap-only gpeak without proof.

The terminal result must place the decided language in host DSPACE with an
explicit O(S log(S + 2)) bound, or the rigorously justified stronger bound,
where S states exactly which code, stack, heap and initialization data count.

B5. Carry M14-SPACE-REASONABLE: a host-machine-to-lambda compiler and the
space analysis of its collected Krivine execution.

Specify program and input encodings, the acceptance Boolean and the treatment
of read-only input. Prove simulation and a polynomial space overhead without
first bounding space by total runtime. Combine both directions into a genuine
space-invariance theorem for a precisely defined lambda evaluation model.

Do not infer exact lambda LOGSPACE from O(S log S) or polynomial overheads.
Count immutable code, input, stack and live data honestly. If input retention
prevents a sublinear claim, prove the correct polynomial-space theorem and
identify the separate read-only-input construction needed for a sharper one.

TRACK C — RECURSION THEORY: AN ACTUAL FINITE-INJURY CONSTRUCTION

Close M16-FRIEDBERG-MUCHNIK. Construct two c.e. sets A and B, their effective
stage approximations, priorities, restraints, witnesses and injury rules.
Prove finite injury and that every requirement is eventually satisfied; then
prove neither characteristic oracle is Turing reducible to the other and
derive a c.e. degree strictly between zero and the halting degree.
The stage construction must use finite approximations and bounded simulation,
not an oracle for the limit sets whose effective enumerability it must prove.

Instantiate the existing requirements/finite-injury framework with this
concrete strategy. A theorem about an arbitrary strategy assumed to meet all
requirements is not the construction. The imported rigidity/forcing library
does not replace the missing priority argument. Close its existing DONE_WEAK
framework rows only when their concrete obligations are actually discharged.

Afterwards continue with M16-SACKS-SPLITTING. The perfect-tree route of
M16-MINIMAL-DEGREE is an independent alternative if it yields a concrete closed
construction sooner; name the selected route and keep its obligations explicit.

TRACK D — ALGORITHMIC INFORMATION: COUNTING AND THE CORRECT SYMMETRY LAW

Work on M19-SYMMETRY-HARD-HALF, beginning with M19-DESCRIPTION-COST-AUDIT.
kolm and kolmCond use Lambda.size, not binary program length. Prove the finite
counting/encoding bounds required by the intended information inequality.
Do not silently apply a binary-string counting theorem to raw syntax size.

Develop the enumeration, counting and conditional decoding argument needed for
the hard half. Use the existing Kraft-Chaitin/universal prefix machinery where
appropriate and state every additive constant and logarithmic correction.
Prove the strongest justified theorem for the actual measure. If the board's
claimed error term is too strong, demonstrate the obstruction with a proved
bound or counterexample, state the corrected claim precisely, and separately
establish the bit-description version with rigorous comparison maps.

Keep the existing complexity functions intact. An arbitrary polynomial error
is not the logarithmic symmetry theorem. A justified correction of a faulty
quantitative target is substantive research; an unproved assertion is not.

TRACK E — CIRCUITS AND TIME MODELS

Build the missing connection between explicit polynomial-time tape machines
and the library's Cobham-based P. Implement the needed compilation and
polynomial bounds; computability alone is not polynomial-time equivalence.

Then integrate DepthThree with the host circuit theory. State the basis,
fan-in, depth and size measures explicitly. The upstream circuit is unbounded
fan-in OR/AND/OR; the host binary-gate representation cannot be identified with
it while pretending depth remains unchanged. Add a suitable reusable circuit
interface if needed and prove the precise size/depth-preserving translations.

The payoff is a language in the HOST P class with the genuine upstream
depth-three lower bound stated through a host-compatible circuit interface,
and its relationship to PolyCircuit/UniformCircuit. Preserve the nonuniform
strength of the original lower bound.

TRACK F — REALIZABILITY AND SEMANTICS

Carry M17-EXREG-PROJ-REGULAR -> M17-EXREG-UNIVERSAL -> M17-EFF-TOPOS.
Construct exponentials and a subobject classifier with the characteristic-map
property for every mono, and identify the resulting effective topos through
the existing assembly/exact-completion development.

Only then advance M17-INTERNAL-CT: provide enough internal arithmetic logic
to prove that every internal N -> N function has an index, together with the
specified Markov/failed-excluded-middle results. Claims about the metatheory's
functions do not establish an internal Church's thesis theorem.

TRACK G — GANDY: A FOUNDATIONAL RESEARCH TARGET

Take up M20-GANDY as the programme's flagship exploration. Use Gandy's 1980
"Church's Thesis and Principles for Mechanisms" as the primary specification:
https://cse.buffalo.edu/~rapaport/Papers/Papers.by.Others/gandy80.pdf

Formalize the structural description, limitation of hierarchy, unique
reassembly and local-causation principles faithfully, including atom-renaming
invariance and the required finite bounds. Explain exactly how the chosen
Lean definitions correspond to the principles in the paper.

Code the ambient finite structural universe effectively, and prove that a
partial recursive operation agrees with global evolution on admissible codes,
respecting atom renaming where appropriate. Do not assume the admissible-state
class itself is decidable merely to make the simulation easy.
Computability of that transition must be a conclusion, not a field of the
mechanism structure. State any effective-presentation requirement explicitly
and justify it without hiding an oracle. Connect the resulting simulation to
the library's Church-Turing equivalence.

Exercise the framework on concrete mechanisms. A restricted cellular-automaton
case is a useful first milestone, but does not by itself establish the full
Gandy theorem. If the full axiomatization is not reached, report the exact
principle or representation bridge still missing. This is an independent
research line; it must not delay already reachable type/cost-model results.

EXECUTION AND TASK BOARD

Prioritize A1/A2 and B1/B3 as the two main lines of the next delivery. A4,
Track C and Track D are independent research branches you may advance when a
main line reaches a precisely identified obstruction. Tracks E and F are the
next research horizon; G is the foundational flagship exploration. These are
not permission to replace unfinished central results
with more definitions.

Reuse the existing M14/M16/M17/M19/M23 task IDs. Put genuinely new model-transfer
work under M27: SPACE-MODEL-COMPILE, SPACE-MODEL-TOTALIZE, LOGSPACE-TRANSFER,
POLYTIME-MODEL-EQUIV and DEPTH3-HOST. The description-cost audit belongs to
M19, before M19-SYMMETRY-HARD-HALF. Do not duplicate
tasks or reopen already proved M26 absorption results. Preserve local tooling
and delivery-record rows if present. This programme authorizes independent
tracks to advance without waiting for every earlier global-queue milestone.

Each new interface should be exercised by its intended concrete construction.
Do not spend the delivery only writing a plan, renaming imported modules or
reporting that the work is large. Pursue actual proofs. When blocked, state the
first missing lemma or construction exactly, record it and continue an
independent ready branch. Do not upgrade DONE_WEAK to DONE_STRONG to meet a
quota; record which central objectives remain open.

VERIFY AND DELIVER

In your Aristotle workspace, run lake build and the manifest, sorry, closure
and task-board checks. Check terminal axioms; import and register all new
modules. Keep transport attachments, credentials and scratch files outside
the delivered library. Do not weaken a gate to make a delivery pass.

Commit first, then create the archive with exactly:

scripts/pack_gate.sh HEAD && git archive --format=tar.gz HEAD -o delivery.tar.gz

REPORT

For each advanced track give its furthest verbatim terminal statement, the
actual constructed witness/model/strategy/compiler, and the main new proof
idea. State what is classical, what formalization/interface is new here, the
exact remaining boundary, and the evidence for its status. Include the exact
packaging command, delivered commit and gate outputs. A definitions-only
delivery must be described as such, not as closure of the research objective.
