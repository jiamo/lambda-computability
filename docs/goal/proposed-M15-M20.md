# Proposed research queue: M15–M20

Six milestones for the phase after M14, written in the schema of `docs/goal/task-board.yaml`
so that the rows below can be pasted into it directly.  Ranks continue from the current
maximum (950).  `latest_evidence` on a task that has not started points at the evidence of a
prerequisite, as `M14-TQBF-PSPACE-HARD` does; replace it when the task's own note is written.

The six lines are ordered by how much of their prerequisite is already in the library:

| Milestone | Theme | Prerequisites in the library | Character |
|---|---|---|---|
| M15 | Relativization and the barriers | oracle machines, P/NP, PSPACE, TQBF | classical, fully specified |
| M16 | The priority method | `KleenePost`, `OracleJump`, `PostSimple` | classical, method absent from the library |
| M17 | The effective topos and its internal logic | `AsmExRegProj`, `AsmExRegEffective` | classical, long chain |
| M18 | Higher-order computability | `KleeneTwo`, `PCAMorphism`, `ComputableReal` | partly open |
| M19 | Metacomplexity | `LevinKt`, `Kolmogorov*`, circuits, P/NP | current research frontier |
| M20 | Open problems | various | genuinely unsolved |

---

## M15 — Relativization and the barriers

The one barrier theorem the library is fully equipped for: `OracleMachine`,
`OracleUniversal`, `OracleJump` give the machines, `ComplexityClasses` gives P and NP,
`SpaceMachine` gives PSPACE, and `Qbf` is about to give a PSPACE-complete language.

```yaml
  - id: M15-ORACLE-CLASSES
    priority: P1
    status: TODO_READY
    track: theory/complexity
    title: "Relativized complexity classes: P^A, NP^A and PSPACE^A"
    latest_evidence: "docs/goal/evidence/M13-SPACE-MODEL.md"
    open_boundary: ""
    milestone: M15
    depends_on:
      - M13-SPACE-MODEL
    rank: 1000
    exit_criteria:
      - "A polynomial-time machine with an oracle tape is defined, with its query cost, on top of Start/OracleMachine.lean."
      - "Complexity.InP_rel, Complexity.InNP_rel and Complexity.InPSPACE_rel are defined for an arbitrary oracle."
      - "The unrelativized classes are recovered by the empty oracle, and P^A subseteq NP^A subseteq PSPACE^A for every A."
    required_gates:
      - "python3 scripts/goal_state.py validate"
      - "python3 scripts/check_closure.py"
      - "lake build"

  - id: M15-BGS-EQUAL
    priority: P1
    status: TODO_READY
    track: theory/complexity
    title: "An oracle that collapses: P^A = NP^A for A a PSPACE-complete language"
    latest_evidence: "docs/goal/evidence/M13-SAVITCH-SPACE.md"
    open_boundary: ""
    milestone: M15
    depends_on:
      - M15-ORACLE-CLASSES
      - M14-TQBF-PSPACE-HARD
    rank: 1010
    exit_criteria:
      - "A nondeterministic polynomial-time machine with a PSPACE-complete oracle is simulated in polynomial space, using Savitch."
      - "Every language of PSPACE is decided in polynomial time with that oracle by a single query."
      - "Complexity.bgs_equal : P^TQBF = NP^TQBF (= PSPACE)."

  - id: M15-BGS-DIFFERENT
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/complexity
    title: "An oracle that separates: P^B != NP^B by stage-wise diagonalization"
    latest_evidence: "docs/goal/evidence/M13-SPACE-MODEL.md"
    open_boundary: "The construction is by stages against an enumeration of polynomial-time oracle machines; the library has no such enumeration yet, and it is the part to design first."
    milestone: M15
    depends_on:
      - M15-ORACLE-CLASSES
    rank: 1020
    exit_criteria:
      - "Polynomial-time oracle machines are enumerated, with a time bound uniform in the index."
      - "An oracle B is built in stages so that the unary language {1^n : some word of length n lies in B} is in NP^B but not in P^B."
      - "Complexity.bgs_different : P^B != NP^B."

  - id: M15-NO-RELATIVIZING-PROOF
    priority: P1
    status: TODO_READY
    track: theory/complexity
    title: "The relativization barrier: no relativizing argument settles P vs NP"
    latest_evidence: "docs/goal/evidence/M13-SPACE-MODEL.md"
    open_boundary: ""
    milestone: M15
    depends_on:
      - M15-BGS-EQUAL
      - M15-BGS-DIFFERENT
    rank: 1030
    exit_criteria:
      - "A proof technique is called relativizing when its conclusion holds with every oracle attached; this is stated for the pair of statements P = NP and P != NP."
      - "Complexity.no_relativizing_resolution : neither P = NP nor P != NP relativizes."

  - id: M15-TIME-HIERARCHY-REL
    priority: P2
    status: TODO_READY
    track: theory/complexity
    title: "What does relativize: the time hierarchy theorem holds with every oracle"
    latest_evidence: "docs/goal/evidence/M13-SPACE-MODEL.md"
    open_boundary: ""
    milestone: M15
    depends_on:
      - M15-ORACLE-CLASSES
    rank: 1040
    exit_criteria:
      - "The deterministic time hierarchy theorem is proved for machines with an arbitrary oracle, by the same diagonalization."
      - "Together with M15-NO-RELATIVIZING-PROOF this exhibits the line between what relativizes and what cannot."
```

## M16 — The priority method

The largest single gap in the library's recursion theory.  `KleenePost` has the
finite-extension method, `OracleJump` the jump, `PostSimple` simple sets; nothing anywhere
uses a priority construction, and priority arguments are close to absent from the
formalization literature generally.

```yaml
  - id: M16-REQUIREMENT-FRAMEWORK
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/recursion
    title: "Requirements, strategies and the use function: the frame a priority construction runs in"
    latest_evidence: "docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md"
    open_boundary: "The shape of the framework is the design question: what a requirement is, how a strategy owns a witness, and how the use of an oracle computation is read off Start/OracleSim.lean."
    milestone: M16
    depends_on: []
    rank: 1100
    exit_criteria:
      - "The use function of an oracle computation is defined and its monotonicity and the use principle proved."
      - "A requirement is a predicate on the stage-indexed approximation, with a notion of being met and of being injured."
      - "A construction is a stage-indexed sequence of finite approximations, with the enumeration it defines proved c.e."

  - id: M16-FINITE-INJURY
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/recursion
    title: "The finite injury lemma: each requirement is injured finitely often and is met"
    latest_evidence: "docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md"
    open_boundary: ""
    milestone: M16
    depends_on:
      - M16-REQUIREMENT-FRAMEWORK
    rank: 1110
    exit_criteria:
      - "Requirements are linearly ordered by priority and a requirement is injured only by one of higher priority acting."
      - "Each requirement acts finitely often, hence is injured finitely often, hence is met from some stage on."

  - id: M16-FRIEDBERG-MUCHNIK
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/recursion
    title: "Friedberg-Muchnik: two incomparable c.e. degrees, and Post's problem"
    latest_evidence: "docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md"
    open_boundary: ""
    milestone: M16
    depends_on:
      - M16-FINITE-INJURY
    rank: 1120
    exit_criteria:
      - "Two c.e. sets A, B are built so that no oracle machine computes A from B or B from A."
      - "Lambda.friedberg_muchnik : the degrees of A and B are incomparable."
      - "Post's problem is solved: there is a c.e. degree strictly between 0 and 0'."

  - id: M16-SACKS-SPLITTING
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/recursion
    title: "The Sacks splitting theorem"
    latest_evidence: "docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md"
    open_boundary: ""
    milestone: M16
    depends_on:
      - M16-FRIEDBERG-MUCHNIK
    rank: 1130
    exit_criteria:
      - "Every noncomputable c.e. set is the disjoint union of two c.e. sets, neither of which computes it."

  - id: M16-MINIMAL-DEGREE
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/recursion
    title: "A minimal Turing degree, by Spector's tree construction"
    latest_evidence: "docs/goal/evidence/M10-POST-SIMPLE-INCOMPLETE.md"
    open_boundary: "This is not a priority construction but a forcing with perfect trees; it may be cheaper than M16-SACKS-SPLITTING and can be attempted independently, on top of Start/OracleForcing.lean."
    milestone: M16
    depends_on:
      - M16-REQUIREMENT-FRAMEWORK
    rank: 1140
    exit_criteria:
      - "Splitting trees and their properties are defined on top of Start/OracleForcing.lean."
      - "A degree is built that is nonzero and has nothing strictly between it and zero."
```

## M17 — The effective topos and its internal logic

`AsmExRegProj` and `AsmExRegEffective` have exactness over the regular projectives.  The
boundary note of `M12-EXREG-PROJ-EXACT` lists the next four steps; beyond them is the part
that makes the construction worth having, the internal logic.

```yaml
  - id: M17-EXREG-PROJ-REGULAR
    priority: P1
    status: TODO_READY
    track: theory/semantics
    title: "The completion over the regular projectives is a regular category in its own right"
    latest_evidence: "docs/goal/evidence/M12-EXREG-PROJ-EXACT.md"
    open_boundary: ""
    milestone: M17
    depends_on: []
    rank: 1200
    exit_criteria:
      - "Finite limits and image factorizations of the restricted subcategory stay inside it, not merely up to isomorphism."

  - id: M17-EXREG-UNIVERSAL
    priority: P1
    status: TODO_READY
    track: theory/semantics
    title: "The universal property of the completion among exact categories"
    latest_evidence: "docs/goal/evidence/M12-EXREG-PROJ-EXACT.md"
    open_boundary: ""
    milestone: M17
    depends_on:
      - M17-EXREG-PROJ-REGULAR
    rank: 1210
    exit_criteria:
      - "A regular functor out of the assemblies extends to an exact functor out of the completion, uniquely up to isomorphism."

  - id: M17-EFF-TOPOS
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/semantics
    title: "The completion is a topos: a subobject classifier and exponentials"
    latest_evidence: "docs/goal/evidence/M12-EXREG-PROJ-EXACT.md"
    open_boundary: ""
    milestone: M17
    depends_on:
      - M17-EXREG-UNIVERSAL
    rank: 1220
    exit_criteria:
      - "The object of propositions is built and every mono is the pullback of true along a unique characteristic map -- for every mono, unlike Start/AssemblySubobject.lean."
      - "Exponentials exist, so the completion is cartesian closed, hence an elementary topos."

  - id: M17-EFF-IDENTIFY
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/semantics
    title: "The identification with the effective topos"
    latest_evidence: "docs/goal/evidence/M12-EXREG-PROJ-EXACT.md"
    open_boundary: ""
    milestone: M17
    depends_on:
      - M17-EFF-TOPOS
    rank: 1230
    exit_criteria:
      - "The completion over the partitioned assemblies of Kleene's first algebra is identified with Hyland's effective topos."

  - id: M17-INTERNAL-CT
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/semantics
    title: "Church's thesis holds internally: every function on the natural numbers object is computable"
    latest_evidence: "docs/goal/evidence/M12-EXREG-PROJ-EXACT.md"
    open_boundary: "The internal language has to be set up first; this is the design question, and Start/Realizer.lean may already carry part of it."
    milestone: M17
    depends_on:
      - M17-EFF-TOPOS
    rank: 1240
    exit_criteria:
      - "The internal logic of the topos is available, at least for arithmetical formulas."
      - "The internal statement that every f : N -> N has an index is proved."
      - "Excluded middle fails internally, and Markov's principle holds."

  - id: M17-REALIZABILITY-HA
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/semantics
    title: "Kleene's 1945 realizability interprets Heyting arithmetic"
    latest_evidence: "docs/goal/evidence/M10-PCA-KLEENE.md"
    open_boundary: ""
    milestone: M17
    depends_on:
      - M17-INTERNAL-CT
    rank: 1250
    exit_criteria:
      - "Heyting arithmetic is defined, with its deduction relation."
      - "Realizability of a formula is defined and every theorem of HA is realized."
      - "Consequently HA is consistent, and the disjunction and existence properties hold."
```

## M18 — Higher-order computability and computable analysis

`KleeneTwo` gives K2, `PCAMorphism` applicative morphisms, `KleeneNoRetraction` the first
separation, `EffectiveOperation` and `ComputableReal` the first analysis.  From here on the
questions stop being uniformly settled.

```yaml
  - id: M18-KLS
    priority: P1
    status: TODO_READY
    track: theory/computability
    title: "Kreisel-Lacombe-Shoenfield: an effective operation on total computable functions is continuous"
    latest_evidence: "docs/goal/evidence/M11-MYHILL-SHEPHERDSON.md"
    open_boundary: ""
    milestone: M18
    depends_on: []
    rank: 1300
    exit_criteria:
      - "An effective operation on the total computable functions is defined by an index-wise computable map respecting extensional equality."
      - "Every such operation is continuous in the Baire topology, by the Kreisel-Lacombe-Shoenfield argument."

  - id: M18-WEIHRAUCH
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/computability
    title: "Weihrauch reducibility and the first degrees"
    latest_evidence: "docs/goal/evidence/M11-COMPUTABLE-REAL-CONTINUITY.md"
    open_boundary: ""
    milestone: M18
    depends_on: []
    rank: 1310
    exit_criteria:
      - "Multi-valued functions on represented spaces, and Weihrauch reducibility between them, are defined over K2."
      - "The reducibility is a preorder and its degrees form a lattice under the usual operations."
      - "LPO and LLPO are defined and separated."

  - id: M18-EXTENSIONAL-COLLAPSE
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/computability
    title: "The extensional collapse of Kleene's second algebra"
    latest_evidence: "docs/goal/evidence/M11-KLEENE-TWO-PCA.md"
    open_boundary: "Longley's programme; the general theory of extensional collapses of PCAs is not fully settled in the literature, so the task should be scoped to K2 first."
    milestone: M18
    depends_on:
      - M18-KLS
    rank: 1320
    exit_criteria:
      - "The extensional collapse of K2 is constructed and compared with the total continuous functionals."

  - id: M18-PCA-LATTICE
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/computability
    title: "The order of PCAs under applicative morphisms"
    latest_evidence: "docs/goal/evidence/M11-KLEENE-NO-RETRACTION.md"
    open_boundary: "Which PCAs are comparable, and which give equivalent realizability toposes, is only partly known; this task formalizes the order and the separations that are known, and states the open ones."
    milestone: M18
    depends_on: []
    rank: 1330
    exit_criteria:
      - "Applicative morphisms are preordered by existence, and the induced equivalence is defined."
      - "K1 < K2 is proved strict, extending Start/KleeneNoRetraction.lean."
      - "The statement that two PCAs with equivalent realizability toposes are equivalent is either proved or recorded as open."
```

## M19 — Metacomplexity

The library is unusually well placed here: it has time-bounded Kolmogorov complexity
(`LevinKt`), the plain and prefix versions, circuits, and P/NP.  Almost nothing in this
milestone has been formalized anywhere.

```yaml
  - id: M19-SYMMETRY-HARD-HALF
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/kolmogorov
    title: "Symmetry of information, the hard half"
    latest_evidence: "docs/goal/evidence/M6-KOLMOGOROV-CORE.md"
    open_boundary: "Start/KolmogorovCond.lean has the easy half, kolm_le_kolmCond_add. The converse needs the counting argument over the description sets, with the Kraft-Chaitin machine of Start/KCMachine.lean."
    milestone: M19
    depends_on: []
    rank: 1400
    exit_criteria:
      - "K(s, y) >= K(y) + K(s | y) - O(log(min(K s, K y)))."
      - "Together with the easy half this gives the symmetry of information up to a logarithmic term."

  - id: M19-KT-DEFINITIONS
    priority: P1
    status: TODO_READY
    track: theory/kolmogorov
    title: "Time-bounded Kolmogorov complexity K^t and its basic theory"
    latest_evidence: "docs/goal/evidence/M10-LEVIN-KT.md"
    open_boundary: ""
    milestone: M19
    depends_on: []
    rank: 1410
    exit_criteria:
      - "K^t is defined as an instance of Start/DescriptionSystem.lean, with invariance up to a change of machine and a polynomial change of the bound."
      - "K^t decreases in t and is bounded below by K and above by the length plus a constant."
      - "The set of pairs (x, k) with K^t(x) <= k is in NP."

  - id: M19-MCSP
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/complexity
    title: "The minimum circuit size problem"
    latest_evidence: "docs/goal/evidence/M9-COMPLEXITY-CLASSES.md"
    open_boundary: "Whether MCSP is NP-complete is open; the task is to define it, place it in NP, and prove what is known unconditionally."
    milestone: M19
    depends_on:
      - M19-KT-DEFINITIONS
    rank: 1420
    exit_criteria:
      - "MCSP is defined on truth tables using the circuits of Start/PolyCircuit.lean and placed in NP."
      - "The known unconditional consequences of MCSP being easy are proved, or their statements are recorded with an honest boundary."

  - id: M19-OWF-KT
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/complexity
    title: "One-way functions and the average-case hardness of K^t (Liu-Pass)"
    latest_evidence: "docs/goal/evidence/M10-LEVIN-KT.md"
    open_boundary: "Recent research, 2020; the equivalence needs a probabilistic framework the library does not have, so the first half of the task is to decide how much probability to import from Mathlib."
    milestone: M19
    depends_on:
      - M19-KT-DEFINITIONS
      - M19-SYMMETRY-HARD-HALF
    rank: 1430
    exit_criteria:
      - "One-way functions are defined with respect to a polynomial-time adversary and a distribution."
      - "One direction of the Liu-Pass equivalence is proved: if K^t is mildly hard on average then one-way functions exist, or conversely."
```

## M20 — Open problems

The tier where the answer is not known.  A task here succeeds by formalizing the statement
and the known partial results, and by recording honestly what is open; it is not expected to
close the problem.

```yaml
  - id: M20-RANGE-PROPERTY
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/lambda
    title: "Barendregt's range property, and what is known about it"
    latest_evidence: "docs/goal/evidence/M10-LAMBDA-THEORY-LATTICE.md"
    open_boundary: "Open. The range of a lambda-definable function on a lambda-theory is conjectured to be either a singleton or infinite; it is known for beta and for some theories, open in general."
    milestone: M20
    depends_on: []
    rank: 1500
    exit_criteria:
      - "The range property is stated for an arbitrary lambda-theory, on top of Start/LambdaTheory.lean."
      - "It is proved for beta-conversion, by the Boehm-tree argument."
      - "The general case is recorded as open, with the known sufficient conditions stated."

  - id: M20-EASY-TERMS
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/lambda
    title: "Jacopini's theorem: Omega is easy"
    latest_evidence: "docs/goal/evidence/M5-SOLVABILITY.md"
    open_boundary: "Whether every unsolvable term is easy is open; Jacopini's theorem for Omega itself is not."
    milestone: M20
    depends_on: []
    rank: 1510
    exit_criteria:
      - "A term is easy when it can consistently be equated with any closed term; this is defined on top of Start/LambdaTheory.lean."
      - "Omega is proved easy."
      - "The question whether every unsolvable term is easy is recorded as open."

  - id: M20-THEORY-LATTICE-UNCOUNTABLE
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/lambda
    title: "The lattice of lambda-theories is uncountable"
    latest_evidence: "docs/goal/evidence/M10-LAMBDA-THEORY-LATTICE.md"
    open_boundary: ""
    milestone: M20
    depends_on: []
    rank: 1520
    exit_criteria:
      - "An uncountable family of pairwise distinct lambda-theories is built."
      - "The structure of the lattice beyond cardinality is recorded as largely open."

  - id: M20-GANDY
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/computability
    title: "Gandy's theorem: a discrete deterministic mechanical device computes only computable functions"
    latest_evidence: "docs/goal/evidence/M4-CHURCH-TURING-LAMBDA.md"
    open_boundary: "Never formalized, as far as is known. This is the physical form of the Church-Turing thesis, and the one the name of this library refers to; the design question is the formalization of Gandy's four principles."
    milestone: M20
    depends_on: []
    rank: 1530
    exit_criteria:
      - "Gandy machines are defined by the four principles: a form of states, a bound on assembly, local causation, and determinism."
      - "The cellular automata of Start/UniformCA.lean are exhibited as Gandy machines."
      - "Every Gandy machine's state transition is computable, so it computes only computable functions."

  - id: M20-RULE-110
    priority: P2
    status: TODO_NEEDS_DESIGN
    track: theory/computability
    title: "Rule 110 is universal"
    latest_evidence: "docs/goal/evidence/M4-TM2-IMP-PARTREC.md"
    open_boundary: "Cook's proof is long and combinatorial; the task is a serious engineering effort with a fully classical statement."
    milestone: M20
    depends_on: []
    rank: 1540
    exit_criteria:
      - "Rule 110 is defined as an instance of Start/UniformCA.lean."
      - "A cyclic tag system is simulated by it, and cyclic tag systems are proved universal."
```

---

## Notes for whoever schedules these

* **M15 is the cheapest and the most quotable.**  Baker-Gill-Solovay needs only what
  `M14-TQBF-PSPACE-HARD` is about to provide, and its conclusion — that a whole class of
  proof techniques cannot settle P vs NP — is a result the library can state in full.
* **M16 is the biggest methodological gap.**  A finite-injury framework, once built, is
  reusable for a dozen further theorems, and priority arguments are close to unformalized
  anywhere.
* **M17 is the longest chain** but every step is written down already in the boundary note
  of `M12-EXREG-PROJ-EXACT`.
* **M19 is where the library has an advantage nobody else has**: time-bounded Kolmogorov
  complexity, circuits and P/NP in one place.
* **M20 is deliberately not closable.**  Its tasks succeed by stating precisely what is
  known and what is not; `M20-GANDY` is the one that matches the name of the library.
