# Proposed milestone M25 — the type systems of functional languages

The library already contains most of the *theory* a functional language's type system rests
on: `Start/Stlc.lean` and its cartesian closed semantics, nine `SystemF*` modules with
parametricity (`Start/SystemFParam.lean`) and a PER model (`Start/PERSystemF.lean`), System T
with a denotational semantics, forty `LambdaPi*` modules with a *bidirectional type inference
algorithm* that is proved sound, complete and decidable (`Start/LambdaPiInfer.lean`),
intersection and multi types, domain models with full abstraction results, and the Krivine
machine with time and space cost models.

What it does not contain is the part a programming language actually ships:

| missing | occurrences in `Start/` |
|---|---|
| Hindley–Milner, algorithm W, principal types | 0 |
| first-order unification | 0 |
| call-by-value and call-by-need evaluation | 0 |
| call-by-push-value | 0 |
| type classes, row polymorphism, records | 0 |
| monads and algebraic effects | 0 |

Two of these are structural rather than cosmetic.

**Hindley–Milner is absent and System F does not replace it.**  System F is stronger but its
inference is undecidable; what makes ML and Haskell work is that HM has complete inference
*and principal types*.  That theorem is not in the library in any form.

**Only one evaluation order is covered.**  `Start/Krivine.lean` says so in its own header: the
machine is the standard call-by-name one.  ML is call-by-value, Haskell is call-by-need with
thunk update, and `Start/KrivineHeap.lean`'s sharing is a space measure rather than a
call-by-need semantics.  So the invariance programme of M11–M12, which is the library's most
implementation-relevant work, currently speaks about the evaluation order that no mainstream
functional language uses.

`cslib`, already a dependency, supplies System F<: with preservation and progress
(`Cslib/Languages/LambdaCalculus/LocallyNameless/Fsub/Safety.lean`); no module of `Start/`
references it.  Re-proving soundness would be waste, so the F<: row below goes past it to the
theorem that belongs in this library rather than in a PL one.

## Rows

Ranks continue from the current maximum, 2280.

```yaml
  - id: M25-UNIFICATION
    priority: P1
    status: TODO_READY
    track: theory/types
    title: "First-order unification and the most general unifier"
    latest_evidence: "docs/goal/evidence/M7-STLC-SN.md"
    open_boundary: ""
    milestone: M25
    depends_on: []
    rank: 2300
    exit_criteria:
      - "Type terms over a signature with variables, substitutions and their composition."
      - "A unification algorithm, with termination proved by the standard measure."
      - "Soundness: the result is a unifier. Completeness: it is most general, every unifier factors through it."
      - "Failure is correct: when the algorithm fails there is no unifier."
    required_gates:
      - "python3 scripts/goal_state.py validate"
      - "python3 scripts/check_closure.py"
      - "lake build"

  - id: M25-HM-TYPING
    priority: P1
    status: TODO_READY
    track: theory/types
    title: "The Hindley-Milner type system: monotypes, schemes and let-generalization"
    latest_evidence: "docs/goal/evidence/M9-SYSTEM-F.md"
    open_boundary: ""
    milestone: M25
    depends_on: []
    rank: 2310
    exit_criteria:
      - "Monotypes, type schemes, instantiation and generalization relative to a context."
      - "The typing judgement, with the let rule that generalizes and the variable rule that instantiates."
      - "Weakening, substitution and subject reduction."
      - "Every HM-typable term is typable in System F, by erasing the schemes to prefixes of universal quantifiers."

  - id: M25-HM-ALGORITHM-W
    priority: P1
    status: TODO_READY
    track: theory/types
    title: "Algorithm W, and its soundness"
    latest_evidence: "docs/goal/evidence/M9-SYSTEM-F.md"
    open_boundary: ""
    milestone: M25
    depends_on:
      - M25-UNIFICATION
      - M25-HM-TYPING
    rank: 2320
    exit_criteria:
      - "Algorithm W as a function returning a substitution and a type, or failure."
      - "Soundness: when it returns, the substituted context types the term with the returned type."

  - id: M25-HM-PRINCIPAL
    priority: P1
    status: TODO_READY
    track: theory/types
    title: "Principal types: algorithm W is complete, and typability is decidable"
    latest_evidence: "docs/goal/evidence/M9-SYSTEM-F.md"
    open_boundary: ""
    milestone: M25
    depends_on:
      - M25-HM-ALGORITHM-W
    rank: 2330
    exit_criteria:
      - "Completeness: every typing of a term is an instance of the one W computes."
      - "Hence a typable term has a principal type, and W computes it."
      - "W fails exactly on the untypable terms, so HM typability is decidable -- the property System F lacks."

  - id: M25-CBV-MACHINE
    priority: P1
    status: TODO_READY
    track: theory/semantics
    title: "Call-by-value: an abstract machine, and its simulation"
    latest_evidence: "docs/goal/evidence/M11-KRIVINE-MACHINE.md"
    open_boundary: ""
    milestone: M25
    depends_on: []
    rank: 2340
    exit_criteria:
      - "Call-by-value reduction on the untyped terms of Start/Reduction.lean, with values and evaluation contexts."
      - "A CEK-style machine with environments and a continuation stack."
      - "Bidirectional simulation against call-by-value reduction, in the shape of Start/KrivineDecode.lean."

  - id: M25-CBV-COST
    priority: P1
    status: TODO_READY
    track: theory/complexity
    title: "The call-by-value cost model"
    latest_evidence: "docs/goal/evidence/M11-KRIVINE-INVARIANCE.md"
    open_boundary: ""
    milestone: M25
    depends_on:
      - M25-CBV-MACHINE
    rank: 2350
    exit_criteria:
      - "The number of machine transitions is polynomially related to the number of call-by-value steps."
      - "One transition is realized by a tape program, through Complexity.Space.Realizes of Start/SpaceCompile.lean."
      - "So the number of call-by-value beta steps is a reasonable time cost model, as it is for call-by-name."

  - id: M25-CBNEED-MACHINE
    priority: P1
    status: TODO_READY
    track: theory/semantics
    title: "Call-by-need: thunks, update, and the sharing that makes laziness lazy"
    latest_evidence: "docs/goal/evidence/M12-KRIVINE-SPACE-LIVE.md"
    open_boundary: ""
    milestone: M25
    depends_on: []
    rank: 2360
    exit_criteria:
      - "A call-by-need machine whose heap cells are thunks, overwritten by their value when first forced."
      - "The sharing is semantic, not only a space measure: a thunk forced twice is evaluated once, and this is proved."
      - "The machine computes the same weak head normal forms as the call-by-name machine of Start/Krivine.lean."

  - id: M25-CBNEED-COST
    priority: P2
    status: TODO_READY
    track: theory/complexity
    title: "What laziness costs, and what it saves"
    latest_evidence: "docs/goal/evidence/M11-KRIVINE-INVARIANCE.md"
    open_boundary: ""
    milestone: M25
    depends_on:
      - M25-CBNEED-MACHINE
    rank: 2370
    exit_criteria:
      - "A time cost model for call-by-need, in the form of M11-KRIVINE-INVARIANCE."
      - "A family of terms on which call-by-need takes exponentially fewer steps than call-by-name, and the proof that it never takes more."

  - id: M25-CBPV
    priority: P2
    status: TODO_READY
    track: theory/types
    title: "Call-by-push-value: one calculus containing both evaluation orders"
    latest_evidence: "docs/goal/evidence/M9-SYSTEM-F.md"
    open_boundary: ""
    milestone: M25
    depends_on:
      - M25-CBV-MACHINE
    rank: 2380
    exit_criteria:
      - "Value types and computation types, with thunk and force, and the typing judgement."
      - "The call-by-value translation and the call-by-name translation, each preserving typing."
      - "Each translation preserves reduction, so the two evaluation orders are two fragments of one calculus."

  - id: M25-FSUB-UNDECIDABLE
    priority: P1
    status: TODO_NEEDS_DESIGN
    track: theory/types
    title: "Subtyping in full System F-sub is undecidable (Pierce)"
    latest_evidence: "docs/goal/evidence/M4-TM2-IMP-PARTREC.md"
    open_boundary: "The design question is which undecidable problem to reduce from and how to encode its configurations as subtyping judgements. cslib supplies the calculus and its soundness, so none of that has to be rebuilt."
    milestone: M25
    depends_on: []
    rank: 2390
    exit_criteria:
      - "The subtyping relation of cslib's Fsub is connected to a decision problem on words."
      - "A two-counter machine, or another undecidable problem already in this library, is reduced to it."
      - "Subtyping in full F-sub is proved undecidable, hence type checking is."
      - "The decidable kernel fragment is identified, and the row records that it is where real languages live."
```

## Why these rows and not others

* **Hindley–Milner first**, because the principal types theorem is what the library's existing
  type theory is missing in kind, not merely in coverage: every other system here is checked,
  not inferred, and `Start/LambdaPiInfer.lean` is bidirectional rather than inferring.
* **The two evaluation orders next**, because the invariance programme is the library's most
  distinctive complexity work and it currently covers call-by-name alone.  `M25-CBNEED-COST`
  is where it gets interesting: laziness is supposed to pay off, and the row asks for the
  family of terms where it does and the proof that it never loses.
* **F<: undecidability last and separately.**  cslib already proves preservation and progress,
  so soundness is not worth redoing.  Pierce's theorem is: it is a famous negative result about
  a type system real languages took seriously, and it is proved with exactly the undecidability
  machinery this library has and a PL library would not.
