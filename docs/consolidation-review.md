# Consolidation review: which modules should be merged?

The research queue (`docs/goal/goal-prompt.md`) carries one standing item that had never been
looked at in detail: *"replacing families of near-duplicate modules by a single general interface,
where doing so makes the library smaller"*.  This note is that investigation.  It reports what was
measured, what turned out **not** to be duplicated, the one place where duplication is real, and a
concrete, bounded plan for it.  The plan is also on the task board
(`M11-REWRITING-INTERFACE`, `M11-REWRITING-MIGRATE`, both `TODO_READY`).

## Method

Three passes over the 347 modules under `Start/`:

1. **Name-level.** Every top-level `def`/`theorem`/`structure`/`inductive`, qualified by the
   enclosing `namespace`, collected per file and grouped.  Only 8 fully qualified names occur in
   two files at all, and each is a section-local or `protected` helper (for example
   `LambdaPi.Lookup.det` in `LambdaPiUnique.lean` and `LambdaPiTypeUnique.lean`); there is **no
   public declaration defined twice**.
2. **Family-level.** Modules grouped by name prefix, and the docstring of each member of a family
   read, to see whether the members repeat one construction or genuinely extend it.
3. **Theory-level.** A search for the recurring mathematical patterns — reflexive–transitive
   closures, parallel reduction, the diamond property, the strip lemma, commutation, postponement,
   Newman's lemma — across all files, to find theory that is re-derived rather than reused.

## What is *not* duplicated

Two families look like duplication from the file names and are not.

**Realizability: `Assembly*` (12 modules), `Modest*` (7), `PER*` (3).**  The three layers are
related by results, not by copied proofs.  `ModestEquiv.lean` proves `Realizability.perEquivModest`
— the PERs *are* the modest assemblies — and the PER-level results are transported along it
(`PERNNO.lean` transports the natural numbers object, `ModestCcc.lean` transports the closed
structure), while the `Modest*` modules carry real extra content: that the construction in
`Asm(A)` lands in the full subcategory (modesty of the exponential, of the image, of the natural
numbers object over an algebra with more than one element).  Merging them would delete theorems,
not duplication.  **Recommendation: leave as is.**

**Algorithmic information theory: `Kolmogorov*` (9), `KCMachine`, `DescriptionSystem`,
`PlainVsPrefix`, `KolmogorovRepresentation`.**  This family has *already* been consolidated, and is
the model the rest of the library should imitate: `DescriptionSystem.lean` isolates the single
construction `K x = inf {|p| : p describes x}` from a type of programs, a size and an output
relation, and `KolmogorovMachines.lean` exhibits plain, relative, conditional, prefix, locally
nameless and time-bounded complexity as instances, so that invariance and subadditivity are proved
once.  **Recommendation: leave as is; cite as the pattern to follow.**

## What is duplicated: abstract rewriting

Every calculus in the library re-derives the same rewriting theory over its own syntax.  The
measurements:

- **Fourteen hand-rolled reflexive–transitive closures**, each with its own `refl`/`tail`
  constructors and its own `trans`, `head`, `single` lemmas: `Lambda.reduces` (`Reduction.lean`),
  `etaReduces` (`LambdaEta.lean`), `betaEtaReduces`, `betaEtaTStar`, `betaEtaConv`
  (`LambdaBetaEta.lean`), `Red`, `Conv`, `Pars` (`LambdaPi.lean`), `EtaRed`, `BetaEtaRed`,
  `BetaEtaConv` (`LambdaPiEta.lean`), `reduces` (`SystemT.lean`), `Conv` (`Stlc.lean`),
  `reducesIn` (`ReducesIn.lean`), `Lambda.reduces_correct` (`Arithmetic.lean`).
- **Four parallel-reduction/diamond/strip developments**: `Lambda.step_p` with
  `step_p_diamond`, `strip_lemma`, `confluence_theorem` (`Reduction.lean`, 329 lines);
  `LambdaPi.Par` with `Par.triangle`, `Par.diamond`, `Pars.strip`, `church_rosser`
  (`LambdaPi.lean`, of 737 lines); `SystemTConfluence.lean` (373 lines, diamond plus Newman);
  `SystemFCConfluence.lean` (324 lines).  `GrossKnuth.lean` adds a fifth, small one.
- **Hindley–Rosen commutation, twice**: for the untyped calculus in `LambdaBetaEta.lean` (403
  lines) and for `λΠ` on erased terms in `LambdaPiEtaConfluent.lean` (638 lines).
- **η-postponement, twice**: `LambdaEtaPostpone.lean` (247 lines) and
  `LambdaPiEtaPostpone.lean` (473 lines).  The second was written by transporting the first
  argument by hand, which is what made the duplication visible.

The syntax-specific content of these files is irreducible — the parallel-reduction relation, the
substitution lemmas, the local diagrams — but the *combinators* on top of it are not.  The
following are statements about an arbitrary binary relation and are currently proved between two
and five times each:

| Generic statement | Occurrences |
|---|---|
| closure: `trans`, `head`, `single`, splitting a nonempty reduction at the head | 14 |
| diamond ⟹ strip lemma ⟹ confluence of the closure | 4 |
| confluence ⟹ conversion is joinability | 4 |
| strong commutation ⟹ commutation of the closures (Hindley) | 2 |
| two confluent commuting relations ⟹ their union is confluent (Hindley–Rosen) | 2 |
| local postponement ⟹ postponement of the closures | 2 |
| a relation that decreases a `ℕ`-valued measure terminates | 3 |
| termination of one relation plus postponement ⟹ termination of the union | 1 (would be 2) |
| local confluence plus termination ⟹ confluence (Newman) | 1 |

## Proposal

Add one module, `Start/Rewriting.lean`, developing the above for `r : α → α → Prop`:

- `Rewriting.Star r`, `Rewriting.Conv r`, with the closure API;
- `Diamond`, `Confluent`, `Commute`, `StronglyCommute`, `Postpones`, `Terminating`;
- `confluent_of_diamond`, `conv_iff_join_of_confluent`, `commute_of_stronglyCommute`,
  `confluent_union_of_commute` (Hindley–Rosen), `postpone_star_of_postpone_step`,
  `terminating_of_measure`, `terminating_union_of_postpone`, `confluent_of_newman`.

Each calculus then keeps its own inductive closure and adds a single bridging lemma
`Red t u ↔ Star Step t u`, after which the generic results apply.  Nothing needs to be restated,
and no existing theorem name has to change.

Two board entries carry this:

- `M11-REWRITING-INTERFACE` — write `Start/Rewriting.lean` and prove the generic lemmas, with no
  changes to any existing module.  Self-contained and independently verifiable.
- `M11-REWRITING-MIGRATE` — migrate the clients one at a time, in the order
  `LambdaPiEtaConfluent`, `LambdaPiEtaPostpone`, `LambdaBetaEta`, `LambdaEtaPostpone`,
  `SystemTConfluence`, `SystemFCConfluence`, `Reduction`, `LambdaPi`, keeping every public name
  and every gate green after each step.

An honest estimate of the saving, from the counts above: of the roughly 3 500 lines in the files
listed, something like 500–700 lines are instances of the nine generic statements.  The point is
less the line count than the next calculus: with the interface in place, adding η, or a new
system, costs only the local diagrams.

## Smaller observations

- `Start/GrossKnuth.lean` (80 lines) is a third parallel-reduction strategy for the untyped
  calculus, on top of `Reduction.lean` and the Gross–Knuth development; after the migration it
  should be checked whether it still needs its own diamond argument.
- `Start/ReducesIn.lean` (89 lines) is a *clocked* closure, `reducesIn n`, and is genuinely a
  different relation (it counts steps); it belongs in the generic layer as `Star`-with-a-counter
  if that turns out to be needed by more than one client, and otherwise should stay where it is.
- `Start/Reduction.lean` still carries the Church numerals, the combinators `I`, `K`, `S`,
  `pair`/`fst`/`snd` and `LambdaComputable` next to the confluence proof — three unrelated
  concerns in one file inherited from the original `Start/Basic.lean` split.  Splitting it is
  independent of the rewriting interface and would make the migration above smaller.
