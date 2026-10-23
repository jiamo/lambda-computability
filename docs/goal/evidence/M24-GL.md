# M24-GL: the provability logic GL

## Big round 2, run 2

Item W13: **advanced** (first exit criterion: soundness half done; completeness open). About
55 minutes used (of 150).

- Lean, `Start/ModalGL.lean`:
  - `ModalGL.Fml` (variables, `⊥`, `→`, `□`), `ModalGL.Fml.neg`;
  - `ModalGL.Provable`: GL as a Hilbert system — `p → (q → p)`,
    `(p → (q → r)) → ((p → q) → (p → r))`, `(¬p → ¬q) → (q → p)`, `K`, Löb's axiom
    `□(□p → p) → □p`, modus ponens, necessitation;
  - `ModalGL.Forces R V w φ`: Kripke semantics;
  - `ModalGL.loeb_valid`: Löb's axiom holds in every finite transitive irreflexive model (the
    converse of a finite strict order is well-founded, `Finite.wellFounded_of_trans_of_irrefl`;
    take a maximal counter-world);
  - **`ModalGL.sound`**: every GL theorem holds at every world of every finite, transitive,
    irreflexive Kripke model;
  - `ModalGL.sound_of_wf`: soundness for every transitive frame whose converse relation is
    well-founded (`ModalGL.loeb_valid_of_wf`); the finite case is a corollary (`ModalGL.wf_of_finite`);
  - **`ModalGL.loeb_frame_iff`**: frame correspondence — Löb's axiom holds on a frame under every
    valuation iff the relation is transitive and its converse is well-founded;
  - `ModalGL.consistent : ¬ Provable .bot`, `ModalGL.not_provable_reflection : ¬ Provable (□⊥ → ⊥)`.
- Completeness tools: `ModalGL.Der` (derivations from hypotheses), the deduction theorem
    `ModalGL.Der.deduction`, `ModalGL.Der.provable`, `Provable.imp_self`, `Provable.trans`,
    `Provable.bot_imp`, `Provable.box_mono`, `Der.mono`, `Provable.dne` (`⊢ ¬¬p → p`),
    `ModalGL.Consistent`, `consistent_neg_of_not_der`, conjunction `Fml.and` with
    `Provable.and_intro`, `and_left`, `and_right`;
  - **`ModalGL.Provable.four`**: GL proves axiom 4, `□p → □□p` (Löb's axiom applied to `p ∧ □p`).
  - `ModalGL.Der.cut`, `ModalGL.Der.box_of` (`Γ ⊢ p` gives `□Γ ⊢ □p`) and **`ModalGL.Der.loeb_rule`**,
    the modal lemma of the completeness proof: if `□ψ, B, □B ⊢ ψ` then `□B ⊢ □ψ`.
  - **`ModalGL.lindenbaum`**: a consistent list extends to a consistent list deciding every
    formula of a given finite list `L`, adding only members of `L` and their negations
    (`consistent_neg_of_inconsistent`); the subformula list `ModalGL.Fml.sub` (`mem_sub_self`,
    `sub_trans`); the canonical relation `ModalGL.CanR` (transitive, irreflexive:
    `CanR.trans`, `CanR.irrefl`); deductive closure and the implication clause of decided
    consistent lists (`mem_of_der`, `imp_mem_iff`).
- Next steps for completeness: the closure of the target formula under subformulas and negation; the canonical model on the maximal
  consistent subsets with `R Γ Δ` iff the boxed formulas of `Γ` and their bodies are in `Δ` and
  some boxed formula of `Δ` is not in `Γ` (finite, transitive, irreflexive); the truth lemma.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` (`M24-GL-axioms.txt`).
- First missing lemma (completeness, by the finite canonical model over the subformulas):
  `theorem ModalGL.complete {φ : ModalGL.Fml} (h : ∀ (W : Type) [Finite W] (R : W → W → Prop), (∀ a b c, R a b → R b c → R a c) → (∀ a, ¬ R a a) → ∀ (V : W → ℕ → Prop) (w : W), ModalGL.Forces R V w φ) : ModalGL.Provable φ`.
  The second exit criterion (arithmetical soundness for PA from M24-GODEL2-ARITH) is not started.

## Big round 2, run 3

Item W13: the first exit criterion is met. `Start/ModalGLComplete.lean`:

* `ModalGL.CanWorld L` — finite canonical model on a list `L`: consistent finite sets inside
  `L ∪ ¬L` that decide every member of `L` (finite: they inject into the powerset of the closure);
  accessibility `ModalGL.canRel` = `ModalGL.CanR` (transitive, irreflexive), valuation
  `ModalGL.canVal`.
* **`ModalGL.truth`** — truth lemma for subformula-closed `L`.  Box case: if `□a ∉ w`, then
  `¬a, □a, B, □B` (with `B` the bodies of the boxed members of `w`) is consistent, since
  otherwise `ModalGL.Der.loeb_rule` gives `□B ⊢ □a` and so `□a ∈ w`; Lindenbaum's lemma extends
  it to a world `v` with `CanR w v` (witness `□a`) and `a ∉ v`.
* **`ModalGL.complete`** (the former first missing lemma) and **`ModalGL.provable_iff_valid`**:
  `Provable φ ↔` `φ` is forced at every world of every finite transitive irreflexive model.

Remaining: the second exit criterion (arithmetical soundness of GL for PA), which needs the
provability predicate of `M24-GODEL2-ARITH` (TODO_READY; now listed as a dependency).  First
missing lemma: `theorem ModalGL.arith_sound {φ : ModalGL.Fml} (h : ModalGL.Provable φ) (σ : ℕ → PA sentence) : PA ⊢ ModalGL.realize σ φ`,
with `realize` interpreting `□` by the PA provability predicate of `M24-GODEL2-ARITH`; it needs
the Hilbert–Bernays–Löb derivability conditions and formalized Löb's theorem in PA.

## Big round 2, run 6 (restoration after the move to a new project)

The big round 2 sections of this note (runs 1 to 3) were lost with the old project and were recreated
in run 6 from its command logs, which record the text that was appended; the Lean modules they cite
were restored from the old project's export, rebuilt with `lake build --wfail`, and their axioms
regenerated (`docs/goal/evidence/*-axioms.txt`, section "Big round 2, run 6").
