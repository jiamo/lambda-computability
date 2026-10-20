# M25-FSUB-UNDECIDABLE — undecidability of subtyping in full F<: (round 5: F1 and design F2)

Module: `Start/FsubGhelli.lean` (`lake build --wfail`; axioms in
`M25-FSUB-UNDECIDABLE-axioms.txt`).

## F1. Ghelli's divergence (proved)

The algorithm for full F<: reduces goals `Γ ⊢ S <: T`: a variable on the left is promoted to its
bound, and `∀X<:S₁.S₂ <: ∀X<:T₁.T₂` reduces to `T₁ <: S₁` and `Γ, X<:T₁ ⊢ S₂ <: T₂`.

* `FsubGhelli.AlgStep` — the goal-reduction step as a relation (goal ⟶ each subgoal), on de Bruijn
  types `FsubGhelli.Ty` (`top`, `var`, `all`).
* `FsubGhelli.ghelliGoal` — `α₀ <: ∀α₁<:Top. ¬(∀α₂<:α₁. ¬α₂) ⊢ α₀ <: ∀α₁<:α₀. ¬α₁`, with
  `¬S = ∀γ<:S. γ`.
* `FsubGhelli.cycle_step k : TransGen AlgStep (H k) (H (k+1))` — the recurring goal
  `H k = (α<:α)ᵏ, α₀<:T ⊢ T <: ∀α₁<:α. ¬α₁` reappears after `k + 4` steps (body of `∀`, bound of
  `¬`, then `k + 2` promotions back to `T`).
* `FsubGhelli.ghelli_chain` — an infinite chain of goal reductions from Ghelli's goal.
* **`FsubGhelli.ghelli_not_acc : ¬ Acc (fun g' g => AlgStep g g') ghelliGoal`** — the procedure
  does not terminate on Ghelli's goal.

The relation is defined in this file rather than on cslib's `Fsub` (locally nameless, with
cofinite quantification): the divergence is a property of the algorithm, not of the declarative
relation, and cslib does not define the algorithm.  Connecting `FsubGhelli.Sub` (the inductive
closure of the algorithm, defined in the module) to cslib's `Sub` is part of the plan below.

## F2. Design of the reduction (fixed)

Encoding: **Pierce 1994**, two-counter machines → rowing machines → F<:^D (the deterministic
fragment whose subtyping derivations are linear) → F<:.

1. Source problem: halting of two-counter machines, `FsubGhelli.CM`, `FsubGhelli.CM.Step`,
   `FsubGhelli.CM.Halts` (defined in the module).  The repository has **no** counter machines
   under `Start/` (grep for two-counter / Minsky: nothing); the undecidable problems available are
   Mathlib's `Nat.Partrec.Code` halting (`ComputablePred.halting_problem`) and the λ-calculus
   results of `Start/HaltingComplete.lean`.  The first infrastructure lemma is therefore the
   undecidability of `CM.Halts`, by simulating Mathlib's `Turing.TM2` (or partial recursive codes)
   with two counters (Minsky's Gödel-numbering of stacks); this is a separate, self-contained
   step.
2. Rowing machines: configurations as F<: contexts of "row" variables; each counter value as a
   nesting depth of negations.
3. F<:^D: the fragment where the algorithm is deterministic, so a derivation is one chain of goal
   reductions (`AlgStep`), and a goal is derivable iff the chain reaches an axiom.
4. Embedding of F<:^D in F<: preserving derivability.

First lemma, stated in Lean (as a `Prop`, not proved): `FsubGhelli.RowingFirstLemma :=
∃ enc : CM → ℕ → ℕ → Goal, ∀ M a b, CM.Halts M a b ↔ Sub (enc M a b)`.

## F3. Kernel F<: (not done)

The decidable fragment is kernel F<: (Cardelli–Wegner): the quantifier rule requires equal bounds,
`Γ ⊢ ∀X<:U.S₂ <: ∀X<:U.T₂` iff `Γ, X<:U ⊢ S₂ <: T₂`, so the bound is never compared
contravariantly and the context grows only with bounds already present in the goal.  Its
algorithm terminates (the standard measure: the size of the goal's types with variables weighted
by the size of their bounds).  Not formalized this round.

Status: the design is fixed, so the row moves from `TODO_NEEDS_DESIGN` to `TODO_READY`.
