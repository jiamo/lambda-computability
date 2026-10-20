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

## Round 6 — F<:^D, its embedding in full F<:, and the reduction of D1 to a simulation (`Start/FsubRowing.lean`)

`lake build --wfail`; axioms `propext` (`M25-FSUB-UNDECIDABLE-axioms.txt`).

* The linear rules of the algorithm for full F<: (on `FsubGhelli.Sub`):
  `FsubRowing.sub_neg_iff : Sub ⟨Γ, neg S, neg T⟩ ↔ Sub ⟨Γ, T, S⟩` (negation swaps the sides, the
  body goal `X <: X` is an axiom), `FsubRowing.sub_allTop_iff` (a `Top`-bounded left quantifier
  needs no bound check), `FsubRowing.sub_var_iff` (promotion is forced).
* `FsubRowing.SubD` — **F<:^D**: `Top`, reflexivity, promotion, the `Top`-bounded quantifier rule
  and the negation rule, each with at most one premise.
* **D2**: `FsubRowing.SubD.toSub {g : Goal} (h : SubD g) : Sub g` — F<:^D subtyping embeds into
  full F<: subtyping (the algorithmic relation of `Start/FsubGhelli.lean`).
* `FsubRowing.DStep`, `FsubRowing.DStep.deterministic`, `FsubRowing.SubD.linear` and
  `FsubRowing.subD_iff_run : SubD g ↔ DRun g` — a goal is derivable in F<:^D iff the deterministic
  run from it reaches an axiom: the form in which a machine is simulated.
* `FsubRowing.rowingFirstLemma_of_simulation` — `RowingFirstLemma` follows from an encoding
  `enc : CM → ℕ → ℕ → Goal` with `CM.Halts M a b ↔ DRun (enc M a b)` and conservativity
  `Sub (enc M a b) → SubD (enc M a b)`.

**D1/D3, first missing lemma**: the simulation itself,
`∃ enc : CM → ℕ → ℕ → Goal, (∀ M a b, CM.Halts M a b ↔ DRun (enc M a b)) ∧ ∀ M a b,
Sub (enc M a b) → SubD (enc M a b)` — Pierce's rowing-machine encoding (configurations as
contexts of row variables, each instruction a context entry that the promotion steps dispatch to).
Rowing machines were not defined: the encoding goes directly from two-counter machines to F<:^D
runs, and the definition of the intermediate machine model is part of that lemma.

**D2, cslib connection**: not attempted.  cslib's `Fsub` subtyping is declarative and locally
nameless with cofinite quantification; connecting it to `FsubGhelli.Sub` needs a de Bruijn
translation and the soundness and completeness of the algorithm with respect to the declarative
rules (transitivity elimination).  This is stated as the gap in the row.

**D4**: gap row M25-COUNTER-MACHINE-UNDECIDABLE (undecidability of `CM.Halts`, by a two-counter
simulation of a universal machine, reducing from `ComputablePred.halting_problem` or
`not_computablePred_codeConverges`).  F3 (kernel F<: termination) not done.

Status: TODO_READY, now depending on M25-COUNTER-MACHINE-UNDECIDABLE.

## Round 7 — Pierce's simulation (`Start/FsubPierce.lean`) and Minsky's reduction (`Start/Minsky.lean`)

**D1/D3 closed: the simulation.**  The rules of F<:^D are read as a continuation-passing machine:
a goal `Γ ⊢ P <: ∀X₁<:V₁ … ∀Xₘ<:Vₘ. ¬K` calls the process `P` with arguments `V̄` and continuation
`K`; a process `∀X̄<:Top. ¬F` (`lamN`) binds its arguments in the context and the negation rule
swaps the sides, so the frame `F` becomes the next goal's right-hand side (`call_steps`); a
variable on the left is a reference followed by promotion (`res_steps`).  All calls have arity
`n + 6` for a program of length `n`: two counter slots, two scratch slots, the codes of the `n`
instructions and of halting.  A trampoline `dispT` re-issues the call of the code it receives.
Counters are numerals `succT s (… zeroT)`; a zero test stores the two branch codes in the scratch
slots and calls the counter.  The halting code reaches the axiom `· <: Top`.  No intermediate
(rowing) machine was needed: the invariant `DInv` relates a machine configuration directly to the
context and the four components of the dispatch goal.

Proved (axioms in `M25-FSUB-UNDECIDABLE-axioms.txt`, at most `propext, Classical.choice,
Quot.sound`):

```lean
theorem FsubPierce.sim_step (h : DInv M Γ p is q c) (hs : CM.Step M c c') :
    ∃ Γ' p' is' q', Relation.TransGen DStep (dispGoal M.length Γ p is q)
      (dispGoal M.length Γ' p' is' q') ∧ DInv M Γ' p' is' q' c'
theorem FsubPierce.halts_iff_drun (M : CM) (a b : ℕ) : CM.Halts M a b ↔ DRun (enc M a b)
theorem FsubPierce.enc_conservative (M : CM) (a b : ℕ) : Sub (enc M a b) → SubD (enc M a b)
theorem FsubPierce.simulation : ∃ enc : CM → ℕ → ℕ → Goal,
    (∀ M a b, CM.Halts M a b ↔ DRun (enc M a b)) ∧ ∀ M a b, Sub (enc M a b) → SubD (enc M a b)
theorem FsubPierce.rowingFirstLemma : RowingFirstLemma
theorem FsubPierce.cm_halts_iff_sub (M : CM) (a b : ℕ) : CM.Halts M a b ↔ Sub (enc M a b)
theorem FsubPierce.cm_halts_iff_subD (M : CM) (a b : ℕ) : CM.Halts M a b ↔ SubD (enc M a b)
```

The step lemma: an increment is two calls, a zero test four.  Both instruction kinds went
through; no instruction kind resisted.  Conservativity is proved in general
(`sub_to_subD_of_noStuck`: full F<: is conservative over F<:^D on every goal whose deterministic
run never gets stuck) and the encoded goals satisfy the hypothesis (`enc_noStuck`).

**D4, step B1 (row M25-COUNTER-MACHINE-UNDECIDABLE).**  `Start/Minsky.lean`: `k`-counter machines
`Minsky.KM` (instructions `inc i l`, `test i l₁ l₂`), compiled into `FsubGhelli.CM` with the
Gödel number `∏_{i<k} pᵢ^{rᵢ}` in the first counter, the second counter as scratch.  The bases
are the Fermat numbers `pᵢ = 2^(2^i) + 1` (pairwise coprime, Mathlib's
`Nat.coprime_fermatNumber_fermatNumber`), so `pᵢ ∣ godel k r ↔ 0 < rᵢ`.

```lean
theorem Minsky.sim_step {M : KM} {k : ℕ} (hk : RegsBelow M k) {c c' : KConf} (hs : KM.Step M c c') :
    Relation.TransGen (CM.Step (compile M)) (encC M k c) (encC M k c')
theorem Minsky.halts_iff {M : KM} {k : ℕ} (hk : RegsBelow M k) (r : ℕ → ℕ) :
    KM.Halts M r ↔ CM.Halts (compile M) (godel k r) 0
theorem Minsky.halts_iff_sub {M : KM} {k : ℕ} (hk : RegsBelow M k) (r : ℕ → ℕ) :
    KM.Halts M r ↔ Sub (FsubPierce.enc (compile M) (godel k r) 0)
```

**B2, first missing piece**: a source of undecidability for `k`-counter machines — a compilation
of Mathlib's `Nat.Partrec.Code` (or of `Turing.TM2`) into `Minsky.KM` preserving halting, together
with `Primcodable` instances for `CM` and `KM` and the computability of `compile`, `godel` and of
that compilation.  Without it `FsubGhelli.cm_halts_undecidable` is not proved; the gap row is
M25-KCM-UNIVERSAL.

**cslib link**: unchanged (not attempted); gap row M25-FSUB-CSLIB-LINK.

Status: M25-FSUB-UNDECIDABLE is DONE_WEAK (simulation, RowingFirstLemma and `CM.Halts ≤ Sub`
proved; undecidability of `Sub` waits for the undecidability of `CM.Halts`, and the cslib link
is open).  M25-COUNTER-MACHINE-UNDECIDABLE is DONE_WEAK (B1 proved; B2 open).

## Round 8 — register-machine macros (`Start/MinskyMacros.lean`)

Path chosen: compilation of `Nat.Partrec.Code` into `Minsky.KM` by Shepherdson–Sturgis macros.
Proved, each as a run lemma *in place* (the macro's instructions at given labels of any program):

* `Macro.clear_run` (`r i := 0`), `Macro.transfer_run` (`r j += r i; r i := 0`),
  `Macro.transfer2_run` (`r j += r i; r t += r i; r i := 0`), `Macro.copy_run`
  (`r j += r i` with `r i` restored through a zero scratch register), `Macro.mul_run`
  (`r k += r i * r j`, `r j` preserved, `r i := 0`).

First macro not built: **the pairing macro** `r k := Nat.pair (r i) (r j)`, which needs a
comparison loop (`r i < r j`) besides `mul_run`; then `Nat.unpair` (an integer square root loop),
then the compilation of `zero, succ, left, right, pair, comp, prec, rfind'` with a stack of
frames stored in one register through `Nat.pair`, its simulation lemma, and the computability
obligations (`Primcodable KM`, computability of the compilation, of `Minsky.compile` and of
`Minsky.godel`).  `FsubGhelli.cm_halts_undecidable` and the undecidability of `Sub` are not
derived this round.
