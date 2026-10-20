# M23-SIZE-CHANGE — size-change termination

Round 7.  Status **DONE_STRONG** for the statement below (single parameter set).

Reference: C. S. Lee, N. D. Jones and A. M. Ben-Amram, *The size-change principle for program
termination*, POPL 2001 — the basis of Agda's termination checker.

Module: `Start/SizeChange.lean` (imports Mathlib only).

## Definitions

* `SizeChange.SCG n := Finset (Fin n × Fin n × Bool)` — a size-change graph over the parameters
  `Fin n`; an arc `(x, y, true)` is a strict decrease `x ↓ y`, `(x, y, false)` a non-increase
  `x ↓= y`.
* `SizeChange.SCG.comp` — composition: an arc `x → z` for each `x → y` in `G` and `y → z` in `H`,
  strict when either is (`SCG.mem_comp`); associative (`SCG.comp_assoc`).
* `SizeChange.SCT 𝒢` — the call-sequence semantics: every infinite multipath `g : ℕ → SCG n` with
  all `g k ∈ 𝒢` has, from some position on, an infinite thread with infinitely many strict
  descents.
* `SizeChange.InCl 𝒢` — the composition closure; `SizeChange.Criterion 𝒢` — every idempotent
  `G = G;G` in the closure has a strict self-arc `(x, x, true)`.

## Theorems

```lean
theorem SizeChange.ramsey_pairs {α : Type} [Finite α] (c : ℕ → ℕ → α) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : α, ∀ i j, i < j → c (f i) (f j) = a
theorem SizeChange.sct_of_criterion {𝒢 : Finset (SCG n)} (hc : Criterion 𝒢) : SCT 𝒢
theorem SizeChange.criterion_of_sct {𝒢 : Finset (SCG n)} (hs : SCT 𝒢) : Criterion 𝒢
theorem SizeChange.sct_iff_criterion (𝒢 : Finset (SCG n)) : SCT 𝒢 ↔ Criterion 𝒢
theorem SizeChange.mem_closureFS_iff {𝒢 : Finset (SCG n)} {G : SCG n} :
    G ∈ closureFS 𝒢 ↔ InCl 𝒢 G
instance SizeChange.Criterion.decidable (𝒢 : Finset (SCG n)) : Decidable (Criterion 𝒢)
instance SizeChange.SCT.decidable (𝒢 : Finset (SCG n)) : Decidable (SCT 𝒢)
```

* **Ramsey.**  No infinite Ramsey theorem for pairs was found in the pinned Mathlib (it has
  Hindman's and Hales–Jewett's theorems), so `ramsey_pairs` is proved here: iterate "take a point
  of an infinite set and an infinite monochromatic set of later points", then apply the infinite
  pigeonhole principle to the colours of the chosen points.
* **Criterion ⇒ SCT** (`sct_of_criterion`, the direction a termination checker uses): colour
  `i < j` by the composition of the block `[i, j)`; a homogeneous sequence gives a graph `G` in the
  closure with `G;G = G`; its strict self-arc `x → x` gives a path with a descent in every block,
  and the paths are glued into an infinite thread.
* **SCT ⇒ criterion** (`criterion_of_sct`): an idempotent graph of the closure is the composition
  of a finite block of graphs of `𝒢` (`InCl.realize`); the periodic multipath has a descending
  thread; at block boundaries the thread visits some parameter `x` infinitely often, and between
  two such visits with a descent in between, idempotence gives the arc `(x, x, true)` in `G`.  No
  Ramsey argument is needed in this direction.
* **Decidability**: `closureFS 𝒢` saturates `𝒢` under composition for `Fintype.card (SCG n)`
  steps; `iterCl_stable` shows the saturation reaches a fixed point within that bound, and
  `mem_closureFS_iff` that it computes the closure.  The criterion is then a finite check
  (`criterion_iff_finite`), and SCT is decidable through `sct_iff_criterion`.

Axioms: `docs/goal/evidence/M23-SIZE-CHANGE-axioms.txt` (`propext, Classical.choice,
Quot.sound`; no `native_decide`, no `Lean.ofReduceBool`).

## Scope

The formalisation uses one parameter set for all graphs, so every sequence of graphs of `𝒢` is a
multipath.  The program setting of the paper (a parameter set per function, graphs labelled by
calls, multipaths restricted to paths of the call graph) is not formalised.  The row's exit criteria are
stated for the single-set form.
