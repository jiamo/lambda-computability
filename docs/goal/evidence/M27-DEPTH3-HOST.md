# M27-DEPTH3-HOST — the absorbed depth-three lower bound in the host theory

Status: DONE_STRONG.

## Terminal statement (the row's former open boundary, verbatim)

```lean
theorem Complexity.DepthThreeHost.depthThree_lower_bound_host :
    ∃ L : Language, InP L ∧ ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n, N ≤ n → ∀ C : ACCirc, C.IsSigma3 →
      (∀ x : Word, x.length = n → (C.eval x = true ↔ L x)) →
        (2 : ℝ) ^ (A * Real.sqrt n) < C.size
```

(`Start/DepthThreeHost.lean`), with

```lean
def ACCirc.IsTopShape : ACCirc → Prop
  | .or _ => True | .lit _ _ => True | .const _ => True | _ => False
def ACCirc.IsSigma3 (C : ACCirc) : Prop := C.depth ≤ 3 ∧ IsTopShape (C.nnf true)
```

i.e. `C.depth ≤ 3` and the output gate of `C.nnf true` is an `OR`, a literal or a constant.

## Translation contract (`toCircuit3`)

* Basis: host literals `xᵢ`/`¬xᵢ` and constants (a literal with `i ≥ n` reads `false` and becomes
  a constant), unbounded fan-in `AND`/`OR`.  After `nnf true` there is no `NOT` gate
  (`noNot_nnf`), with the same function (`eval_nnf`), depth (`depth_nnf`) and no larger size
  (`size_nnf`).
* Shape: the output `OR` (merged with its `OR` children) becomes the top gate of the upstream
  `Circuit3`; each other depth-≤2 child becomes a middle `AND`; each depth-≤1 gate becomes bottom
  clauses (an `AND` of literals is split into unit clauses).  Fan-in is unbounded on both sides.
* Depth: three on both sides.
* Function: `toCircuit3_eval : C.IsSigma3 → (toCircuit3 n C).eval f = C.eval (List.ofFn f)`.
* Size: `toCircuit3_gateCount : (toCircuit3 n C).gateCount ≤ 2 * C.size + 1`; every bottom clause
  and every middle gate is charged to a distinct node of the host tree.

## The language in host P

Upstream's language is decided by a `FiniteMultiTapeMachine` within `Cc · (n + 1)^a` steps; it is
in `InP` by `MultiTapeCobham.inP_of_multiTapeHaltsIn` (row M27-POLYTIME-TO-COBHAM).  The lower
bound for `A` is obtained from upstream's bound for `A + 2`, which absorbs the factor 2 and the
additive 1 of the size translation once `n ≥ 1`.

## Relation to PolyCircuit / UniformCircuit

The bound is for the genuine non-uniform, unbounded fan-in depth-three model: host trees
`ACCirc` (`Start/AC0.lean`), the model of `InAC0`.  `Start/PolyCircuit.lean` and
`Start/UniformCircuit.lean` use shared circuits of fan-in two, where constant depth is not a
meaningful restriction (an unbounded fan-in gate of fan-in `m` costs depth `log m`), so no
depth-three statement is made there; at constant depth, trees and shared circuits differ only
polynomially (`Start/AC0.lean`, header), so the `2^{A √n}` bound transfers to shared unbounded
fan-in depth-three circuits up to the exponent constant.  The host interface was extended
conservatively: only the new predicate `IsSigma3` (and `IsTopShape`) was added, in the new module.

## Axioms

`#print axioms Complexity.DepthThreeHost.depthThree_lower_bound_host`:
`[propext, Classical.choice, Quot.sound]`.
