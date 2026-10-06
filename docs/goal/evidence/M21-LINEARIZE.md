# M21-LINEARIZE — Shen's linearization keeps the protocol's polynomials of low degree

**Status:** DONE_STRONG

## Terminal statements (`Start/QbfLinearize.lean`)

```lean
def Complexity.Qbf.linOp (j : ℕ) (f : (ℕ → R) → R) (a : ℕ → R) : R :=
  a j * f (Function.update a j 1) + (1 - a j) * f (Function.update a j 0)
theorem Complexity.Qbf.linOp_eq_of_bool (j) (f) (a) (h : a j = 0 ∨ a j = 1) : linOp j f a = f a
theorem Complexity.Qbf.uniDeg_linOp_self (j) (f) : UniDeg (linOp j f) j 1
theorem Complexity.Qbf.QBF.eval_toOp_bool (N) (p) :
    ∀ a, IsBool a → Op.eval a (toOp N p) = arith a p
theorem Complexity.Qbf.QBF.tqbf_iff_toOp [Nontrivial R] (N) {p} (hp : p.Closed) :
    TQBF p ↔ Op.eval (fun _ => (0 : R)) (toOp N p) = 1
theorem Complexity.Qbf.QBF.uniDeg_toOp : p.varBound ≤ N → ∀ j, UniDeg (fun a => Op.eval a (toOp N p)) j p.size
theorem Complexity.Qbf.QBF.roundDeg_toOp : p.varBound ≤ N → RoundDeg R (2 * p.size) (toOp N p)
theorem Complexity.Qbf.QBF.size_toOp (N) (p) : (toOp N p).size ≤ (N + 1) * p.size
```

`#print axioms Complexity.Qbf.QBF.roundDeg_toOp`: `propext, Classical.choice, Quot.sound`.

## Route

The original exit criteria asked for the operator *sequence* of a prenex formula (Shen's
`Q₁ L₁ Q₂ L₁ L₂ …`).  The route taken inserts the linearizations into the formula *tree*:
`toOp N` replaces every quantifier node `Q x_i p` by `L_0 L_1 … L_{N-1} (Q x_i (toOp N p))`.
Conjunctions and disjunctions stay binary nodes, which the protocol of `M21-SUMCHECK-GAME`
handles by having the prover send both child values.  This removes the need for a normal form
(`M21-QBF-SIMPLE-FORM`), whose own gap stays open and is recorded on that row.

Degrees are semantic.  `UniDeg f j d` means that every restriction of `f` to a line in direction
`j` is a polynomial of degree at most `d`.  This is what the honest prover sends, and what the
soundness estimate needs.  The bound `2 · size p` replaces the criterion's
`max(2, deg matrix)`.  In the tree setting the "matrix" is the formula itself.
