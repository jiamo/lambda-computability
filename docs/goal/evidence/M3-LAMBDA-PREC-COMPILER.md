# M3-LAMBDA-PREC-COMPILER

General primitive-recursion compiler: translate every `Nat.Primrec` construction into a
lambda term.

## Claim

Every primitive recursive function has a closed lambda term that computes it on Church
numerals.

## Evidence

`Start/Realizer.lean` introduces the realizability predicate

```lean
def Lambda.Realizes (F : Lambda) (f : ℕ → ℕ) : Prop :=
  Lambda.IsClosed F ∧ ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n))
```

and gives a realizer for each constructor of `Nat.Primrec`:

| constructor | realizer | correctness |
| --- | --- | --- |
| `zero` | `Lambda.mkConst 0` | `Lambda.Realizes.zero` |
| `succ` | `Lambda.succ` | `Lambda.Realizes.succ` |
| `left` | `Lambda.unpairLeft_impl` | `Lambda.Realizes.left` |
| `right` | `Lambda.unpairRight_impl` | `Lambda.Realizes.right` |
| `pair` | `Lambda.mkApp2 Lambda.natPair' _ _` | `Lambda.Realizes.natPair` |
| `comp` | `Lambda.mkApp1 _ _` | `Lambda.Realizes.comp1` |
| `prec` | `Lambda.precRealizer _ _` | `Lambda.Realizes.prec` |

The `prec` case is compiled as an iteration of a state transformer over the Church numeral
of the recursion argument (`Lambda.mkIter`, `Lambda.precStep`, `Lambda.precInit`), with the
numeric model `Lambda.precStepNum` and the loop invariant `Lambda.precStepNum_iterate`.  This
replaces the earlier specialised `Lambda.prec_works`, which is still available.

The compiler itself:

```lean
theorem Lambda.exists_realizer_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ F : Lambda, Lambda.Realizes F f

theorem Lambda.lambdaComputable_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    LambdaComputable (fun n => Part.some (f n))
```

Both are proved by induction on `Nat.Primrec`, with no `sorry` and no new axiom.

## Gates

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
