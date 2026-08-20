# M3-PARTREC-IMP-LAMBDACOMPUTABLE

Reverse main theorem: recursive implies lambda-computable.

## Claim

Every **total** computable function `f : ℕ → ℕ` is lambda-computable:

```lean
theorem Lambda.exists_realizer_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F : Lambda, Lambda.Realizes F f

theorem lambdaComputable_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    LambdaComputable (fun n => Part.some (f n))
```

(`Start/PartrecLambda.lean`.)

## How the compilation works

The compilation follows the inductive structure of the recursive functions in two layers.

1. Every constructor of `Nat.Primrec` is compiled by induction into a closed lambda realizer
   (`Lambda.exists_realizer_of_primrec`, see `M3-LAMBDA-PREC-COMPILER`).

2. Kleene's normal form reduces the general case to minimisation over a primitive recursive
   predicate.  From `Computable f` one gets a code `c` with `c.eval = fun n => Part.some (f n)`
   (`Nat.Partrec.Code.exists_code`), and the two arithmetised primitive recursive functions

   ```lean
   def Lambda.kleeneTest  (c : Nat.Partrec.Code) (p : ℕ) : ℕ   -- 0 iff evaln succeeded
   def Lambda.kleeneValue (c : Nat.Partrec.Code) (p : ℕ) : ℕ   -- the value found
   ```

   are primitive recursive (`Lambda.kleeneTest_primrec`, `Lambda.kleeneValue_primrec`, from
   `Nat.Partrec.Code.primrec_evaln`).  Totality of `f` gives a witness for every argument
   (`Lambda.kleene_exists_witness`, from `Nat.Partrec.Code.eval_eq_rfindOpt`), and any witness
   yields the right value (`Lambda.kleene_value_eq`, from `Nat.Partrec.Code.evaln_sound`).

3. The search itself is performed by the lambda minimisation combinator, in parameterised
   form: `Lambda.muParam H` reduces `church n` to the Church numeral of the least `y` with
   `h (pair n y) = 0` (`Lambda.Realizes.muParam`, built on `Lambda.muCorrectness`).

   The realizer is then `Lambda.mkApp1 G (Lambda.mkApp2 Lambda.natPair' Lambda.I (Lambda.muParam H))`.

## Class the result is stated on

The implication is closed for **total** computable functions.  For genuinely partial
functions the definition of `LambdaComputable` also demands that the term reduce to *no*
Church numeral on divergent inputs, which needs the divergence half of minimisation; see
`M3-LAMBDA-MU-CORRECTNESS` for exactly what is missing there.

## Gates

```
python3 scripts/goal_state.py validate   # OK
lake build                               # Build completed successfully
```
