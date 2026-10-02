# M21-QBF-ARITH and M21-SUMCHECK-ROUND — arithmetization of QBF, and one round of sum-check

**Status:** both DONE_STRONG (for the claims stated below; the rest of `IP = PSPACE` is split into
the later M21 rows of the task board).

`Start/QbfArith.lean` is the first module of the `IP = PSPACE` line.  It is deliberately small: it
fixes the two mathematical facts every later row consumes.

Note on the earlier modules.  `Start/QbfCob*.lean` are **not** an arithmetization: `Cob` stands for
Cobham's class, and those modules write the reduction formula of `PSPACE`-hardness by
polynomial-time word operations.  The arithmetization proper starts here.

## What is proved

* `Complexity.Qbf.QBF.arith` — Shamir's arithmetization of a formula of `Start/Qbf.lean` in an
  arbitrary commutative ring: `¬a ↦ 1 - a`, `a ∧ b ↦ ab`, `a ∨ b ↦ 1 - (1-a)(1-b)`,
  `∀x. p ↦ p[x:=0] · p[x:=1]`, `∃x. p ↦ 1 - (1 - p[x:=0])(1 - p[x:=1])`.
* `Complexity.Qbf.QBF.arith_bool` — on `0/1` values of the variables it computes exactly the truth
  value (`1` or `0`), in **every** commutative ring.
* `Complexity.Qbf.QBF.tqbf_iff_arith` — a closed formula is true iff its arithmetization is `1`, in
  every nontrivial commutative ring.  In particular, over `ZMod p` no condition on `p` is needed:
  the value is exactly `0` or `1`, never a multiple of `p` in disguise.
* `Complexity.Qbf.QBF.arithPoly`, `Complexity.Qbf.QBF.eval_arithPoly` — the same map with values in
  `MvPolynomial ℕ R`, the quantifiers acting by substitution (`bind₁`), evaluating to `arith`.
* `Polynomial.card_eval_eq_le` — two different polynomials of degree `≤ d` over a finite field
  agree on at most `d` points; `Polynomial.card_eval_eq_le_div` — the same as the probability
  bound `d / |F|` that a verifier checking a false claim at a uniformly random point is fooled.

`#print axioms` on these results: `propext`, `Classical.choice`, `Quot.sound`.

## Boundary (recorded as separate rows, not as a gap of these two)

* The degrees of `arithPoly` are **not** bounded polynomially: each quantifier can double them.
  The degree reduction (Shen's linearization operators) is `M21-LINEARIZE`.
* No interactive-proof framework yet (`M21-IP-DEF`), no multi-round protocol (`M21-SUMCHECK-GAME`),
  no polynomial-time verifier (`M21-FIELD-COBHAM`, `M21-VERIFIER-POLY`).

## Gates

```
lake build Start.QbfArith
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```
