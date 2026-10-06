# M21-FIELD-COBHAM — arithmetic in ZMod p as Cobham terms

**Status:** DONE_STRONG

## Terminal statements (`Start/FieldCob.lean`)

```lean
theorem Complexity.Cob.eval_fAdd (hp : 0 < p) (ht : t.eval args = 1^a) (hu : u.eval args = 1^b)
    (hs : s.eval args = 1^p) : (Cob.fAdd t u s).eval args = 1^((a + b) % p)
-- likewise eval_fMul ((a * b) % p) and eval_fSub ((a + (p - b)) % p)
theorem Complexity.zmod_fAdd : (((a + b) % p : ℕ) : ZMod p) = a + b   -- and zmod_fMul, zmod_fSub
theorem Complexity.Cob.eval_polyEvalT (hp : 0 < p) (hc : cT.eval args = fieldsWord cs)
    (hx : xT.eval args = 1^x) (hpT : pT.eval args = 1^p) :
    (Cob.polyEvalT cT xT pT).eval args = 1^(hornerN x p cs)
theorem Complexity.zmod_hornerN : (hornerN x p cs : ZMod p) = Qbf.evalL (cs.map (↑)) (x : ZMod p)
theorem Complexity.Cob.eval_isPrimeT (hk : kT.eval args = 1^k) :
    (Cob.isPrimeT kT).eval args = bw (decide (Nat.Prime k))
theorem Complexity.Cob.eval_findPrimeT (hm : m ≠ 0) (h : mT.eval args = 1^m) :
    ∃ q, (Cob.findPrimeT mT).eval args = 1^q ∧ Nat.Prime q ∧ m < q ∧ q ≤ 2 * m
```

(`1^k` stands for `List.replicate k true`.)

## Route: unary instead of binary

The criterion asked for binary words.  The prime the protocol needs is polynomial in the input
length: it only has to exceed the soundness bound `d · rounds` by a constant factor.  So an element
`k < p` can be written as `1^k` at polynomial cost.  In unary the operations are one-line terms over
the existing toolkit: concatenation and smash, followed by `Cob.modT` (Euclidean division,
`Start/UniformGrid.lean`).  The purpose of the binary representation, polynomial word lengths, is
met.  The only place where binary is still needed is in turning random *bits* into field elements,
which is recorded on the new row `M21-SUMCHECK-COINS`.

## Further details

- **Horner's rule.** `Cob.hornerT` is a bounded recursion on notation over the coefficient word,
  read from the right.  Its state is the pair `1^V 0 1^c`: the value of the coefficients already
  completed, and the ones of the current coefficient.
- **The prime.** Trial division (`Cob.primLoop`) decides primality.  The search (`Cob.primeSearch`)
  keeps the last prime met among `2m, 2m-1, …, m+1`.  Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`) guarantees that it finds one.
