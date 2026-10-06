# M21-IP-DEF — Interactive proofs

**Status:** DONE_STRONG

## Terminal statements

`Start/InteractiveProof.lean`, `Start/CountProb.lean`:

```lean
structure Complexity.Verifier where
  rounds coins msgLen ask decide : Cob
abbrev Complexity.Prover := Word → Word
def Complexity.Verifier.accProb (V : Verifier) (P : Prover) (x : Word) : ℚ :=
  (V.accCount P x : ℚ) / 2 ^ V.numCoins x      -- accCount = cntL (numCoins x) (accepts P x)
def Complexity.IP (L : Language) : Prop :=
  ∃ V : Verifier, ∀ x, (L x → ∃ P, (2:ℚ)/3 ≤ V.accProb P x) ∧ (¬ L x → ∀ P, V.accProb P x ≤ 1/3)
theorem Complexity.inIP_of_inNP {L} : InNP L → IP L
theorem Complexity.IP.of_reduction {L₁ L₂} : L₁ ≤ₘᵖ L₂ → IP L₂ → IP L₁
theorem Complexity.Verifier.length_transcript_le :
    (V.transcript P x r).length ≤ V.numRounds x * (2 * (2 * V.maxMsg x + 1))
theorem Complexity.cntL_eq_card (n) (E) :
    cntL n E = (Finset.univ.filter (fun f : Fin n → α => E (List.ofFn f) = true)).card
```

## The protocol

- The verifier is five Cobham terms.
  - The number of rounds, the number of private random bits and the message-length bound are the
    lengths of `rounds(x)`, `coins(x)` and `msgLen(x)`.
  - Its messages are `ask(x, r, t)` and its verdict is `decide(x, r, t)`.
- The prover is an arbitrary function of the transcript.
- Messages are cut to the length bound and recorded as `1^{|w|} 0 w` (`Complexity.encMsg`).
- All lengths are lengths of Cobham values on `x`, hence polynomial (`Complexity.Cob.polyLen`), and
  so is the transcript.
- The acceptance probability is a finite average over the random words of length `|coins(x)|`.

Because the round count, the coin count and the length bound are polynomial-time functions of `x`
rather than of `|x|`, closure under reductions is plain composition (`Verifier.precomp`).

`#print axioms` for `inIP_of_inNP` and `IP.of_reduction` gives `propext, Classical.choice, Quot.sound`.
