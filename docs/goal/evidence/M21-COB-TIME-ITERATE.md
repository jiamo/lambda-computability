# M21-COB-TIME-ITERATE — iterating a Cobham term polynomially often

**Status:** DONE_STRONG (row opened and closed in this delivery, as the first piece of
`M21-VERIFIER-POLY`)

## Terminal statement (`Start/CobhamTimeIter.lean`)

```lean
def Complexity.Cob.iterT (init step bnd : Cob) (c : ℕ) : Cob
theorem Complexity.Cob.eval_iterT (init step bnd : Cob) (ctx : List Word) :
    ∀ w : Word,
      (∀ j, 1 ≤ j → j ≤ w.length →
        ((fun s => step.eval (s :: ctx))^[j] (init.eval ctx)).length ≤ (bnd.eval ctx).length) →
      (Cob.iterT init step bnd ctx.length).eval (w :: ctx) =
        (fun s => step.eval (s :: ctx))^[w.length] (init.eval ctx)
```

The construction is a bounded recursion on notation over the counter word, with the bound
evaluated on the context.  Because no intermediate state exceeds the bound, the truncation that
`bRec` imposes has no effect.  This is the time-model counterpart of `Start/CobhamIterate.lean`,
which runs any number of rounds on a tape in polynomial space.

The verifier of `M21-VERIFIER-POLY` is meant to be `iterT` of one replay step
(`M21-VERIFIER-STEP-COB`).
