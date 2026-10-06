# M25-HM-ALGORITHM-W — algorithm W and its soundness

**Status:** DONE_STRONG

## Terminal statements (`Start/HMAlgorithmW.lean`)

```lean
def HM.W : List Sch → Expr → ℕ → Option ((ℕ → Ty) × Ty × ℕ)
theorem HM.W_sound {e} : ∀ {Γ n s τ m}, W Γ e n = some (s, τ, m) → Typing (ctxSubst s Γ) e τ
theorem HM.W_sound_closed (h : W [] e n = some (s, τ, m)) : Typing [] e τ
```

* `W Γ e n` takes a supply `n` of fresh type variables and returns a substitution, a type and the
  new supply, or fails (unbound variable or failed unification, through `HM.mgu`).  It is a total
  function by structural recursion on the term.
* Soundness needs no invariant on the supply: the `let` case uses the derived rule
  `HM.Typing.let_subst` (the `let` rule after a substitution of the context), which is proved by
  the same renaming argument as `HM.Typing.subst`.
* Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates

`lake build`, `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
