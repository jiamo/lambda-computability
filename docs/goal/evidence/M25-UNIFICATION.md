# M25-UNIFICATION — first-order unification and the most general unifier

**Status:** DONE_STRONG

## Terminal statements (`Start/Unification.lean`)

```lean
inductive HM.Ty | var : ℕ → Ty | con : ℕ → Ty | arrow : Ty → Ty → Ty
def HM.unify : HM.Eqs → Option (ℕ → HM.Ty)          -- Robinson, on a list of equations
theorem HM.unify_sound {E u} (h : unify E = some u) : Unifies u E
theorem HM.unify_mgu {E u} (h : unify E = some u) {s'} (hs' : Unifies s' E) (v : ℕ) :
    (u v).subst s' = s' v
theorem HM.unify_none {E} (h : unify E = none) (s : ℕ → Ty) : ¬ Unifies s E
theorem HM.unify_vars {E u} (h : unify E = some u) (v : ℕ) : (u v).vars ⊆ insert v (eqsVars E)
theorem HM.mgu_iff (t₁ t₂ : Ty) :
    (∃ s, t₁.subst s = t₂.subst s) ↔
      ∃ u, mgu t₁ t₂ = some u ∧ t₁.subst u = t₂.subst u ∧
        ∀ s', t₁.subst s' = t₂.subst s' → ∀ v, (u v).subst s' = s' v
```

* Terms: variables, constants and one binary symbol (the monotypes of Hindley–Milner);
  substitutions are maps `ℕ → Ty`, applied by `Ty.subst`, composed by `Ty.subst_subst`.
* Termination: well-founded recursion on the lexicographic measure (number of variables of the
  problem, size of the problem) — `HM.eqsMeasure`; the elimination step strictly decreases the
  first component (`HM.card_elim_lt`).
* Most generality is in the strong form `s' = s' ∘ u`: every unifier factors through `u`, via
  itself.
* Failure: a constructor clash, or the occurs check (`HM.Ty.size_lt_subst`).
* Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Scope note

The signature is the one Hindley–Milner needs (constants and the arrow).  A general first-order
signature `f(t₁,…,tₙ)` can be curried into it (`arrow` as application, `con f` as the head), but
that encoding is not formalized here.

## Gates

`lake build`, `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
