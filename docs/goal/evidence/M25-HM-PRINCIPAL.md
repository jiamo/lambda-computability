# M25-HM-PRINCIPAL — principal types, completeness of W, decidability

**Status:** DONE_STRONG

## Terminal statements (`Start/HMPrincipal.lean`)

```lean
theorem HM.W_complete {e : Expr} :
    ∀ {Γ : List Sch} {n : ℕ} {s' : ℕ → Ty} {τ' : Ty}, (∀ v ∈ ctxFvs Γ, v < n) →
      Typing (ctxSubst s' Γ) e τ' →
      ∃ s τ m, W Γ e n = some (s, τ, m) ∧
        ∃ r : ℕ → Ty, τ' = τ.subst r ∧ ∀ v < n, s' v = (s v).subst r

theorem HM.principal {Γ : List Sch} {e : Expr} (h : ∃ s' τ', Typing (ctxSubst s' Γ) e τ') :
    ∃ s τ m, W Γ e (ctxBound Γ) = some (s, τ, m) ∧ Typing (ctxSubst s Γ) e τ ∧
      ∀ s' τ', Typing (ctxSubst s' Γ) e τ' →
        ∃ r : ℕ → Ty, τ' = τ.subst r ∧ ∀ v ∈ ctxFvs Γ, s' v = (s v).subst r

theorem HM.principal_closed {e : Expr} (h : ∃ τ, Typing [] e τ) :
    ∃ s τ m, W [] e 0 = some (s, τ, m) ∧ ∀ τ', Typing [] e τ' ↔ ∃ r : ℕ → Ty, τ' = τ.subst r

theorem HM.W_none_iff (hfv : ∀ v ∈ ctxFvs Γ, v < n) :
    W Γ e n = none ↔ ¬ ∃ s' τ', Typing (ctxSubst s' Γ) e τ'
theorem HM.W_closed_none_iff : W [] e 0 = none ↔ ¬ ∃ τ, Typing [] e τ

theorem HM.typable_iff (Γ : List Sch) (e : Expr) :
    (∃ τ, Typing Γ e τ) ↔
      ∃ s τ m, W Γ e (ctxBound Γ) = some (s, τ, m) ∧ RenamingOn s (ctxFvs Γ)
instance HM.decTypable (Γ : List Sch) (e : Expr) : Decidable (∃ τ, Typing Γ e τ)
instance HM.decTypableClosed (e : Expr) : Decidable (∃ τ, Typing [] e τ)

theorem HM.not_typable_selfApp : ¬ ∃ τ, Typing [] (Expr.lam (Expr.app (Expr.var 0) (Expr.var 0))) τ
```

* Completeness is Damas–Milner's: the bookkeeping invariant of the fresh-variable supply is
  `HM.W_inv`; the `app` case extends the witness by the fresh variable and uses the strong mgu
  property of `HM.mgu_most_general`; the `let` case uses that substituting after generalizing is
  more general than generalizing after substituting (`HM.moreGen_subst_gen`).
* Typability in a fixed context reduces to W plus a finite check: the returned substitution must
  be an injective renaming on the free type variables of the context (`HM.exists_inverse_iff`).
* The self-application is untypable, so W fails on it (`HM.W_selfApp`); `let id = λx.x in id id`
  is typable (`HM.typing_let_id_id`).  Neither direction is vacuous.
* Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates

`lake build`, `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
