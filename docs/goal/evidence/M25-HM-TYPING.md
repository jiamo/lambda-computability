# M25-HM-TYPING — the Hindley–Milner type system

**Status:** DONE_STRONG

## Terminal statements

`Start/HindleyMilner.lean`:

```lean
inductive HM.Sch | fv | bv | con | arrow      -- schemes; bound variables named, `bv`
def HM.Sch.inst (ts : ℕ → Ty) : Sch → Ty      -- instantiation
def HM.gen (Γ : List Sch) (τ : Ty) : Sch       -- generalization relative to Γ
inductive HM.Expr | var | app | lam | let_
inductive HM.Typing : List Sch → Expr → Ty → Prop
  | var (ts) : Γ[i]? = some σ → Typing Γ (var i) (σ.inst ts)          -- instantiates
  | app | lam
  | let_ : Typing Γ a A → Typing (gen Γ A :: Γ) b B → Typing Γ (let_ a b) B   -- generalizes
theorem HM.Typing.subst (h : Typing Γ e τ) (s) : Typing (ctxSubst s Γ) e (τ.subst s)
theorem HM.Typing.weaken (h : Typing Γ e τ) (σ) : Typing (σ :: Γ) (e.rename Nat.succ) τ
theorem HM.Typing.substE : Typing Γ e τ →
    (∀ i σ, Γ[i]? = some σ → ∀ ts, Typing Δ (f i) (σ.inst ts)) → Typing Δ (e.substE f) τ
theorem HM.Typing.preservation (hs : Step e e') : Typing Γ e τ → Typing Γ e' τ
theorem HM.typing_let_id_id   -- `let id = λx.x in id id` is typable
```

`Start/HMSystemF.lean`:

```lean
theorem HM.typing_systemF (h : HM.Typing Γ e τ) :
    SystemF.Typing (Γ.map schF) (erase e) (tyF τ)
theorem HM.sn_of_typing (h : HM.Typing Γ e τ) : Lambda.SN (erase e)
```

* `Step` is β-reduction, `let`-reduction and all congruences.
* `erase` sends `let x = a in b` to `(λx. b) a`; `schF σ` is `σ.bnd` universal quantifiers over
  the body.  Type constants are sent to the closed System F type `∀α. α` (System F of the library
  has no base types; any closed type would do, since only typing is preserved).
* The `let` cases of the substitution, weakening and term-substitution lemmas rename the
  generalized variables away first (`HM.moreGen_gen_rename`); typing is monotone in the
  instance order on schemes (`HM.Typing.mono`).
* Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates

`lake build`, `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
`python3 scripts/goal_state.py validate`.
