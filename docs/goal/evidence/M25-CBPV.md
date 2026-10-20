# M25-CBPV — call-by-push-value

Status: **DONE_STRONG**.  Module `Start/CBPV.lean` (self-contained; source is a small simply typed
λ-calculus defined in the same file, with its call-by-name and call-by-value reductions).

## The calculus

* Value types `VTy`: `base`, `U B`; computation types `CTy`: `F A`, `A → B` (mutual inductive).
* Terms `CT` (one de Bruijn syntax): `var`, `thunk M`, `force V`, `ret V`, `bind M N`
  (`M to x. N`), `lam M`, `app M V`; renaming `CT.ren`, substitution `CT.subst` with the fusion
  lemmas `ren_ren`, `subst_ren`, `ren_subst`, `subst_var`.
* Typing `CTyp Γ M T` with `T : Sort'` either `.v A` (a value of value type `A`) or `.c B` (a
  computation of computation type `B`); rules var, thunk, force, ret, bind, lam, app.
  `CTyp.ren`: weakening along renamings.
* Reduction `CStep` (evaluation of computations): `force (thunk M) → M`,
  `ret V to x. N → N[V]`, `(λx. M) V → M[V]`, and the evaluation contexts `□ to x. N`, `□ V`.
* Administrative contraction `Admin`: `force (thunk M) ⇝ M` in any position.

## The translations

Source: `STm` (`var`, `lam`, `app`), typing `STyp`, call-by-name `NStep` (weak head:
`(λt) u → t[u]`, `t u → t' u`), call-by-value `VStep` (`(λt) w → t[w]` for a value `w`, `t u → t' u`,
`w u → w u'`).

* Call-by-name: `tyN ι = F ι`, `tyN (A → B) = U (tyN A) → tyN B`;
  `tn x = force x`, `tn (λt) = λ (tn t)`, `tn (t u) = (tn t) (thunk (tn u))`.
* Call-by-value: `tyV ι = ι`, `tyV (A → B) = U (tyV A → F (tyV B))`;
  `tv x = ret x`, `tv (λt) = ret (thunk (λ (tv t)))`,
  `tv (t u) = tv t to f. (tv u to x. (force f) x)`; values `val x = x`,
  `val (λt) = thunk (λ (tv t))`, so `tv w = ret (val w)` for a value `w`.

```lean
theorem tn_typing {Γ : List STy} {t : STm} {A : STy} (h : STyp Γ t A) :
    CTyp (Γ.map fun A => .U (tyN A)) (tn t) (.c (tyN A))
theorem tv_typing {Γ : List STy} {t : STm} {A : STy} (h : STyp Γ t A) :
    CTyp (Γ.map tyV) (tv t) (.c (.F (tyV A)))
```

## Preservation of reduction (simulation)

```lean
theorem tn_sim {t t' : STm} (h : NStep t t') :
    ∃ M, CStep (tn t) M ∧ Relation.ReflTransGen Admin M (tn t')
theorem tv_beta (t w : STm) (hw : w.IsVal) :
    Relation.TransGen CStep (tv (.app (.lam t) w)) (tv (t.subst (cons w STm.var)))
theorem tv_sim {t t' : STm} (h : VStep t t') :
    ∃ M, Relation.TransGen CStep (tv t) M ∧ Relation.ReflTransGen CStep (tv t') M
```

* Call-by-name: a source step is **exactly one** CBPV step followed by administrative
  contractions.  They are needed because `tn` maps a variable to `force x`, so substituting
  `thunk (tn u)` produces `force (thunk (tn u))` where `tn (t[u])` has `tn u` (`tn_subst`, with the
  representation predicate `RepN`).
* Call-by-value: a β step is **exactly four** CBPV steps (`tv_beta`: two `bind`-`ret`
  reductions, one `force`-`thunk`, one β), landing exactly on the translation of the reduct
  (`tv_subst`: substitution of values commutes with `tv`).  A congruence step in argument position
  `w u → w u'` first performs the administrative `ret`-`bind` step of the function value, so in
  general `tv t` and `tv t'` meet: `tv t →⁺ M` and `tv t' →* M`.

## Axioms

`M25-CBPV-axioms.txt`: at most `[propext, Quot.sound]`.
