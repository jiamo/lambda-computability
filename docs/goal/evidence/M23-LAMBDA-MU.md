# M23-LAMBDA-MU — Parigot's λμ and its CPS translation

Status: **DONE_WEAK** (gap row M23-LAMBDA-MU-SN).  Modules `Start/LambdaMu.lean`,
`Start/LambdaMuCPS.lean`; axioms in `M23-LAMBDA-MU-axioms.txt`
(`[propext, Classical.choice, Quot.sound]` for every terminal theorem).

## Calculus (`Start/LambdaMu.lean`)

* Types `Ty`: atoms and implication (`Ty.atom n`, `Ty.arr A B`).  ⊥ is not needed: the CPS
  answer type is the base type of the target.
* Terms `Tm`: `var i`, `lam t`, `app t u`, `mu β t` = `μα.[β]t` (the command is stored with its
  binder).  Term variables and names share one de Bruijn space; `Typ Γ t A` is
  `Γ ⊢ t : A | Δ` with `Γ` and `Δ` interleaved in one `List Entry` (`Entry.tm A`, `Entry.nm A`).
* `Step`: β; structural `(μα.c) u → μα.c[[α](w u)/[α]w]` (`Tm.sstr`); renaming
  `[β]μα.c → c[β/α]`; compatible closure.

```lean
theorem subject_reduction {Γ : List Entry} {t t' : Tm} {A : Ty} (h : Typ Γ t A)
    (hs : Step t t') : Typ Γ t' A
theorem typ_callcc (Γ : List Entry) (A B : Ty) :
    Typ Γ Tm.callcc (.arr (.arr (.arr A B) A) A)
```

`Tm.callcc := lam (mu 0 (app (var 1) (lam (mu 2 (var 1)))))`, i.e.
`λf. μα.[α](f (λx. μδ.[α]x))`.  Subject reduction rests on `Typ.ren`, `Typ.subst` and
`Typ.sstr` (the structural substitution is typed).

## CPS translation (`Start/LambdaMuCPS.lean`)

Call-by-name, Plotkin style, into the Curry-style simply typed calculus of
`Start/SimpleTypes.lean`, with answer type `o = Lambda.Ty.base` and `¬X = X ⇒ o`:
`atom* = o`, `(A → B)* = ¬¬A* ⇒ ¬¬B*`; a term of type `A` becomes a term of type `¬¬A*`, a name
of type `A` a variable of type `¬A*`.  Environment-passing: `⟦x⟧ = ρ x`,
`⟦λx.t⟧ = λk. k (λx.⟦t⟧)`, `⟦t u⟧ = λk. ⟦t⟧ (λm. m ⟦u⟧ k)`, `⟦μα.[β]t⟧ = λα. ⟦t⟧ β`, and
`cps t = cpsE etaV t` with `etaV i = λk. i k`.

```lean
theorem typing_cps {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    Lambda.Typing (Γ.map entS) (cps t) (tyN A)
theorem cps_step {Γ : List Entry} {t t' : Tm} {A : Ty} (h : Typ Γ t A) (hs : Step t t') :
    ∃ c, Lambda.reduces (cps t) c ∧ Lambda.reduces (cps t') c
theorem cps_beta {Γ : List Entry} {M N : Tm} {A : Ty} (h : Typ Γ (.app (.lam M) N) A) :
    Lambda.reduces (cps (.app (.lam M) N)) (cps (Tm.subst (Tm.single N) M))
theorem cps_rename (β γ : ℕ) (t : Tm) :
    Lambda.reduces (cps (.mu β (.mu γ t)))
      (cps (.mu (Tm.nameOf (Tm.single (.var β) γ)) (Tm.subst (Tm.single (.var β)) t)))
```

So typing is preserved with double negation of types, and every λμ step of a well-typed term
becomes a β-conversion of the images (a common β-reduct); β and renaming steps are even forward
reductions.  Key lemmas: `cpsE_subst`, `cpsE_ren`, `cpsE_substTm` (substitution commutes with the
translation for name-to-name substitutions), `cpsE_sstr` (structural substitution, up to `Join`),
`cpsE_reduces_env`.

## Open boundary (row M23-LAMBDA-MU-SN)

Strict simulation is not proved.  In the structural case the image of the redex makes one β-step
to `λk. ⟦t⟧[α := λm. m ⟦u⟧ k] β`, while in the image of the reduct each `[α](w u)` becomes
`⟦w u⟧ α = (λk. ⟦w⟧ (λm. m ⟦u⟧ k)) α`, an administrative redex.  The two meet after that
administrative step, so the image of the reduct reduces to the common term but is not itself a
reduct of the image of the redex.  Hence `cps_step` is a join, and strong normalization of typed
λμ does not follow from `Lambda.sn_of_typing`.  (The CBN translation passes `⟦u⟧` unevaluated,
so steps inside discarded arguments are not erased; the obstacle is the administrative redex.)

First missing lemma: a colon-style (administrative-redex-free) variant of the translation with
typing preservation and

```lean
theorem LambdaMu.cps_step_strict {Γ : List Entry} {t t' : Tm} {A : Ty} (h : Typ Γ t A)
    (hs : Step t t') : Relation.TransGen Lambda.step (cps t) (cps t')
```

or, directly, `theorem LambdaMu.sn_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
Acc (fun a b => Step b a) t`.
