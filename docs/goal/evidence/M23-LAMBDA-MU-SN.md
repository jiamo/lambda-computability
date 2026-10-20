# M23-LAMBDA-MU-SN — strong normalization of typed λμ (partial; stop rule)

Status: **TODO_READY** (not closed).  The target

```lean
theorem LambdaMu.sn_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) : LambdaMu.SN t
```

is not proved.  M23-LAMBDA-MU stays DONE_WEAK.

## What is proved (`Start/LambdaMuSN.lean`)

The reducibility framework of Parigot's proof, on the calculus of `Start/LambdaMu.lean`:

* `SN t := Acc (fun a b => Step b a) t`, with `SN.step`, `SN.intro`, `sn_of_map`, `sn_app_left`,
  `sn_app_right`, `sn_lam_inv`, `sn_mu_inv`, `sn_var`, `sn_lam`;
* `VarHead` (variable-headed spines, which create no redex), `VarHead.step`, and
  `sn_app_varHead : VarHead h → SN h → SN u → SN (app h u)`;
* the candidates `Red (atom k) = SN`, `Red (A → B) = {t | ∀ u ∈ Red A, t u ∈ Red B}` and

```lean
theorem red_cr (A : Ty) :
    (∀ t, Red A t → SN t) ∧ (∀ t t', Red A t → Step t t' → Red A t') ∧
      (∀ h, VarHead h → SN h → Red A h)
theorem red_iff_stk (A : Ty) : ∀ t, Red A t ↔ ∀ π, Stk A π → SN (apps t π)
```

  (`Stk A`: the reducible stacks of `A = A₁ → ⋯ → Aₙ → o`).  The stack form is the one in which the
  μ-case of the fundamental lemma is stated: `μα.c ∈ Red A` iff `(μα.c) π ∈ SN` for every
  reducible stack `π`.

## Exactly what remains

The fundamental lemma (induction on typing, with a simultaneous substitution of reducible terms
for term variables and of (name, reducible stack) pairs for names) needs two expansion lemmas:

1. **β-expansion**: `SN u → (∀ v ∈ π, SN v) → SN (apps (t[u/0]) π) → SN (apps ((λt) u) π)`;
2. **μ-expansion**: `(∀ v ∈ π, SN v) → SN (c[α := π]) → SN (apps (μα.c) π)` where `c[α := π]`
   is the iterated structural substitution `Tm.sstr`.

Both rest on the **first missing lemma**, stability of reduction under substitution:

```lean
theorem Step.subst {t t' : Tm} (hs : Step t t') {σ : ℕ → Tm}
    (hσ : ∀ i, NameRespecting σ t i) : Step (subst σ t) (subst σ t')
```

where `NameRespecting` says that `σ` sends every index used as a name in `t` to a variable (on
non-variables `subst` sends a name to the junk index `0`, so the lemma is false without it), and
its structural analogue `Step.sstr : Step t t' → Relation.TransGen Step (sstr a v t) (sstr a v t')`.
Their proofs need the substitution algebra of `Start/LambdaMu.lean` that is not yet there:
`subst`∘`subst`, `sstr`∘`subst`, `sstr`∘`sstr` and `sstr`∘`ren` commutation.  The renaming rule
adds a further case to μ-expansion: `μα.[α]μγ.c'` under the substitution `α := π` is no longer a
renaming redex, and is matched by `|π|` structural steps followed by one renaming step.

The alternative route, a strict CPS translation, is blocked as recorded in M23-LAMBDA-MU.md:
the structural step is only joinable under `LambdaMu.cps`.

## Axioms

`M23-LAMBDA-MU-SN-axioms.txt` (for the lemmas above): `[propext]`.
