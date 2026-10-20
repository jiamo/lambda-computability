# M23-NBE-STLC — decidable βη-conversion for the simply typed λ-calculus by NbE (round 6)

Modules: `Start/StlcNbE.lean` (model, evaluation, normalization, soundness) and
`Start/StlcNbEComplete.lean` (completeness, decidability).  `lake build --wfail`; axioms in
`M23-NBE-STLC-axioms.txt` (`propext, Quot.sound`).

This is the first step toward decidable conversion for Martin-Löf type theory by normalization by
evaluation (the Agda side: Abel–Öhman–Vezzosi): the same three ingredients — a Kripke model, a
logical relation for soundness, a Kripke PER for completeness — in the simply typed case.

## The calculus

The intrinsically typed calculus of `Start/Stlc.lean`: a base type, `unit`, products and
functions; `Tm Γ A` are the well-typed terms (no separate typing judgement), and the typed
βη-equality judgement is `Stlc.Conv` (the least congruence with β and η for functions, the
projection rules and surjective pairing for products, and the terminality rule for `unit`).  The
repository's Curry-style calculus `Start/SimpleTypes.lean` was not used: its abstractions carry no
type, so evaluation cannot be defined by recursion on terms (a typing derivation is a proof, not
data).

## Definitions

* `StlcNbE.Sem : Ty → Ctx → Type` — the **Kripke model of presheaves on context renamings**:
  `Sem base Γ = Tm Γ base`, `Sem unit Γ = PUnit`, `Sem (A × B) Γ = Sem A Γ × Sem B Γ`,
  `Sem (A ⇒ B) Γ = ∀ Δ, Ren Γ Δ → Sem A Δ → Sem B Δ`; `StlcNbE.Sem.ren` is the presheaf action
  (`Sem.ren_ren`, `Sem.ren_id`: functoriality).
* `StlcNbE.eval : Tm Γ A → Env Γ Δ → Sem A Δ`.
* `StlcNbE.reflect`, `StlcNbE.reify` (mutual, by recursion on the type) — reification η-expands at
  function, product and unit types, so `reify` produces β-normal η-long forms.
* `StlcNbE.nf t := reify A (eval t (idEnv Γ))`, with `idEnv` reflecting every variable.

## Soundness (`Start/StlcNbE.lean`)

`StlcNbE.R A t v` — the Kripke logical relation (`Conv t v` at the base type, componentwise at
products, and at `A ⇒ B`: for every renaming `r` and related `s`, `a`, the application of the
renamed `t` to `s` is related to `f Δ r a`).  `R.conv` (closed under conversion), `R.ren`
(stable under renaming), `reflect_reify` (reflected terms are related; a related value reifies to
a convertible term), `fundamental` (substitution instances in related environments).

```lean
theorem StlcNbE.nf_sound {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Conv t (nf t)
```

## Completeness and decidability (`Start/StlcNbEComplete.lean`)

`StlcNbE.EqS A a b` — the Kripke PER: equality at the base type, componentwise at products, and at
`A ⇒ B` extensionality together with **uniformity** (`Sem.ren r' (f Δ r a)` related to
`f Θ (r' ∘ r) (Sem.ren r' a)`, for both functions).  Uniformity is what makes the η-rule and the
application case of naturality go through; without it the Kripke function space contains
non-natural functions and `eval` is not natural.  Lemmas: `EqS.per` (symmetric, transitive),
`EqS.ren`, `reflect_reify_eq` (reflection uniform and natural; reification identifies related
values and commutes with renaming), `eval_resp` (evaluation respects related environments and is
natural), `eval_ren`, `eval_sub`, `eval_conv` (convertible terms evaluate to related values).

```lean
theorem StlcNbE.nf_complete {Γ : Ctx} {A : Ty} {t u : Tm Γ A} (h : Conv t u) : nf t = nf u
theorem StlcNbE.conv_iff_nf_eq {Γ : Ctx} {A : Ty} (t u : Tm Γ A) : Conv t u ↔ nf t = nf u
instance StlcNbE.decidableConv {Γ : Ctx} {A : Ty} (t u : Tm Γ A) : Decidable (Conv t u)
```

`DecidableEq` for `Stlc.Var` and `Stlc.Tm` is derived in `Start/StlcNbEComplete.lean`.

Status: all three exit criteria met, `DONE_STRONG`.  Not done (not required by the row): a
syntactic predicate of β-normal η-long forms with the proof that `nf` lands in it.
