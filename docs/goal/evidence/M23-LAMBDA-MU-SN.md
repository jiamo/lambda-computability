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

## Round 3 — the substitution calculus (`Start/LambdaMuSubstLemmas.lean`)

Proved: `up_id`, `ren_id`, `up_comp`, `ren_ren`, `nameOf_ren`, `upS_up`, `subst_ren`, `ren_upS`,
`ren_subst`, `upS_comp`, `subst_subst`, `subst_var`, `subst_single`, and `sstr_ren` (structural
substitution commutes with an injective renaming).

Still open: `LambdaMu.sn_of_typ`. The first missing lemma is the commutation `sstr ∘ subst` for a
name-respecting `σ` (one that sends names to variables and is injective on names). After it
come `Step.ren`, `Step.subst` (`Step t t' → Step (subst σ t) (subst σ t')` for name-respecting
`σ`) and the structural analogue `Step t t' → TransGen Step (sstr a v t) (sstr a v t')`. Then
the β- and μ-expansion lemmas, the fundamental lemma, and `sn_of_typ`.

## Round 4 — stability of reduction (`Start/LambdaMuStep.lean`)

Proved (axioms at most `[propext, Classical.choice, Quot.sound]`):

* `Tm.NameFree a t` (the index `a` is not a free name of `t`) and `sstr_nameFree`
  (structural substitution at such an `a` is the identity), with `nameFree_ren`,
  `nameFree_ren_of_ne`, `nameFree_ren_succ`;
* `Tm.subst_sstr` — **the commutation `subst ∘ sstr`**: for `τ` with `NamesVar τ t`, `τ a = var a`,
  no other index sent to the name `a`, and no `τ i` mentioning the name `a`,
  `subst τ (sstr a v t) = sstr a (subst τ v) (subst τ t)`;
* `Step.ren : Step t t' → Function.Injective r → Step (ren r t) (ren r t')`;
* `Step.subst : Step t t' → NamesVar σ t → Step (subst σ t) (subst σ t')`.

Still open: `LambdaMu.sn_of_typ`.  **First missing lemma:** the structural analogue

```lean
theorem Step.sstr {t t' : Tm} (hs : Step t t') (a : ℕ) (v : Tm) :
    Relation.TransGen Step (Tm.sstr a v t) (Tm.sstr a v t')
```

Its β case needs `sstr a v (subst (single u) b) = subst (single (sstr a v u)) (sstr (a+1) (ren
succ v) b)` (expected from `subst_sstr` and `ren_single`, not yet derived), and its structural and
renaming cases need the commutation `sstr ∘ sstr` of two structural substitutions at different
names, which is not proved; a renaming step at the name `a` itself becomes one structural step
followed by one renaming step (hence `TransGen`, not `Step`).  After it: the β- and μ-expansion
lemmas, the fundamental lemma, and `sn_of_typ`.

## Round 5 — stability under structural substitution (`Start/LambdaMuSstr.lean`)

Proved (`lake build --wfail`; axioms `propext, Classical.choice, Quot.sound` or fewer):

* `LambdaMu.Tm.TmFree a t` — the index `a` is never used as a *term* variable of `t`;
  `LambdaMu.Typ.tmFree` — in a well-typed term, every name of the context is `TmFree`.
* `LambdaMu.Tm.sstr_sstr` — **the commutation `sstr ∘ sstr`**:
  `b ≠ c → NameFree b w → sstr c w (sstr b x t) = sstr b (sstr c w x) (sstr c w t)`.
* `LambdaMu.Tm.sstr_subst`, `LambdaMu.Tm.sstr_subst2` — `sstr` after a substitution that sends one
  name, resp. merges two names, onto the structural name.
* **`LambdaMu.Step.sstr`** `(hs : Step t t') (a : ℕ) (v : Tm) (ha : Tm.TmFree a t) :
  Relation.TransGen Step (Tm.sstr a v t) (Tm.sstr a v t')` — one step becomes one step, except a
  renaming redex `[a]μγ.c`, which becomes two steps (a structural step, then the renaming step).
  Compared with the round-4 statement, the side condition `TmFree a t` is needed (if `a` is also a
  term variable of `t`, a β-step can substitute a term for it and `sstr` no longer commutes); it
  holds for every name of a well-typed term, giving `LambdaMu.Step.sstr_of_typ`.

Route: the original de Bruijn representation (names and term variables share one index space);
the two-sort fallback was not needed for this lemma.

Open: `theorem LambdaMu.sn_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
LambdaMu.SN t`.  **First missing lemma**: the μ-expansion lemma with stacks,
`sn_apps_mu : (∀ u ∈ π, SN u) → SN (muStk β t π) → SN (apps (mu β t) π)`
(SN of a μ-abstraction applied to a stack from SN of the iterated structural substitution of the
stack), whose proof is an induction on the SN of the components using `Step.sstr` for the steps
inside `t`; then the β-expansion lemma, the fundamental lemma for `Red` and `sn_of_typ`.

## Round 6 — strong normalization of typed λμ (closed)

Modules: `Start/LambdaMuExpand.lean`, `Start/LambdaMuFund.lean` (`lake build --wfail`; axioms
`propext, Classical.choice, Quot.sound`, see `M23-LAMBDA-MU-SN-axioms.txt`).

* `LambdaMu.SN.ren`, `LambdaMu.sn_mu` — SN under renaming and under μ-abstraction
  (`step_ren_inv`: a step of a renamed term comes from a step of the term).
* **μ-expansion with stacks** — `LambdaMu.sn_apps_mu : ∀ (π : List Tm) {Δ A R β t}, Typ Δ (mu β t) A →
  TStk Δ A π R → (∀ v ∈ π, SN v) → SN (mu β (sbs π β t)) → SN (apps (mu β t) π)`.  Compared with
  the round-5 statement it carries a typing of the μ-abstraction and of the stack (`TStk`), which
  supplies the `TmFree` side condition of `Step.sstr` for the name `β`, and the iterated structural
  substitution `sbs π β t` is kept under its μ-binder.
* **β-expansion with stacks** — `LambdaMu.sn_apps_beta (hu : SN u) : Typ (.tm C :: Δ) X B →
  (∀ v ∈ π, SN v) → SN (apps (subst (single u) X) π) → SN (apps (app (lam X) u) π)`.
* The fundamental lemma: `Tm.msub σ ρ` (simultaneous substitution of terms for term variables and
  stacks for names, `sstr_msub`, `sbs_msub`), Kripke candidates `RedK A Δ` (over renamings `RenOK`)
  with stack candidates `RStk`, and `Good Γ Δ σ ρ` (related substitutions; it carries the `TmFree`
  condition for the names of well-typed terms):
  `LambdaMu.fundamental (h : Typ Γ t A) : Good Γ Δ σ ρ → RedK A Δ (Tm.msub σ ρ t)`.
* **The terminal theorem**:

```lean
theorem LambdaMu.sn_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) : SN t
```

* Corollary (normalization of classical natural deduction through `call/cc`):
  `LambdaMu.sn_callcc_proof (hf : Typ Γ f (.arr (.arr A B) A)) : SN (app Tm.callcc f)` and
  `LambdaMu.callcc_proof_normalizes (hf : Typ Γ f (.arr (.arr A B) A)) : ∃ n,
  Relation.ReflTransGen Step (app Tm.callcc f) n ∧ ∀ n', ¬ Step n n'` — every proof of a Peirce
  instance built with `callcc` reduces to a normal form.

Status: `DONE_STRONG` (exit criterion: typed λμ proved strongly normalizing directly).  The parent
row M23-LAMBDA-MU, whose only open point was this gap, is `DONE_STRONG`.
