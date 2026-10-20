# M25-SYSTEM-FC — System F with type-equality coercions (round 4)

Lean: `Start/SystemFCoerce.lean`, namespace `FCoerce` (the existing `Start/SystemFC*.lean` files
are Church-style System F, namespace `SystemFC`).  Style of Sulzmann, Chakravarty, Peyton Jones
and Donnelly (2007), over the types of `Start/SystemF.lean`: type variables, `→`, `∀`.

## Syntax and typing

* Coercions `Co`: `refl A`, `sym γ`, `trans γ δ`, `arr γ δ` (application of the arrow
  constructor, `γ → δ`), `all γ` (congruence under `∀`), `inst γ C` (instantiation `γ @ C`),
  `ax i` (the `i`-th axiom), `left γ`, `right γ` (decomposition of an arrow coercion, used by the
  push rule).
* `CoTyping Ax γ A B` — `γ : A ~ B` for the axiom set `Ax : List (FTy × FTy)`.
* Terms `Tm`: Church-style System F plus the cast `cast t γ` (`t ▷ γ`); `Typing Ax Γ t A`, with
  `Γ ⊢ t : A`, `γ : A ~ B` ⟹ `Γ ⊢ t ▷ γ : B`.
* `Step`: β, type-β, all congruences, and the coercion rules
  `(t ▷ γ) ▷ δ ⟶ t ▷ (γ ; δ)`,
  `((λx:A. t) ▷ γ) u ⟶ ((λx:A. t) (u ▷ sym (left γ))) ▷ right γ`,
  `((Λ. t) ▷ γ) C ⟶ ((Λ. t) C) ▷ (γ @ C)`.

## Results

```lean
def FCoerce.AxClosed (Ax : List (FTy × FTy)) : Prop :=
  ∀ p ∈ Ax, ∀ s : ℕ → FTy, tySubst s p.1 = p.1 ∧ tySubst s p.2 = p.2

theorem FCoerce.Typing.preservation (hAx : AxClosed Ax) {Γ : List FTy} {t : Tm} {A : FTy}
    (h : Typing Ax Γ t A) : ∀ t' : Tm, Step t t' → Typing Ax Γ t' A

def FCoerce.Consistent (Ax : List (FTy × FTy)) : Prop :=
  ∀ (γ : Co) (A₁ B₁ C : FTy),
    ¬ CoTyping Ax γ (.arrow A₁ B₁) (.all C) ∧ ¬ CoTyping Ax γ (.all C) (.arrow A₁ B₁)

theorem FCoerce.Typing.progress (hcon : Consistent Ax) {t : Tm} {A : FTy} (h : Typing Ax [] t A) :
    Value t ∨ ∃ t', Step t t'

theorem FCoerce.Typing.safety (hAx : AxClosed Ax) (hcon : Consistent Ax) {t t' : Tm} {A : FTy}
    (h : Typing Ax [] t A) (hs : Relation.ReflTransGen Step t t') :
    Typing Ax [] t' A ∧ (Value t' ∨ ∃ t'', Step t' t'')
```

Values are abstractions and type abstractions, possibly under one cast.  The consistency
hypothesis is stated explicitly (`Consistent`): no coercion derivable from the axioms relates an
arrow type and a `∀`-type.  It is used exactly in the two stuck cases of progress
(`((Λ. t) ▷ γ) u` with `γ : ∀A ~ (A₂ → B₂)`, and `((λx. t) ▷ γ) C` with `γ : (A → B) ~ ∀B'`).
Preservation needs closed axioms (`AxClosed`), because a type abstraction may contain a cast by
an axiom and type-β substitutes into it.

## Gap (row M25-SYSTEM-FC-TYCON)

The type language has only `→` and `∀`, so "application" coercions are applications of the arrow
constructor and axioms relate closed `→`/`∀` types.  FC proper has data type constructors and
type-level application `T τ₁ ⋯ τₙ` (type families, newtypes), with application coercions
`γ₁ γ₂`, their decompositions, and consistency stated as "no coercion between distinct type
constructor heads".  First missing construction: a type syntax with constructors and type
application, its substitution calculus (the analogue of `Start/SystemFSubst.lean`), and the push
rule for data constructors (`K (t ▷ γ)` case analysis).  Hence the row is DONE_WEAK.

Axioms: `M25-SYSTEM-FC-axioms.txt`, at most `[propext, Classical.choice, Quot.sound]`.

## Round 5 — data types, type application and application coercions (row M25-SYSTEM-FC-TYCON)

Modules: `Start/SystemFCTyConTypes.lean` (types with constructors `con T` and type application,
their substitution calculus, `tapps T σ`, coercions with `capp`, `appL`/`appR` decompositions and
axiom schemes, `CoTyping` and its substitution lemma, `liftCo`, `conCo`, `nthCo`, `nthCos`) and
`Start/SystemFCTyCon.lean` (data signatures, constructors and `case`, typing, reduction with the
push rule `casePush`, preservation, consistency, progress, safety).

Terminal theorems (`lake build --wfail`; axioms in `M25-SYSTEM-FC-TYCON-axioms.txt`):

* `FCTyCon.Typing.preservation (hD : SigOK D) (hAx : AxOK Ax) (h : Typing D Ax Γ t A) :
  ∀ t', Step D t t' → Typing D Ax Γ t' A`;
* `FCTyCon.Consistent Ax` — a derivable coercion never relates types with different heads
  (`→`, `∀`, or a type constructor); `FCTyCon.Consistent.tapps_ne` (distinct constructor heads are
  never related), `FCTyCon.consistent_nil`;
* `FCTyCon.Typing.progress (hcon : Consistent Ax) (h : Typing D Ax [] t A) :
  Value t ∨ ∃ t', Step D t t'`;
* `FCTyCon.Typing.safety`.

Scope.  Constructors take one field (several fields are a tuple-typed field; a nullary
constructor is a field of a closed type); axioms are schemes `(n, τ₁, τ₂)` over `n` parameters,
which covers type-family instances `F σ ~ τ` and newtypes `N α ~ φ`.  With this the exit
criterion of M25-SYSTEM-FC ("System F with type-equality coercions ... preservation, then progress
under an explicitly stated consistency hypothesis") holds for FC with data types; both rows are
`DONE_STRONG`.
