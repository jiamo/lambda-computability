# M29 — Expansion postponement for pure type systems (TLCA open problem 23)

Module: `Start/PTSExpansion.lean` (imports `Start/PTSTyping.lean` and
`Start/PTSNormalization.lean`; no existing module was edited).

## Summary of the outcome

| Row | Status | What is proved |
| --- | --- | --- |
| M29-EP-STATEMENT | IN_PROGRESS | exit criterion 1 (definitions, `HasTypeR.toHasType`); also `expansionPostponement_iff_sortedSubjectReductionR`. **Poll's theorem (exit criterion 2) is not proved.** |
| M29-EP-CLASS | TODO_READY | nothing; no route was found |
| M29-EP | TODO_READY | nothing beyond the equivalent reformulation; neither direction closed |

Stage A did **not** fully close. Under the stop rule the first missing lemma is recorded
below and in each row's `open_boundary`.

## Definitions (verbatim, no change of form)

```lean
namespace PureTypeSystem

/-- Typing with the conversion rule replaced by beta-reduction of the type. -/
inductive HasTypeR {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeR P [] (.sort s) (.sort t)
  | var {Γ A s} : HasTypeR P Γ A (.sort s) →
      HasTypeR P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasTypeR P Γ M B → HasTypeR P Γ A (.sort s) →
      HasTypeR P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasTypeR P Γ A (.sort s₁) →
      HasTypeR P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeR P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasTypeR P (A :: Γ) b B →
      HasTypeR P Γ (.pi A B) (.sort s) →
      HasTypeR P Γ (.lam A b) (.pi A B)
  | application {Γ f a A B} : HasTypeR P Γ f (.pi A B) →
      HasTypeR P Γ a A → HasTypeR P Γ (.app f a) (B.instantiate a)
  | reduction {Γ M A B} : HasTypeR P Γ M A → Beta A B → HasTypeR P Γ M B

def ExpansionPostponement {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ M A, HasType P Γ M A →
    ∃ B, Relation.ReflTransGen Beta A B ∧ HasTypeR P Γ M B
```

The two definitions are exactly the ones in the instruction. Auxiliary notions added:
`ValidContextR` (contexts typed in `HasTypeR`), `TypedSubstitutionR`, and

```lean
def SortedSubjectReductionR {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ M M' s, HasTypeR P Γ M (.sort s) → Beta M M' → HasTypeR P Γ M' (.sort s)
```

## Proved results (all with only the standard axioms)

```lean
theorem HasTypeR.toHasType (h : HasTypeR P Γ M A) : HasType P Γ M A
theorem HasTypeR.subst (h : HasTypeR P Γ M T) (hΔ : ValidContextR P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitutionR P Γ Δ σ) : HasTypeR P Δ (M.subst σ) (T.subst σ)
theorem HasTypeR.instantiate (hb : HasTypeR P (A :: Γ) b B) (ha : HasTypeR P Γ a A) :
    HasTypeR P Γ (b.instantiate a) (B.instantiate a)
theorem HasTypeR.weaken_under ...
theorem HasTypeR.generation_pi ...   -- generation for products
theorem HasTypeR.generation_lam ...  -- generation for abstractions
theorem expansionPostponement_of_sortedSubjectReductionR
    (hsr : SortedSubjectReductionR P) : ExpansionPostponement P
theorem expansionPostponement_iff_sortedSubjectReductionR (P : Specification S) :
    ExpansionPostponement P ↔ SortedSubjectReductionR P
```

`toHasType`: the reduction case uses `regularity` (the type is a sort, which is normal and
cannot reduce, or is typed by a sort), then `subject_reduction` for the new type and the
conversion rule.

`expansionPostponement_iff_sortedSubjectReductionR` holds for **every** specification (no
normalization and no functionality). (→): take the `HasType` subject reduct (by
`subject_reduction`) and apply EP; a sort only reduces to itself. (←): induction on the `HasType`
derivation. The conversion case needs only confluence. The application case joins the two reducts
of the domain. The abstraction case is the only place where reduction of a subject is needed:
the body is typed at a reduct `B'` of `B`, and `Π A B'` must be typed from `Π A B` (product
generation, then `SortedSubjectReductionR` on the codomain `B`).

## Why `ExpansionPostponement` is TLCA's statement

TLCA problem 23 compares the system with conversion and the system ⊢βη in which conversion is
split into a reduction rule (`Γ ⊢ M : A`, `A ↠ B` gives `Γ ⊢ M : B`) and an expansion rule
(`Γ ⊢ M : B`, `Γ ⊢ A : s`, `A ↠ B` gives `Γ ⊢ M : A`). Expansion postponement says that every
⊢βη derivation can be rearranged so that expansion is used at most once, as the last step.

* A derivation whose only expansion is its last step consists of a `HasTypeR` derivation of
  `Γ ⊢ M : B` followed by one expansion to a type `A` with `A ↠β B`. So "`Γ ⊢ M : A` has such a
  derivation" means `∃ B, A ↠β B ∧ HasTypeR P Γ M B`, together with the side premise `Γ ⊢ A : s`
  of that expansion.
* That side premise is itself reduction-only whenever `ExpansionPostponement` holds: applied to
  `Γ ⊢ A : s`, it gives `HasTypeR P Γ A s'` with `s ↠β s'`, and `s' = s` because a sort is
  normal (`HasTypeR.sort_reduces`).
* By confluence (`Reduces.confluent`, `Converts.join`), conversion is a combination of a
  reduction and an expansion. So the reduction-and-expansion system derives exactly the
  judgements of `HasType`: reduction steps are sound by `HasTypeR.toHasType`, and expansion
  steps are instances of the conversion rule.

The equivalence with the derivation-shaped formulation is argued here and is not proved in Lean.

## Poll's theorem: not proved

Neither `expansionPostponement_of_sn` nor `expansionPostponement_of_wn` is in the library.
Nothing has been proved under either name, and no weaker statement has been put under them.

By `expansionPostponement_iff_sortedSubjectReductionR`, and by `weak_implies_strong` for the weak
form, both follow from the **first missing lemma**:

```lean
theorem sortedSubjectReductionR_of_sn {S : Type u} {P : Specification S}
    (hsn : SystemStronglyNormalizing P) : SortedSubjectReductionR P
```

The route would be:

```lean
theorem expansionPostponement_of_sn {S : Type u} {P : Specification S}
    (hsn : SystemStronglyNormalizing P) : ExpansionPostponement P :=
  expansionPostponement_of_sortedSubjectReductionR (sortedSubjectReductionR_of_sn hsn)
theorem expansionPostponement_of_wn {S : Type u} {P : Specification S}
    (hwn : SystemWeaklyNormalizing P) : ExpansionPostponement P :=
  expansionPostponement_of_sn (weak_implies_strong P hwn)
```

No extra hypothesis (such as functionality) has been identified as needed.

### Where normalization is used, and where the attempted proof breaks

The argument we tried, written out here because it locates the difficulty, is an induction on
`HasTypeR` derivations proving subject reduction with context reduction. Its statement: from
`Γ ⊢R M : C`, `Γ ↠ Γ'` (pointwise, `Γ'` valid in `HasTypeR`) and `M ↠ M'`, get some `C'` with
`C ↠ C'` and `Γ' ⊢R M' : C'`.

* All structural cases go through. The `reduction` case uses confluence. The non-head
  application case joins the two domain reducts. The abstraction case applies the induction
  hypothesis on the product premise at the reduct `Π A₁ B₃`: since that hypothesis covers every
  reduct of the subject, the multi-step reduction of the codomain causes no trouble.
* **The step that uses normalization** is the head-redex case `(λx:X. c) a ↠ c[a/x]`. The
  argument `a` is typed only at a reduct `Z` of `X`. So the body `c` must be retyped in the context
  `x : Z` (a context reduction), then instantiated (`HasTypeR.instantiate`), and then the
  reducts of `c[a/x]` must be typed. The derivations of `c` and `c[a/x]` are not subderivations.
  Under strong normalization they are reached by an outer well-founded induction on the subject,
  over "β-reduct or proper subterm" (`StronglyNormalizing.induction_subterms`); `c`, `X` and
  `c[a/x]` all lie strictly below `(λx:X. c) a` in this order.
* **Why this does not close.** The outer induction is on the subject. The inner induction on the
  derivation must therefore carry the outer hypothesis down to every subderivation. The premise
  `Γ ⊢R Π A B : s` of an abstraction has subject `Π A B`, where `B` is the type of the body. This
  subject is not below `λ A b` in the order, so the outer hypothesis is not available for redexes
  inside `B`. Normalizing types first (Poll's normal-form systems) moves the same obstruction to
  the substitution lemma: in its abstraction case, `Π A[σ] nf(B[σ↑])` must be typed from
  `(Π A B)[σ]`.

This confirms the reading in the instruction: the difficulty is the redex case, where the
context entry must be reduced, and that re-enters subject reduction at product-formation
premises. In addition, it locates the circle more precisely. With an outer induction on the
subject, the product premise of an abstraction is a judgement about the *type* of the body, which
no order on subjects controls. A proof (of Poll's case or of the general case) needs a measure
that controls the types of bodies as well as subjects, or an argument that avoids retyping
bodies.

## Stage B (M29-EP-CLASS)

No class was reached, and no route was written down as a list of Lean lemmas. First missing
lemma, for a class `C`:

```lean
theorem sortedSubjectReductionR_of_class {S : Type u} {P : Specification S} (hC : C P) :
    SortedSubjectReductionR P
```

after which `expansionPostponement_of_sortedSubjectReductionR` closes the row.

Barthe's notion, as we recall it (please check it against Barthe 1998/1999 before relying on
it): a PTS is *injective* if it is functional, that is, `(s, t)` and `(s, t')` in the axioms
imply `t = t'`, and `(s₁, s₂, s₃)` and `(s₁, s₂, s₃')` in the rules imply `s₃ = s₃'`. In addition,
`(s, t), (s', t)` in the axioms imply `s = s'`, and `(s₁, s₂, s₃), (s₁, s₂', s₃)` in the rules imply
`s₂ = s₂'`. We are not certain this matches Barthe's definition exactly. In particular, under
this reading System U⁻ (`Start/PTSHurkens.lean`) appears to be injective, so a Stage B witness
would need extra, non-injective axioms or rules.

## Stage C (M29-EP)

Not closed in either direction. The equivalent form proved for every specification:
`ExpansionPostponement P ↔ SortedSubjectReductionR P`.

* Proof direction, first missing lemma:
  ```lean
  theorem sortedSubjectReductionR_all {S : Type u} (P : Specification S) :
      SortedSubjectReductionR P
  ```
* Counterexample direction: by the equivalence, a counterexample is a specification with a
  `HasTypeR` judgement `Γ ⊢R M : s` and a step `M →β M'` such that `Γ ⊢R M' : s` is not
  derivable. Ruling that out needs the generation lemmas (`HasTypeR.generation_pi`,
  `HasTypeR.generation_lam` are proved) and an invariant. No candidate specification was
  searched.
