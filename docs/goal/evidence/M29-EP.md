# M29 — Expansion postponement for pure type systems (TLCA open problem 23)

Modules:
* `Start/PTSExpansion.lean` — the reduction-only judgement `HasTypeR`, `ExpansionPostponement`,
  and `expansionPostponement_iff_sortedSubjectReductionR` (earlier delivery).
* `Start/PTSExpansionLevels.lean` — **Stage B**: `Stratification` and
  `expansionPostponement_of_stratification`; U⁻ and the non-dependent cube corners are stratified.
* `Start/PTSExpansionBeyondPoll.lean` — **Stage B witness** `W`.
* `Start/PTSExpansionPoll.lean` — **Stage A**: Poll's theorem reduced to `ProductNormalizationR`.

No existing module was edited except `Start.lean` and `Start/Capstones.lean` (imports and
`#check` registration).  `Start/PTSBasic.lean` and `Start/PTSExpansion.lean` are unchanged, no
axiom was added.

## Summary of the outcome

| Row | Status | What is proved |
| --- | --- | --- |
| M29-EP-STATEMENT | IN_PROGRESS | exit criterion 1; `expansionPostponement_iff_sortedSubjectReductionR`; for weakly normalizing `P`, `ExpansionPostponement P ↔ ProductNormalizationR P`. **Poll's theorem (exit criterion 2) is not proved.** |
| M29-EP-CLASS | DONE_STRONG | `expansionPostponement_of_stratification`; the class contains `W`, which is not weakly normalizing and not functional. |
| M29-EP-BEYOND-POLL | DONE_STRONG | `W` (5 sorts), `W_typed_type_not_wn`, `W_not_functional`, `W_expansionPostponement`. |
| M29-EP | TODO_READY | not closed in either direction; stopped under the stop rule. |

`#print axioms` for every theorem named in this file reports only `propext`,
`Classical.choice`, `Quot.sound` (see the end of the file).

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


## Stage B: expansion postponement for stratified systems (M29-EP-CLASS)

### Statement (form unchanged)

```lean
structure Stratification {S : Type u} (P : Specification S) where
  level : S → ℕ
  bound : ℕ
  level_le : ∀ s, level s ≤ bound
  axiom_level : ∀ s t, P.axioms s t → level t = level s + 1
  rule_level : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁

theorem expansionPostponement_of_stratification {S : Type u} {P : Specification S}
    (L : Stratification P) : ExpansionPostponement P
```

Both are exactly as in the instruction.  `Stratification` is a structure (data), so the class is
the predicate `C P := Nonempty (Stratification P)`; it is defined without reference to expansion
postponement.

### The proof, step by step, against the sketch

**Step 1 (level of a term).** Instead of the syntactic `lev Γ M` of the sketch, the proof uses the
*relational* formulation that the instruction allows:

```lean
def Stratification.TypeLevel (Γ : List (Expr S)) (T : Expr S) (k : ℕ) : Prop :=
  (∃ t, T = .sort t ∧ L.level t + 1 = k) ∨ (∃ s, HasType P Γ T (.sort s) ∧ L.level s = k)
```

("the inhabitants of `T` live at level `k`").  Typing determines it:

```lean
theorem Stratification.level_unique (ht : HasType P Γ M T) (ht' : HasType P Γ M T')
    (hT : L.TypeLevel Γ T k) (hT' : L.TypeLevel Γ T' k') : k = k'
theorem Stratification.conv_level (hc : Converts T T') (hT : L.TypeLevel Γ T k)
    (hT' : L.TypeLevel Γ T' k') : k = k'
```

With `M : T`, `T : s` this is the sketch's `lev Γ M = level s`, and with `M : sort t` it is
`lev Γ M = level t + 1`.  *Repair needed here:* the sketch says "induct on the derivation"; the
conversion case of that induction needs "convertible typable types have sorts of equal level",
which is the statement itself applied to the common reduct, a term with an unrelated derivation.
So a plain induction on derivations is circular.  The repair: `level_unique_aux` is a
*downward induction on the level* `k` (measure `bound + 2 − k`), with an inner structural
induction on the subject `M`.  The conversion step (`conv_level_of`) for types at level `k` only
needs uniqueness for the common reduct `C : sort s` with `level s = k`, i.e. for a subject whose
types are at level `k + 1` — available from the outer induction.  All other cases use the
generation lemmas and the structural hypothesis at the same level: for `Π A B` the codomain `B`
(level `level s₂ + 1 = level s₃ + 1`), for `λ A b` the body `b` (level `level s₂ = level s₃`), for
`f a` the head `f` (level `level r₃ = level r₂`).  No syntactic level function is needed.

**Step 2 (core lemma).** Exactly as in the sketch:

```lean
theorem Stratification.core (L : Stratification P) (hΓ : ValidContextR P Γ)
    (h : HasType P Γ M T) : ∃ T', Reduces T T' ∧ HasTypeR P Γ M T'
```

proved by `core_aux`, a well-founded induction on `(bound + 2 − k, M)` lexicographically (outer
induction on `n ≥ bound + 2 − k`, inner structural induction on `M`), where `k` is a level with
`TypeLevel Γ T k`.  The cases follow the sketch with no change:
* `var`: `HasTypeR.lookup`, `Converts.join`, `HasTypeR.reduces`; no recursive call.
* `sort`: `HasTypeR.sort_of_valid`; no recursive call.
* `pi A B`: calls on `A` (level `level s₁ + 1 ≥ level s₂ + 1 = k`, subterm) and on `B` in `A :: Γ`
  (level `k`, subterm).
* `app f a`: calls on `f` (level `k`, subterm) and on `a` (level `level r₁ ≥ level r₂ = k`, subterm;
  **this is where `level s₂ ≤ level s₁` is used**); the two domain reducts are joined by confluence.
* `lam A b`: calls on `A` (level `level s₁ + 1`), on `b` (level `k`, subterm), then
  `Γ ⊢ Π A B' : s` in `HasType` by `subject_reduces`, and the call on that judgement at level
  `level s + 1 = k + 1` — **the only call on a subject that is not a subterm; it strictly
  decreases the first component**.  Close with `HasTypeR.abstraction`.

The route uses `subject_reduces` for `HasType` (proved) and never subject reduction for
`HasTypeR`, never normalization.  The levels found in each case are those of the sketch; the
sketch's `bound + 3` became `bound + 2` because `TypeLevel` is one less than `lev` of a sort.

**Step 3.** `Stratification.validContextR : ValidContext P Γ → ValidContextR P Γ` by induction on
`Γ` with the core lemma, and the theorem follows (`regularity` supplies a level for the type).

**Step 4 (what the class contains).**  Proved in Lean:
* `Hurkens.uMinus_stratified : Stratification uMinus` (`∗ ↦ 0`, `□ ↦ 1`, `△ ↦ 2`), hence
  `uMinus_expansionPostponement`.
* `cube_stratified f (hf : f.dep = false)` and `cube_expansionPostponement`: `λ→`, `λ2`, `λω̲`, `λω`.
* `cube_not_stratified f (hf : f.dep = true)`: `λP`, `λP2`, `λPω̲`, `λC` are not stratified, because
  of the rule `(∗,□)` (general form `not_stratified_of_dependent_rule`).
* `lambdaStar_not_stratified`: `λ*` is not, because of `∗ : ∗` (`not_stratified_of_axiom_self`).

Not in Lean, by inspection: System U (axioms `∗ : □`, `□ : △`; rules `(∗,∗)`, `(□,∗)`, `(□,□)`,
`(△,∗)`, `(△,□)`) is stratified with the same levels as U⁻.

### The witness `W` (M29-EP-CLASS and M29-EP-BEYOND-POLL)

`W` is exactly the specification of the instruction (sorts `o, t, t', k, u`, levels
`0, 1, 1, 2, 3`).  Proved (`Start/PTSExpansionBeyondPoll.lean`, namespace
`PureTypeSystem.BeyondPoll`):

```lean
def W_stratified : Stratification W
theorem W_not_functional : ¬ ∀ s a b, W.axioms s a → W.axioms s b → a = b
theorem W_hurkens_typed : HasType W ([]) hurkensW (.pi (.sort .t) (.var 0))
    -- hurkensW := hurkens.mapSort shift, by HasType.mapSort from hurkens_typed
theorem W_not_wn : ¬ SystemWeaklyNormalizing W
theorem W_closed_normal_not_o {N : Expr WSort} (h : HasType W ([]) N (.sort .o))
    (hn : Normal N) : False
theorem W_type_not_wn : HasType W ([]) typeA (.sort .o) ∧ ¬ WeaklyNormalizing typeA
    -- typeA := .app hurkensW (.sort .o)
theorem W_typed_type_not_wn : ∃ Γ a T, HasType W Γ a T ∧ ¬ WeaklyNormalizing T
    -- Γ = [typeA], a = var 0, T = typeA (typeA is closed: typeA_rename)
theorem W_expansionPostponement : ExpansionPostponement W
theorem W_in_class : Nonempty (Stratification W) ∧ ¬ SystemWeaklyNormalizing W ∧
    ¬ (∀ s a b, W.axioms s a → W.axioms s b → a = b)
```

(The bound variables of `W.axioms` and of `W_not_functional` are named `a b` instead of `t t'`,
because `t`, `t'` are constructor names of `WSort`; the meaning is unchanged.)

`W_closed_normal_not_o` is the key lemma of the instruction: by structural induction on `N` with
`normal_shape`; a sort is never typed by `o` (no axiom `_ : o`), a neutral closed term is untyped
(`neutral_nil_untyped`), an abstraction is never typed by a sort, and a product typed by `o` needs
the rule `(o,o,o)`, so its domain is a closed normal term of type `o` (induction hypothesis).

So `W` has a typing judgement whose type has no normal form: **`W` lies outside Poll's
hypothesis** (normalising types).  It is not functional, hence not injective in any sense that
includes functionality.

### Literature check

What we know of each paper, and what we do not know:

* **Poll (1998)**, "Expansion postponement for normalising pure type systems", JFP 8(1).  As
  described in the M29 instruction (we did not have the paper's text): the theorem is stated for
  PTSs with *normalising types* (every `A` with `Γ ⊢ a : A` has a β-normal form), which is weaker
  than weak normalization of the system; the proof goes through the system `⊢nf` (Theorems 8, 11,
  12, Lemmas 9, 10).  Poll's Open Problem 6 and the remark after it state that EP is equivalent to
  weak subject reduction (WSR) for `⊢r`; **`expansionPostponement_iff_sortedSubjectReductionR` is
  a Lean form of that remark, not a new result.**  Poll cites Pollack (1994, LEGO thesis) for a
  counterexample to plain subject reduction for `⊢r`, which is why the sorted/weak form is the
  right one.  `W` is outside Poll's hypothesis (`W_typed_type_not_wn`).
* **Barthe (1999)**, "Type-checking injective pure type systems", JFP 9(6).  We know only the
  published abstract as quoted in the instruction: the result is for a *variant* of injective
  PTSs, in which a clause of the abstraction rule is replaced by constraints on two syntactically
  computed sorts.  The TLCA entry summarizes it as "EP holds for injective PTSs".  As far as we
  know, Barthe's injective PTSs are in particular functional (axioms and rules are functional
  relations, plus injectivity conditions); we have not been able to check the exact definition.
  On that reading `W` is not covered, since `W_not_functional`.  We do not know whether the
  variant system of the paper coincides with `HasType` on any class containing `W`.
* **Song Fangmin (1997)**, "The expansion postponement in pure type systems", J. Comput. Sci. &
  Technol. 12(6).  We know only that it gives necessary and sufficient conditions for EP, and
  sufficient conditions.  We do not know these conditions, so we cannot say whether they cover
  `W` or the stratified class, or whether the level argument appears there.
* **Gutiérrez & Ruiz (2003)**, "Expansion postponement via cut elimination".  Listed in the
  instruction's sources; we do not know its precise class and make no claim about it.

Whether the level argument or the stratified class appears in any of these papers: not in Poll's
argument as described (it is driven by normal forms of types, not by levels), and, for Barthe, not
as far as the abstract shows.  For Song and for Gutiérrez–Ruiz we cannot tell.  **We do not claim
the result is new.**  The Lean formalization is new either way.

## Stage A: Poll's theorem (M29-EP-STATEMENT)

Not proved.  No weaker theorem was put under the names `expansionPostponement_of_sn`,
`expansionPostponement_of_wn`.

### What is proved: a reduction to one lemma (`Start/PTSExpansionPoll.lean`)

```lean
def ProductNormalizationR {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ A B B' s, HasTypeR P Γ (.pi A B) (.sort s) → Reduces B B' → Normal B' →
    HasTypeR P Γ (.pi A B') (.sort s)

theorem productNormalizationR_of_expansionPostponement (h : ExpansionPostponement P) :
    ProductNormalizationR P
theorem expansionPostponement_of_productNormalizationR (hw : SystemWeaklyNormalizing P)
    (hpn : ProductNormalizationR P) : ExpansionPostponement P
theorem expansionPostponement_iff_productNormalizationR (hw : SystemWeaklyNormalizing P) :
    ExpansionPostponement P ↔ ProductNormalizationR P
theorem expansionPostponement_of_productNormalizationR_sn (hsn : SystemStronglyNormalizing P)
    (hpn : ProductNormalizationR P) : ExpansionPostponement P
```

### The routes

**Route (a), relaxed `⊢nf`.**  With the relaxed abstraction rule
(`Γ, x:A ⊢nf b : B`, `Γ ⊢nf Π A B₀ : s`, `B₀ ↠ B` gives `Γ ⊢nf λx:A.b : Π nf(A) B`), the
substitution lemma needs no subject reduction and `⊢ ⊆ ⊢nf` is immediate by induction on `⊢`
(under normalising types).  The bridge `⊢nf ⊆ ⊢r` is a plain induction on `⊢nf` except in the
abstraction case, which needs `Γ ⊢r Π A B : s` from the induction hypothesis `Γ ⊢r Π A B₀ : s`,
with `B = nf(B₀)` normal: this is literally `ProductNormalizationR`.
`expansionPostponement_of_productNormalizationR` formalizes the composite `⊢ ⊆ ⊢nf ⊆ ⊢r` directly,
without introducing `⊢nf`: induction on `HasType`, normalizing the body type in the abstraction
case.  So route (a) closes exactly when `ProductNormalizationR` is proved.  We found no measure
that makes the bridge's abstraction case well founded under `SystemStronglyNormalizing`: the
subject `Π A nf(B₀)` is not below `λ A b` in any order on subjects we could control (subterm,
β-reduct, or the SN order of `λ A b`), because `B₀` is the type of the body, not part of it.

**Route (b), the Stage B induction with `B' = nf(B)`.**  Under normalization the abstraction case
can take `B' = nf(B)`.  What fails is the measure, not the abstraction case: with dependent rules
the application case calls on the argument `a` at a *lower* level (and the product case on the
domain), and abstractions inside `a` call back up on `Π A' nf(B'')` for a different subject.
We looked for an order combining strong normalization (`weak_implies_strong`) with levels, and
found none for which "strict subterm" and "`λx:A.b` to `Π A nf(B)`" both decrease: the second step
produces the normal form of a *type of a subterm*, whose SN height and size are unrelated to those
of `λx:A.b`.

**Route (c).**  None written down.

**First missing lemma** (recorded in the row's `open_boundary`):

```lean
theorem productNormalizationR_of_wn {S : Type u} {P : Specification S}
    (hw : SystemWeaklyNormalizing P) : ProductNormalizationR P
```

With it, `expansionPostponement_of_wn` is `expansionPostponement_of_productNormalizationR hw
(productNormalizationR_of_wn hw)`, and `expansionPostponement_of_sn` follows via
`weaklyNormalizing_of_stronglyNormalizing`.  No extra hypothesis has been identified as needed.

### Verdict on Poll's Lemma 10

**The gap is genuine** as far as Poll's argument goes, with the unrelaxed `nf-abstraction` rule.
Exact case: the abstraction case of Lemma 10.  Premises `Γ, x:a, Δ, y:C ⊢nf b : B` and
`Γ, x:a, Δ ⊢nf Π C B : s`; the conclusion must be `Γ, Δσ ⊢nf λy:Cσ. bσ : Π nf(Cσ). nf(Bσ↑)`.  The
induction hypothesis gives `Γ, Δσ ⊢nf Π Cσ. Bσ↑ : s`, but `nf-abstraction` needs the premise
`Γ, Δσ ⊢nf Π Cσ. nf(Bσ↑) : s`; `Bσ↑` is not normal in general (substitution creates redexes).
Getting from one to the other is subject reduction for `⊢nf` at a sort-typed judgement, i.e.
Theorem 11, which is proved using Lemma 10.  The circularity cannot be broken by a simultaneous
induction on derivation size, because the derivation given by the induction hypothesis of the
substitution lemma is not a subderivation and has no size bound.  We have **not repaired** it: the
relaxed rule removes the gap from Lemma 10 but moves the same statement to the bridge
`⊢nf ⊆ ⊢r` (route (a) above), where it is `ProductNormalizationR`.  We have not shown that Poll's
theorem is false, nor that his other lemmas fail.

## Earlier delivery: the attempted subject-reduction argument

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



## Stage C: the general problem (M29-EP)

Not closed in either direction; stopped under the stop rule.

After Stage B, an open case has dependent rules (`level s₂ > level s₁` for every leveling),
unbounded levels, or no stratification at all; and (if Poll's theorem holds) a type with no
normal form.  The Stage B proof breaks only in the measure: in the application case the argument
sits at a lower level, and in the product case the domain does.

Test cases recorded in Lean (`Start/PTSExpansionBeyondPoll.lean`, `Start/PTSExpansionLevels.lean`):
* `Wdep` := `W` plus the dependent rule `(o, t, t)`: `Wdep_not_stratified`, `Wdep_not_wn`.
* `lambdaStar` (`∗ : ∗`, rule `(∗,∗,∗)`): `lambdaStar_not_stratified`.

* **Measure direction.** We did not find a measure for `Wdep`, for U⁻ plus `(∗,□,□)`, or for `λ*`.
  For `Wdep`, the chain of calls can go: abstraction at level 1 (sort `t`) → its product type
  `Π A nf(B)` at level 2 → inside it, through the dependent rule `(o,t,t)`, an application
  argument at level 0 (sort `o`) → an abstraction there → its product type at level 1 → … ; the
  subjects reached are normal forms of types of subterms, so neither the level nor the size
  decreases along such a chain.  First missing lemma:
  ```lean
  theorem Wdep_expansionPostponement : ExpansionPostponement Wdep
  ```
  (equivalently, by `expansionPostponement_iff_sortedSubjectReductionR`,
  `SortedSubjectReductionR Wdep`).
* **Counterexample direction.** A counterexample in `Wdep` would need a judgement whose chain of
  calls never terminates and an invariant on `HasTypeR` derivations excluding the reduction-only
  judgement.  We did not find a candidate term and did not state an invariant; no route was
  written as Lean lemma statements, so we stopped.
* The general first missing lemma is unchanged:
  ```lean
  theorem sortedSubjectReductionR_all {S : Type u} (P : Specification S) :
      SortedSubjectReductionR P
  ```

## `#print axioms`

All of the following report `[propext, Classical.choice, Quot.sound]` or a subset:
`expansionPostponement_of_stratification`, `Stratification.level_unique`,
`Stratification.conv_level`, `Stratification.core`, `Hurkens.uMinus_stratified`,
`cube_expansionPostponement`, `cube_not_stratified`, `lambdaStar_not_stratified`,
`BeyondPoll.W_stratified`, `BeyondPoll.W_not_functional`, `BeyondPoll.W_hurkens_typed`,
`BeyondPoll.W_not_wn`, `BeyondPoll.W_closed_normal_not_o`, `BeyondPoll.W_type_not_wn`,
`BeyondPoll.W_typed_type_not_wn`, `BeyondPoll.W_expansionPostponement`, `BeyondPoll.W_in_class`,
`BeyondPoll.Wdep_not_stratified`, `BeyondPoll.Wdep_not_wn`,
`expansionPostponement_iff_productNormalizationR`,
`expansionPostponement_of_productNormalizationR_sn`.  The exact output is in
`docs/goal/evidence/M29-EP-axioms.txt`.

## Later delivery: syntax-directed completeness, the note, and the dependent case

* **M29-SD-COMPLETE (DONE_STRONG).**  `Start/PTSSyntaxDirected.lean` proves completeness of
  Pollack's syntax-directed system `HasTypeSD` for every functional stratified PTS
  (`sd_complete_of_stratification`), with corollaries for U⁻, the non-dependent cube corners and
  `W₀` (functional, stratified, a well-typed type with no normal form).  Details and literature:
  `docs/goal/evidence/M29-SD-COMPLETE.md`.
* **M29-EP-NOTE.**  A self-contained mathematical note on the level argument, both theorems and
  the witnesses: `docs/goal/evidence/M29-EP-NOTE.md`.
* **M29-EP, dependent case: no route.**  Under the stop rule we continued only while a route was
  written as Lean lemma statements; none was.  The instruction's observation locates the two
  places where a call one level up is needed in `⊢r` (exposing a `Π` in the type of a function,
  and retyping the codomain `D` of an application in the context `x : W` for a reduct `W` of the
  domain `X`).  We could not state, for a dependent system such as `Wdep`, an invariant that
  controls the second place at every level (the argument sits at a lower level, so the retyping
  of `D` is not bounded by the level measure), nor a candidate term on which both places fail.
  The row M29-EP is unchanged; its first missing lemmas remain `Wdep_expansionPostponement` and
  `sortedSubjectReductionR_all`.

## M29-EP-LOCAL: levels without a bound (DONE_STRONG)

Module `Start/PTSExpansionLocal.lean`.  No normalization hypothesis, no bound on the levels.

* `expansionPostponement_of_levels (level : S → ℕ) (hax : ∀ s t, P.axioms s t → level t = level s + 1)
  (hrule : ∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → level s₃ = level s₂ ∧ level s₂ ≤ level s₁) :
  ExpansionPostponement P`.
* `sd_complete_of_levels (hf : Functional P) level hax hrule (h : HasType P Γ M T) :
  ∃ T', HasTypeSD P Γ M T' ∧ Converts T' T`.

Proof, as in the route of the instruction:

1. `HasType.finite_support` (`Start/PTSRestriction.lean`) gives a derivation of the same judgement
   in `P.restrict A R` with `A`, `R` finite.
2. `levelsStratification`: on `P.restrict A R`, `fun s => min (level s) N`, with `N =
   levelsBound level A R` the largest level occurring in `A` and `R`, is a `Stratification`
   (every sort of a restricted axiom or rule has level `≤ N`, so the truncation does not change
   it there).
3. The bounded theorems `expansionPostponement_of_stratification` and
   `sd_complete_of_stratification` apply to the restriction; `Functional.restrict` transfers
   functionality.
4. The results are transported back to `P` by the two monotonicity lemmas `HasTypeR.monotone`
   and `HasTypeSD.monotone`.

**Poll's Open Problem 6** (for `HasTypeR`), proved for *every* specification with
`ExpansionPostponement P`:

* `HasTypeR.weak_subject_reduction : HasTypeR P Γ a A → Reduces a a' → ∃ A', Reduces A A' ∧
  HasTypeR P Γ a' A'` (soundness, `subject_reduces`, then expansion postponement);
* `HasTypeR.correctness_of_types : HasTypeR P Γ a A → (∃ s, A = .sort s) ∨ ∃ s, HasTypeR P Γ A
  (.sort s)` (soundness, `regularity`, then expansion postponement at a sort, which is normal).

So both halves hold for every stratified specification and every specification in the class of
this row.

**Example.** `NatHierarchy.natHier`: sorts `ℕ`, axioms `n : n+1`, rules `(m, n, n)` for `n ≤ m`.
It is functional, has infinitely many sorts, all used by axioms (`natHier_infinite`), and has no
`Stratification` (`natHier_not_stratified`: a stratification would give `n ≤ level n ≤ bound` for
all `n`).  With `level = id` it is in the class: `natHier_expansionPostponement`,
`natHier_sd_complete`, `natHier_weak_subject_reduction`, `natHier_correctness_of_types`.

## M29-EP-CUBE: the dependent corners (TODO_READY, stopped under the stop rule)

Module `Start/PTSExpansionCube.lean`.

* `cube_expansionPostponement_iff_productNormalizationR (f) : ExpansionPostponement (cubeSpec f)
  ↔ ProductNormalizationR (cubeSpec f)`, for every corner, dependent or not.
* `cube_productNormalizationR (f) (hf : f.dep = false)` (from the stratified case).

**Use of normalization.** The equivalence uses strong normalization of the cube
(`cube_stronglyNormalizing`, `Start/CoCSN.lean`) in exactly one place: in the abstraction case of
`expansionPostponement_of_productNormalizationR` (`Start/PTSExpansionPoll.lean`), to reduce the
type `B` of the body to its normal form `B'` so that the two reducts of `B` (the one given by the
induction hypothesis and `B'`) can be joined at `B'`.  No other case uses normalization.

**First missing lemma** (for λP):

```lean
theorem lambdaP_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP)
```

With it, `cube_expansionPostponement_of_productNormalizationR lambdaP` gives
`ExpansionPostponement (cubeSpec lambdaP)`; the same statement for `λP2`, `λPω̲`, `coc` gives the
other dependent corners.

**Why we stopped.** Unfolding `ProductNormalizationR` through `generation_pi`, what is needed is:
`HasTypeR P (A :: Γ) B (.sort s₂) → Reduces B B' → Normal B' → HasTypeR P (A :: Γ) B' (.sort s₂)`,
i.e. sorted subject reduction for `HasTypeR` at a normal reduct.  The natural attempt is an
induction on normal subjects, typed at normal types in an `HasTypeR`-valid context:

```lean
theorem normal_typing (hΓ : ValidContextR P Γ) (hM : Normal M) (hT : Normal T)
    (h : HasType P Γ M T) : HasTypeR P Γ M T
```

Its abstraction case `λA. b : Π A. B''` calls the lemma on `Π A. B''`, which is not a subterm,
and its application case `x N₁ … Nₖ` calls it on the arguments `Nᵢ` at the normal forms of the
domains.  In the cube one would order the calls by the degree of Barendregt's classification
(objects, constructors, kinds), but in λP the arguments `Nᵢ` of a type family have *lower* degree
than the family application, so neither the lexicographic order (degree, size) nor (size,
degree) decreases along both kinds of call.  The erasure lead of the instruction (erasing λP
types to simple types, invariant under conversion) suggests ordering object arguments by their
erased types and the families by their position in the context, but we could not write the
measure as a Lean statement whose decrease we could check in both cases, so under the stop rule
we did not continue.  The `Wdep` lead (the same measure without normalization) is therefore not
reached either; M29-EP is unchanged.

`#print axioms` output for the terminal theorems of this delivery: `docs/goal/evidence/M29-PART1-axioms.txt` (only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`).

## M29-EP-CUBE closed for λP (DONE_STRONG; this delivery)

Module `Start/PTSExpansionLambdaP.lean` (new; no existing module edited).

```lean
theorem lambdaP_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP)
theorem lambdaP_expansionPostponement : ExpansionPostponement (cubeSpec lambdaP)
```

This is a complete formal proof of a result known on paper (Poll 1998 for normalizing PTSs;
Barthe for injective PTSs); no novelty is claimed.

**Route (canonical forms, after Watkins–Cervesato–Pfenning–Walker and Harper–Licata).**

1. *Erasure* `Expr.erase : Expr S → STy` (Harper–Honsell–Plotkin): `pi A B ↦ arr (erase A)
   (erase B)`, `lam _ F ↦ erase F`, `app F _ ↦ erase F`, otherwise `base`.  `Expr.ErGood M`
   says that every application argument inside `M` erases to `base`.  Erasure is invariant under
   renaming, under substitution of base-erased terms (`Expr.erase_subst`), and under reduction of
   `ErGood` terms (`Reduces.erGood_erase`).
2. *Canonical judgement* `HasTypeNR P Γ M T`: the rules of `HasTypeR` without the reduction rule;
   the application rule normalizes `B[a]`, requires `app F a` normal, and (a change with respect
   to the plan) requires the argument to erase to `base`.  All subjects, types and context entries
   are normal (`HasTypeNR.normal`), and `HasTypeNR.toHasTypeR` is soundness.  For λP the side
   condition `a.erase = base` always holds (`HasTypeNR.erase_base`, `lambdaP_kind_not_star`:
   arguments are objects, typed by types of sort `∗`).
3. *Hereditary substitution* `HasTypeNR.hsubst` (`hsubst_aux`): induction on the size of the
   erasure of the type of the substituted variable, then on the derivation.  The head case
   `x Q₁ … Qₖ` with `N = λy:C. e` fires the redex and recurses with `y : C`, whose erasure is a
   proper part of the erasure of `Π y:C. D` (`STy.ArrSuffix.dom_lt`); later arguments are typed
   at domains whose erasure is a suffix of it (`ArrSuffix`).  The Π premise of an abstraction is a
   premise of the canonical rule, so it is substituted hereditarily, and the gap of Poll's Lemma
   10 does not arise.
4. *Normalization of derivations* `HasTypeR.normalizeNR` (λP): every `HasTypeR` derivation
   normalizes to a canonical derivation, in a pointwise reduct of the context, of a reduct of the
   subject at a reduct of the type.  This replaces steps 4 (regularity) and 5 (completeness on
   normal subjects) of the plan: no induction on normal subjects is needed, and so the measure
   problem of the previous delivery does not occur.
5. *Context expansion* `HasTypeR.ctx_expand`: a `HasTypeR` derivation in a pointwise reduct of a
   valid context is a derivation in the context itself.
6. `lambdaP_productNormalizationR` combines 4, 5 and soundness with `generation_pi`, and
   `cube_expansionPostponement_of_productNormalizationR lambdaP` gives EP.

**Use of normalization (exit criterion 2).**  Weak normalization of λP
(`lambdaP_weaklyNormalizing`, from `cube_lambdaP_sn`, `Start/CoCSN.lean`) is used in exactly two
places, both to normalize the *type* `B[a]` of a neutral application `F a` (the canonical
application rule needs a normal type): in the neutral case of `hsubst_aux`, and in the application
case of `HasTypeR.normalizeNR`.  It is also used, as before, in the abstraction case of
`expansionPostponement_of_productNormalizationR`.  The *subjects* are normalized by hereditary substitution itself,
by the erasure measure, without appeal to the normalization theorem.

**λPω̲ (not attempted in this delivery).**  In λPω̲ type variables can be substituted by type
constructors, and the erasure `erase` of this module is not invariant under such a substitution
(the substituted variable can sit in head position of a type).  The measure needs a level-stratified
erasure (kinds to simple kinds for constructor variables, types to simple types for object
variables), with hereditary substitution at both levels.  First missing lemma:

```lean
theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar)
```

recorded in the new row M29-EP-CUBE-REST, with `lambdaP2` and `coc` (impredicative; the erasure
measure fails, and a normalization argument in the style of Poll is needed).

**Stretch (completeness of `HasTypeSD` for λP, Poll's Open Problem 16) — not attempted.**  First
missing lemma:

```lean
theorem lambdaP_sd_complete {Γ : List (Expr Srt)} {M A : Expr Srt}
    (h : HasType (cubeSpec lambdaP) Γ M A) :
    ∃ A', HasTypeSD (cubeSpec lambdaP) Γ M A' ∧ Converts A A'
```

`#print axioms`: `docs/goal/evidence/M29-M28-axioms.txt`.

## M29-EP-CUBE-REST: λPω̲ (stop rule fired)

`Start/PTSExpansionLambdaPOmegaBar.lean` proves steps 1–2 of the two-level hereditary substitution
plan:

* `cube_classification`: in every corner of the cube a legal term is a kind (`T = □`), a
  constructor (`Γ ⊢ T : □`) or an object (`Γ ⊢ T : ∗`); from `HasType.regularity`.
* `Expr.eraseK` (object binders dropped, constructor binders become arrows) and `eraseK_subst`:
  kind erasure is invariant under every substitution of non-kinds with trivial kind erasure
  (`NoKindSubst`), which covers the objects and constructors of λPω̲ (no rule `(□,∗)`).

Not done: a canonical judgement for λPω̲ (the λP judgement `HasTypeNR` requires base-erased
application arguments, which fails for constructor arguments `α G`), object-level hereditary
substitution (step 3) and constructor-level hereditary substitution by `eraseK` of the kind
(step 4).  First missing lemma:

```
theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar)
```

with which `cube_expansionPostponement_of_productNormalizationR` gives
`ExpansionPostponement (cubeSpec lambdaPOmegaBar)`.  The row M29-EP-IMPREDICATIVE was not added,
since λPω̲ did not close.

### This delivery: the corrected measure (stop rule fired again)

The previous measure `eraseK` drops object binders, so it does not decrease when a constructor
`λy:A. G'` is applied to an object.  `Start/PTSExpansionLambdaPOmegaBarSkel.lean` adds the kind
skeleton, which keeps them:

* `Expr.skelK`: `skel ∗ = base`, `skel (Π x:A. K) = arr base (skel K)` (A not a kind; this encodes
  `obj (skel K)`), `skel (Π α:K₁. K₂) = arr (skel K₁) (skel K₂)`, and `base` on non-kinds;
* `skelK_rename`, `skelK_subst`: invariant under renaming and under every `NoKindSubst`
  substitution (objects and constructors of λPω̲), same proof as `eraseK_subst`;
* `skelK_size_pi_obj`, `skelK_size_pi_kind`: the skeletons of the body (and the domain, for a
  constructor binder) of a product kind are strictly smaller.

Still missing: the canonical λPω̲ judgement (β-normal subjects and types; application result by
hereditary substitution at the argument's level; no base-erasure restriction), object-level
hereditary substitution by erasure of the variable's type, and constructor-level hereditary
substitution by `skelK` of the variable's kind.  First missing lemma (unchanged):

```
theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar)
```

M29-EP-CUBE-REST stays IN_PROGRESS; M29-EP-IMPREDICATIVE was not added, since λPω̲ did not close.

## λPω̲: canonical judgement and object-level hereditary substitution (this delivery)

* Step 1. `Start/PTSExpansionLambdaPOmegaBarCanon.lean` defines the canonical judgement
  `HasTypeNW`: the rules of `HasTypeR` without the conversion rule; subjects and types are
  β-normal; in the application rule the result type is a normal form of `B[a]`; arguments are not
  restricted to base-erased ones.  Proved: `toHasTypeR`, `normal`, `rename`, `lam_inv`,
  `HasTypeNR.toHasTypeNW`, `app_type_exists`.
* Step 2. `Start/PTSExpansionLambdaPOmegaBarObj.lean` proves `HasTypeNW.hsubst_obj`
  (object-level hereditary substitution `x := N` in λPω̲), by strong induction on the size of the
  erasure of the type of `x`.  Key facts: `not_vis_of_typed` (an object variable never occurs at
  a position the erasure inspects in a constructor, kind or type, so object substitution never
  changes the erasure of a normal type: `erase_isKindB_reduces_subst`), and `head_lookup_obj`
  (the type of a spine headed by an object variable is, up to erasure, a codomain of the
  variable's type, so a created redex is at a strictly smaller erasure).
* Stop rule.  Step 3 (constructor-level hereditary substitution by induction on `skelK`) is not
  done.  First missing lemma:

```lean
theorem HasTypeNW.hsubst_con {Γ : List (Expr Srt)} {N K M B : Expr Srt}
    (hK : K.isKindB = true) (hN : HasTypeNW PWbar Γ N K)
    (hM : HasTypeNW PWbar (K :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNW PWbar Γ M' B'
```

  followed by `normalizeNR` for λPω̲, `lambdaPOmegaBar_productNormalizationR` and
  `cube_expansionPostponement_of_productNormalizationR`.

## λPω̲ closed: constructor-level hereditary substitution and EP (round 1, steps 3–5)

* Step 3. `Start/PTSExpansionLambdaPOmegaBarCon.lean` proves the lemma recorded on the board,
  with exactly the requested statement:

```lean
theorem HasTypeNW.hsubst_con {Γ : List (Expr Srt)} {N K M B : Expr Srt}
    (hK : K.isKindB = true) (hN : HasTypeNW PWbar Γ N K)
    (hM : HasTypeNW PWbar (K :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNW PWbar Γ M' B'
```

  Route as planned: the generalized form `hsubst_con_aux` (`Δ ++ K :: Γ`, `CtxSubstRed`), by
  strong induction on `STy.size` of `K.skelK`, then on the derivation.  A constructor `N : K` is
  not a kind (`NoKindVal`), so `skelK_subst'` keeps the skeleton of every kind.
  `head_lookup_con` (with `ArrSuffix`) puts the type of a spine headed by the substituted variable
  at a skeleton suffix of `skelK K`.  A created redex at a constructor binder recurses at the
  smaller `K₁` (`skelK_size_pi_kind`), and one at an object binder is fired by `hsubst_obj`.
  `K ≠ □` is an internal hypothesis of the aux lemma, derived in the wrapper.
* Steps 4–5. `Start/PTSExpansionLambdaPOmegaBarEP.lean`:

```lean
theorem HasTypeR.normalizeNW {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasTypeR PWbar Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW PWbar Γ' M' T'
theorem lambdaPOmegaBar_productNormalizationR : ProductNormalizationR (cubeSpec lambdaPOmegaBar)
theorem lambdaPOmegaBar_expansionPostponement :
    ExpansionPostponement (cubeSpec lambdaPOmegaBar)
```

  (`normalizeNW`, so that the name does not clash with the λP `HasTypeR.normalizeNR`.)  Axioms:
  `[propext, Classical.choice, Quot.sound]` for all four (`M29-EP-LAMBDAPOMEGABAR-axioms.txt`).
  EP now holds for every corner of the cube except λP2 and coc.  M29-EP-CUBE-REST is DONE_WEAK,
  depending on the new row M29-EP-IMPREDICATIVE (first lemma
  `lambdaP2_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP2)`, then coc).

## Research: routes for λP2 and coc (paper only, no Lean)

These are checked against the repository's `HasTypeR` (reduction-only conversion) and `HasTypeNW`.
Common obstruction: under (□,∗), substituting a type for a type variable changes erasures and
skeletons, so neither measure bounds the created redexes.

**(i) normalizeNR by induction on SN of the subject.**  The order is lexicographic: first the
multiset of (reduction height, size) of the context entries and the subject, then the derivation.
In the β case the head redex is fired by ordinary substitution.  The typing of the substituted
body comes from the substitution lemma for `HasTypeR`, which holds because `Reduces` is closed
under substitution; subject reduction for `HasTypeR` is never needed, so the argument is *not*
circular.  The subject strictly reduces, so the measure decreases.
*Fails at the abstraction case*: `HasTypeNW` needs `Π A' nf(B) : s` canonically.  `nf(B)` is
neither a subterm nor a reduct of the subject, and B's SN height is unrelated to the measure:
this is Poll's Lemma 10 gap again.  Adding types to the measure breaks the application premise
`F : Π A B` instead.  With canonical regularity the route closes on paper.  First missing lemma:

```lean
theorem HasTypeNW.regular_lambdaP2 {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasTypeNW (cubeSpec lambdaP2) Γ M T) :
    T = .sort .box ∨ ∃ s, HasTypeNW (cubeSpec lambdaP2) Γ T (.sort s)
```

The proof of this lemma needs normalization of `B[a]` in the application rule, which is the same
recursion again: a mutual-measure problem.

**(ii) Tait/Girard predicate on derivations.**  Call a `HasType` derivation good if it
normalizes (context, subject, type) to `HasTypeNW`.  In the abstraction case the premise
`Π A B : s` is itself a subderivation, so the gap of (i) does not arise.  The application case is
the reducibility clause.  The impredicative quantifier (rule (□,∗)) needs *typed* candidates:
sets of good derivations indexed by context and type, closed under weakening (Kripke).  The
untyped saturated sets of `Start/CoCSN.lean` lose the typing information that `HasTypeNW`
demands.  Only the candidate structure (saturation, the Π clause, quantification over
candidates of each kind) carries over.  No gap was found, but the construction is large: a
typed copy of the CoCModel interpretation with its substitution and conversion lemmas.
**Recommended route.**  First missing lemma:

```lean
theorem HasType.normalizeNW_lambdaP2 {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasType (cubeSpec lambdaP2) Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW (cubeSpec lambdaP2) Γ' M' T'
```

From it, `lambdaP2_productNormalizationR` follows exactly as for λP and λPω̲ (`generation_pi`,
`normal_unique`, `toHasTypeR`, `ctx_expand`), after the `HasTypeR`-to-`HasType` inclusion.

**(iii) Poll's Theorem 11 (strengthening with ⊢nf) proved simultaneously with Lemma 10.**  In the
formulation by normalization of derivations, the abstraction gap disappears: the Π premise is a
subderivation, as in (ii).  The difficulty moves to the application case.  There the canonical
function type must be instantiated with a canonical argument, which is hereditary substitution.
Theorem 11 supplies no measure for it: the derivation of the argument it produces is not a
subderivation, and in λP2 the erasure of the instantiated codomain can grow.  So (iii) reduces to
the missing lemma

```lean
theorem HasTypeNW.hsubst_lambdaP2 {Γ : List (Expr Srt)} {N A M B : Expr Srt}
    (hN : HasTypeNW (cubeSpec lambdaP2) Γ N A)
    (hM : HasTypeNW (cubeSpec lambdaP2) (A :: Γ) M B) :
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧
      HasTypeNW (cubeSpec lambdaP2) Γ M' B'
```

whose termination is exactly strong normalization of λP2.  Its proof must therefore go through a
model, as in (ii); no syntactic measure is known.

## λP2 (round 2): EP reduced to hereditary substitution; where route (ii) stops

Status of M29-EP-IMPREDICATIVE: **TODO_READY** (not closed).  The targets
`lambdaP2_productNormalizationR` and `lambdaP2_expansionPostponement` are not proved.

**Proved** (`Start/PTSExpansionLambdaP2.lean`, axioms in `M29-EP-IMPREDICATIVE-axioms.txt`,
`[propext, Classical.choice, Quot.sound]`):

```lean
def HSubstNW (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A M B : Expr Srt}, HasTypeNW P Γ N A → HasTypeNW P (A :: Γ) M B →
    ∃ M' B', Reduces (M.instantiate N) M' ∧ Reduces (B.instantiate N) B' ∧ HasTypeNW P Γ M' B'
theorem HasTypeR.normalizeNW_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f))
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasTypeR (cubeSpec f) Γ M T) :
    ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
      HasTypeNW (cubeSpec f) Γ' M' T'
theorem productNormalizationR_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f)
theorem expansionPostponement_of_hsubst (f : CubeFeatures) (hs : HSubstNW (cubeSpec f)) :
    ExpansionPostponement (cubeSpec f)
theorem lambdaP2_expansionPostponement_of_hsubst (hs : HSubstNW (cubeSpec lambdaP2)) :
    ProductNormalizationR (cubeSpec lambdaP2) ∧ ExpansionPostponement (cubeSpec lambdaP2)
theorem hsubstNW_lambdaPOmegaBar : HSubstNW (cubeSpec lambdaPOmegaBar)
```

The λPω̲ normalization argument is corner-independent except in the application case, where a
created head redex `(λx:C. e) a'` is fired by hereditary substitution; `normalizeNW_of_hsubst`
is that argument with hereditary substitution as a hypothesis, in every corner of the cube.  So
for λP2 the **only** remaining lemma is `HSubstNW (cubeSpec lambdaP2)`, i.e. the lemma
`HasTypeNW.hsubst_lambdaP2` of route (iii) above.  `hsubstNW_lambdaPOmegaBar` checks that the
hypothesis is the right one: it holds for λPω̲ (from `hsubst_obj` and `hsubst_con`).

**Where route (ii) stops.**  Route (ii) proves `HSubstNW` (equivalently normalization of
derivations) through a Tait/Girard predicate on derivations.  The fundamental lemma is by
induction on the `HasType` derivation, with a substitution of good derivations for the context.
The ax, var, weaken, product, abstraction and conversion cases are the corresponding cases of
`normalizeNW_of_hsubst` (no new idea needed).  The application case at an object binder of
first-order type is the reducibility clause.  The case that fails with the untyped saturated sets
of `Start/CoCSN.lean` is the application `M N : B[N]` with `M : Π(X:∗). B` and `N : ∗` (rule
(□,∗)).  There the clause must quantify over candidates for `X` that are sets of **good
derivations** `Γ' ⊢ P : X'`, for every context extension `Γ'` and every type `X'` reducing to
the instance of `X`.  Instantiating `X := N` must turn such a candidate into the interpretation of
`N`, i.e. the interpretation must commute with type substitution on typed derivations:

```lean
theorem Good.subst_type {Γ : List (Expr Srt)} {B N : Expr Srt} ...
    -- ⟦B[N/X]⟧ρ = ⟦B⟧(ρ, X ↦ ⟦N⟧ρ) on derivations, for B : ∗ in context X : ∗ :: Γ
```

This is the typed analogue of `CoCModel`'s substitution lemma.  It is the first lemma that has no
counterpart in the repository.  Its statement needs the typed candidate space itself (sets of
`HasType` derivations closed under weakening and under expansion by `HasTypeNW`-normal
derivations), which is not built.  No mathematical gap was found; what remains is the
construction of that interpretation and its substitution and conversion lemmas.
