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

## λP2 and coc, round 4 — route (iii): hereditary substitution bought from SN

`Start/PTSExpansionHSubstSN.lean`.  Strong normalization of every corner is already proved
(`Start/CoCSN.lean`: `CoC.sn_of_hasType`, `cube_stronglyNormalizing f`), so the termination of
hereditary substitution is taken from it instead of a new candidate model.

Proved (no sorry, axioms at most `[propext, Classical.choice, Quot.sound]`):

* `Expr.DescStep x y := Beta y x ∨ ImmSub x y` — one step down: a one-step reduct or an immediate
  subterm; `Expr.acc_descStep_of_sn : StronglyNormalizing t → Acc DescStep t` and its transitive
  form `Expr.acc_desc_of_sn` (subterms of SN terms are SN, and a reduct of a subterm is a subterm
  of a reduct, `sub_beta`).  This is the order of route (iii).
* `Expr.Below x root` — `x` is, up to a renaming, `DescStep*`-below `root`; closed under steps
  down, under un-renaming and under reducts (`Below.down`, `Below.unrename`,
  `Below.trans_reduct`).
* `hsubst_route3_aux` — route (iii) itself: outer well-founded induction on `root = M[N]` (up to
  renaming), inner induction on the canonical derivation of `M` (at any depth `Δ`, into a
  canonically valid target context).  The variable and weakening cases read their declarations
  off the target context; the **application** case fires the created head redex
  `(λx:C'. e) a'` (variable at the head replaced by an abstraction coming from `N`) by the outer
  hypothesis, because `e[a']` is a reduct of `M[N]`; types are handled through `Reduces.to_normal`
  on `B[N]` (types are typed, hence SN).
* `hsubstNW_of_hsubstPi (f : CubeFeatures) (hpi : HSubstPi (cubeSpec f)) : HSubstNW (cubeSpec f)`
  and `cube_expansionPostponement_of_hsubstPi (f) (hpi) : ProductNormalizationR (cubeSpec f) ∧
  ExpansionPostponement (cubeSpec f)` — **for every corner**, including coc.
* `hsubstPi_nil_of_hsubstNW` — sanity check: `HSubstNW` gives the depth-0 instance of `HSubstPi`,
  so the hypothesis is no stronger than the target at depth 0.

**Where route (iii) breaks.**  Exactly one recursive call of the inner induction is not at a
smaller point of the order: the product premise `Θ ⊢ Π C E : s` of the abstraction rule
`Θ ⊢ λC. b : Π C E`.  Its subject `(Π C E)[N]` contains `E[N]`, where `E` is the *type* of the body
`b`, and `E[N]` is neither a reduct nor a subterm of `M[N] = λC[N]. b[N]` (nor of a renaming of
it).  So `Below ((Π C E)[N]) root` is not available, and head redexes created inside `E[N]` would
need the outer hypothesis at points that are not below `root`.  (Taking the pair `(M, B)` as
the root was not tried in Lean; on paper it moves the problem to the product premises of the
abstractions inside `E`, one level up.)  That call is isolated as the hypothesis

```lean
def HSubstPi (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A : Expr Srt} {Δ Δ' : List (Expr Srt)} {C E : Expr Srt} {s : Srt},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) (.pi C E) (.sort s) →
    ∃ C' E', Reduces (C.subst (Expr.substAt N Δ.length)) C' ∧
      Reduces (E.subst (Expr.substAt N (Δ.length + 1))) E' ∧
      HasTypeNW P (Δ' ++ Γ) (.pi C' E') (.sort s)
```

**First missing lemma:** `theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)` (and then
`hsubstPi_cube (f) : HSubstPi (cubeSpec f)`).  With it, `hsubstNW_lambdaP2`,
`lambdaP2_productNormalizationR`, `lambdaP2_expansionPostponement`, `hsubstNW_cube` and
`cube_expansionPostponement_all` follow at once from `hsubstNW_of_hsubstPi` and
`cube_expansionPostponement_of_hsubstPi`.  A natural next attempt (not yet tried in Lean) is a
second outer induction on `Π C E` itself, which is typed and hence SN; its product premises are
again of the same shape, so the open question is whether this nested recursion is well founded.

## λP2 and coc, round 5 — the three measures for the product premise (`Start/PTSExpansionMeasures.lean`)

Target this round: `theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)`.  **Not proved.**
What is proved, and where each of the three suggested measures fails:

Proved (all `lake build --wfail`, axioms `propext, Classical.choice, Quot.sound`):

* `PureTypeSystem.HSubstSort P` — hereditary substitution at depth into a canonical judgement
  `Δ ++ A :: Γ ⊢ M : s` whose type is a **sort** (stage 1 of measure (c)).
* `PureTypeSystem.hsubstPi_iff_hsubstSort (f) : HSubstPi (cubeSpec f) ↔ HSubstSort (cubeSpec f)`
  (from `hsubstPi_of_hsubstSort` and `hsubstSort_of_hsubstPi`).
* `PureTypeSystem.cube_expansionPostponement_of_hsubstSort (f) (h : HSubstSort (cubeSpec f)) :
  ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f)`.
* `PureTypeSystem.HasTypeNW.not_lam_of_sort` — a canonical judgement whose type is a sort never
  has an abstraction as subject.
* `PureTypeSystem.UpDown P Γ x y := Expr.DescStep x y ∨ HasType P Γ y x` and
  `PureTypeSystem.lambdaP2_upDown_not_acc : ¬ Acc (TransGen (UpDown (cubeSpec lambdaP2)
  cycleCtx)) (.var 0)`.

### Measure (a): nested outer induction on the SN of `Π C E`

Route (iii) already runs an outer induction on `M[N]` (up to renaming, `Expr.acc_descStep_of_sn`)
and an inner induction on the canonical derivation of `M`.  Adding a third, outer-most induction on
`SN (Π C E)` (the type of the abstraction) handles the product premise *once*: the recursive call
for `Θ ⊢ Π C E : s` is at a strictly smaller point of the new measure only if the subject
`(Π C E)[N]` is a reduct or a subterm of the term whose SN is being inducted on.  It fails at the
**created redex inside the product premise**: hereditary substitution into `Π C E : s` fires the
redexes that `N` creates inside `E`, and each firing produces a *new* canonical derivation (the
output of the recursive call), whose own product premises are types of abstractions that occur
in `E[N]`'s reducts — not in `Π C E`, not in `M[N]`, and not below the root derivation.  So the
nested measure sees neither a sub-derivation nor a reduct of the inducted term at the second
recursive call: the point where it fails is the call `HSubstPi` on the product premise of an
abstraction **created** by the first firing.

### Measure (b): `Acc` of (DescStep ∪ "is the type of")

* With "is the type of" read in the full system (types up to conversion) the order is **not**
  well founded: `lambdaP2_upDown_not_acc` exhibits the 2-cycle `t ⟶ (λu:P. P) t ⟶ t` in
  `P : ∗, t : P` (the first arrow "is the type of" by conversion, the second "immediate subterm").
* Restricted to canonical (normal) types the cycle disappears (a normal type of `t` is `P`), but
  then well-foundedness is the open question itself: an infinite alternating chain
  (go up to the normal type, go down into a subterm, go up to its type, …) would have to be
  excluded by an order on contexts (each "up" step at a variable moves into the context entry,
  which is shorter) and by the SN of the subterm order at non-variable heads.  This is plausible
  but not proved; it is the first missing lemma of route (b):
  `Acc (TransGen (UpDownNF (cubeSpec lambdaP2) Γ)) M` for canonical `Γ ⊢ M : T`.

### Measure (c): level-stratified induction

Stage 1 is **not a weakening**: `hsubstPi_iff_hsubstSort` proves that hereditary substitution into
sort-typed premises is *equivalent* to `HSubstPi` in every corner.  So the stratification moves the
whole difficulty into stage 1.  The obstruction there: in λP2 a sort-typed judgement
`Θ ⊢ F u₁ ⋯ uₙ : ∗` with `F` a variable of a type-family kind takes **object arguments** `uᵢ`; after
substitution `uᵢ[N]` contains object redexes created by `N` (an object abstraction substituted at
the head of an object application inside a type argument).  These are object redexes, so they are
fired by the object-level procedure of stage 2 — but stage 2 uses stage 1 for its product premise,
and the object abstraction being fired has a product type `Π C E` whose premise is again a stage-1
call on `E[N]`.  The created object redexes inside types are therefore **not** at smaller points of
any order already available (neither the term-SN order of route (iii) nor the size of the kind
skeleton used for λPω̲): the first missing lemma is unchanged.

### First missing lemma

`theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)` — equivalently
`HSubstSort (cubeSpec lambdaP2)`.  With it, `lambdaP2_productNormalizationR` and
`lambdaP2_expansionPostponement` follow by `cube_expansionPostponement_of_hsubstPi lambdaP2`; for coc
the same with `hsubstPi_cube f`.

A different route that avoids the product premise altogether, recorded for the next round:
expansion postponement follows from *canonicalisation of normal subjects*; the only rule of the
canonical system that fails for a normal subject is the abstraction rule's product premise, so it
would suffice to drop that premise from the canonical system and recover it a posteriori from
type correctness (`HasType` gives `Γ ⊢ Π C E : s` in the full system).  Whether the canonical
system without that premise still yields `ProductNormalizationR` is not checked: this is a
suggestion, not attempted in Lean.

## λP2 and coc, round 6 — route C2: Poll's Lemma 10 repaired is the open lemma (`Start/PTSExpansionPollRepair.lean`)

Route chosen: (C2), Poll's proof.  Route (C1) was not pursued this round: its first missing lemma
(the interpretation commutes with type substitution at (□,∗)) is unchanged.

**The step of Lemma 10 that fails.**  The abstraction case: the induction hypothesis gives
`Γ, Δσ ⊢nf Π Cσ. Bσ↑ : s`, and the abstraction rule of `⊢nf` needs `Γ, Δσ ⊢nf Π nf(Cσ). nf(Bσ↑) : s`.
That step is a canonicalisation of a sort-typed *product* judgement.  Stated as a property of a
specification:

```lean
def PureTypeSystem.PollProductCanon (P : Specification Srt) : Prop :=
  ∀ {Γ Γ' : List (Expr Srt)} {C E : Expr Srt} {s : Srt},
    HasType P Γ (.pi C E) (.sort s) → List.Forall₂ Reduces Γ Γ' → ValidContextNW P Γ' →
    ∃ C' E', Reduces C C' ∧ Reduces E E' ∧ HasTypeNW P Γ' (.pi C' E') (.sort s)
```

**Can it be repaired with what is proved?**  No, in the precise sense that the repair is
equivalent to the open lemma.  Using SN of every corner (`cube_stronglyNormalizing`), HSubstPi ⇒
EP (`cube_expansionPostponement_of_hsubstPi`) and the normalisation of reduction-only derivations
(`HasTypeR.normalizeNW_of_hsubst`):

```lean
theorem PureTypeSystem.hsubstPi_of_pollProductCanon {P : Specification Srt}
    (h : PollProductCanon P) : HSubstPi P
theorem PureTypeSystem.pollProductCanon_of_hsubstPi (f : CubeFeatures)
    (hpi : HSubstPi (cubeSpec f)) : PollProductCanon (cubeSpec f)
theorem PureTypeSystem.pollProductCanon_iff_hsubstPi (f : CubeFeatures) :
    PollProductCanon (cubeSpec f) ↔ HSubstPi (cubeSpec f)
theorem PureTypeSystem.cube_expansionPostponement_of_pollProductCanon (f : CubeFeatures)
    (h : PollProductCanon (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f)
```

The forward direction substitutes in the full system (`HasType.subst_at`, no subject reduction
needed) and canonicalises the substituted product in the reduct context given by `CtxSubstRed`
(`CtxSubstRed.forall₂_append`).  The backward direction goes through EP (the type of a sort-typed
judgement reduces only to the sort), then `normalizeNW_of_hsubst`, and identifies the reduced
context with the canonical one (`forall₂_reduces_unique`, `ValidContextNW.normal_entries`).

Together with round 5 (`hsubstPi_iff_hsubstSort`), four formulations are now proved equivalent in
every corner: HSubstPi, HSubstSort, the missing step of Poll's Lemma 10, and (through
`cube_expansionPostponement_of_hsubstPi`) they all imply EP.  Every repair of Lemma 10 must
therefore prove HSubstPi itself; none of the measures examined (round 5) or the SN results
available does it.

**First missing lemma (unchanged)**: `theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)`,
equivalently `PollProductCanon (cubeSpec lambdaP2)`.  This is TLCA open problem 23 for these
systems; the delivery of this round is the precise negative result above.

## λP2 and coc, round 7 — route (ii): the Tait/Girard predicate on derivations (`Start/PTSExpansionRouteII.lean`)

Route (ii) attempted in Lean for the first time.  Status of M29-EP-IMPREDICATIVE: **TODO_READY**
(not closed); of M29-EP-CUBE-REST: DONE_WEAK, unchanged, with this round's results recorded.

**The predicate.**  `RouteII.NormNW P Γ M T` (the judgement normalizes to a canonical `HasTypeNW`
judgement, context, subject and type reducing to it) is the base predicate.  `RouteII.Sk`
(type variables in de Bruijn form, arrows, the quantifier `(□,∗)`) are the skeletons, with
renaming and substitution.  `RouteII.IsCand P C` (typed candidates: `HasTypeR` judgements that
normalize, closed under reduction of the type) and `RouteII.Good P s ξ` (by recursion on `s`,
relative to candidates `ξ` for the type variables): at an arrow, Kripke closure under application
to good arguments in every context extension; at `(□,∗)`, closure under application to every type
argument for **every** typed candidate interpreting the bound variable.

Proved (axioms in `M29-EP-IMPREDICATIVE-axioms.txt`, at most `propext, Classical.choice,
Quot.sound`):

```lean
theorem PureTypeSystem.RouteII.Good.isCand (P : Specification Srt) :
    ∀ (s : Sk) (ξ : ℕ → Cand), (∀ i, IsCand P (ξ i)) → IsCand P (Good P s ξ)
theorem PureTypeSystem.RouteII.Good_subst (P : Specification Srt) :
    ∀ (s : Sk) (σ : ℕ → Sk) (ξ : ℕ → Cand),
      Good P (s.subst σ) ξ = Good P s (fun i => Good P (σ i) ξ)
theorem PureTypeSystem.RouteII.Good_inst (P : Specification Srt) (τ t : Sk) (ξ : ℕ → Cand) :
    Good P (τ.subst (single t)) ξ = Good P τ (consC (Good P t ξ) ξ)
theorem PureTypeSystem.RouteII.Good.tyApp ... (h : Good P (.all τ) ξ Γ M T)
    (hT : Reduces T (.pi K B)) (hU : HasTypeR P Γ U K) :
    Good P (τ.subst (single t)) ξ Γ (.app M U) (B.instantiate U)
theorem PureTypeSystem.RouteII.NormNW.abstraction
    (hb : NormNW P (C :: Γ) b E) (hp : NormNW P Γ (.pi C E) (.sort s)) :
    NormNW P Γ (.lam C b) (.pi C E)
theorem PureTypeSystem.RouteII.NormNW.product ... : NormNW P Γ (.pi A B) (.sort s₃)
theorem PureTypeSystem.RouteII.hsubstSort_iff_sortFundamental (P : Specification Srt) :
    HSubstSort P ↔ SortFundamental P
theorem PureTypeSystem.RouteII.cube_expansionPostponement_of_sortFundamental (f : CubeFeatures)
    (h : SortFundamental (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f)
```

**The lemma named in round 2 is proved.**  "The interpretation commutes with type substitution
at (□,∗)" is `Good_subst` / `Good_inst`: `⟦τ[t/X]⟧ξ = ⟦τ⟧(ξ, X ↦ ⟦t⟧ξ)`, by induction on the
skeleton after the renaming lemma `Good_rename`.  It goes through because the clauses of `Good`
mention the type of the judgement only through reductions `T ↠ Π A B`, never through its syntax,
so the interpretation depends on the skeleton and the candidate assignment alone.
`Good.tyApp` is then the type-application case of the fundamental lemma.  Route (ii) does **not**
fail at `(□,∗)`.

**The product premise.**  As requested, it is handled by the predicate on the product's own
derivation: `NormNW.abstraction` builds the canonical abstraction from the normalizability of
the body and of the product (contexts and codomains are identified by uniqueness of normal
forms), with no measure on the product.  In the fundamental lemma this is a structural call: the
product premise is a sub-derivation of the `HasTypeR` abstraction derivation.

**Where the fundamental lemma stands.**  `SortFundamental P` is the fundamental lemma restricted
to sort-typed judgements and a single substitution; `hsubstSort_iff_sortFundamental` shows it is
**equivalent** to `HSubstSort P` (hence, in every corner, to `HSubstPi`, `PollProductCanon`, and it
gives EP).  So route (ii) gives no shortcut around the open lemma: its fundamental lemma at
sort-typed judgements *is* the open lemma (a fifth equivalent formulation).  What route (ii)
offers is a different induction to prove it: structural on the `HasTypeR` derivation, over all
good substitutions, instead of the outer well-founded inductions of routes (iii)/(a)–(c).

The λ2 fragment check was not completed: for λ2 (`systemF`, `f.dep = false`) EP is proved by
stratification (`cube_expansionPostponement`), but `HSubstNW (cubeSpec systemF)` is not in the
repository, so the equivalence above gives no free check there; the check would be the
fundamental lemma for `systemF` itself.

**First missing lemma of route (ii)** (in order):

1. the **erasure of type-level terms to skeletons**, `sk : Expr Srt → Sk`, relative to the
   classification of context entries (object / type variable / family variable), with
   `sk (B[u/x]) = sk B` for an object `u` and `sk (B[U/X]) = (sk B).subst (single (sk U))` for a
   type `U`, and `sk` invariant under β on types.  In λP2 this needs the syntactic classification of
   terms by degree (objects, types/families, kinds); no such classification for λP2 was found in
   the repository.
2. **CR3 for the base predicate**: a canonical neutral judgement applied to normalizable
   arguments is normalizable (uses SN of every corner, `cube_stronglyNormalizing`, to normalize
   the instantiated codomain).
3. the substitution lemma for `HasTypeR` (`HasTypeR.subst`), for the soundness field of `Good`.
4. the fundamental lemma: `HasTypeR P Γ M T → ∀ good substitution ρ, Good P (sk T) ξ (Mρ) (Tρ)`.

Steps 1–4 were not attempted in Lean this round; on paper no obstruction was identified in them,
which is not a proof.  The precise negative result of this
round is the equivalence `hsubstSort_iff_sortFundamental` (route (ii) at its product premise is the
open lemma), and the positive result is that the step at `(□,∗)` named in round 2 holds.

## Round 8 — route (ii): the erasure, the predicate indexed by it, and the first failing step

### A1. The erasure of λP2 constructors to λ2 skeletons (`Start/PTSErasureP2.lean`), proved

The first missing lemma of round 7, step 1, is closed.  The classification is `CoC.cl` of
`Start/CoCModel.lean` (kinds `.kind k`, constructors `.constr k`, objects `.obj`, with
`CoC.classify`, `CoC.cl_beta`, `CoC.kind_beta`); kinds erase to their kind skeletons (`.kind k`).
Constructors erase by

* `ErasureP2.er Δ ρ M : RouteII.Sk`, where `Δ : ℕ → Cls` classifies the free variables and
  `ρ : ℕ → Sk` gives the skeleton of each free constructor variable: a constructor variable to
  `ρ n`; `Π x:A. B` with `A` not a kind to the arrow `er A ⇒ er B`; `Π α:K. B` with `K` a kind
  (rule `(□,∗)`) to `∀. er B` (with `ρ` lifted by `upS`); object abstraction and object
  application are forgotten; everything not classified as a constructor erases to the closed
  junk skeleton `∀X. X` (`er_junk`).

Proved, with no typing hypothesis:

* `er_rename`, `er_skRename`, `er_skSubst` — commutation with renaming of expressions and with
  renaming/substitution of skeletons;
* `er_subst` — commutation with any substitution respecting the classification;
* `er_instantiate_obj` — **invariance under object substitution**:
  `er Δ ρ (B[N]) = er (ncons (cl Δ N) Δ) (ncons t ρ) B` for every `t` when `N` is not a
  constructor (`er_obj_irrel`: the skeleton of an object variable is irrelevant);
* `er_instantiate` — **commutation with constructor substitution**:
  `er Δ ρ (B[U]) = (er (ncons (cl Δ U) Δ) (upS ρ) B)[er Δ ρ U]`.

Proved for well-typed λP2 terms:

* `er_beta`, `er_reduces`, `er_conv` — **invariance under β-reduction and β-conversion**.  The
  only typed case is the head redex: `lam_dom_not_kind` shows that in λP2 (no rule `(□,□)`) a
  typed abstraction classified as a constructor has a domain which is not a kind, so the
  argument of a constructor-level redex is an object and `er_instantiate_obj` applies.

coc: **the erasure does not extend as it stands** — `er_beta_fails_coc`: in `[α : ∗]`, the
typed coc (already λω) redex `(λβ:∗. β) α` erases to the junk skeleton while its contractum `α`
erases to the type variable.  The failing step is the head case of `er_beta` (the equation
`er (app (lam K b) U) = er (b[U])` with `K` a kind).  λ2 skeletons have no type-level
abstraction; the target has to be Fω types (with type-level λ and application) taken modulo β,
and the predicate defined by recursion on their β-normal forms (normalization of the
simply-typed type level), as in Geuvers' proof for coc.

### A2. Route (ii) indexed by the erasure (`Start/PTSRouteIIErased.lean`), proved

* `RouteII.GoodE ξ ρ Γ M T := Good (cubeSpec lambdaP2) (er (ctxCl Γ) ρ T) ξ Γ M T`;
* `GoodE.reduceType` (invariance under reduction of a well-typed type), `GoodE.escape`,
  `GoodE.typed`;
* `GoodE.app` — the object-application case in erased form (`er_instantiate_obj`);
* `GoodE.tyApp` — **the `(□,∗)` case in erased form**: the typed Kripke candidate chosen for
  the bound variable is `⟦er U⟧ξ` and the skeleton of `B[U]` is `(er B)[er U]`
  (`er_instantiate` with `Good_inst`);
* `NormNW.expand` — CR3 in its head-expansion form for the base predicate.

### A3. The fundamental lemma: the first failing step

Not proved.  The exact first failing case is **CR3 at neutral applications** (the "reflect"
half needed for variables at arrow skeletons and for the base candidates): for a variable
`x : Π A B` of `Γ` and a normalizable argument `N : A`, the base predicate requires

  `NormNW P Γ (app x N) (B[N])`,

i.e. a canonical (`HasTypeNW`) judgement `Γ' ⊢ x N' : T'` with `T'` the **normal form of the type
`B[N]`, carrying a canonical derivation of `T' : s`**.  Strong normalization
(`cube_stronglyNormalizing`) gives the normal form of the term `B[N]` but not a canonical
derivation of it; that derivation is exactly `HSubstSort` for the sort-typed judgement
`B : s` and the substitution `N/x` — the open lemma itself (equivalently `SortFundamental`,
round 7).  So the fundamental lemma of route (ii) at objects needs the open lemma at their types,
and the round-7 note "CR3 uses SN to normalize the instantiated codomain" is corrected: SN
normalizes the codomain as a term, not as a canonical judgement.  The equation that does not
close is

  `NormNW (cubeSpec lambdaP2) Γ (.app (.var x) N) (B.instantiate N)`

for `HasTypeNW Γ (.var x) (.pi A B)` and `NormNW Γ N A`, and its missing ingredient is
`HSubstSort (cubeSpec lambdaP2)` at `B`.  `hsubstPi_lambdaP2` and
`lambdaP2_expansionPostponement` are therefore not derived; the open lemma is unchanged:
`theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)`.

What would break the circularity: a predicate on *types* defined first (by recursion on the
kind skeleton, `CoC.cl`'s `.kind k`) whose base case is `HSubstSort`-style canonicity of types
under object substitution, proved by induction on the erasure of the type (`er`), before the
object-level predicate; the object arguments occurring in λP2 types then need the object-level
predicate at strictly smaller erased types.  Whether this mutual induction is well founded is the
remaining question; it was not settled this round.

## Round 9 — route (ii) for λP2: the round-8 failing step is closed; the two-level relation

Module: `Start/PTSRouteIITwoLevel.lean`.  Status: M29-EP-IMPREDICATIVE stays **TODO_READY**;
M29-EP-CUBE-REST stays **DONE_WEAK**.  New DONE_STRONG row M29-EP-TWO-LEVEL-CR for the pieces
below.  Axioms in `M29-EP-TWO-LEVEL-CR-axioms.txt` (at most `propext, Classical.choice,
Quot.sound`).

### A0. Is the round-8 failing step the unrestricted open lemma? — Neither: it is not open

Round 8 recorded that CR3 at a neutral application, the equation

  `NormNW (cubeSpec lambdaP2) Γ (.app (.var x) N) (B.instantiate N)`,

needs a canonical derivation of the normal form of `B[N]` (`HSubstSort` at `B`).  That reading of
the canonical judgement is **wrong**.  The application rule of `HasTypeNW`
(`Start/PTSExpansionLambdaPOmegaBarCanon.lean`) is

  `HasTypeNW Γ F (Π A B) → HasTypeNW Γ a A → Reduces (B[a]) B' → Normal B' → Normal (F a) →
   HasTypeNW Γ (F a) B'`

and asks for the normal form `B'` and `Normal B'` only, not for a derivation of `B' : s`.  The
normal form exists by strong normalization of the cube (`HasTypeNW.app_type_exists`).  The
equation is now proved, in every corner of the cube, with no hereditary substitution and no
restriction on `N` beyond normalizability:

```lean
theorem PureTypeSystem.RouteII.NeNW.app (f : CubeFeatures) {Γ : List (Expr Srt)} {F N A B : Expr Srt}
    (hF : NeNW (cubeSpec f) Γ F (.pi A B)) (hN : NormNW (cubeSpec f) Γ N A) :
    NeNW (cubeSpec f) Γ (.app F N) (B.instantiate N)
theorem PureTypeSystem.RouteII.cr3_var_app (f : CubeFeatures) {Γ : List (Expr Srt)} {x : ℕ} {N A B : Expr Srt}
    (hx : NormNW (cubeSpec f) Γ (.var x) (.pi A B)) (hN : NormNW (cubeSpec f) Γ N A) :
    NormNW (cubeSpec f) Γ (.app (.var x) N) (B.instantiate N)
```

(the contexts of the two premises and the domains are identified by uniqueness of normal forms;
`NeNW.weaken` and `NeNW.app_wk` give the Kripke form in context extensions).

### A0'. Where the circularity of the one-level relation really is

Checked on paper against the round-7/8 predicate `RouteII.Good` (not formalized as a negative
result).  Two places, and the user's reading is right about the second:

1. **`HasTypeR` in the candidates.**  `IsCand` asks for reduction-only judgements.  In the
   abstraction case of the fundamental lemma, the Kripke clause supplies an argument `N` typed at
   a *reduct* `A'` of the substituted domain, while the induction hypothesis for the body needs
   `N` at the domain itself; for `HasTypeR` that is closure under expansion of the type, which is
   expansion postponement.  Repair: drop `HasTypeR` from the candidates.  The base predicate is
   closed under *conversion* of the type (`NormNW.convType`), so the candidates `IsCandN` are
   closed under conversion and under expansion of the subject.
2. **The type-application clause carries no information about the constructor.**  At `∀X:K. B`
   the round-7 clause quantifies over every `U` with `HasTypeR Γ U K` and every candidate.  In the
   `(□,∗)` abstraction case the body may form `X N : ∗` (or `Π y : X N. C`); after substitution
   this is `U N'` for an arbitrary `U`, and the induction hypothesis needs `NormNW (U N') ∗`.  If
   `U = λz. T`, that is the hereditary substitution of `N'` into `T`: `HSubstSort` at sort `∗`.
   So the one-level relation needs the open lemma, but **only for reducible arguments `N'` in a
   type that is itself reducible**.  The two-level relation supplies exactly this from type
   reducibility (`TRed.app`), not from `HSubstSort`.

### A1. Type reducibility (proved)

`RouteII.TRed Cs Γ U K`, by recursion on the *semantic kind* `Cs : List Cand`, the candidates of
the domains of the λP2 kind `Π x₁:A₁ … Π xₙ:Aₙ. ∗` (kinds of λP2 have only object binders, rule
`(□,□)` is absent): at `[]` the judgement normalizes; at `C :: Cs` it normalizes and, in every
context extension `Γ₀`, for every reduct `K↑ ↠ Π A K'` and every `N ∈ C` at `A`,
`TRed Cs (U↑ N) (K'[N])`.  It is environment free, because the domains are given as candidates.
Proved: `TRed.escape` (CR1), `TRed.reflect` (CR3 for neutral constructors, from `NeNW.app_wk`),
`TRed.var`, `TRed.app` (the family-application case), `TRed.reduceKind`, `TRed.expand`.

### A2. Term reducibility relative to type reducibility (proved)

Skeletons `SkP` (`base`, `arr`, `all κ τ`) whose quantifier records the kind skeleton
`κ : KSkP` (the list of domain skeletons) of the bound constructor variable; `KSem κ ξ` is the
semantic kind.  `RouteII.GoodP s ξ` is the round-7 predicate with two changes: no `HasTypeR`
field, and at `all κ τ` the clause quantifies over constructors `U` with
`TRed (KSem κ ξ) (Γ₀ ++ Γ) U K` (and every candidate `C` for the bound variable).  Proved:

```lean
theorem PureTypeSystem.RouteII.GoodP.isCandN : ∀ (s : SkP) (ξ : ℕ → Cand), (∀ i, IsCandN (ξ i)) → IsCandN (GoodP s ξ)
theorem PureTypeSystem.RouteII.GoodP_subst : ∀ (s : SkP) (σ : ℕ → SkP) (ξ : ℕ → Cand),
    GoodP (s.subst σ) ξ = GoodP s (fun i => GoodP (σ i) ξ)
```

`GoodP.isCandN` is CR1 (escape), CR3 (neutral judgements are reducible, at arrows and at `all`
through `NeNW.app_wk`), closure under conversion of the type and under expansion of the subject.
`GoodP.var` (variables whose judgement normalizes are reducible: the identity substitution),
`GoodP.app` (object application), `GoodP.tyApp` / `GoodP.tyApp_subst` (type application with
the candidate `⟦t⟧ξ`, via `GoodP_inst`), `GoodP.lam_arr` (abstraction by β-expansion).

### A3. The fundamental lemma — not built; first missing lemma

No case of the two-level relation was found to fail: the relation-level steps of the variable,
application, type-application, abstraction and family-application cases are proved above.  What
is missing is the syntactic side for the new skeletons:

**First missing lemma**: the erasure of λP2 types into `SkP`, `ErasureP2.erP Δ ρ T : SkP`, equal
to the round-8 `er` except that `Π α:K. B` (rule `(□,∗)`) goes to `.all (erK Δ ρ K) (erP … B)`
with `erK (Π x:A. K') = .pi (erP A) (erK K')`, `erK ∗ = .star`, together with the analogues of
`er_instantiate_obj`, `er_instantiate` (now with `KSkP.subst`) and `er_conv`.  After it: the
fundamental lemma for `HasType (cubeSpec lambdaP2)` (conversion, not `HasTypeR`), for valid
target contexts (normalizable) and reducible substitutions (objects in `GoodP (erP A) ξ`,
constructor variables `X : K` in `TRed (KSem (erK K) ξ)`), with `TRed` as the conclusion for
constructors and `NormNW` for kinds; then `hsubstSort` for λP2 by the identity substitution
(`GoodP.var`, `TRed.var`), `hsubstPi_lambdaP2` through `hsubstPi_iff_hsubstSort`, and
`lambdaP2_expansionPostponement`.  None of these is proved this round.

coc: not started (stop rule: only if A closes for λP2).

## Round 10 — expansion postponement for λP2

Modules: `Start/PTSErasureP2Kind.lean` (A1), `Start/PTSRouteIIFundamental.lean` (A2–A4), and a
change to `Start/PTSRouteIITwoLevel.lean`.  Status: the row is split.  New **DONE_STRONG** row
M29-EP-LAMBDAP2 for the λP2 corner; M29-EP-IMPREDICATIVE becomes **DONE_WEAK** with the new gap row
M29-EP-COC (coc); M29-EP-CUBE-REST stays **DONE_WEAK** (λPω̲ and λP2 closed, coc open).  Axioms in
`M29-EP-LAMBDAP2-axioms.txt` (at most `propext, Classical.choice, Quot.sound`).

### A1. The erasure into `SkP` and `KSkP`

`ErasureP2.erP Δ ρ T : SkP` and `ErasureP2.erK Δ ρ K : KSkP` (mutual), indexed by the
classification `Δ : ℕ → Cls` of the variables and an environment `ρ : ℕ → SkP` for the
constructor variables:

* `Π α:K. B` (rule `(□,∗)`) goes to `.all (erK K) (erP B)`; `Π x:A. B` (rule `(∗,∗)`) to an
  arrow; object abstractions and applications are transparent, constructor applications erase
  their object arguments;
* `erK (Π x:A. K') = .pi (erP A) (erK K')`, `erK ∗ = .star`.

Proved with no typing hypothesis: `erPK_rename`, `erPK_skRename`, `erPK_skSubst`; **`erP_subst` /
`erK_subst`** (commutation with a substitution that respects the classification; one hypothesis
more than round 8's `er_subst`: the target classification has no kind variables,
`∀ n a, Δ' n ≠ .kind a`, which holds in λP2 because there are no `(□,□)` binders);
**`erP_instantiate_obj` / `erK_instantiate_obj`** (invariance under object substitution);
**`erP_instantiate` / `erK_instantiate`** (commutation with constructor substitution, with
`SkP.subst` and `KSkP.subst`).  Proved for well-typed λP2 terms: `erPK_beta`, `erP_beta`,
`erP_reduces`, **`erP_conv`**, `erK_beta`, `erK_reduces`, **`erK_conv`**.

### A2. The fundamental lemma

`RouteII.SemT Γ ξ Δ T X Y`: at `□`, `NormNW P2 Δ X Y`; at a kind `T`, `TRed (KSem (erK T) ξ) Δ X Y`;
at a type `T`, `GoodP (erP T) ξ Δ X Y`.  `RouteII.SubstOK Γ Δ σ ξ`: every `ξ i` is a candidate,
`Δ` reduces pointwise to a valid canonical context, and every declaration `n : A` of `Γ` is sent
to `σ n` with `Sem Γ ξ Δ (var n) A σ`.  `SubstOK.tail`, `SubstOK.weaken` (Kripke),
`SubstOK.cons`, `SubstOK.lift`.

**`RouteII.fundamental`**: `HasType (cubeSpec lambdaP2) Γ M T → SubstOK Γ Δ σ ξ → Sem Γ ξ Δ M T σ`,
one case per rule of `HasType`: axiom, variable, weakening, product (the three rules `(∗,∗)`,
`(□,∗)`, `(∗,□)`), abstraction (Kripke: `body_inst`, with `TRed.lam` and `GoodP.lam_all`,
`GoodP.lam_arr`), application (`GoodP.app`, `GoodP.tyApp` with `erP_instantiate`,
`TRed.app` with `erK_instantiate`, object instantiation with `erP_instantiate_obj`), conversion
(`erP_conv`, `erK_conv`, `TRed.convKind`, `SemT_srcConv`).  No case failed.

One change to round 9 was needed: the candidates `IsCandN` carry one more closure property,
**weakening** (`NormNW.weaken`), used by `SubstOK.weaken`; `isCandN_normNW` and
`GoodP.isCandN` are updated.

### A3–A4. The terminal statements

* `RouteII.SubstOK.ids` — the identity substitution is reducible (`GoodP.var`, `TRed.var`);
* `RouteII.sortFundamental_lambdaP2`, hence `hsubstSort_lambdaP2 : HSubstSort (cubeSpec lambdaP2)`
  (through `hsubstSort_iff_sortFundamental`);
* **`hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)`** (through `hsubstPi_iff_hsubstSort`);
* **`lambdaP2_expansionPostponement : ExpansionPostponement (cubeSpec lambdaP2)`** (through
  `cube_expansionPostponement_of_hsubstPi`), and `lambdaP2_productNormalizationR`.

Both are the board's targets as defined in the repository, with no hypothesis.

### coc: the first missing lemma

By `er_beta_fails_coc` (round 8), an erasure of coc types into λ2-like skeletons is not
invariant under β: coc has `(□,□)` abstractions, so a constructor variable can be bound by a
type-level λ and applied, and the skeleton of `(λα:∗. α) X` must be the skeleton of `X`.  The
skeletons must therefore be Fω type constructors modulo β.  **First missing lemma**:
`ErasureCoC.erω_conv` — an erasure of coc constructors into Fω type constructors (with their
kinds), commuting with substitution and invariant under conversion modulo Fω β-conversion —
together with `GoodPω_beta`, the invariance of the term relation at an Fω skeleton under Fω β.
Then the coc analogues of `TRed`, `GoodP` and `RouteII.fundamental`.  Row M29-EP-COC.

## Round 11 — expansion postponement for coc, and for the whole λ-cube

Modules: `Start/PTSErasureCoCOmega.lean` (A1), `Start/PTSRouteIICoC.lean` (A2),
`Start/PTSRouteIICoCFundamental.lean` (A3), `Start/PTSExpansionCoC.lean` (A4–A5).  Status:
**M29-EP-COC, M29-EP-IMPREDICATIVE and M29-EP-CUBE-REST are DONE_STRONG**.  Axioms in
`M29-EP-COC-axioms.txt` (at most `propext, Classical.choice, Quot.sound`; no `sorry`, no
`native_decide`).

### A1. The Fω interpretation, over an arbitrary base

Following the suggestion (Geuvers' short SN proof for coc), kinds and constructors are interpreted
directly in a semantics, not in Fω syntax modulo β.  The repository already had this
interpretation for saturated sets (`CoC.interp`, `Start/CoCModel.lean`, with `CoC.interp_conv` in
`Start/CoCSN.lean`); round 11 abstracts its base:

* `ErasureCoC.KSkω` (`star`, `arr`), `erKω : CoC.Sk → KSkω` (object products dropped,
  constructor products kept), `Vω B : KSkω → Type`, and `V_erKω : V B k = Vω B (erKω k)`;
* `ErasureCoC.KAlg B` — a default element `dflt`, the product over a constructor variable
  `piK : (a : Sk) → B → (V B a → B) → B` and the object product `piO : B → B → B`;
* `interpK 𝔄 Δ T k ξ : V B k` — the interpretation at an expected skeleton, total (default
  element on a shape mismatch); constructor λ ↦ `fun v => ⟦b⟧(ξ, v)`, constructor application ↦
  `⟦F⟧ξ (⟦U⟧ξ)`, object λ and object application transparent, products by `piK`/`piO`;
* proved for every algebra: `interpK_rename`, **`interpK_subst`** and
  **`interpK_instantiate`** (`⟦b[U/x]⟧ξ = ⟦b⟧(ξ, ⟦U⟧ξ)`; an object `U` is irrelevant by
  `interpK_agree`), `interpK_beta`, `interpK_reduces` and **`interpK_conv`** (the plan's
  `erω_conv`): the interpretation of well-typed kinds and types is invariant under conversion, in
  every corner of the cube.  The classification is stable under reduction and substitution by
  `CoC.cl_beta` and `CoC.cl_subst` (round M23-COC-SN).
* `interpK_omegaRedex` — the equation refuted for the λ2 erasure by `er_beta_fails_coc` holds
  for every algebra.

### A2. The coc candidates

`RouteIICoC.IsCandC` (normalizable, closed under conversion of the type, CR3 for neutral
judgements, expansion, weakening — round 10's `IsCandN` for `cubeSpec coc`); `CandC k v`
(`IsCandC` at `∗`, preservation at `arr`: the plan's `TRed` at `arr κ₁ κ₂`, on the semantic side);
`candAlg : KAlg Cand` with `piOC` (Kripke closure under application, `GoodP` at an arrow) and
`piKC a X F` (Kripke closure under application to every constructor `U` in the candidate `X` of
the bound kind, for every `v` with `CandC a v`).  Proved: `isCandC_piO`, `isCandC_piK` (CR1–CR3,
expansion, weakening) and **`interpC_cand`** (the interpretation of a well-classified kind or
constructor under a good valuation is a candidate).

The syntactic part of the plan's `TRed` (constructor `U` at kind `K`) is carried by the candidate
`⟦K⟧ξ` itself: a kind is interpreted at `∗` like a type, `Π x:A. K` by an object product and
`Π α:K₁. K₂` by `piKC`, so no separate kind-indexed relation is needed.

### A3. The fundamental lemma

`RouteIICoC.SemC Γ ξ Δ T X Y` — normalization if `T = □`, otherwise `⟦T⟧ξ Δ X Y`;
`RouteIICoC.SubstOK` (good valuation, normalizable target context, admissible declared types,
variables in the semantics); `tail`, `weaken`, `cons`, `lift`, `body_inst`.

**`RouteIICoC.fundamental`**: `HasType (cubeSpec coc) Γ M T → SubstOK Γ Δ σ ξ → Sem Γ ξ Δ M T σ`,
one case per rule: axiom, variable, weakening, product (all four rules, through
`NormNW.product`), abstraction (one case for a kind domain — rules `(□,∗)` and `(□,□)` — and one
for a type domain — rules `(∗,∗)` and `(∗,□)`), application (the same split, with
`interpK_instantiate` and `interpK_agree`), conversion (`interpK_conv`).  No case failed.

### A4–A5. The terminal statements

* `RouteIICoC.SubstOK.ids`, `RouteIICoC.substOK_substAt`, `RouteIICoC.sortFundamental_coc`;
* `hsubstSort_coc`, **`hsubstPi_coc : HSubstPi (cubeSpec coc)`** (through `hsubstPi_iff_hsubstSort`);
* **`coc_expansionPostponement : ExpansionPostponement (cubeSpec coc)`** (through
  `cube_expansionPostponement_of_hsubstPi`), and `coc_productNormalizationR`;
* **`cube_expansionPostponement_all (f : CubeFeatures) : ExpansionPostponement (cubeSpec f)`** —
  the non-dependent corners by `cube_expansionPostponement`, λP, λPω̲, λP2 and coc by their
  theorems.

Exactly the board's targets, with no hypothesis.  This proof of the coc corner does not use Poll's
Lemma 10 / Theorem 11.

### M29-EP-STATEMENT, exit criterion 2, for the cube

Criterion 2 asks for `expansionPostponement_of_sn` and `expansionPostponement_of_wn` for every
`Specification`.  For the eight corners of the cube the conclusion now holds
(`cube_expansionPostponement_all`), without Poll's argument.  What remains of criterion 2 is the
general statement: normalizing specifications outside the cube (with other sorts, axioms or
rules).  First missing lemma, unchanged:
```lean
theorem expansionPostponement_of_wn {S : Type u} (P : Specification S)
    (hw : SystemWeaklyNormalizing P) : ExpansionPostponement P
```
Route (ii) of this round uses the cube's classification (`CoC.cl`: kinds, constructors, objects)
and a model of the kind level; a general normalizing specification has no such classification.

## Round 11, Stage C experiment (B1)

A scratch checker (Python, kept outside the repository) implements `HasTypeR` of
`Start/PTSExpansion.lean` literally — the seven rules `ax`, `var`, `weaken`, `product`,
`abstraction`, `application`, `reduction` (one β step of the type), with `rename`, `subst`,
`instantiate` and `Beta` as in `Start/PTSBasic.lean` — and `SortedSubjectReductionR` as defined in
`Start/PTSExpansion.lean`: for each found `Γ ⊢r M : s` with `s` a sort and each one-step reduct
`M'` of `M`, it searches for `Γ ⊢r M' : s`.

Search 1 enumerates all judgements with a derivation of at most `N` rule nodes, keeping terms and
types of size ≤ `SZ` and contexts of length ≤ `CL`; search 2 is the same enumeration, with bounds
`N₂`, `SZ₂`, restricted to the contexts (and their suffixes) of the reducts.

Specifications:
* `Wdep` (as in `Start/PTSExpansionBeyondPoll.lean`): sorts `o, t, t', k, u`; axioms
  `o:t, o:t', t:k, k:u`; rules `(o,o,o), (t,t,t), (k,t,t), (k,k,k), (u,k,k)` and the dependent
  rule `(o,t,t)`.
* `Wdep2` := `Wdep` plus the dependent rule `(o,t',t')` (also not weakly normalizing, since it
  contains `Wdep`, and not functional: `o:t` and `o:t'`).

| spec | N | SZ | CL | judgements | typed by a sort | (judgement, reduct) pairs | N₂ | SZ₂ | judgements (search 2) | failures |
|---|---|---|---|---|---|---|---|---|---|---|
| Wdep | 14 | 9 | 3 | 2182 | 1562 | 25 | 18 | 11 | 505 | 0 |
| Wdep | 16 | 11 | 3 | 4592 | 3180 | 97 | 22 | 13 | 7708 | 0 |
| Wdep2 | 16 | 11 | 3 | 4600 | 3188 | 97 | 22 | 13 | 7719 | 0 |
| Wdep | 20 | 11 | 3 | 18667 | 12477 | 790 | 26 | 13 | 36466 | 0 |
| Wdep | 22 | 13 | 4 | 41812 | 25899 | 1847 | 28 | 15 | 83763 | 0 |

Smallest judgements with a redex (derivation sizes 10–12): `[] ⊢r (λx:t. x) o : t`,
`[] ⊢r (λx:k. o) t : t`, `[] ⊢r (λx:t. o) o : t`, `[o] ⊢r (λx:t. x) o : t`; each reduct
(`o : t`) is found.  **No failure** of `SortedSubjectReductionR` was found within these bounds;
the chains of Stage C (through `(o,t,t)`) need terms far larger than these bounds (Hurkens' term
has hundreds of nodes), so the experiment neither supports a counterexample nor tests the critical
chain.

B2 (counterexample) was therefore not started: no candidate survived.  B3 (positive direction):
no invariant was extracted from the data; the route (ii) proof of this round needs normalizing
candidates and so does not apply to `Wdep`, which is not weakly normalizing.  First missing lemma:
```lean
theorem Wdep_expansionPostponement : ExpansionPostponement Wdep
```
(equivalently `SortedSubjectReductionR Wdep`); in general, unchanged,
`theorem sortedSubjectReductionR_all {S : Type u} (P : Specification S) : SortedSubjectReductionR P`.

## Series V, round 1

### Part B (B1): the chain of calls for `Wdep`, in Lean terms

Lean-checked in this round: `BeyondPoll.Wdep_typeA_domain` (`Start/PTSExpansionWdepChain.lean`):
`⊢ Π x : typeA. o : t` in `Wdep` (through `(o, t, t)`), and `typeA` has no normal form.
Everything else in this subsection is analysis on paper; nothing of it is claimed as proved.

**Where `core_aux` uses the stratification.**  Take the levels of `W_stratified`
(`o ↦ 0`, `t, t' ↦ 1`, `k ↦ 2`, `u ↦ 3`).  `Wdep` satisfies `axiom_level` and every `rule_level`
except `level s₂ ≤ level s₁` for `(o, t, t)`.  In `Stratification.core_aux` (measure
`(bound + 2 − k, M)`, `k` the `TypeLevel`) the inequality `level s₂ ≤ level s₁` is used in exactly
two calls:
* `pi` case, `ihA` on the domain: the product `Π A B : s₃` is at `k = level s₃ + 1`, its domain at
  `level s₁ + 1`; the structural call needs `level s₁ ≥ level s₃ = level s₂`.  For `(o, t, t)`:
  from `k = 2` down to `k = 1`.
* `app` case, `iha` on the argument: `f a` with `f : Π D E : r₃` is at `k = level r₂`, the argument
  at `level r₁`.  For `(o, t, t)`: from `k = 1` down to `k = 0`.
The `lam` case is unaffected (its domain call needs only `level s₁ + 1 ≥ level s₂`, true for
`(o, t, t)`), and the only non-structural call (`ihn` on `Π A B'`, `B'` the reduct returned for the
body) goes up one level, as in Stage B.  So the chain of an open induction is: a level-1 `λ`
(a U⁻ proof) → `ihn` on its product type `Π A B'` at level 2, where `B'` is a reduct of the type
of the body (not a subterm) → a `(o, t, t)` domain inside `B'` at level 1, or an object argument at
level 0 → a `λ` inside that subject → `ihn` on its type → …

**Candidate 1: Stage B's measure on an object-erasure.**  Let `|·|` drop `(o, t, t)` domains and
object arguments (the λP → λ→ erasure).  Every call of `core_aux` except the two above maps to a
call on the erasure that the Stage B measure accepts; the two exceptional calls go to subjects
that `|·|` deletes.  So the erasure reduces the problem to the termination of the calls *on the
deleted subjects* — `o`-types (level 1) and objects (level 0) — which is candidate 2.

**Candidate 2: a separate inner induction for the object layer.**  It does not exist in the
form proposed, because the deleted subjects do not form a lower layer:
* an `o`-type is a level-1 term, i.e. an arbitrary U⁻ proof of `o`; its `λ`-subterms are level-1
  abstractions whose product types are level-2 terms, which may again contain `(o, t, t)`
  domains (the rule is available everywhere in the U⁻ part);
* so the "object layer" contains, through the types of its abstractions, the whole level 1–2 part
  of the system, and an inner induction on it is the original problem;
* an inner measure bought from normalization (as for coc, measure (a) of round 5) is excluded:
  `Wdep_typeA_domain` shows that a non-normalizing `o`-type is a legal `(o, t, t)` domain.

**Decision.**  No well-founded order is found.  The structural fact that an order would need is
the termination of the relation "`N` is a `(o, t, t)` domain or object argument occurring in a
reduct of the type of a level-1 abstraction occurring in `M`" on `Wdep`-typable terms; neither
candidate gives it, and its natural measures (size, level, SN of the type) all fail (the second
by the chain above, the third by `Wdep_typeA_domain`).

**B2/B3.**  B2 was not started (no order).  B3 was not started: the calls are not deterministic
(`B'` is any reduct the induction returns), so a non-terminating chain of calls is not by itself
a judgement without a reduction-only derivation; no invariant of `HasTypeR Wdep` derivations was
found.  First missing lemma, unchanged:
```lean
theorem Wdep_expansionPostponement : ExpansionPostponement BeyondPoll.Wdep
```
No class version (B2's `expansionPostponement_of_<class>`) is stated: without an order there is
no candidate hypothesis on the bottom layer that the proof would use.

### Part C: specifications with a morphism into coc (row M29-EP-COC-MORPHISM)

Modules: `Start/PTSExpansionSNGeneric.lean`, `Start/PTSExpansionCoCMorphism.lean`.  Axioms in
`M29-EP-COC-MORPHISM-axioms.txt`.

**C1 (proved).**
```lean
structure CoCMorphism {S : Type} (P : Specification S) where
  φ : S → Srt
  axiom_map : ∀ s t, P.axioms s t → (cubeSpec coc).axioms (φ s) (φ t)
  rule_map : ∀ a b c, P.rule a b c → (cubeSpec coc).rule (φ a) (φ b) (φ c)
```
with `CoCMorphism.rule_eq` (`φ s₃ = φ s₂`), `CoCMorphism.hasType` (transport, by
`HasType.mapSort`), `CoCMorphism.validContext`, and **`CoCMorphism.stronglyNormalizing :
SystemStronglyNormalizing P`** (from `coc_stronglyNormalizing` and
`StronglyNormalizing.of_mapSort`).  Hence `CoCMorphism.expansionPostponement_iff_productNormalizationR`.

**C2 (half proved).**  The round-11 chain is
`SortFundamental → HSubstSort → HSubstPi → HSubstNW → ProductNormalizationR → ExpansionPostponement`.
`Start/PTSExpansionSNGeneric.lean` restates its definitions over an arbitrary sort type
(`SNGeneric.NormNW`, `SortFundamental`, `HSubstSort`, `HSubstPi`, `HSubstNW`; definitionally the
round-11 ones at `Srt`, `sortFundamental_iff`) and reproves every link after the first for an
arbitrary specification with strong normalization as the only hypothesis
(`hsubst_route3_aux`, `hsubstNW_of_hsubstPi`, `normalizeNW_of_hsubst`,
`productNormalizationR_of_hsubst`, **`expansionPostponement_of_sortFundamental`**); the cube
versions used `cube_stronglyNormalizing` and nothing else specific to the cube.  Sanity check:
`SNGeneric.coc_expansionPostponement'` re-derives coc from `RouteIICoC.sortFundamental_coc`.
Therefore
```lean
theorem CoCMorphism.expansionPostponement_of_sortFundamental (m : CoCMorphism P)
    (h : SNGeneric.SortFundamental P) : ExpansionPostponement P
```
and the target `expansionPostponement_of_cocMorphism` is reduced to route (ii) for `P`.

Route (ii) itself, first two layers, also generalized and proved (any sort type, SN hypothesis
only where CR3 needs it):
* base predicate (`Start/PTSExpansionSNGeneric.lean`): `SNGeneric.NormNW.reduceType`,
  `NormNW.abstraction`, `NormNW.product`, `NormNW.expand`, `NormNW.convType`, `NormNW.weaken`,
  `NeNW`, `NeNW.of_var`, `NeNW.app` (with `hsn` in place of `cube_stronglyNormalizing`),
  `NeNW.weaken`, `NeNW.app_wk`;
* candidates (`Start/PTSRouteIIMorphismCand.lean`): `SNGeneric.IsCandC P`, `piOC P`, `piKC P`,
  `CandC P`, `candAlg P : KAlg (CandP S)` (the round-11 algebra over sets of `P`-judgements),
  `isCandC_piO`, `isCandC_piK`, and `interpC_cand` (the interpretation of a well-classified coc
  term under a good valuation of `P`-candidates is a `P`-candidate).
What is not written is the third layer: `SemC`/`SubstOK`/`fundamental` of
`PTSRouteIICoCFundamental.lean` and `SubstOK.ids`/`substOK_substAt` of `PTSExpansionCoC.lean`.

**Stop rule (C2).**  First missing lemma:
```lean
theorem sortFundamental_of_cocMorphism {S : Type} {P : Specification S} (m : CoCMorphism P) :
    SNGeneric.SortFundamental P
```
The first definition of round 11 that does not generalize verbatim is `RouteIICoC.SemC`:
```lean
def SemC (Γ) (ξ) (Δ) (T X Y : Expr Srt) : Prop :=
  if T = .sort .box then NormNW PC Δ X Y else interpK candAlg (ctxCl Γ) T .star ξ Δ X Y
```
It tests the P-type syntactically against coc's `□` and interprets it with coc's classification.
For `P` it must become `if T.mapSort m.φ = .sort .box then SNGeneric.NormNW P Δ X Y else
interpK candAlgP (ctxCl (Γ.map (Expr.mapSort m.φ))) (T.mapSort m.φ) .star ξ Δ X Y`, with
`candAlgP` the round-11 algebra over candidates of `P`-judgements.  The equations the cases then
need are the round-11 ones transported along `mapSort` (`Expr.mapSort_subst`,
`Expr.mapSort_instantiate`, `Beta.mapSort`, `Converts.mapSort`, `CoCMorphism.hasType` for
`interpK_conv`), plus, in the axiom case, `HasTypeNW P Δ (.sort s) (.sort t)` for `P.axioms s t`
in place of `HasTypeNW.star_box_of_valid'`.  In this analysis no case of the fundamental lemma
fails for a non-functional `P` (the candidates are sets of `P`-judgements, so two kinds `□, □'`
above `∗` are simply two judgements); but the generalized fundamental lemma (about 470 lines of
`PTSRouteIICoCFundamental.lean` plus the two closing lemmas of `PTSExpansionCoC.lean`, over the
generic base predicate and candidates above) was not written in this round, so this paragraph is
analysis, not a Lean result.

**C3 (proved).**  `CoCMorphism.cube f` (the eight corners, `φ = id`;
`cube_in_cocMorphism_class`); `cocBox2` (sorts `∗, □, □'`, axioms `∗ : □`, `∗ : □'`, rules
`(s₁, s₂, s₂)` for all sorts) with `cocBox2_cocMorphism` (`□' ↦ □`), `cocBox2_not_functional`,
`cocBox2_not_stratified`, `cocBox2_in_class` (morphism, not functional, not stratified, strongly
normalizing) and `cocBox2_expansionPostponement_iff : ExpansionPostponement cocBox2 ↔
ProductNormalizationR cocBox2`.  Expansion postponement of `cocBox2` itself is not concluded.

**M29-EP-STATEMENT, criterion 2, after C.**  What remains: (1) for strongly normalizing `P`,
exactly `SNGeneric.SortFundamental P` (route (iii) and the product-normalization step are now
generic); (2) for `P` with a morphism into coc, `sortFundamental_of_cocMorphism` above; (3) the
weakly-but-not-strongly normalizing case, `expansionPostponement_of_wn`, unchanged.

## Series V, round 1, run 2

### Part A: the route (ii) fundamental lemma through a morphism into coc (proved)

Module `Start/PTSRouteIIMorphismFundamental.lean` (over `Start/PTSRouteIIMorphismCand.lean`).
Axioms in `M29-EP-COC-MORPHISM-FUNDAMENTAL-axioms.txt` (standard axioms only).

**A1.**  The round-11 third layer, generalized along `m : CoCMorphism P` (namespace
`PureTypeSystem.MorphFund`):
* `SemC P Γc ξ Δ T X Y := if T = □ then SNGeneric.NormNW P Δ X Y else interpK (candAlg P)
  (ctxCl Γc) T ∗ ξ Δ X Y` — `Γc`, `T` are coc terms, `X`, `Y`, `Δ` are `P`-terms;
* `Sem m Γ ξ Δ M T σ := SemC P (Γ.map (mapSort m.φ)) ξ Δ (T.mapSort m.φ) (M.subst σ) (T.subst σ)`
  — the type of a `P`-judgement is tested and interpreted through its image;
* `SubstOK m Γ Δ σ ξ` (good valuation for the image context, normalizable target context,
  admissible image types, variables in the semantics), `SubstOK.tail/weaken/cons/lift`,
  `body_inst`;
* **`MorphFund.fundamental (m : CoCMorphism P) (h : HasType P Γ M T) : SubstOK m Γ Δ σ ξ →
  Sem m Γ ξ Δ M T σ`** — by induction on the `P`-derivation; every classification fact
  (`CoC.wc_of_hasType`, `relC_of_sorted`, `type_sorted`, `ne_box_of_hasType`, `classify`,
  `not_conv_box`, `interpK_conv`, `regularity`) is applied to the image derivation
  `m.hasType h`; the equations are `Expr.mapSort_rename`, `Expr.mapSort_instantiate`,
  `Converts.mapSort`, `List.map_cons`; the axiom case uses
  `MorphFund.HasTypeNW.ax_of_valid : ValidContextNW P Δ → P.axioms s t → HasTypeNW P Δ (.sort s)
  (.sort t)`; strong normalization enters only through `interpC_cand` (CR3 at neutral
  applications), with `m.stronglyNormalizing`;
* `SubstOK.ids`, `substOK_substAt`, and
```lean
theorem sortFundamental_of_cocMorphism {S : Type} {P : Specification S} (m : CoCMorphism P) :
    SNGeneric.SortFundamental P
```
No case failed: the run-1 analysis (no case of the fundamental lemma uses functionality of `P`)
is confirmed by Lean.

**A2.**
```lean
theorem expansionPostponement_of_cocMorphism {S : Type} {P : Specification S}
    (m : CoCMorphism P) : ExpansionPostponement P
theorem cocBox2_expansionPostponement : ExpansionPostponement cocBox2
```
with no other hypothesis (through `CoCMorphism.expansionPostponement_of_sortFundamental`).

**A3.**  A second instance outside the cube: `cocDouble` over `Srt4 = {∗, ∗', □, □'}`, axioms
`s : t` for `s ∈ {∗, ∗'}`, `t ∈ {□, □'}`, rules `(s₁, s₂, s₃)` whenever `s₃` and `s₂` collapse to
the same coc sort; `cocDouble_cocMorphism` (the collapse `∗' ↦ ∗`, `□' ↦ □`),
`cocDouble_axioms_not_functional` (`∗ : □`, `∗ : □'`), `cocDouble_rules_not_functional`
(`(∗, ∗, ∗)`, `(∗, ∗, ∗')`), `cocDouble_axioms_not_injective` (`∗ : □`, `∗' : □`),
`cocDouble_not_stratified`, and `cocDouble_expansionPostponement : ExpansionPostponement cocDouble`.

Which published hypotheses the instances meet (as far as we know the papers; see the literature
check above):
* *Poll (normalising types).*  Every specification with a morphism into coc is strongly
  normalizing (`CoCMorphism.stronglyNormalizing`), so every type of a derivable judgement has a
  normal form: the cube corners, `cocBox2` and `cocDouble` all meet Poll's hypothesis.  Our proof
  does not use Poll's argument (whose Lemma 10 has the gap recorded above).
* *Barthe (injective PTSs, which are in particular functional).*  The cube corners are functional;
  whether they meet Barthe's exact injectivity conditions we have not checked.  `cocBox2` is not functional (`cocBox2_not_functional`), hence outside.
  `cocDouble` has non-functional axioms, non-functional rules and non-injective axioms, hence
  outside on every reading of "injective" that includes functionality.

**Boards.**  M29-EP-COC-MORPHISM-FUNDAMENTAL: DONE_STRONG.  M29-EP-COC-MORPHISM: all four exit
criteria met, DONE_STRONG.  M29-EP-STATEMENT, criterion 2: what remains is (1) the strongly
normalizing case without a morphism into coc, `SNGeneric.SortFundamental P`, and (2) the
weakly-but-not-strongly normalizing case, `expansionPostponement_of_wn`.

### Part C: `Wdep`, seeded counterexample search (C1, C3)

Everything in this subsection is an unverified computation (Python, `wip/c1_wdep.py`, kept outside
the repository); nothing in it is Lean-checked and no claim about `Wdep` is made.

**Checker.**  Run 1's checker was gone; a new one was written.  Terms in de Bruijn form as in
`Start/PTSBasic.lean`; `Wdep` = sorts `o, t, t', k, u`, axioms `o:t, o:t', t:k, k:u`, rules
`(o,o,o), (t,t,t), (k,t,t), (k,k,k), (u,k,k), (o,t,t)`.  `infer` computes syntactic types of
`HasType` (conversion tested by a bounded common-reduct search); `inferR` computes the minimal
types of `HasTypeR` (the reduction rule is the closure under reducts; the abstraction rule keeps a
reduct `B'` of the body type only when `Π A B'` is `HasTypeR`-typed by a sort; the application
rule needs the argument type to reduce to the domain exactly).  A judgement `Γ ⊢ M : A` is a
*bounded candidate* when no bounded reduct of `A` is a bounded reduct of an `inferR` type of `M` —
the counterexample form of M29-EP's exit criterion, up to the bounds.  Reduct sets: breadth-first
to depth 3 on terms of size ≤ 400, plus 40 leftmost-outermost steps (the only reducts computed
for `typeA`, whose size is 2907).  `typeA` is read from Lean (`#eval` of an S-expression printer
on `BeyondPoll.typeA`); the checker gives `typeA : o` in both systems, as `typeA_typed`.

**Seeds.**  `typeA` and its first two leftmost-outermost reducts `A₁, A₂`; for each `A` among
them: `Π x:A. o`, `Π x:A. x`, `λx:A. x`, `λx:A. o`, `λy:(Π x:A. o). y`, `(λx:o. x) A`,
`(λx:o. Π y:x. o) A`, `λx:x. x`; small material (`o`, `Π o o`, `λx:o. x`, `(λx:t. x) o`, …);
each wrapped as `M`, `λz:o. M`, `λz:z. M`, `(λz:o. M) z`; contexts `[]`, `[o]`, `[t]`,
`[Π o t]`, `[Π o o, o]`, `[A]`, `[Π A t]`, `[A, Π A o]`.

**Result.**  Without `typeA` (sanity run): 140 seed judgements, 70 typed, 0 bounded candidates.
With `typeA` (time limit 600 s): 85 seeds tried, all in the empty context (the limit was reached
before the other contexts), 48 typed judgements, **0 bounded candidates**.  Typing each
`typeA`-seed costs about 60 s in the checker (the abstraction rule of `inferR` explores reducts of
body types), which is what bounded the run.

**Closest misses.**  None to report: every typed seed had an `inferR` type sharing a bounded
reduct with its `HasType` type, and the checker records no finer distance.  The seeds that would
exercise the `(o,t,t)` chain of part B (an abstraction whose body type reaches a product only
through `typeA`'s infinite reduction) need the non-empty contexts that the run did not reach.

**C2** was not started (no candidate).  First missing lemma, unchanged:
```lean
theorem BeyondPoll.Wdep_expansionPostponement : ExpansionPostponement BeyondPoll.Wdep
```
and, for a negative answer, a judgement `HasType Wdep Γ M A` with
`¬ ∃ B, Relation.ReflTransGen Beta A B ∧ HasTypeR Wdep Γ M B`, together with an invariant of all
`HasTypeR Wdep` derivations in `Γ` that `M` violates.

## Series V, round 2, run 1

### Part A: beyond coc — a top sort (rows M29-EP-TOP-MORPHISM, M29-EP-CCOMEGA)

Modules: `Start/PTSExpansionTop.lean`, `Start/PTSExpansionTopSN.lean`,
`Start/PTSExpansionTopKindFree.lean` (axioms: `M29-EP-TOP-MORPHISM-axioms.txt`).

**Proved.**
* `cocTop` (sorts `∗, □, Δ`; axioms `∗ : □`, `□ : Δ`; the four coc rules, none mentioning `Δ`) and
  `lambdaHOL` (same axioms; rules `(∗,∗)`, `(□,∗)`, `(□,□)`).
* `lambdaHOL_not_cocMorphism : CoCMorphism lambdaHOL → False` (`∗ : □` forces `φ □ = □`, `□ : Δ`
  forces `φ □ = ∗`); `lambdaHOL_topMorphism`; `CoCMorphism.toTop` (the coc-morphism class is
  contained in the top-morphism class); `lambdaHOL_in_top_class`.
* `TopMorphism.sort_untypable` (a sort sent to `Δ` is never a typable subject) and
  `TopMorphism.top_typed_sort` (only sorts are typed by a sort sent to `Δ`).
* **`TopSN.cocTop_stronglyNormalizing : SystemStronglyNormalizing cocTop`**, by route (ii) of the
  task: `TopSN.kindSubst` sends every valid context to a valid *kind-free* context (no declaration
  `K : □`) by a typed substitution (`K ↦ ∗`); `TopSN.kf_coc` sends kind-free judgements whose type
  is not `Δ` to coc judgements along the collapse `Δ ↦ □`.  The only delicate case of `kf_coc` is
  conversion to the target `□` (its premise `□ : Δ` has no coc image); there the coc image of the
  source type converts to `□`, and since `□` is untypable in coc the source type must be `□`
  itself.  SN is pulled back by `StronglyNormalizing.of_subst` and `StronglyNormalizing.of_mapSort`.
* **`TopMorphism.stronglyNormalizing`** for every top-morphism specification;
  `lambdaHOL_stronglyNormalizing`.
* **`TopMorphism.expansionPostponement_of_sortFundamental (m : TopMorphism P)
  (h : SNGeneric.SortFundamental P) : ExpansionPostponement P`** — SN is no longer a hypothesis.
* **`lambdaHOL_expansionPostponement`**: `λHOL` is stratified (`∗ ↦ 0`, `□ ↦ 1`, `Δ ↦ 2`), so
  Stage B applies.  `cocTop_not_stratified`.
* **`TopSN.cocTop_expansionPostponement_kindFree`**: expansion postponement for every `cocTop`
  judgement in a kind-free context whose type is not `Δ` (from `coc_expansionPostponement`, along
  `Δ ↦ □` and back; `TopSN.noTop`: legal expressions do not mention `Δ`).

**Not proved.** `expansionPostponement_of_topMorphism` and `cocTop_expansionPostponement`.
First missing lemma:
```lean
theorem sortFundamental_of_topMorphism {S : Type} {P : Specification S} (m : TopMorphism P) :
    SNGeneric.SortFundamental P
```
(for `cocTop` itself: `SNGeneric.SortFundamental cocTop`).  The first case that fails when
`MorphFund` is transported to `cocTop`: the variable/weakening cases for a declaration `x : K` with
`K` a kind variable (`K : □`).  `MorphFund.SemC` interprets a type through the coc skeleton model
of `Start/CoCSN.lean` (`ErasureCoC.interpK` over `CoC.Sk`, `CoC.cl`, `CoC.ctxCl`), which computes
the skeleton of a kind syntactically from the kind expression; a kind variable has no syntactic
skeleton, so `interpK` of a type of kind `K` is undefined.  The kind substitution used for SN does
not help here: it changes the subject, and `HasTypeR` derivations do not commute with it.  In
kind-free contexts the gap is closed (`cocTop_expansionPostponement_kindFree`).

**A2 (`CC^ω`).** Defined: `ccOmega` (sorts `Prop`, `Type n`), `CCOmegaMorphism`,
`coc_ccOmegaMorphism`, `lambdaHOL_ccOmegaMorphism`, `cocTop_ccOmegaMorphism`,
`TopMorphism.toCCOmega`, and `ccOmega_not_topMorphism` (`Prop : Type 0 : Type 1 : Type 2` needs
four levels).  SN of `CC^ω` was not started (A1 did not close).  Which parts of `Start/CoCSN.lean`
generalize: the candidate algebra (`SNGeneric.CandP`, `IsCandC`, saturation) and the product/
abstraction cases do not depend on the number of sorts; the skeleton model does not, because it
has exactly two skeleton levels (objects typed by `∗`, constructors typed by kinds) and computes
skeletons of kinds syntactically.  A predicative hierarchy needs a skeleton (a set-theoretic
interpretation of kinds) at every level `Type n`, with kind variables at every level interpreted
by arbitrary skeleton sets — the same obstruction as the kind variables of `cocTop`, iterated.
First missing lemma toward `SystemStronglyNormalizing ccOmega`: the skeleton interpretation of
`Type n`-kinds with variables, i.e. a generalization of `CoC.Sk`/`CoC.cl` to contexts declaring
variables of type `Type n` (no Lean statement yet beyond
`theorem ccOmega_stronglyNormalizing : SystemStronglyNormalizing ccOmega`).
The kind-substitution route of A1 does not generalize: for `CC^ω` there is no top level whose
variables can be substituted away.

### Part C: λ* (row M29-EP)

**C1 (positive direction).** Not proved.  The obstacle is unchanged: in the β-redex
`(λx:C''. e) a` with `Γ ⊢r λx:C''. e : Π C'' E''`, `Π C'' E'' →* Π C E` and `Γ ⊢r a : C`, the
substitution lemma needs `a : C''`, and the reduction-only system has no way to expand `C` back to
`C''`.  Functionality of `λ*` (one axiom, one rule) does not give such an expansion: the
`HasTypeR` rules only ever reduce types.  First missing lemma (a substitution lemma along a
reduction of the declared type), as a Lean statement:
```lean
theorem lambdaStar_substR_expand {Γ : List (Expr Unit)} {C'' C e E a : Expr Unit}
    (hC : Relation.ReflTransGen Beta C'' C) (he : HasTypeR lambdaStar (C'' :: Γ) e E)
    (ha : HasTypeR lambdaStar Γ a C) :
    ∃ E', Relation.ReflTransGen Beta (E.instantiate a) E' ∧
      HasTypeR lambdaStar Γ (e.instantiate a) E'
```
It implies `SortedSubjectReductionR lambdaStar` at the root β-step; it is not proved.

**C2 (negative direction).** Seeded search `wip/c2_lstar.py` (the round 1 run 2 checker with
`AX = {∗ : ∗}`, `RULES = {(∗,∗,∗)}`), seeded with small material and with β-redex domains
`(λy:∗. y) ∗` in contexts and abstractions.  The Hurkens material of `Start/PTSHurkens.lean` was
not exported (no S-expression printer for it this run).
* bounds: reducts breadth-first to depth 3 on terms of size ≤ 400 plus 40 leftmost-outermost steps; time limit 120 s;
* run: 336 seed judgements tried, 311 typed;
* result: 0 bounded candidates (not Lean-checked; no claim either way).

## Series V, round 2, run 2

### Part A: kind variables in the skeleton model (rows M29-EP-TOP-SORT-FUNDAMENTAL, M29-EP-TOP-MORPHISM, M29-EP-CCOMEGA)

**A1 design (`Start/PTSExpansionTopSkel.lean`, builds, standard axioms only).**
* Skeletons get variables: `SkV ::= ∗ | arrO k | arr a k | svar i`, classes `ClsV`, and skeleton
  substitution `SkV.ssubst θ`, `ClsV.ssubst θ`.  Candidate spaces are taken relative to a closed
  skeleton valuation `θ : Nat → CoC.Sk` (`VV θ`, with `VV θ (svar i) = CoC.V (θ i)`).
* Observation that fixes the shape: in `cocTop` no rule has `s₁ = Δ` (`cocTop.rule` requires
  `s₁ ≠ top`), and `□ : Δ`, so **no binder binds a kind variable**: kind variables `K : □` occur only
  in the context.  So a skeleton variable can be the de Bruijn *level* of its declaration
  (`ctxClV`: `K : □` gets class `kind (svar ℓ)`), stable under weakening and untouched by binders;
  no skeleton binders are needed.  (This is exactly what fails for `CC^ω`, see A3.)
* Classifier `clV` (as `CoC.cl`, with `□` and `Δ` unclassified) and the commutation lemmas:
  `bindV_ssubst`, `domV_ssubst`, `lamV_ssubst`, `piV_ssubst` hold unconditionally;
  `appV_ssubst` needs the head not to be a constructor of variable skeleton, and
  `appV_ssubst_fails` shows the side condition is necessary.
* `clV_ssubst θ M Δ (h : WCV Δ M) : clV (ClsV.ssubst θ ∘ Δ) M = (clV Δ M).ssubst θ` — the new case of
  `cl_subst` (substituting a kind `N` for `K` agrees with assigning `N`'s skeleton to `K`'s skeleton
  variable), on well-classified expressions (`WCV`: no application whose head has class
  `constr (svar i)`); `clV_ssubst_fails` is the counterexample without `WCV` (`x ∗` with `x : K`,
  `K := ∗ → ∗`).

**Stop rule (first failing case of the generalized `cl_subst`).**  The application case `F U` with
`clV Δ F = constr (svar i)`: goal `appV ((constr (svar i)).ssubst θ) = (appV (constr (svar i))).ssubst θ`,
i.e. `constr k = obj` when `θ i = arr a k` — false.  The missing equation is supplied by typing: the
head of an application has a product type, and a kind variable is convertible only to itself, so
`clV F = constr (svar i)` cannot occur at an application head of a well-typed expression.  First
missing lemma:

```lean
theorem TopSkel.classifyV {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T) :
    WCV (ctxClV Γ) M ∧ ∀ k, clV (ctxClV Γ) M = .constr k → clV (ctxClV Γ) T = .kind k
```

(the `cocTop` analogue of `CoC.classify` with `kind_conv`; then `interpK`/`SemC` over `VV θ`, and
the MorphFund cases).  `cl_beta`, `interpK_conv` and regularity were not reached.

**A2** (`sortFundamental_of_topMorphism`, `expansionPostponement_of_topMorphism`,
`cocTop_expansionPostponement`) is not proved; no new instance was added.

**A3 (plan for `CC^ω`, not started in Lean).**  In `CC^ω` the rules `(Type i, Type j, Type (max i j))`
allow binders over kinds (`Π K : Type 0. …`), so kind variables are bound inside terms and the
level trick of A1 does not apply.  Iterating A1 over the levels needs skeletons with *binders*
(skeleton-level polymorphism: `SkV` with `Π`-skeletons over skeleton variables, one layer per level
`Type n`) and candidate spaces indexed by skeleton environments, i.e. a Λ-set/realizability-style
model.  First lemma toward `ccOmega_stronglyNormalizing` (statement only):
`theorem CCO.clV_ssubst_level (n : ℕ) : ∀ θ M Δ, WCVₙ Δ M → clVₙ (ssubst θ ∘ Δ) M = (clVₙ Δ M).ssubst θ`
for the classifier of level-`n` kinds with skeleton binders (definitions to be designed).

### Part C: λ* (row M29-EP)

**C1 (Python, `wip/c1_subst.py`, not Lean-checked).**  Instances of `lambdaStar_substR_expand`:
contexts `[]`, `[∗]`; declared types `C''` among five β-redexes with `C` their contractum;
bodies `e` (all terms of size ≤ 7) with an R-type `E` under `C'' :: Γ`; arguments `a` (size ≤ 7)
with R-type exactly `C`; check that `e[a/x]` has an R-type joinable (bounded reducts, DEPTH 3,
CAP 400) with `E[a/x]`.
* bounds: size ≤ 7, ≤ 2 types per body, ≤ 6 arguments per (context, redex);
* run: 9954 typed bodies, 44742 instances;
* result: 0 failures.  (A first run with a wrong contractum for one redex produced 224 spurious
  failures; corrected by computing `C` as the leftmost-outermost contractum.)

**C2 (analysis; no Lean proof).**  Induction on the `⊢r`-derivation of `e`, generalizing `C''` to a
context reducing to the one used for `a`: the variable case uses `C'' →* C`; the application case
closes by confluence (the type of the argument and the domain of the head's product have a common
reduct, and `HasTypeR.reduction` needs no typing premise); the **abstraction case does not close**:
from the IH `body[a] : B'` with `B[a] →* B'` one needs `Π A[a] B' : s`, while only `Π A[a] B[a] : s`
is available.  That is sorted subject reduction for `⊢r` on a product codomain — the λ* instance
of the expansion-postponement target itself.  First missing lemma:

```lean
theorem lambdaStar_pi_codomain_reduce {Γ : List (Expr Unit)} {A B B' : Expr Unit} {s : Unit}
    (h : HasTypeR lambdaStar Γ (.pi A B) (.sort s)) (hB : Relation.ReflTransGen Beta B B') :
    HasTypeR lambdaStar Γ (.pi A B') (.sort s)
```

No counterexample to `lambdaStar_substR_expand` was found.

**C3 (Hurkens).**  `wip/hurkens_sexp.lean` prints `Hurkens.hurkens` (sorts collapsed to `∗`,
i.e. read in λ*) as an S-expression (`wip/hurkens.sexp`, size 2905).  The checker types it
`Π A:∗. A` in both systems.  Seeded C1 (`wip/c3_hurkens.py`): `C'' = (λy:∗. y) (Π A:∗. A)`,
`a = Hurkens`, bodies of size ≤ 5: 54 typed bodies, 54 instances, 1 reported failure, which is a
bound artifact: for `e = λz:(x ∗). x`, the target `Π (H ∗). (Π A:∗. A)` is a one-step reduct of
`E[H/x]` and an R-type of `e[H/x]` (both checked by `wip/c3_check_fail.py`), but the bounded reduct search follows the
non-terminating reduction of `H` first.  No counterexample candidate.

## Series V, round 3, run 1

### B1: `classifyV` (`Start/PTSExpansionTopClassify.lean`, `Start/PTSExpansionTopClassifyV.lean`)

* Structural: `clV_rename`, `WCV_rename`, `clV_subst`, `clV_instantiate`, `WCV_subst`,
  `WCV_instantiate`, `ctxClV_comp_succ`, `ctxClV_cons_of_ne` (at a declaration `A ≠ □` the context
  classifier is the `ncons`-extension), `ctxClV_cons_box`.
* `cocTop` facts: `top_untypable`, `not_conv_top`, `not_beta_box`, `eq_box_of_conv` (a typable
  expression convertible to `□` is `□`; by head induction on the reduction to `□`: a typable redex
  never contracts to `□`, since `λx:A. □` and `(λx:A. x) □` would need a type convertible to `Δ`).
* `cocTop_functional`, `sort_unique_conv` (via `HasType.type_unique_of_functional`).
* `kindV_cl` (kinds are kinds; a kind variable has class `kind (svar ℓ)`), `notKindV` (an expression
  with a type of sort `∗` or `□` is not a kind; a variable of class `kind` has declared type `□`),
  `kindV_beta`, `kindV_reduces`, `kindV_conv` (a kind variable is convertible only to itself),
  `classifyFull` (`clV M = bindV (clV T)` for `T ∉ {□, Δ}`), `wcv_of_hasType`, and
  `theorem TopSkel.classifyV {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T) :
  WCV (ctxClV Γ) M ∧ ∀ k, clV (ctxClV Γ) M = .constr k → clV (ctxClV Γ) T = .kind k`.
* `clV_beta`, `clV_reduces` (the analogue of `CoC.cl_beta`).

### B2: not reached in Lean

The interpretation of kinds and constructors over `VV θ` (the analogue of `CoC.interp` with
`interp (svar i) := θ i`-valued candidates), its invariance under β (`interp_beta`), `SemC` relative
to `θ`, and the cases of `MorphFund` were not started.  First missing lemma:
`TopSkel.interpV_beta` (the analogue of `CoC.interp_beta` for the interpretation relative to a
closed skeleton valuation `θ`).  The stop rule ("first case of the generalized fundamental lemma
that fails") is not reached: the generalized fundamental lemma is not yet stated, since it is
phrased in terms of `interpV`.  `sortFundamental_of_topMorphism`,
`expansionPostponement_of_topMorphism`, `cocTop_expansionPostponement` are not proved; no new
instance.

### B3: not reached (B2 did not close).

## Series V, round 3, run 2

### A1: the interpretation relative to a skeleton valuation (`Start/PTSExpansionTopInterpV.lean`, `Start/PTSExpansionTopInterpVBeta.lean`)

* `evalSk θ`, `evalCls θ` evaluate skeleton variables; `evalCls` commutes with `bindV`, `domV`,
  `lamV`, `piV`, and with `appV` away from constructors of variable skeleton.
* `interpV 𝔄 θ Δ M := ErasureCoC.interpK 𝔄 (evalCls θ ∘ Δ) (M.mapSort srtC)` (`srtC`: `∗ ↦ ∗`,
  `□, Δ ↦ □`).  The dependency of `VV θ` on `θ` is resolved by evaluating the class first: a kind
  variable of class `kind (svar ℓ)` ranges over `V B (θ ℓ)`.
* `cl_toC`: on well-classified expressions the coc classifier of the image is the evaluated `clV`.
* `interpV_rename`, `interpV_subst` (any substitution respecting the evaluated classes; source and
  target valuations `θ'`, `θ` may differ), `interpV_instantiate`.
* The kind-variable case: `interpV_kindVar_cond` — for a well-classified `N` of class `kind a`, the
  side condition of `interpV_subst` at a variable of class `kind (svar ℓ)` is exactly
  `θ' ℓ = evalSk θ a` (`θ'` extends `θ` by the skeleton of `N`); `interpV_subst_kind`.
* `wc_toC`: the coc image of a `cocTop`-typable expression is well classified (`CoC.WC`) in the
  evaluated context classifier (from `classifyFull`, `kindV_cl`, `wcv_of_hasType`).
* `interpV_beta`, `interpV_reduces`, `interpV_conv` (the proof of `ErasureCoC.interpK_beta`, with
  `cl_toC_beta` from `clV_beta` and `evalCtx_cons` at declarations `A ≠ □`).

### A2: the fundamental lemma (`Start/PTSRouteIITopFundamental.lean`)

`TopFund.SemC θ Γ ξ Δ T X Y` tests whether the image `T.mapSort srtC` is `□` (i.e. `T ∈ {□, Δ}`)
and otherwise membership in the candidate `interpK (candAlg P) (evalCls θ ∘ ctxClV Γ) …`.  The
generalized fundamental lemma `TopFund.fundamental (m : TopMorphism P) (θ) : HasType P Γ M T →
SubstOK m θ Γ Δ σ ξ → Sem m θ Γ ξ Δ M T σ` closes in every case; the stop rule is not triggered.
New points against `MorphFund`: admissibility `tyOK_of_sorted` holds for every sort (a type of sort
`Δ` is `□`, by `not_top_typed`); the rule sorts are never `Δ` (`rule_map`), which gives the
declarations `A ≠ □` needed for `evalCtx_cons`; the conversion case splits on whether the target
type's image is `□`, and otherwise uses `interpV_conv` (both sides sorted by sorts other than `Δ`,
via `eq_box_of_conv`, `not_conv_top`).  Kind variables need no substitution agreement: no `cocTop`
binder binds a kind variable, and the semantics of `K : □` is normalization; `θ` is a free
parameter (`fun _ => ∗` in the final theorem).

* `theorem sortFundamental_of_topMorphism {S : Type} {P : Specification S} (m : TopMorphism P) :
  SNGeneric.SortFundamental P`
* `theorem expansionPostponement_of_topMorphism {S : Type} {P : Specification S} (m : TopMorphism
  P) : ExpansionPostponement P`
* `theorem cocTop_expansionPostponement : ExpansionPostponement cocTop`
* New instance `cocTopTwo` (sorts `∗, □, Δ, Δ'`; axioms `∗ : □`, `□ : Δ`, `□ : Δ'`; rules
  `(s₁, s₂, s₂)` with `s₁, s₂ ∈ {∗, □}`): `cocTopTwo_not_functional`, `cocTopTwo_not_cocMorphism`,
  `cocTopTwo_not_stratified`, `cocTopTwo_expansionPostponement`.

### A3: not started

A2 closed about 20 minutes into the run, with less than 20 minutes of A's share left, so by the
rule A3 was not started.  First lemma unchanged: `CCO.clV_ssubst_level`.

## Series V, round 4, run 1

Part B (row M29-EP-CCOMEGA), `Start/PTSExpansionCCOSkel.lean`, standard axioms only.

* B1.  Skeletons with level-indexed binders: `CCO.Sk ::= ∗ | arrO k | arr a k | svar n | all ℓ k`
  (de Bruijn skeleton variables, counted over the binders of kind variables only), with renaming,
  parallel substitution, instantiation and the σ-calculus laws (`Sk.rename_rename`,
  `Sk.ssubst_rename`, `Sk.rename_ssubst`, `Sk.ssubst_ssubst`, `Sk.ssubst_svar`,
  **`Sk.ssubst_inst`**).  Candidate spaces `CCO.V Λ L ρ k`, defined by well-founded recursion on
  `(L, k)`: `V (all ℓ k)` is a product over the closed skeletons of level `≤ ℓ`; a skeleton variable
  is interpreted by its closed value read at level `L - 1`.  Predicativity is what makes this
  recursion well founded.  No level-irrelevance lemma for `V` yet.
* B2.  The classifier `CCO.clO` with classes `univ ℓ` (the sort `Type ℓ`), `kind ℓ k`,
  `constr k`, `obj`; `Prop` is `kind 0 ∗`; a binder over `Type ℓ` declares a kind variable
  `kind ℓ (svar 0)` and shifts the skeleton variables of the context (`ext`); `lamO`, `piO`, `appO`
  (application of `constr (all ℓ k)` to a kind of skeleton `s` gives `constr (k.inst s)`), `WC`,
  `ctxClO`.

  ```
  theorem CCO.clV_ssubst_level (M : Expr CSrt) :
      ∀ (σ : ℕ → Sk) (Δ : ℕ → Cls), WC Δ M → clO (Cls.ssubst σ ∘ Δ) M = (clO Δ M).ssubst σ
  ```

  proved (under a binder over `Type ℓ` the substitution becomes `up σ`, `ext_ssubst`); the
  application case uses `Sk.ssubst_inst`.  `clV_ssubst_level_fails`: without `WC` it fails, as for
  `cocTop`.  The level discipline of `σ` is not needed for the equation, only for `V`.
* B3 stop.  The classifier is first-order in kinds.  `CC^ω` has kind-level functions (the rule
  `(Type 1, Type 1, Type 1)` types `λK : Type 0. K : Type 0 → Type 0`), which this classifier sends
  to `obj`.  `CCO.clO_beta_fails`: `(λK : Type 0. K) Prop` has class `obj`, its β-reduct `Prop` has
  class `kind 0 ∗`.  So the interpretation cannot be β-invariant on top of this classifier.
  First missing lemma: `CCO.clO_beta`, β-invariance of a level-generic classifier.  It needs classes
  for kind-level functions, that is, skeletons computed by a level-`(n + 1)` classifier.  The
  skeletons then become a stratified Fω-like calculus, one layer per `Type n`, and `V` has to
  interpret skeleton-level λ-terms up to β.  The interpretation and the generalized fundamental
  lemma are not started.

## Series V, round 4, run 2

Part B (row M29-EP-CCOMEGA), `Start/PTSExpansionCCOSkelFun.lean`, standard axioms only.

* B1, design.  Kind-level functions get classes in a stratified simply typed calculus of skeletons:
  skeleton types `SkTy ::= base ℓ | arr a b` (`base ℓ`: skeletons of kinds of level `ℓ`; `arr`:
  kind-level functions; `SkTy.lev (arr a b) = max (lev a + 1) (lev b)`), intrinsically typed
  skeleton terms `SkT Γ a` with variables, an opaque constant `cst ℓ` (the skeleton `∗` at level
  `ℓ`), `λ` and application; renaming, parallel substitution, `sub0` and the β-step `SkT.Step`
  (closed under all formers) with its closure `SkT.Steps`.
* B1, route.  Instead of normalizing skeleton terms by recursion on the level and classifying into
  normal skeletons, the classes are values in a set-theoretic model: `SkT.Sem D (base ℓ) = D ℓ`,
  `Sem D (arr a b) = Sem D a → Sem D b`, and `SkT.eval c t ρ` is defined by structural recursion on
  `t`, so it is total without any normalization theorem (the stratification is only needed later,
  for the predicative candidate spaces `V`).  This is shorter because the β-invariance of the
  classes then reduces to the substitution lemma of the model:

  ```
  theorem SkT.eval_subst {Γ Δ : List SkTy} {a : SkTy} (t : SkT Γ a) :
      ∀ (σ : Sub Γ Δ) (ρ : Env D Δ), eval c (subst σ t) ρ = eval c t (fun v => eval c (σ v) ρ)
  theorem SkT.eval_step {Γ : List SkTy} {a : SkTy} {t t' : SkT Γ a} (h : Step t t') :
      ∀ ρ : Env D Γ, eval c t ρ = eval c t' ρ
  theorem SkT.eval_steps … (h : Steps t t') (ρ : Env D Γ) : eval c t ρ = eval c t' ρ
  ```

  and `SkT.eval_idKind_beta` is the example of `CCO.clO_beta_fails` (the skeleton of
  `(λK : Type 0. K) Prop` and that of `Prop` have the same value).
* `CCO.clV_ssubst_level` (`Start/PTSExpansionCCOSkel.lean`) is untouched and still builds.
* Stop (first lemma of B1 that does not close; not stated in Lean).  The level-generic classifier
  of `CC^ω` expressions into `SkT` is not defined: it must assign to an expression `M` in a
  classifier context a skeleton type `a` and a term of `SkT Γ a` (a dependent, partial function
  of an untyped `Expr CSrt`), and the next statement is its compatibility with term substitution,
  `clF (M [N/0]) = (clF M) [clF N / 0]` for a kind-level argument `N` (`CCO.clF_subst`), from which
  `CCO.clO_beta` follows with `SkT.eval_step`.  Goal state (informal): for `M = (λK : Type ℓ. B) A`
  with `B` a kind, `eval (clF M) ρ = eval (clF (B [A/K])) ρ`, where the left side is
  `eval (clF B) (cons (eval (clF A) ρ) ρ)` by `eval_step`, and the missing step is
  `clF (B [A/K]) = subst (sub0 (clF A)) (clF B)`.
* B2 (V over values, level irrelevance, the interpretation, its β-invariance, the generalized
  fundamental lemma): not started.

## Series V, big round, run 2

Item B1 (row M29-EP-CCOMEGA).  Lean, `Start/PTSExpansionCCOClF.lean`, axioms in
`docs/goal/evidence/M29-EP-CCOMEGA-axioms.txt`:

* `ClfData C` — a class type `C` with the classes of `Prop` and `Type ℓ` and three combinators
  `appF`, `lamF`, `piF`; the binder combinators take the class of the body **as a function of the
  class of the bound variable** (`C → C`);
* `clF D ρ M` — the classifier of `Expr CSrt` relative to an environment `ρ : ℕ → C`, by
  structural recursion (`lam A b ↦ lamF (clF ρ A) (fun v => clF (envCons v ρ) b)`);
* `clF_rename`, **`clF_subst`** (`clF ρ (M.subst σ) = clF (fun n => clF ρ (σ n)) M`) and
  **`clF_instantiate`** (`clF ρ (b[A/0]) = clF (envCons (clF ρ A) ρ) b`): the level-generic
  `CCO.clF_subst`, in semantic form, for every choice of combinators;
* `clF_beta_of`, `clF_beta` — root β-invariance from the β-law `appF (lamF cA f) cU = f cU` of the
  combinators at the classes involved.

Design consequence.  With environment semantics the substitution lemma is free; all the content
moves into the class type.  A class type in which kind-level functions are semantic functions on
classes is not a Lean inductive (`C → C` occurs negatively), so it has to be stratified by level:
kinds of level `ℓ` take values in a predicative domain `SkL ℓ` whose binder `∀κ : ℓ'. k` (with
`ℓ' < ℓ`) is a function `SkL ℓ' → SkL ℓ` (positive once `SkL ℓ'` is fixed; the family is defined
by recursion on `ℓ`), and kind-level functions of skeleton type `a` take values in
`Sem a` over that domain.  This replaces the syntactic skeleton variables of `CCO.clO` (and the
shifting of `ext`) by values, as `CCO.V` already does with closed skeletons.

Stop (first missing lemma; B1 continues, ≈25 of 150 min used): the concrete class type and its
β-law on well-classified arguments,

```
def CCO.SkL : ℕ → Type        -- predicative semantic skeletons
def CCO.ccoClf : ClfData CCOCls
theorem CCO.ccoClf_beta {ρ : ℕ → CCOCls} {A b U : Expr CSrt} (h : ClfWC ρ (.app (.lam A b) U)) :
    clF ccoClf ρ (.app (.lam A b) U) = clF ccoClf ρ (b.instantiate U)
```

then the `classifyV` analogue (a typed expression is well classified, and the class of its type
determines its own).

## Series V, big round, run 3

Item B1 (the level-generic classifier for CC^ω) is **blocked**. It used about 35 of its 150
minutes.

- Lean, `Start/PTSExpansionCCOClFLimit.lean`: `ClfData.subsingleton_of_beta`. If the combinators
  satisfy the β-law `appF (lamF cA f) cU = f cU` for every class and every `f : C → C`, then `C`
  has at most one element (diagonal argument). Corollary: `ClfData.not_beta_of_ne`. The β-law of
  a CC^ω classifier can therefore only be asked on well-classified arguments, which is what
  `clF_beta_of` already allows.
- Obstruction to the concrete class type (design analysis, not Lean-checked). In CC^ω a kind can
  depend on the value of a constructor variable of the same level whose own type is a
  *dependent* product. An example is `ΠK : (ΠY : Type 0. Y → Type 0). ΠY : Type 0. Πy : Y. K Y y → K Y y`:
  the domain `ΠY : Type 0. Y → Type 0` and the product both live at `Type 1`, and the value
  space of `K` is the dependent `Π (y : U₀), El₀ y → U₀`. Domains like `Type 0 → Type 0`,
  whose value space is a simple type over lower universes, do not cause this. A faithful class
  domain must therefore contain, at level `ℓ`, dependent products
  `pi (a : U ℓ) (b : El ℓ a → U ℓ)` over the decodings of codes of the same level. That is a
  Tarski universe closed under dependent Π, i.e. an inductive-recursive definition.
  - The draft `CCO.SkL` (wip) quantifies only over strictly lower universes (`all ℓ' f`,
    `ℓ' < ℓ`), so it does not cover this case.
  - Any encoding without induction-recursion puts level `ℓ + 1` in a higher Lean universe than
    level `ℓ`, so it cannot be indexed uniformly by `ℓ : ℕ`.
- First missing lemma: a concrete `D : ClfData C` for CC^ω with
  `theorem CCO.ccoClf_beta (h : ClfWC ρ (.app (.lam A b) U)) : clF D ρ (.app (.lam A b) U) = clF D ρ (b.instantiate U)`.
  This needs a class type `C : Type` with dependent value spaces at each level, which Lean has
  no inductive-recursive definition for. A non-faithful (erasing) class type would need its own
  proof that the erasure commutes with β on kinds that depend on constructor values.
- Possible routes, both unverified: (a) a Lean-universe-polymorphic model, proving the
  fundamental lemma separately for each finite bound on the levels occurring in a derivation,
  with the bound as a parameter; (b) the normalization-based routes of item B4.

## Big round 2, run 2

Item B1 (lane B, slot D): **advanced**; the former first missing lemma `CCO.ccoClf_beta` is proved
for a concrete classifier. About 45 minutes used (of 200).

- Lean, `Start/PTSExpansionCCOCodes.lean`. The obstruction recorded in big round run 3 (a class
  type `C : Type` with dependent value spaces needs induction-recursion) is avoided by taking the
  class type to be `ZFSet` (one Lean universe, `Type 1`; `ClfData` is now universe-polymorphic).
  Dependent products over codes of the same level are then ordinary sets, built by replacement,
  and no inductive-recursive universe is needed:
  - `zfLam A f` (graph of `f` on `A`), `zfApp` (value of a graph), `zfPi A f` (dependent
    functions); `zfApp_zfLam` (the β-law on the domain), `mem_zfPi`, `zfLam_mem_zfPi`;
  - the hierarchy: `cU ℓ = V_(ω·(ℓ+1))` classifies `Type ℓ`, `cU_mem_succ : cU ℓ ∈ cU (ℓ+1)`,
    `cU_mono`; `propC = 𝒫 {∅}` classifies `Prop` (one fixed set, proof irrelevance),
    `propC_mem_cU : propC ∈ cU 0`;
  - `ccoD : ClfData ZFSet` and the well-classification predicate `ClfWC ρ M` (in every
    application the class of the argument is in the domain of the class of the function; binders
    are well classified at every class of their domain);
  - **`CCO.ccoClf_beta (h : ClfWC ρ (.app (.lam A b) U)) : clF ccoD ρ (.app (.lam A b) U) = clF ccoD ρ (b.instantiate U)`**;
  - `ClfWC_rename`, `ClfWC_subst`, `ClfWC_instantiate`, `ClfWC.beta` (a well-classified root
    redex has a well-classified contractum), `ClfWC.arg_mem`;
  - `zfApp_mem_zfPi` (application of a dependent function lands in the family);
    `depKind_wc`: the kind `ΠK : (ΠY : Type 0. Y → Type 0). ΠY : Type 0. Πy : Y. K Y y → K Y y`,
    whose value space blocked an inductive-recursive class type, is well classified in every
    environment;
  - `zfPi_mem_cU_zero`: `cU 0 = V_ω` is closed under dependent products over its members
    (hereditarily finite sets; `finite_of_mem_cU_zero`), i.e. the universe bound at level 0;
  - `zfPi_not_mem_propC`: with `piF = zfPi` the class of a product into `Prop` is not in the
    class of `Prop` (`zfPi {∅} (fun _ => {∅}) ∉ propC`), so the impredicative rule needs its own
    case of `piF`; this is a Lean-checked instance of the design note below.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` (see `M29-EP-CCOMEGA-axioms.txt`).
- What is not done, in order (design, not Lean-checked):
  1. The typed classification lemma: a typed expression is well classified and a constructor's
     class lies in the class of its type. Proof subterms must be erased first (classified by
     `∅`): with `propC = 𝒫 {∅}`, the class of a proposition may be `∅`, so a proof variable has
     no class in the class of its type, and `ClfWC` fails for proof applications. Applying the
     classifier to the constructor skeleton (proofs erased, as `clO` does) avoids this; `zfApp ∅ x = ∅`
     already holds.
  2. The universe bound `clF ρ K ∈ cU ℓ` for kinds `K : Type ℓ` (closure at level 0 is
     `zfPi_mem_cU_zero`). For `ℓ ≥ 1`, `V_(ω·(ℓ+1))` is not closed under
     dependent products indexed by arbitrary members (a family with ranks cofinal in `ω·(ℓ+1)`
     escapes), so the bound must go through the rank of the syntactic family:
     `rank (clF ρ M) ≤ max (ranks of ρ on the free variables) (ω·(top level of M + 1)) + c·size M`.
- First missing lemma (item B1, step 1):
  `theorem CCO.clF_typed {Γ : List (Expr CSrt)} {M A : Expr CSrt} (h : HasType ccOmega Γ M A) (ρ : ℕ → ZFSet) (hρ : CCO.EnvOK Γ ρ) : ClfWC ρ (CCO.erase Γ M) ∧ clF ccoD ρ (CCO.erase Γ M) ∈ clF ccoD ρ (CCO.erase Γ A)`
  (constructor case), with `CCO.erase` the proof-erasing skeleton and `CCO.EnvOK` the
  environment condition; both still to be defined.
- Design note for step 1 (not Lean-checked). Proof terms are the difficulty, as in the
  proof-irrelevant models of Miquel and Werner: (a) with `propC = 𝒫 {∅}` a proposition can be
  classified by `∅`, so an environment for a proof variable may not exist; (b) giving every
  proposition the class `{∅}` (`propC = {{∅}}`) needs a special case of `piF` for products into
  `Prop` (`{∅}` when all values are `{∅}`) and of `lamF` (collapse to `∅` when all values are `∅`,
  which keeps `zfApp_zfLam` on the domain since `zfApp ∅ x = ∅`), but then `ClfWC` can no longer
  read the domain of a collapsed abstraction off its class, and `ccoClf_beta` needs the domain
  condition from the typing derivation, not from the classes. Both routes lead to a typed
  invariant (classes of arguments lie in the classes of their types), which is `CCO.clF_typed`.

## Big round 2, run 7 (restoration after the export of run 6)

The platform's export of run 6's project dropped this note; it was put back from its copy at the end of run 3; it already contains the big round 2 sections of runs 1 to 3. The axioms files of the big round 2 rows
were regenerated with `#print axioms` in run 7 (section "Big round 2, run 7").
