# M29-SD-COMPLETE — Completeness of Pollack's syntax-directed type checking for stratified functional PTSs

Module: `Start/PTSSyntaxDirected.lean` (new).  Registered in `Start.lean` and
`Start/Capstones.lean`.  No existing module was edited apart from those two (imports and `#check`
lines); `Start/PTSBasic.lean`, `Start/PTSExpansion.lean`, `Start/PTSExpansionLevels.lean` and all
existing statements are unchanged.  No axiom was added.

## Definitions (as given; one change of form)

```lean
/-- Weak-head β-step: contracts the head redex of an application spine. -/
inductive WhBeta {S : Type u} : Expr S → Expr S → Prop
  | head (A b a : Expr S) : WhBeta (.app (.lam A b) a) (b.instantiate a)
  | app_left {f f' a : Expr S} : WhBeta f f' → WhBeta (.app f a) (.app f' a)

def WhReduces {S : Type u} : Expr S → Expr S → Prop := Relation.ReflTransGen WhBeta

def Functional {S : Type u} (P : Specification S) : Prop :=
  (∀ s t t', P.axioms s t → P.axioms s t' → t = t') ∧
  (∀ s₁ s₂ s₃ s₃', P.rule s₁ s₂ s₃ → P.rule s₁ s₂ s₃' → s₃ = s₃')

/-- Pollack's syntax-directed system (Pollack 1992; Poll 1998, Definition 14). -/
inductive HasTypeSD {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeSD P ([]) (.sort s) (.sort t)
  | var {Γ A T s} : HasTypeSD P Γ A T → Reduces T (.sort s) →
      HasTypeSD P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken_var {Γ n B A T s} : HasTypeSD P Γ (.var n) B → HasTypeSD P Γ A T →
      Reduces T (.sort s) → HasTypeSD P (A :: Γ) (.var (n + 1)) (B.rename Nat.succ)
  | weaken_sort {Γ t B A T s} : HasTypeSD P Γ (.sort t) B → HasTypeSD P Γ A T →
      Reduces T (.sort s) → HasTypeSD P (A :: Γ) (.sort t) (B.rename Nat.succ)
  | product {Γ A B TA TB s₁ s₂ s₃} : HasTypeSD P Γ A TA → Reduces TA (.sort s₁) →
      HasTypeSD P (A :: Γ) B TB → Reduces TB (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeSD P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B T s} : HasTypeSD P (A :: Γ) b B →
      HasTypeSD P Γ (.pi A B) T → Reduces T (.sort s) →
      HasTypeSD P Γ (.lam A b) (.pi A B)
  | application {Γ f a F A' B A} : HasTypeSD P Γ f F → WhReduces F (.pi A' B) →
      HasTypeSD P Γ a A → Converts A A' → HasTypeSD P Γ (.app f a) (B.instantiate a)
```

**Change of form (syntax only):** the empty context in `ax` (and in `ValidContextSD.nil`) is
written `([])` instead of `[]`.  With the library's imports, `HasTypeSD P []` does not parse
(`[]` after an identifier is read as an index-notation bracket); the rest of the library writes
`([])` for the same reason (e.g. `Start/PTSExpansionBeyondPoll.lean`).  The meaning is identical.
Everything else is character-for-character the text of the instruction.

Against Poll's Definition 14: sd-axiom is `ax`; sd-variable is `var` (the premise
`Γ ⊢sd A :↠ s` is `HasTypeSD P Γ A T ∧ T ↠ s`); sd-weakening with `b ∈ Var ∪ S` is split into
`weaken_var` and `weaken_sort` (in de Bruijn form the variable `n` of `Γ` becomes `n + 1`);
sd-formation is `product`; sd-abstraction is `abstraction`; sd-application is `application`, with
`Γ ⊢sd b :↠wh Πx:A'.B` as `HasTypeSD P Γ f F ∧ WhReduces F (.pi A' B)`.

## Theorems

```lean
theorem HasTypeSD.toHasType (h : HasTypeSD P Γ M A) : HasType P Γ M A     -- Poll's Theorem 15

theorem Converts.whReduces_pi {F A B : Expr S} (h : Converts F (.pi A B)) :
    ∃ A' B', WhReduces F (.pi A' B') ∧ Converts A' A ∧ Converts B' B       -- step 1

theorem HasType.type_unique_of_functional (hf : Functional P)
    (hT : HasType P Γ M T) (hT' : HasType P Γ M T') : Converts T T'      -- step 2

theorem Stratification.sd_core (hf : Functional P) (L : Stratification P)
    (hΓ : ValidContextSD P Γ) (h : HasType P Γ M T) :
    ∃ T', HasTypeSD P Γ M T' ∧ Converts T' T                              -- step 4

theorem sd_complete_of_stratification {S : Type u} {P : Specification S}
    (hf : Functional P) (L : Stratification P) {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) : ∃ A', HasTypeSD P Γ M A' ∧ Converts A' A
```

Corollaries (step 5):

```lean
theorem Hurkens.uMinus_sd_complete (h : HasType uMinus Γ M A) :
    ∃ A', HasTypeSD uMinus Γ M A' ∧ Converts A' A
theorem cube_sd_complete (f : CubeFeatures) (hd : f.dep = false)
    (h : HasType (cubeSpec f) Γ M A) : ∃ A', HasTypeSD (cubeSpec f) Γ M A' ∧ Converts A' A
theorem BeyondPoll.W0_functional : Functional W0
def     BeyondPoll.W0_stratified : Stratification W0
theorem BeyondPoll.W0_type_not_wn : HasType W0 ([]) typeA0 (.sort .o) ∧ ¬ WeaklyNormalizing typeA0
theorem BeyondPoll.W0_not_wn : ¬ SystemWeaklyNormalizing W0
theorem BeyondPoll.W0_in_class : Functional W0 ∧ Nonempty (Stratification W0) ∧
    ∃ T s, HasType W0 ([]) T (.sort s) ∧ ¬ WeaklyNormalizing T
theorem BeyondPoll.W0_sd_complete (h : HasType W0 Γ M A) :
    ∃ A', HasTypeSD W0 Γ M A' ∧ Converts A' A
```

`W0` has sorts `o, t, k, u` (a new inductive `W0Sort`), axioms `o : t`, `t : k`, `k : u`, rules
`(o,o,o)`, `(t,t,t)`, `(k,t,t)`, `(k,k,k)`, `(u,k,k)`: exactly `W` without `t'` and the axiom
`o : t'`.  `typeA0 := L o` with `L` Hurkens' term moved up one level (`hurkensW0`).  The proofs
are those of `W`, repeated for the new sort type.

`#print axioms` for every theorem above (and `Reduces.stdRed`, `Reduces.whReduces_pi`,
`W0_hurkens_typed`, `W0_closed_normal_not_o`, `uMinus_functional`, `cube_functional`): only
`propext`, `Classical.choice`, `Quot.sound` or a subset; exact output in
`docs/goal/evidence/M29-SD-COMPLETE-axioms.txt`.

## The proof, against the sketch

**Step 1 (weak-head standardization).**  Done by confluence and a standardization theorem, as
suggested, but not by Takahashi's parallel-reduction factorization: the library's `Parallel`
relation is not reused.  Instead `StdRed` is the inductive *standard reduction* relation
(weak-head reduce to a head shape `x`, `s`, `P Q`, `λA.b`, `ΠA.B`, then reduce the components
standardly; the formulation of Kashima's and Loader's proofs of the standardization theorem).
Lemmas: `StdRed.refl`, `StdRed.wh_prefix` (a weak-head prefix can be absorbed),
`StdRed.rename`, `StdRed.subst` (pointwise standard substitutions), `StdRed.beta` (a standard
reduction followed by one β-step is standard; the head-redex case uses `StdRed.subst`), hence
`Reduces.stdRed : Reduces M N → StdRed M N`.  Inverting `StdRed F (Π A₁ B₁)` gives
`Reduces.whReduces_pi`, and with `Converts.join` and `Reduces.pi_inv`, `Converts.whReduces_pi`.

**Step 2 (uniqueness of types).**  Induction on the subject, as `CoC.type_unique`, with
`Functional` in place of the cube's functionality.  The product case needs both domain and
codomain sorts equal (`sort_inj` of the two induction hypotheses), then rule functionality.

**Step 3 (contexts).**  `ValidContextSD` (cons: `Γ ⊢sd A : T`, `T ↠ s`), with
`ValidContextSD.lookup` (by `var` and `weaken_var`) and `ValidContextSD.sort` (by `ax` and
`weaken_sort`); `Stratification.validContextSD : ValidContext P Γ → ValidContextSD P Γ` by
induction on the context with the core lemma, as `Stratification.validContextR`.

**Step 4 (core lemma).**  `sd_core_aux`: outer induction on `n ≥ bound + 2 − k`, inner structural
induction on `M`, where `L.TypeLevel Γ T k` (the convention of `core_aux`; the sketch's
`bound + 3` is `bound + 2` here because `TypeLevel` of a sort `t` is `level t + 1`).  The level
facts (`conv_level`, `rule_level`) are reused from `Start/PTSExpansionLevels.lean`.
* `var`, `sort`: from `ValidContextSD`; no recursive call.
* `pi A B`: calls on `A` and on `B` (in `A :: Γ`).  The returned types convert to the
  generation sorts `s₁`, `s₂`, so they *reduce* to them (`Converts.reduces_sort`); no
  `sort_inj` step is needed, the generation rule `(s₁,s₂,s₃)` applies directly.
* `app f a`: as sketched.  The call on `f` gives `F =β Π D E`; step 1 gives `F ↠wh Π A' B'`
  with `A' =β D`, `B' =β E`; the call on `a` gives `Aₐ =β D =β A'`; result type
  `B'[a] =β E[a] =β T`.  Levels as in `core_aux`.
* `lam A b`: as sketched.  Call on `A` (gives `ValidContextSD (A :: Γ)`), call on `b` (gives
  `B_sd =β B`).  Then `A :: Γ ⊢ B_sd : s₂`: by soundness and `regularity`, `B_sd` is a sort `t`
  (then `B ↠ t`, so `A :: Γ ⊢ t : s₂` by `subject_reduces`) or `A :: Γ ⊢ B_sd : t'`; in the
  second case uniqueness of types on a common reduct of `B_sd` and `B` gives `t' = s₂`.  So
  `Γ ⊢ Π A B_sd : s` by the product rule, and the call one level up on `Π A B_sd` gives the
  abstraction premise.  **Functionality is used only here** (the only use of
  `type_unique_of_functional`, and `hf` is used nowhere else in the core lemma).

**Which case needed repair:** none.  The deviations are of form only: standardization by
`StdRed` instead of Takahashi's factorization, and in the product case `reduces_sort` directly
instead of `reduces_sort` followed by `sort_inj`.

## Literature

* **Poll (1998), Open Problem 16** (as given in the instruction; we did not have the text):
  completeness of `⊢sd` for functional PTSs is open; Pollack (1992) gives a counterexample for a
  non-functional PTS; since `⊢sd ⊆ ⊢r`, expansion postponement is necessary.  Our proof uses
  functionality exactly once, in the abstraction case, to identify the sort of the
  syntax-directed body type with the sort of the declared body type, which is where a
  non-functional system can fail.
* **Pollack (1992)**, "Typechecking in pure type systems": introduces `⊢sd`, proves it sound
  (Poll's Theorem 15 is our `HasTypeSD.toHasType`), and gives the non-functional counterexample.
  We do not know the paper's text beyond what Poll reports.
* **van Benthem Jutting, McKinna, Pollack (1993)**, "Checking algorithms for pure type systems",
  LNCS 806.  As far as we know (not checked against the text): they treat *normalizing*
  functional PTSs and semi-full PTSs; for semi-full systems they use a modified algorithm whose
  abstraction rule avoids retyping `Πx:A.B` (it computes the sort of `B` and checks a rule), and
  their completeness results for functional systems assume normalization (and, for `⊢sd` itself,
  a property amounting to expansion postponement).  Which algorithm their completeness theorem
  covers exactly — `⊢sd` or the modified one — we cannot confirm without the text.  None of this
  covers non-normalizing systems such as U⁻ or `W0`.
* **Poll (1998)**: proves expansion postponement for PTSs with normalising types; as far as we
  know this, combined with van Benthem Jutting–McKinna–Pollack, gives completeness of `⊢sd` for
  normalizing functional PTSs, leaving the general functional case (Open Problem 16) open.
* **Barthe (1999)**, "Type-checking injective pure type systems", JFP 9(6).  We know only the
  abstract: a variant syntax-directed algorithm for (a variant of) injective PTSs, proved sound
  and complete, and expansion postponement for those systems.  As far as we can tell U⁻ and `W0`
  are injective in the usual sense (functional, axioms injective, rules `(s₁,s₂,s₂)`), so they may
  fall under Barthe's class; but his result concerns his variant algorithm, and we do not know
  whether it yields completeness of Pollack's `⊢sd` itself.

**Novelty.**  We do not claim the result is new.  What we can say: the theorem covers
non-normalizing systems (U⁻; `W0`, which has a well-typed type with no normal form), which the
normalization-based results above do not; whether Barthe (1999) or later work already implies
completeness of `⊢sd` for stratified functional PTSs we do not know.
