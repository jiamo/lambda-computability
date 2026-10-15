# Levels, expansion postponement and syntax-directed typing for stratified PTSs

*A note for type theorists.  Every claim is proved in Lean 4 (only the axioms `propext`,
`Classical.choice`, `Quot.sound`); the Lean name is given in brackets.  Modules:
`Start/PTSExpansion.lean`, `Start/PTSExpansionLevels.lean`, `Start/PTSExpansionBeyondPoll.lean`,
`Start/PTSSyntaxDirected.lean`.*

## 1. Setting and definitions

A PTS is given by sorts `S`, axioms `A ⊆ S × S` and rules `R ⊆ S × S × S`; terms, contexts and the
typing relation `Γ ⊢ M : T` are the usual ones (rules ax, var, weakening, Π-formation,
abstraction, application, and conversion `Γ ⊢ M : A`, `Γ ⊢ B : s`, `A =β B ⟹ Γ ⊢ M : B`).  Terms
use de Bruijn indices.  `P` is *functional* if `A` and `R` are partial functions
(`(s,t),(s,t') ∈ A ⟹ t = t'`, `(s₁,s₂,s₃),(s₁,s₂,s₃') ∈ R ⟹ s₃ = s₃'`) [`Functional`].

**Stratification** [`Stratification`].  A level map `ℓ : S → {0,…,N}` such that
`(s,t) ∈ A ⟹ ℓ(t) = ℓ(s) + 1` and `(s₁,s₂,s₃) ∈ R ⟹ ℓ(s₃) = ℓ(s₂) ≤ ℓ(s₁)`.
So every axiom goes up exactly one level, and no product is dependent in the sense that its
codomain sort lies above its domain sort.  Examples: System U⁻ (`∗,□,△ ↦ 0,1,2`)
[`Hurkens.uMinus_stratified`] and System U; the cube corners `λ→, λ2, λω̲, λω`
[`cube_stratified`].  Non-examples: any system with an axiom `s : t` and a rule `(s,t,_)`, hence
`λP, λP2, λPω̲, λC` [`cube_not_stratified`], and `λ*` [`lambdaStar_not_stratified`].

**The reduction-only system `⊢r`** [`HasTypeR`]: the rules of `⊢` with conversion replaced by
`Γ ⊢r M : A`, `A →β B ⟹ Γ ⊢r M : B`.  **Expansion postponement** [`ExpansionPostponement`]:
`Γ ⊢ M : A ⟹ ∃B. A ↠β B ∧ Γ ⊢r M : B`.  Soundness `⊢r ⊆ ⊢` [`HasTypeR.toHasType`].  For every PTS,
EP is equivalent to weak subject reduction of `⊢r` at sorts [`expansionPostponement_iff_
sortedSubjectReductionR`]; this is a formal version of a remark of Poll (1998).

**Pollack's syntax-directed system `⊢sd`** [`HasTypeSD`] (Poll 1998, Definition 14), where
`Γ ⊢sd a :↠ A` means `Γ ⊢sd a : A'` with `A' ↠β A`, and `↠wh` is weak-head reduction [`WhReduces`]:
* `⊢sd s : t` for `(s,t) ∈ A`;
* `Γ ⊢sd A :↠ s ⟹ Γ, x:A ⊢sd x : A`;
* `Γ ⊢sd b : B`, `Γ ⊢sd A :↠ s`, `b` a variable or a sort `⟹ Γ, x:A ⊢sd b : B`;
* `Γ ⊢sd A :↠ s₁`, `Γ, x:A ⊢sd B :↠ s₂`, `(s₁,s₂,s₃) ∈ R ⟹ Γ ⊢sd Πx:A.B : s₃`;
* `Γ, x:A ⊢sd b : B`, `Γ ⊢sd Πx:A.B :↠ s ⟹ Γ ⊢sd λx:A.b : Πx:A.B`;
* `Γ ⊢sd b :↠wh Πx:A'.B`, `Γ ⊢sd a : A`, `A =β A' ⟹ Γ ⊢sd b a : B[x:=a]`.

`⊢sd ⊆ ⊢` [`HasTypeSD.toHasType`] (Poll's Theorem 15).

## 2. Theorems

**Theorem 1** [`expansionPostponement_of_stratification`].  Every stratified PTS has expansion
postponement.  No normalization hypothesis.

**Theorem 2** [`sd_complete_of_stratification`].  If `P` is functional and stratified, then
`Γ ⊢ M : A` implies `Γ ⊢sd M : A'` for some `A' =β A`.  No normalization hypothesis.
Corollaries: System U⁻ [`Hurkens.uMinus_sd_complete`], the cube corners without `(∗,□)`
[`cube_sd_complete`], and the system `W₀` of §4 [`BeyondPoll.W0_sd_complete`].

Auxiliary results used for Theorem 2:
* *Weak-head standardization to a product* [`Converts.whReduces_pi`]: `F =β Πx:A.B` implies
  `F ↠wh Πx:A'.B'` with `A' =β A`, `B' =β B`.  Proof: by confluence `F ↠ Πx:A₁.B₁` with
  `A ↠ A₁`, `B ↠ B₁`; by the standardization theorem [`Reduces.stdRed`], in the inductive form
  "weak-head reduce to a head shape, then reduce the components standardly" (Kashima, Loader),
  `F ↠wh Πx:A'.B'` with `A' ↠ A₁`, `B' ↠ B₁`.
* *Uniqueness of types* for functional `P` [`HasType.type_unique_of_functional`]:
  `Γ ⊢ M : T`, `Γ ⊢ M : T'` imply `T =β T'` (induction on `M` with generation).

## 3. Proofs

**Levels of types** [`Stratification.TypeLevel`].  Say `T` *has level* `k` in `Γ` if either
`T` is a sort `t` and `k = ℓ(t) + 1`, or `Γ ⊢ T : s` and `k = ℓ(s)`.  Thus the inhabitants of `T`
"live at level `k`", and `k ≤ N + 1`.

**Lemma A (uniqueness of levels)** [`Stratification.level_unique`, `Stratification.conv_level`].
If `Γ ⊢ M : T`, `Γ ⊢ M : T'`, `T` has level `k` and `T'` has level `k'`, then `k = k'`.  Hence
convertible types have the same level.
*The repair.*  A plain induction on derivations is circular: the conversion case needs "two
convertible types have the same level", i.e. uniqueness of levels for a common reduct `C` of the
two types, a term with an unrelated derivation.  The proof is therefore a *downward induction on
the level* (measure `N + 2 − k`) with an inner induction on `M`.  For types at level `k`, the
conversion step needs uniqueness for `C : s`, `C : s'` with `ℓ(s) = k`, a subject whose types are
at level `k + 1`: this is the outer hypothesis.  The other cases use generation and the inner
hypothesis on a subterm at the same level: in `Πx:A.B` the codomain `B` (level
`ℓ(s₂)+1 = ℓ(s₃)+1`), in `λx:A.b` the body (level `ℓ(s₂) = ℓ(s₃)`), in `f a` the head `f`.

**Core lemma for Theorem 1** [`Stratification.core`].  If `Γ` is valid for `⊢r` and `Γ ⊢ M : T`,
then `Γ ⊢r M : T'` for some `T ↠ T'`.
**Core lemma for Theorem 2** [`Stratification.sd_core`].  If `Γ` is valid for `⊢sd`
[`ValidContextSD`] and `Γ ⊢ M : T`, then `Γ ⊢sd M : T'` for some `T' =β T`.

Both are proved by well-founded induction on the pair `(N + 2 − k, M)` ordered
lexicographically, where `T` has level `k`.  The cases (for Theorem 2; Theorem 1 is the same with
`⊢r` and confluence in place of standardization):
* *Variable, sort.*  Read off the context: lookup through sd-variable and sd-weakening
  [`ValidContextSD.lookup`, `ValidContextSD.sort`].  No recursive call.
* *Product `Πx:A.B`*, by generation `Γ ⊢ A : s₁`, `Γ,x:A ⊢ B : s₂`, `(s₁,s₂,s₃) ∈ R`,
  `T =β s₃`.  Calls on the subterms `A` (level `ℓ(s₁)+1 ≥ ℓ(s₂)+1 = k`) and `B` (level `k`).  The
  types returned convert to `s₁`, `s₂`, hence reduce to them; the same rule applies.
* *Application `f a`*, by generation `Γ ⊢ f : Πx:D.E`, `Γ ⊢ a : D`, `T =β E[a]`.  Calls on `f`
  (level `ℓ(s₃) = k`) and on `a` (level `ℓ(s₁) ≥ ℓ(s₂) = k`; **here `ℓ(s₂) ≤ ℓ(s₁)` is used**).
  The call on `f` gives `F =β Πx:D.E`; standardization gives `F ↠wh Πx:A'.B'`; the call on `a`
  gives a type `=β D =β A'`; the result `B'[a] =β E[a] =β T`.
* *Abstraction `λx:A.b`*, by generation `Γ,x:A ⊢ b : B`, `Γ ⊢ Πx:A.B : s` with rule
  `(s₁,s₂,s)`, `T =β Πx:A.B`, so `k = ℓ(s)`.  Calls on `A` (giving validity of `Γ,x:A`) and on
  `b` (level `ℓ(s₂) = k`), which returns `B_sd =β B`.  Then `Γ,x:A ⊢ B_sd : s₂`: by soundness and
  correctness of types, either `B_sd` is a sort `t` (then `B ↠ t`, and `t : s₂` by subject
  reduction) or `Γ,x:A ⊢ B_sd : t'`, and uniqueness of types applied to a common reduct of `B_sd`
  and `B` gives `t' = s₂`.  **This is the only use of functionality**, matching Pollack's
  non-functional counterexample.  So `Γ ⊢ Πx:A.B_sd : s`, and the call on `Πx:A.B_sd` — the only
  subject that is not a subterm — is at level `ℓ(s) + 1 = k + 1`, so the first component of the
  measure decreases.  Conclude by sd-abstraction.  (For Theorem 1 the body is typed at a reduct
  `B'` of `B`, and `Γ ⊢ Πx:A.B' : s` follows from subject reduction for `⊢`.)

Validity of contexts for `⊢r` and `⊢sd` follows from the core lemma by induction on the context
[`Stratification.validContextR`, `Stratification.validContextSD`]; correctness of types supplies a
level for `T`.

## 4. The witnesses `W` and `W₀`

`W` [`BeyondPoll.W`] is U⁻ moved up one level with an extra bottom sort: sorts `o, t, t', k, u`
at levels `0, 1, 1, 2, 3`, axioms `o : t`, `o : t'`, `t : k`, `k : u`, rules `(o,o,o)`, `(t,t,t)`,
`(k,t,t)`, `(k,k,k)`, `(u,k,k)`.  `W₀` [`BeyondPoll.W0`] is `W` without `t'` (and without `o : t'`).
* Both are stratified [`W_stratified`, `W0_stratified`].  `W` is not functional
  [`W_not_functional`]; `W₀` is functional [`W0_functional`].
* Hurkens' paradox, moved up one level, gives a closed `L : Πx:t. x` [`W_hurkens_typed`,
  `W0_hurkens_typed`], so neither system is weakly normalizing [`W_not_wn`, `W0_not_wn`].
* No closed normal term has type `o` [`W_closed_normal_not_o`, `W0_closed_normal_not_o`]: no sort
  is typed by `o`, a closed neutral term is untypable, a λ is never typed by a sort, and a product
  of type `o` needs `(o,o,o)`, whose domain is again a closed normal term of type `o`.  Hence the
  closed type `L o : o` has no normal form [`W_type_not_wn`, `W0_type_not_wn`]: both systems lie
  outside Poll's hypothesis of normalising types.
* `W` has expansion postponement [`W_expansionPostponement`]; `W₀` has a complete
  syntax-directed system [`W0_sd_complete`, `W0_in_class`].

## 5. What is not known

* **Poll (1998)** proves EP for PTSs with normalising types; we did not have the full text and rely
  on the summaries in our instructions.  His Open Problem 16 (completeness of `⊢sd` for functional
  PTSs) is, as stated there, open in general; Theorem 2 settles only the stratified case.
* **Van Benthem Jutting, McKinna and Pollack (1993)** treat normalizing functional and semi-full
  PTSs; exactly which algorithm their completeness theorem covers (Pollack's `⊢sd` or a modified
  one) we could not check.
* **Barthe (1999)** and **Song (1997)**: we know only the abstracts.  Barthe treats a variant of
  injective PTSs with a variant algorithm; U⁻ and `W₀` may be injective in his sense, so his
  results may overlap with Theorems 1–2 for these systems; we cannot tell whether they imply
  either theorem.  `W` is not functional, so it is outside any class of injective systems that
  includes functionality.  Song gives conditions for EP that we do not know.
* **Folklore.**  We do not know whether the level argument (induction on the level of the type,
  with the abstraction case going one level up) is folklore or appears in the literature.  We
  make no novelty claim.
* The dependent case (rules with `ℓ(s₂) > ℓ(s₁)`, e.g. `λP`, `λC`, or `W` plus `(o,t,t)`) is not
  settled: there the application case calls on the argument at a lower level, and the measure
  fails.
