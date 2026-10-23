# M25-TYPECLASS-COHERENCE — coherence of the dictionary elaboration (round 4, partial)

Lean: `Start/TypeClassCoherence.lean`, on the calculus of `Start/TypeClassElab.lean`
(row M25-TYPECLASS-DICT).  β-conversion is the repository's `Lambda.Conv` (`Start/Scott.lean`).

## E1. The β-law of records

```lean
theorem TypeClass.recProj_recMk (ds : List Lambda) (j : ℕ) (hj : j < ds.length) :
    Lambda.reduces (recProj ds.length j (recMk ds)) (ds[j])
```

Supporting lemmas: `appsL_lams_const` (a constant function of `k` arguments returns its body),
`appsL_lams_var` (selection `(λx₁⋯xₖ. xᵢ) t₁⋯tₖ ↠ t_{k−1−i}`), `subst_appsL`, `subst_lams`.

## E2. Entailment elaboration as a relation; uniqueness in the fragment

`TypeClass.DEnt E P n C d` — `d` is a dictionary for `C` built from a hypothesis (`Lambda.var
(n + i)`), a superclass projection (`recProj … 0 dd`) or an instance applied to dictionaries
for its context.  `DEnt.typing`: every such `d` has type `dictTyC E C`.

`TypeClass.Fragment E P` — the fragment without superclasses (`no_super`) and without overlapping
instances (`no_overlap`: two instance heads that match one constraint come from the same instance,
whose context is then determined), with hypotheses not matched by an instance head
(`hyp_rigid`) and without duplicates (`nodup`).

```lean
theorem TypeClass.DEnt.unique {E : Env} {P : List Cstr} {n : ℕ} (hF : Fragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : d = d'
theorem TypeClass.DEnt.conv {E : Env} {P : List Cstr} {n : ℕ} (hF : Fragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d'
```

So in the fragment, **any two dictionaries for one constraint are β-convertible** (indeed equal).

## E3. Coherence for annotated source terms

`TypeClass.ASexp` — source terms whose applications carry the argument type and whose method
occurrences carry the instance type; `TypeClass.AElab E P Γ e τ t` — elaboration as a relation
(methods through `DEnt`).  `AElab.typing`: elaborations are well typed (`tctx E P Γ`).

```lean
theorem TypeClass.AElab.coherent {E : Env} {P : List Cstr} (hF : Fragment E P) {Γ Γ' : List Mty}
    {e : ASexp} {τ τ' : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t) (h' : AElab E P Γ' e τ' t')
    (hlen : Γ.length = Γ'.length) : t = t'
theorem TypeClass.AElab.conv {E : Env} {P : List Cstr} (hF : Fragment E P) {Γ : List Mty}
    {e : ASexp} {τ : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t) (h' : AElab E P Γ e τ t') :
    Lambda.Conv t t'
```

## Open

1. **Unannotated source terms** (`Sexp`, `STyping`).  A source typing judgement `Γ ⊢ e : τ` does
   not fix the types at which the methods inside `e` are used (a method whose signature does not
   mention the class variable, or a method inside an argument whose type does not occur in `τ`),
   so two derivations can choose dictionaries at different types; with distinct instances those
   dictionaries are distinct normal forms, hence not β-convertible.  This counterexample is
   informal (not formalized).  The faithful statement therefore needs either annotations (done,
   E3) or an ambiguity check on the source judgement.  First missing lemma: an erasure
   `ASexp → Sexp` with `STyping E P Γ (erase a) τ ↔ ∃ annotations, AElab …`, plus the
   unambiguity condition under which two annotations of one judgement agree.
2. **Superclasses.**  With superclasses, a dictionary for `Eq τ` can be built directly or as the
   superclass projection of `Ord τ`; the two agree only up to β, through `recProj_recMk` and the
   superclass field of the instance dictionary.  First missing lemma: for an instance `I` of `c`
   with superclass `d`, `recProj … 0 (dict of I at s) ↠ (the DEnt dictionary of ⟨d, s(head)⟩)`,
   which needs the instance-environment condition that the superclass field of `I.dict` is itself
   elaborated by `DEnt`.

Row status: TODO_READY (partial).  Axioms: `M25-TYPECLASS-COHERENCE-axioms.txt`, at most
`[propext, Classical.choice, Quot.sound]`.

## Round 5 — unannotated judgements and superclasses

Modules: `Start/TypeClassUnannotated.lean`, `Start/TypeClassSuper.lean`
(`lake build --wfail`; axioms in `M25-TYPECLASS-COHERENCE-axioms.txt`).

### E4. Erasure

* `TypeClass.erase : ASexp → Sexp`; `TypeClass.DEnt.ent` and `TypeClass.Ent.dent` (dictionary
  entailment and entailment agree);
* `TypeClass.AElab.styping : AElab E P Γ a τ t → STyping E P Γ (erase a) τ` and
  `TypeClass.STyping.annotate : STyping E P Γ e τ → ∃ a t, erase a = e ∧ AElab E P Γ a τ t`.
  So the elaborations of an unannotated judgement are `ElabS E P Γ e τ t := ∃ a, erase a = e ∧
  AElab E P Γ a τ t`.

### E5. The unambiguity condition and coherence

* `TypeClass.Bidi E b Γ e τ` — bidirectional discipline: variables and applications synthesise,
  abstractions and methods are checked, and a method is only checked against `inst0 σ m` with `m`
  mentioning the class variable (`HasVar m`, so `σ` is determined: `inst0_inj`).  This is the
  analogue of Haskell's ambiguity check.
* `TypeClass.Bidi.annot_unique` — under the condition a judgement has at most one annotation.
* **`TypeClass.coherence_unannotated`** `(hF : Fragment E P) (hB : Bidi E false Γ e τ)
  (hS : STyping E P Γ e τ) : (∃ t, ElabS E P Γ e τ t) ∧ ∀ t t', ElabS E P Γ e τ t →
  ElabS E P Γ e τ t' → t = t'`, and `coherence_unannotated_conv` (β-convertible).
* **`TypeClass.ambiguous_not_coherent`** — the condition is needed: one class with the method
  `base → base → base` (no class variable), instances at `base` and `base → base` whose dictionaries
  hold `λx y. x` and `λx y. y`; the environment is in the coherent fragment, the judgement
  `⊢ m₀ : base → base → base` is derivable, and it has two elaborations that are not β-convertible.

### E6. Superclasses

* `Lambda.substEnv_substEnv` (composition of parallel substitutions), `SystemF.Typing.freeBelow`;
* `TypeClass.DEnt.subst` — dictionary elaboration is stable under instantiating the hypotheses of
  an instance context;
* `TypeClass.SuperField E I` — the instance dictionary is a record whose first field is a
  dictionary for the superclass at the instance head, elaborated from the instance context;
* **`TypeClass.super_coherent`** — for such an instance, the superclass projection of an instance
  dictionary (itself a `DEnt` dictionary, by `sup` of `inst`) reduces to, and so is β-convertible
  to, a dictionary elaborated directly for the superclass constraint.

### Open (gap row M25-TYPECLASS-COHERENCE-SUPER)

The exit criterion, read literally ("any two elaborations of one source typing judgement are
equal up to β"), is **false** without an unambiguity condition (`ambiguous_not_coherent`); it is
proved for unambiguous judgements in the fragment without superclasses.  Remaining: one coherence
theorem for unambiguous judgements in a fragment **with** superclasses.  First missing lemma:
`DEnt.conv_super : SuperFragment E P → DEnt E P n C d → DEnt E P n C d' → Lambda.Conv d d'`
(uniqueness up to β of dictionaries when superclass projections are allowed, by induction on the
two derivations with `super_coherent` for the `sup`-of-`inst` against `inst` case, and a
"no hypothesis is entailed by superclass from a different route" condition on `P`).

## Round 6 — coherence with superclasses (`Start/TypeClassSuperCoh.lean`)

`lake build --wfail`; axioms `propext, Classical.choice, Quot.sound`
(`M25-TYPECLASS-COHERENCE-SUPER-axioms.txt`).

**The round-5 statement of `DEnt.conv_super` needs a condition on the hypotheses.**
`TypeClass.superClosure_not_coherent`: in the environment `supEnv` (classes `Eq`, `Ord <: Eq`,
`Num <: Eq`, no instances, `EnvGood`) with hypotheses `supHyps = [Ord α, Num α]`, the constraint
`Eq α` has the two dictionaries `recProj 1 0 (var 0)` (through `Ord α`) and `recProj 1 0 (var 1)`
(through `Num α`); they are distinct normal forms, hence not β-convertible.

**The fragment.** `TypeClass.SuperFragment E P`: `EnvOK E` (superclasses come earlier, so the
superclass relation `SupStep` is functional and strictly decreasing), no overlapping instances,
instances only for classes without a superclass, the superclass closures (`SupReach`) of distinct
hypotheses at one type are disjoint, and no class in the superclass closure of a hypothesis is an
instance of an instance head.  `TypeClass.superFragment_supEnv` shows it allows superclasses
(`supEnv` under the single hypothesis `Ord α`).

**Proved.** `TypeClass.DEnt.source` (a derivable constraint is an instance of a head or in the
closure of a hypothesis), `TypeClass.SupReach.total` (two classes reachable from one are
comparable), and

```lean
theorem TypeClass.DEnt.unique_super {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperFragment E P)
    {C : Cstr} {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : d = d'
theorem TypeClass.DEnt.conv_super {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperFragment E P)
    {C : Cstr} {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d'
theorem TypeClass.coherence_unannotated_super {E : Env} {P : List Cstr} (hF : SuperFragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) (hS : STyping E P Γ e τ) :
    (∃ t, ElabS E P Γ e τ t) ∧ ∀ t t', ElabS E P Γ e τ t → ElabS E P Γ e τ t' → t = t'
theorem TypeClass.coherence_unannotated_super_conv {E : Env} {P : List Cstr}
    (hF : SuperFragment E P) {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ)
    {t t' : Lambda} (h : ElabS E P Γ e τ t) (h' : ElabS E P Γ e τ t') : Lambda.Conv t t'
```

**Open (gap row M25-TYPECLASS-SUPER-INST).** Instances of classes that have a superclass.  Then a
dictionary for `d` can be the superclass projection of an instance dictionary, and
`super_coherent` reduces it to the instance's superclass field substituted by the context
dictionaries — a derivation that is not a sub-derivation.  First missing lemma:
`DEnt.normalize_super` (every dictionary derivation β-reduces to one without superclass
projections of instance dictionaries), which needs a termination order on instance contexts
(e.g. Paterson's conditions, which `EnvGood` does not impose).  So M25-TYPECLASS-COHERENCE-SUPER is
`DONE_WEAK` and M25-TYPECLASS-COHERENCE stays `DONE_WEAK`.

## Round 8 — normal dictionary derivations (`Start/TypeClassSuperNorm.lean`)

* `TypeClass.DEntN` — normal derivations (no superclass projection of an instance
  dictionary), `DEntN.toDEnt`, `DEntN.weaken_nil`, `DEntN.subst_closed`;
* `TypeClass.NormalSuperFields E` — **the termination condition, as a hypothesis on the
  environment**: every instance of a class with a superclass stores its superclass field as a
  closed normal derivation; `NormalSuperFields.superField` (it implies `SuperField`);
* `TypeClass.DEntN.supInst_contract` — under `NormalSuperFields`, a superclass projection of an
  instance dictionary reduces to a normal derivation of the superclass constraint, and creates
  no new redex.

`DEnt.normalize_super` itself is not proved.  Under `NormalSuperFields` the first missing lemma
is the congruence of β-reduction for parallel substitution,
`Lambda.reduces (Lambda.substEnv u t) (Lambda.substEnv u' t)` when each free `u k` reduces to
`u' k` (the instance case, after normalizing the context dictionaries).  Paterson's conditions
alone were not used: without closed superclass fields, substituting instance dictionaries for
hypotheses under a superclass projection creates new redexes, and the order must combine
Paterson's measure on instance contexts with the size of instance dictionaries.  Coherence for
environments with instances of subclasses is therefore not extended this round.

## Round 9 — normalization and coherence with instances of subclasses (`Start/TypeClassSuperNormalize.lean`)

M25-TYPECLASS-SUPER-INST moves to **DONE_WEAK** with the gap row M25-TYPECLASS-SUPER-FIELD;
M25-TYPECLASS-COHERENCE-SUPER and M25-TYPECLASS-COHERENCE stay DONE_WEAK.  Axioms in
`M25-TYPECLASS-SUPER-INST-axioms.txt`.

Proved:

* `Lambda.substEnv_reduces` (and `Lambda.substEnv_reduces_below`, for the free variables of `t`)
  — the congruence of β-reduction for parallel substitution, the round-8 first missing lemma;
* `DEntN.true_inv`, `reduces_recProj`;
* **`DEnt.normalize_super`** — under `EnvGood E` and `NormalSuperFields E`, every `DEnt`
  derivation reduces (its dictionary term) to a `DEntN` derivation;
* `SuperInstFragment E P` — the round-6 `SuperFragment` without `inst_no_super` (instances of
  classes with a superclass allowed); `SuperFragment.toSuperInst`,
  `SuperFragment.normalSuperFields` (in the round-6 fragment `NormalSuperFields` holds vacuously);
* `DEntN.source`, **`DEntN.unique`** — normal dictionaries are unique in the fragment;
* **`DEnt.conv_superInst`**, `AElab.conv_superInst`, **`coherence_unannotated_superInst`** — any two
  dictionaries for one constraint, and any two elaborations of one unambiguous judgement, are
  β-convertible, in `SuperInstFragment` under `NormalSuperFields`.

**Exit criteria.**  M25-TYPECLASS-SUPER-INST asks for coherence under `SuperField` (superclass
fields that are arbitrary derivations).  The proof uses `NormalSuperFields` (closed normal
superclass fields), which is stronger, so the row is DONE_WEAK.  Gap (row
M25-TYPECLASS-SUPER-FIELD): `DEnt.normalize_super` under `SuperField` alone, where the
superclass field of an instance may use the instance context, so that contracting a superclass
projection of an instance dictionary substitutes the context dictionaries into the field and can
create new projections of instance dictionaries; the termination order must combine Paterson's
measure on instance contexts with the size of the dictionaries.  No example environment with an
instance of a subclass satisfying `SuperInstFragment` and `NormalSuperFields` is built in Lean
this round.  M25-TYPECLASS-COHERENCE-SUPER's exit criterion (fragment without overlap, with
superclasses, instances well formed for their superclass) is the same `SuperField` condition, so
it also stays DONE_WEAK; M25-TYPECLASS-COHERENCE depends on it.

## Round 10 — non-vacuity, and the termination order under `SuperField`

Module `Start/TypeClassSuperExample.lean`.  M25-TYPECLASS-SUPER-INST stays DONE_WEAK,
M25-TYPECLASS-SUPER-FIELD stays TODO_READY.  Axioms appended to
`M25-TYPECLASS-SUPER-INST-axioms.txt`.

**E1 (proved).**  The example environment of `Start/TypeClassExample.lean` — `class Eq a`,
`class Eq a => Ord a`, `instance Eq Base`, `instance Eq b => Eq (a → b)` and `instance Ord Base`
whose superclass field is the `Eq Base` dictionary (`Base` in the role of `Int`) — satisfies
`EnvGood` (`exampleEnv_good`, round 6), **`NormalSuperFields`** (`exampleEnv_normalSuperFields`,
the field is the normal derivation `dentN_eqBase`) and **`SuperInstFragment`**
(`exampleEnv_superInstFragment`).  `example_superInst_coherence` applies
`coherence_unannotated_superInst` to the method `eq` at `Base`, whose constraint `Eq Base` is
entailed both by its instance and through the superclass of `Ord Base`: an elaboration exists and
any two are β-convertible.  So the hypotheses of the round-9 theorem are satisfiable by an
environment with an instance of a subclass.

**E2 (stop rule; analysis, not formalized).**  For `DEnt.normalize_super` under `SuperField`
alone, the first case where the order does not decrease is the superclass projection of an
instance, `sup (inst I ds)`.  Its contraction calls normalization on the field derivation `sd`
of `I` (a derivation of `⟨d, I.head⟩` from `I.ctxt`) with its hypotheses replaced by the context
derivations `ds`.  The constraint `⟨d, I.head[s]⟩` has the same type as the redex, so Paterson's
measure on instance contexts does not decrease; the derivation size does not decrease either (`sd`
may be larger than the instance node and may use a hypothesis several times, duplicating `ds`).
The size of the dictionary term does decrease at this step (`sd` is a strict subterm of `I.dict`),
but that measure fails at the `inst` case, whose recursive calls on context dictionaries not used
by `I.dict` are not subterms.  A working order needs a measure on derivations that is stable under
substitution of hypotheses (for instance a multiset of pairs of Paterson size and field depth).

## Series V, round 4, run 1

Part C2 (row M25-TYPECLASS-SUPER-FIELD), `Start/TypeClassSuperFieldExample.lean`, standard axioms
only.  The Lean example of the failure at `sup (inst I ds)`: `TypeClass.superEnv` has the classes
`Eq`, `Ord` and `Ord₂` (both subclasses of `Eq`) and an instance `Ord₂ Base` whose `Eq` field
`ord2Field` is the projection of the `Ord Base` dictionary.  `superEnv_superField :
SuperField superEnv instOrd2Base` holds; the field is the derivation `sup (inst OrdBase [])`, which
is not normal.  `superEnv_sup_inst_step`: the redex `sup (inst Ord₂Base [])` and its contractum
`sup (inst OrdBase [])` derive the same constraint `Eq Base`, and the contractum is again a
superclass projection of an instance dictionary.  So the Paterson size of the constraint does not
decrease at this step, and one contraction can create a new redex of the same kind.  The multiset
measure of (Paterson size, field depth) pairs is not formalized.  First missing lemma: its decrease
at `sup (inst I ds)` under `SuperField` (to be stated as `DEnt.superMeasure_lt`), then
`DEnt.normalize_super` under `SuperField`.

## Series V, round 4, run 2

Part C (row M25-TYPECLASS-SUPER-FIELD), `Start/TypeClassSuperFieldMeasure.lean`, standard axioms
only.

```
theorem TypeClass.DEnt.superMeasure_lt {E : Env} (hE : EnvGood E) {P : List Cstr} {n : ℕ} {I : Inst}
    (hSF : SuperField E I) {D : ClassDecl} {d : ℕ}
    (hc : E.classes[I.cls]? = some D) (hs : D.super = some d) {s : ℕ → Mty} {ds : List Lambda}
    (hds : ds.length = I.ctxt.length)
    (hall : ∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
      DEnt E P n ((I.ctxt[k]).subst s) (ds[k])) :
    ∃ sd, DEnt E P n ⟨d, msubst s I.head⟩ (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) ∧
      Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) ∧
      dsize (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) <
        dsize (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
          (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
```

The measure.  The multiset of (Paterson size, field depth) pairs was replaced by the size `dsize`
of the elaborated term: the Paterson size is constant at the step (`superEnv_sup_inst_step`), and
under `SuperField` the dictionary is a finite record `recMk (sd :: ms)`, so its field is strictly
smaller than the projection of the record, also after substituting the context dictionaries
(`dsize_lt_recMk`, `dsize_lift`, `Lambda.substEnv_recMk`).  The test case:
`superEnv_superMeasure : dsize ord2Field < dsize (recProj 2 0 ord2BaseDict) ∧
dsize ordBaseDict < dsize ord2BaseDict` (by `decide`).

Normalization under `SuperField` is false:

```
theorem TypeClass.normalize_super_superField_fails :
    ¬ ∀ (E : Env) (P : List Cstr), EnvGood E → SuperInstFragment E P →
      (∀ I ∈ E.insts, SuperField E I) →
      ∀ (n : ℕ) (C : Cstr) (d : Lambda), DEnt E P n C d →
        ∃ b d', DEntN E P n b C d' ∧ Lambda.reduces d d'
```

The witness `loopEnv` (`loopEnv_good`, `loopEnv_superInstFragment` with no hypotheses,
`loopEnv_superField`): classes `Eq`, `Ord <: Eq`;
`instance Eq Base => Eq Base` whose dictionary `eqBaseDict` ignores its context;
`instance Ord Base` with dictionary `recMk [eqBaseDict, cmp]`, whose `Eq` field is derived by
`inst EqLoop [sup (inst OrdLoop [])]` (the context argument does not occur in the term, so its
derivation may be a redex for the instance being defined).  `Eq Base` is derived by
`sup (inst OrdLoop [])`, but it has no normal derivation at all (`loopEnv_DEntN`: without
hypotheses every normal derivation in `loopEnv` is an instance node and none is at `Eq Base`).
Why induction fails in general: the contractum `substEnv ds' sd` is smaller than its redex
(`superMeasure_lt`), but the derivations of context arguments unused in the dictionary term are
not controlled by any term size.

Consequence for the row: `coherence_unannotated_superInst` with `SuperField` cannot be obtained
through `DEnt.normalize_super` and `DEntN.unique`; coherence itself is not refuted (in `loopEnv`
every dictionary for `Eq Base` reduces to `eqBaseDict`, and `loopEnv` has no overlap).  First
missing lemma for a different route: a uniqueness of dictionaries up to β-conversion that does not
go through normal derivations, e.g. `DEnt.conv_superField` (any two `DEnt` dictionaries for one
constraint are β-convertible in a `SuperInstFragment` whose instances satisfy `SuperField`).

## Series V, big round, run 3 (M25-TYPECLASS-SUPER-FIELD)

`Start/TypeClassSuperFieldHead.lean`: `DEntHyp` (superclass projection chains over a
hypothesis), `DEntH` (head forms: a chain, or `inst I ds` with context derivations),
`DEntHyp.toDEnt`, `DEntH.toDEnt`, and **`DEnt.headForm`**: if every instance satisfies
`SuperField`, every `DEnt` dictionary reduces to a head form for the same constraint, of no larger
`dsize`. Proof by strong induction on `dsize` with an inner induction on the derivation; at
`sup (inst I ds)` the contractum from `DEnt.superMeasure_lt` is strictly smaller.

Also `DEntHyp.unique` (two chains for one constraint are equal, via `DEntN.unique`) and
`DEntHyp.not_instHead` (no chain is for an instance head, via `closure_rigid`), so the head-form
comparison is reduced to the instance/instance case.

Still open: `DEnt.conv_superField`. Remaining case: two head forms for one constraint. Chains are
compared via `closure_unique`; a chain against an instance is impossible by `closure_rigid`; two
instances coincide by `no_overlap`, and then only the context arguments that occur free in
`I.dict` need to be compared (`Lambda.substEnv`). Obstacle: `dsize` does not strictly decrease
from `inst I ds` to an argument when `I.dict` is a variable, so the induction needs a second,
lexicographic measure, for example a derivation height on a `Type`-valued copy of `DEnt`.

## Series V, big round, run 4 (M25-TYPECLASS-SUPER-FIELD)

`Start/TypeClassSuperFieldCoh.lean` closes the row.

* `conv_substEnv_of_size`: congruence of `Lambda.substEnv` for convertibility guarded by size.
  If `Lambda.Conv (u k) (v k)` holds for every `k` with
  `dsize (u k) + dsize (v k) ≤ dsize (substEnv u t) + dsize (substEnv v t)`, then
  `Lambda.Conv (substEnv u t) (substEnv v t)`. Every argument that occurs free in `t` satisfies
  the size bound. Arguments that do not occur are never needed, so the derivations of unused
  context arguments (the obstruction in `loopEnv`) play no role.
* **`DEnt.conv_superField`**: let `EnvGood E` hold, let every instance satisfy `SuperField`, and
  let `SuperInstFragment E P` hold. Then any two `DEnt` dictionaries for one constraint are
  β-convertible.
* `AElab.conv_superField` follows, and so does **`coherence_unannotated_superField`**: this is
  `coherence_unannotated_superInst` with `NormalSuperFields` replaced by `SuperField`.
* `loopEnv_conv_eqBase` shows the theorem is not vacuous. It applies in `loopEnv`, where `Eq Base`
  has no normal derivation (`normalize_super_superField_fails`).

**Proof of `DEnt.conv_superField`.** The outer induction is strong induction on
`N ≥ dsize d + dsize d'`. Inside it, the inner induction is structural on the first derivation;
it supplies the second measure that run 3 asked for, without a `Type`-valued copy of `DEnt`. The
second dictionary is first brought to head form with `DEnt.headForm`. Then, by the shape of the
first derivation:

* **hyp:** `DEntHyp.unique` handles the case where the second head form is a chain;
  `DEntHyp.not_instHead` rules out an instance head form.
* **sup dd:** bring `dd` to head form.
  * If it is a chain, the case reduces to a chain against a head form, as above.
  * If it is `inst I ds`, `DEnt.superMeasure_lt` contracts the projection to a strictly smaller
    derivable term, and the outer induction applies.
* **inst I ds:** the second head form is `inst I ds'` with the same instance (`no_overlap`), and
  the contexts agree under the substitution. `conv_substEnv_of_size` reduces the goal to the
  arguments within the size bound. For each such `k` the inner induction hypothesis for the
  subderivation of `ds[k]` applies against the derivation of `ds'[k]`, within the same `N`.

Exit criterion met. The theorem holds in a fragment with no overlap, with superclasses and
instances well formed for their superclass (`SuperField`), under the closure conditions on the
hypotheses (`SuperInstFragment`). Under these assumptions, any two elaborations of one
unambiguous source judgement are β-convertible. Row M25-TYPECLASS-SUPER-FIELD is DONE_STRONG.
Its parent M25-TYPECLASS-SUPER-INST was DONE_WEAK only because of this gap; its exit criterion
(`SuperField` with the hypothesis closure condition) is now met by
`coherence_unannotated_superField`, so it is DONE_STRONG too.

## Series V, big round, delivery

The original exit criterion of row M25-TYPECLASS-COHERENCE was:

> "Without overlapping instances, any two elaborations of one source typing judgement are equal
> up to β (or βη) conversion."

It was restated because, read literally, it is false: `TypeClass.ambiguous_not_coherent` gives a
fragment with no overlapping instances and a source typing judgement with two elaborations that
are not convertible. The row could therefore never reach DONE_STRONG under the original wording,
and after big round run 4 its only gap row, M25-TYPECLASS-COHERENCE-SUPER, was DONE_STRONG, so the
row no longer depended on any open row (AGENTS.md requires a DONE_WEAK row to depend on one).

The restated criterion is: "Decide the claim: without overlapping instances, any two elaborations
of one source typing judgement are equal up to β (or βη) conversion. It is false in general
(TypeClass.ambiguous_not_coherent). For unambiguous judgements it holds in the fragments of
TypeClass.coherence_unannotated and TypeClass.coherence_unannotated_superField."

It is met by `TypeClass.ambiguous_not_coherent` (Start/TypeClassUnannotated.lean),
`TypeClass.coherence_unannotated` (Start/TypeClassUnannotated.lean) and
`TypeClass.coherence_unannotated_superField` (Start/TypeClassSuperFieldCoh.lean). `#print axioms`
for each of the three shows only `propext`, `Classical.choice` and `Quot.sound`. The row is
DONE_STRONG with an empty open boundary, and `TypeClass.coherence_unannotated_superField` is added
to its terminal statement.
