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
