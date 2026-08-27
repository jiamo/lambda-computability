# M9-SYSTEM-F

**Status:** DONE_STRONG

Modules `Start/SystemF.lean`, `Start/SystemFSubst.lean`, `Start/SystemFSR.lean`,
`Start/SystemFChurch.lean`, `Start/SystemFC.lean`, `Start/SystemFCSR.lean`,
`Start/SystemFCSubst.lean`, `Start/SystemFCConfluence.lean` and `Start/SystemFParam.lean`, all
imported by `Start.lean`.  They build
without `sorry` and without linter warnings, and the headline theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`.

The development continues the typed ladder of the project: `Start/SimpleTypes.lean` types the
untyped terms of `Start/Syntax.lean` with simple types and proves strong normalization by Tait's
method; System F is the next rung, where the reducibility predicate can no longer be defined by
recursion on the type and Girard's *reducibility candidates* are needed.

The calculus is presented in **Curry style** (type assignment): the terms are exactly the untyped
terms of the development and reduction is the ordinary β-reduction of `Start/Reduction.lean`, so
every statement below is a statement about the untyped calculus.

## Syntax and typing (first exit criterion)

`Start/SystemF.lean`:

* `SystemF.FTy` — types: `var i`, `arrow A B`, `all A`, with de Bruijn indices for type variables;
* `SystemF.tyRename`, `SystemF.tySubst`, `SystemF.tyShift`, `SystemF.tyInst` — the substitution
  calculus of types;
* `SystemF.Typing Γ t A` — the five rules: variable, application, abstraction, generalization
  (`tlam`, whose premise weakens the whole context by a fresh type variable) and instantiation
  (`tapp`).

## Reducibility candidates and strong normalization (second exit criterion)

* `SystemF.Cand` — a reducibility candidate: CR1 (members are strongly normalizing), CR2 (closed
  under reduction), CR3 (a non-abstraction all of whose reducts are members is a member).  `SN`
  and `NotAbs` are reused from `Start/SimpleTypes.lean`.
* `SystemF.interp A ρ` — the interpretation of a type in a valuation `ρ : ℕ → Cand`; the arrow is
  interpreted by the usual function-space condition and `all A` by the **intersection over all
  candidates**, `∀ K : Cand, interp A (K :: ρ) t`.  Impredicativity is exactly this quantification
  of a `Prop` over the type of candidates.
* `SystemF.interp_cr`, `SystemF.candOf` — the interpretation of every type is itself a candidate,
  by induction on the type.
* `SystemF.interp_tyRename`, `SystemF.interp_tyShift`, `SystemF.interp_tySubst`,
  `SystemF.interp_tyInst` — the semantic renaming, weakening and substitution lemmas, which are
  what make the two quantifier rules sound.
* `SystemF.interp_lam` — the abstraction lemma, proved by the double induction on the strong
  normalization of the body and of the argument.
* `SystemF.interp_substEnv` — the fundamental lemma: a typable term is reducible under every
  reducible parallel substitution.
* **`SystemF.sn_of_typing`** — *every typable term is strongly normalizing*.

## Subject reduction (third exit criterion)

`Start/SystemFSubst.lean` proves the syntactic laws that the semantic argument did not need:

* the composition and cancellation laws `tyRename_tyRename`, `tySubst_tyRename`,
  `tyRename_tySubst`, `tySubst_tySubst`, `tySubst_var_id`, `tySubst_tyCons_tyShift`,
  `tyInst_tyShift`, `tySubst_tyInst`;
* `SystemF.Typing.substTy` — a derivation may be substituted in its **type** variables, and
  `SystemF.Typing.shiftTy` — the weakening by a fresh type variable;
* `SystemF.Typing.lift_gen`, `SystemF.Typing.lift_one` — weakening in the **term** variables;
* `SystemF.Typing.substEnv`, `SystemF.Typing.subst_zero` — substitution of term variables.

`Start/SystemFSR.lean` closes the classical difficulty of the Curry-style presentation: the two
quantifier rules leave the term unchanged, so a derivation of `Γ ⊢ λx. s : A → B` need not end
with the abstraction rule.  The generation lemma is therefore proved with two auxiliary notions:

* `SystemF.AllArrow` — the type of an abstraction is an arrow under its quantifiers
  (`SystemF.allArrow_of_lam`);
* `SystemF.Peel σ T A B` — "instantiating the leading quantifiers of `T` and then substituting `σ`
  gives `A → B`", with `SystemF.peel_tySubst` for composites;
* **`SystemF.Typing.gen_lam`** — the generation lemma, and
* **`SystemF.Typing.preservation`** — subject reduction, with `preservation_reduces` for many
  steps.

## Non-vacuity and consequences (fourth exit criterion)

* `SystemF.typing_I` — the identity has type `∀ α. α → α`;
* `SystemF.typing_selfApp` — **self-application `λx. x x` is typable**, at
  `(∀ α. α → α) → (∀ α. α → α)`, while `SystemF.not_simple_typing_selfApp` shows it is *not*
  typable in the simply typed calculus: System F types strictly more terms;
* `SystemF.not_typing_omega` — `omega` is still untypable, so the untyped calculus is strictly
  larger than System F;
* `Start/SystemFChurch.lean`: `SystemF.natTy` and `SystemF.typing_church` — every Church numeral
  has the polymorphic type `∀ α. (α → α) → α → α`, and `SystemF.typing_succ` — the successor has
  type `nat → nat`, its derivation instantiating the quantifier of its argument;
* `SystemF.hasNormalForm_of_typing` and `SystemF.exists_unique_normal_form` — a typable term has a
  normal form, and (with the confluence theorem of `Start/Reduction.lean`) exactly one.

## The Church-style presentation (fifth exit criterion)

`Start/SystemFC.lean` gives the usual annotated presentation and derives its strong normalization
from the Curry-style theorem:

* `SystemFC.FTm` — terms with an annotation on every abstraction and with `Λ` and instantiation as
  term formers, their term-variable substitution (mirroring `Lambda.lift` and `Lambda.subst`, and
  shifting the type variables of the substituted term when entering a `Λ`) and their
  type-variable substitution;
* `SystemFC.step` — β together with type-β and all the congruences, and `SystemFC.TypingC` — the
  typing rules;
* `SystemFC.typing_erase` — the erasure of a typable term is typable in the Curry-style system at
  the same type;
* `SystemFC.step_erase` — the simulation: a step either erases to a β-step of the untyped
  calculus, or leaves the erasure unchanged and destroys one `Λ` (substituting a type into a term
  creates none, `SystemFC.tlamCount_substTyTm`);
* `SystemFC.snc_of_sn_erase` — the lexicographic combination of the two measures, and
* **`SystemFC.sn_of_typingC`** — *strong normalization for Church-style System F*.

`Start/SystemFCSR.lean` adds the typing lemmas the erasure argument does not need — weakening
(`SystemFC.TypingC.lift_gen`), substitution of the type variables (`SystemFC.TypingC.substTy`) and
of a term variable (`SystemFC.TypingC.subst_gen`, `subst_zero`) — and concludes with
**`SystemFC.TypingC.preservation`**: both β and type-β preserve typing.  Typing is syntax directed
in this presentation, so the generation step is a plain inversion.

## Confluence of the annotated reduction (sixth exit criterion)

`Start/SystemFCSubst.lean` proves the substitution calculus of the annotated terms — how the two
substitutions (`SystemFC.subst` for term variables, `SystemFC.substTyTm` for the type variables of
the annotations) commute with each other and with lifting:

* `SystemFC.substTyTm_substTyTm`, `SystemFC.substTyTm_var_id`, `SystemFC.substTyTm_shiftTyTm`,
  `SystemFC.instTyTm_shiftTyTm` — composition and cancellation for type substitution on terms;
* `SystemFC.substTyTm_lift`, `SystemFC.substTyTm_subst` — a type substitution passes through a
  lifting and through a term substitution;
* `SystemFC.lift_lift`, `SystemFC.lift_subst`, `SystemFC.lift_subst_lo`,
  `SystemFC.lift_subst_zero`, `SystemFC.subst_lift`, `SystemFC.subst_subst`,
  `SystemFC.subst_subst_zero` — the term-variable calculus, the annotated counterpart of the laws
  of `Start/Syntax.lean`;
* `SystemFC.instTyTm_subst`, `SystemFC.subst_instTyTm`, `SystemFC.substTyTm_instTyTm` — the three
  equations the type-β rule needs.

`Start/SystemFCConfluence.lean` then redoes the Tait–Martin-Löf argument of `Start/Reduction.lean`
for a calculus with two redexes:

* `SystemFC.pstep` — parallel reduction, contracting any set of β- and type-β-redexes at once,
  with `SystemFC.pstep_lift`, `SystemFC.pstep_substTyTm` and `SystemFC.pstep_subst`;
* `SystemFC.rho` — the full development, `SystemFC.pstep_rho` and `SystemFC.pstep_triangle`: every
  parallel reduct of a term parallel-reduces to its full development, whence
  `SystemFC.pstep_diamond`;
* `SystemFC.reducesC` — the reflexive-transitive closure of `SystemFC.step` with its congruences,
  `SystemFC.reducesC_of_pstep` and `SystemFC.strip_lemma`;
* **`SystemFC.confluence`** — *Church-Rosser for the annotated calculus*, for arbitrary terms,
  typable or not, and
* **`SystemFC.exists_unique_normal_form`** — a typable annotated term has exactly one normal form,
  by confluence together with `SystemFC.sn_of_typingC`.

## Parametricity and free theorems (seventh exit criterion)

`Start/SystemFParam.lean` interprets a type by a *binary relation* on terms instead of a unary
predicate, the quantifier ranging over all admissible relations:

* `SystemF.Rel` — an admissible relation: a binary relation on terms closed under β-conversion
  (`Lambda.Conv` of `Start/Scott.lean`) in each argument.  Nothing stronger is needed; in
  particular no normalization is used in this file;
* `SystemF.rinterp` — the relational interpretation, with `SystemF.rinterp_conv` (it is again
  conversion-closed), `SystemF.relOf`, and the semantic weakening and substitution lemmas
  `SystemF.rinterp_tyRename`, `SystemF.rinterp_tyShift`, `SystemF.rinterp_tySubst`,
  `SystemF.rinterp_tyInst`;
* **`SystemF.parametricity`** — *Reynolds' abstraction theorem*: a typable term relates to itself
  in the interpretation of its type, under any pair of related substitutions, with
  `SystemF.parametricity_closed` for closed terms;
* **`SystemF.conv_app_of_typing_idTy`** — the free theorem for `∀ α. α → α`: a closed term of that
  type applied to any `v` is convertible to `v`, whence `SystemF.conv_app_of_typing_idTy'`: any
  two closed terms of that type agree at every argument.  `SystemF.conv_app_I` records that the
  hypothesis is satisfiable;
* **`SystemF.conv_iterate_of_typing_natTy`** — the free theorem for `∀ α. (α → α) → α → α`: with
  `SystemF.graphRel`, the graph of a term as a relation, a closed term of that type commutes with
  any `h` intertwining `f` and `g`, so it can only iterate its first argument;
  `SystemF.conv_iterate_church` instantiates it at the Church numerals.

## Boundary

What is not claimed here: no characterization of the functions representable in System F (the
provably total functions of second-order arithmetic), and no converse to parametricity — the
relational interpretation is not shown to be complete for observational equivalence, and no
initial-algebra ("every closed term of `natTy` is a Church numeral") result is proved.
