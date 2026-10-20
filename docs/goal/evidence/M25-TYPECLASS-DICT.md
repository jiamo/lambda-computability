# M25-TYPECLASS-DICT — type classes by dictionary passing

Status: **DONE_STRONG** (E1–E3). E4 (coherence) is open: gap row `M25-TYPECLASS-COHERENCE`.

Modules: `Start/TypeClassDict.lean` (records, monotypes, classes, instances, dictionary types),
`Start/TypeClassElab.lean` (entailment, source typing, elaboration), `Start/TypeClassExample.lean`
(a concrete environment). Target: Curry-style System F, `SystemF.Typing` of `Start/SystemF.lean`.

## Records in System F

Church-style products: `recTy [A₀,…,Aₙ₋₁] = ∀R. (A₀ → ⋯ → Aₙ₋₁ → R) → R` (`recTy`), the record
`recMk ts = Λ λk. k t₀ ⋯ tₙ₋₁` (`recMk`) and the projection `recProj n j d = d (λx₀…xₙ₋₁. xⱼ)`
(`recProj`, `sel`), with `typing_recMk`, `typing_sel` and `typing_recProj`.

## The source calculus

* Monotypes `Mty` (`base`, `var i`, `arrow`), substitution `msubst`, translation `mtyF : Mty → FTy`
  with `mtyF_msubst`.
* A constraint `Cstr = ⟨cls, ty⟩` stands for `C τ`.
* `ClassDecl = ⟨super : Option ℕ, methods : List Mty⟩`: at most one superclass, and method
  signatures in the class variable `var 0`.
* `Inst = ⟨cls, head, ctxt, dict⟩`: `instance ctxt ⇒ cls head`, for example
  `instance Eq b ⇒ Eq (a → b)`. The instance carries its System F dictionary `dict`. This is a
  simplification: the methods are given as System F terms, not as source expressions.
* The dictionary type `dictTy E c τ = recTy (superclass dictionary at τ :: method types at τ)`
  (`dictFields`, defined with fuel in `dictTyF` and unfolded by `dictTy_eq`). It is stable under
  substitution: `dictTy_msubst`, `dictTyC_subst`.
* `EnvOK`: superclasses point to earlier classes, and method signatures mention only `var 0`.
  `EnvGood` adds that every instance dictionary is typed, in the dictionary types of its
  context, at the dictionary type of its head.
* Entailment `Ent E P C` has three rules: a hypothesis in `P`; a superclass of an entailed
  constraint; an instance whose substituted context is entailed.
* Source typing `STyping E P Γ e τ`: var, lam, app, and `method c j` at `m[τ/var 0]` whenever
  `Ent E P ⟨c, τ⟩`.
* Qualified types `∀ᾱ. C₁τ₁ ⇒ ⋯ ⇒ τ` appear at the top level of a program, as the constraint
  context `P` (`elab_program`).

## Results

```lean
theorem ent_dict {E : Env} {P : List Cstr} {C : Cstr} (hE : EnvGood E) (h : Ent E P C) :
    ∀ Δ : List FTy, ∃ d, Typing (Δ ++ P.map (dictTyC E)) d (dictTyC E C)            -- E2
theorem elab_typing {E : Env} {P : List Cstr} {Γ : List Mty} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P Γ e τ) : ∃ t, Typing (tctx E P Γ) t (mtyF τ)  -- E1
theorem elab_sn {E : Env} {P : List Cstr} {Γ : List Mty} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P Γ e τ) :
    ∃ t, Typing (tctx E P Γ) t (mtyF τ) ∧ Lambda.SN t                              -- E3
theorem elab_program {E : Env} {P : List Cstr} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P [] e τ) (K : ℕ) :
    ∃ t, Typing [] t
      (HM.allN K ((P.map (dictTyC E)).foldl (fun B X => FTy.arrow X B) (mtyF τ))) ∧
      Lambda.SN t
```

Here `tctx E P Γ = Γ.map mtyF ++ P.map (dictTyC E)`: the term variables come first, then one
dictionary variable for each constraint of `P`. The dictionary built by `ent_dict` is a variable
for a hypothesis, a projection `recProj _ 0` for a superclass, and, for an instance, the instance
dictionary with the context dictionaries substituted in (`Lambda.substEnv`, via
`Typing.substTy`/`Typing.substEnv`). Elaborating a method is the projection of field
`methodIdx D j` from the dictionary of its constraint.

## Example (`Start/TypeClassExample.lean`)

`class Eq a where eq : a → a → a`, `class Eq a ⇒ Ord a where cmp : a → a → a`, `instance Eq Base`,
`instance Eq b ⇒ Eq (a → b)`, `instance Ord Base`.
`exampleEnv_good : EnvGood exampleEnv`; `ent_eq_arrow` (the instance with a context);
`ent_eq_of_ord` (the superclass); `example_elab` (`λx. eq x x` at `(Base→Base)→(Base→Base)`
elaborates to a strongly normalizing System F term).

## Gap: E4, coherence (row M25-TYPECLASS-COHERENCE)

Not proved. The first missing pieces:
(1) elaboration as a relation or a function on derivations, since `elab_typing` is an
existential;
(2) for the fragment without overlapping instances, uniqueness of entailment derivations of a
constraint up to superclass paths;
(3) the β-law `recProj n i (recMk ds) →β* ds[i]`, which identifies a superclass projection of an
instance dictionary with the directly built dictionary.

## Axioms

`M25-TYPECLASS-DICT-axioms.txt`: at most `[propext, Classical.choice, Quot.sound]`.
