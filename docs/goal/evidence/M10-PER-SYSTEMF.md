# M10-PER-SYSTEMF

**Status:** DONE_STRONG

Modules `Start/PER.lean` and `Start/PERSystemF.lean`, imported by `Start.lean`.  They build without
`sorry`; `#print axioms` on the headline declarations reports only `propext`, `Classical.choice`,
`Quot.sound`.

## Partial equivalence relations — `Start/PER.lean`

`Realizability.PER A` over a partial combinatory algebra `A` is a symmetric, transitive relation on
`A`, with `ext` for extensionality, `dom` for its domain (`dom_left`, `dom_right`), `setoid` and
`Quot` for its quotient, and `cls`, `cls_eq_cls`, `quot_ind` for working with that quotient.

* **`PER.arrow`** with `arrow_apply` — the function-space PER: `r` and `r'` are related when they
  send related arguments to related results;
* **`PER.iInter`** with `iInter_rel` — closure under intersections of *arbitrary* families, in an
  arbitrary sort of indices; this is what makes an impredicative interpretation possible;
* `PER.top`, `PER.toAsm`, `modest_toAsm` — every PER is a modest assembly.

## The model of System F — `Start/PERSystemF.lean`

Over an arbitrary λ-model `M` (a PCA by `instPCACarrier`, with `app_eq` and `arrow_rel_iff`
computing the structure):

* `perCons` extends a PER environment; **`SystemF.Per.tyPer : FTy → (ℕ → PER M.Carrier) → PER
  M.Carrier`** interprets a System F type — a type variable by lookup, an arrow by `PER.arrow`, and
  `∀X. A` by `PER.iInter` over **all** PERs on the carrier, i.e. impredicatively;
* `tyPer_tyRename`, `tyPer_tyShift`, `tyPer_tySubst`, `tyPer_tyInst` — the interpretation is stable
  under type renaming, shifting, substitution and instantiation;
* `RelEnv Γ ρ σ σ'` says two term substitutions are pointwise related at the types of the context;
* **`SystemF.Per.sound`** — soundness: if `Typing Γ t A` then the λ-model interpretations of `t`
  under any two related substitutions are related in `tyPer A ρ`, for every PER environment `ρ`;
* `dom_interp_of_typing` — hence every closed well-typed term denotes an element of the domain of
  the PER interpreting its type;
* `dom_interp_idTy` — non-vacuity: the PER interpreting `∀X. X → X` is inhabited.

Together with the existing syntax, strong normalization and parametricity modules for System F,
this supplies the semantic model those modules lacked: System F is interpretable in the PER model
over any λ-model, and in particular over Kleene's first algebra via the assemblies development.

## Boundary

None for this task.  The PER interpretation is given directly rather than as a functor into a
packaged cartesian closed category of PERs; the connection to the relational parametricity modules
is not itself formalized here.
