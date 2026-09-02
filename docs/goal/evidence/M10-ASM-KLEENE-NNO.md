# M10-ASM-KLEENE-NNO

**Status:** DONE_STRONG

Module `Start/AssemblyKleene.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and its results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this task adds

`Start/AssemblyNNO.lean` builds the natural numbers object of `Asm(A)` over an *arbitrary* partial
combinatory algebra, realized by the Church numerals.  Over Kleene's first algebra `K₁` of
`Start/PCAKleene.lean` there is a second, concrete numbers assembly, in which a number realizes
itself, and this module identifies it.

- `Realizability.Kleene.natK1`, `.modest_natK1` — the standard numbers assembly, `a` realizes `n`
  iff `a = n`; a realizer determines its element, so the assembly is modest.
- **`Realizability.Kleene.tracked_natK1_iff`** — *effective Church's thesis for `Asm(K₁)`*: a
  function `ℕ → ℕ` is tracked exactly when it is computable.  From a tracker `r` one reads
  `f n ∈ φ_r(n)`, and Turing application is partial recursive uniformly in `r`, so `f` is
  computable; conversely a code for `f` is a tracker, since Turing application of its index is
  evaluation of the code.
- `Realizability.Kleene.natK1EndEquiv` — hence the endomorphisms of the standard numbers assembly
  are in bijection with the computable functions.
- `Realizability.Kleene.diag`, `.not_tracked_diag`, `.exists_not_tracked_natK1` — the diagonal
  function `n ↦ φₙ(n) + 1` is not tracked, by the usual fixed-point argument on its own index.
  So the underlying-function map on `Asm(K₁)` is not surjective: `Asm(K₁)` is not the category of
  sets, and `Realizability.Kleene.not_full_gammaFunctor` states this as the failure of fullness of
  the global sections functor of `Start/AssemblyGlobalSections.lean`.
- `Realizability.Kleene.pairK1`, `.computable_pairEl`, `.natApp_fstComb_pairEl`,
  `.natApp_sndComb_pairEl`, **`.tracked_prod_natK1_iff`** — Church pairing and the two projection
  combinators of `K₁` are computable, so a function of *two* natural numbers is tracked out of the
  product of two copies of the standard numbers assembly exactly when it is computable.
- `Realizability.Kleene.realizes_expAsm_natK1`, `.expAsmNatK1Equiv` — reading off the exponential
  of `Start/AssemblyCcc.lean` at that object: the elements of the function object are the
  computable functions and its realizers are exactly the indices of the machines that compute
  them.
- `Realizability.Kleene.zeroK1`, `.succK1`, `.iterApp`, `.partrec_iterApp`, `.iterK1` — zero and
  successor, and the `n`-fold Turing application of a tracker to a base realizer, which is partial
  recursive by the closure of the partial recursive functions under primitive recursion, hence
  computed by a single element of `K₁`.
- **`Realizability.Kleene.isNNO_natK1`** — that element tracks the map defined by iteration, so
  the standard numbers assembly satisfies Lawvere's universal property; uniqueness of the iterate
  is proved by induction on the underlying function.
- `CategoryTheory.Limits.IsNNO.iter`, `.zero_comp_iter`, `.succ_comp_iter`, `.iter_unique`,
  **`.iso`** (in `Start/AssemblyNNO.lean`) — the general API of a natural numbers object, and the
  proof that two natural numbers objects over the same terminal object are isomorphic.
- `Realizability.Kleene.natK1IsoNatAsm` — consequently the standard numbers assembly is isomorphic
  to the Church numeral one in `Asm(K₁)`: numbers and Church numerals of `K₁` are effectively
  interconvertible.

## Gates

- `lake build Start.AssemblyKleene` — success, no warnings.
- `lake build` — the whole library still builds, with no error and no warning.
- `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
