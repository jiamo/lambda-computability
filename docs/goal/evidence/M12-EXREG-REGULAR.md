# M12-EXREG-REGULAR — the exact completion of the assemblies is a regular category

`Start/AsmExRegCover.lean` and `Start/AsmExRegRegular.lean` identify the regular epimorphisms of
the exact completion built in `Start/AsmExReg.lean` and its satellites, and prove the two
conditions which, on top of the finite limits already available
(`Realizability.ExReg.instHasFiniteLimits`), make the completion regular in the sense of
Mathlib's `CategoryTheory.Regular`.

## The covers

* `Realizability.ExReg.IsSection` — the section data of a cover: a function `g` on points and an
  element `s` of the algebra which, from a realizer of `y`, computes the pair of a realizer of
  `g y` and of a proof that `f (g y)` is related to `y`.  This is surjectivity read
  computationally: not that every point of the target is hit, but that a preimage is *computed*
  from a realizer of the point, uniformly.
* `Realizability.ExReg.CoverPre`, `Realizability.ExReg.Cover` — a pre-morphism, respectively a
  morphism, with such a section; `Realizability.ExReg.CoverPre.of_homotopic` — the notion only
  depends on the homotopy class, so `Realizability.ExReg.cover_homOf_iff` reads it off any
  representative.
* Closure properties: `Realizability.ExReg.coverPre_quotPre` and `.cover_quot` — the canonical
  map from the base of a relation is a cover (the section is the identity, and reflexivity turns
  a realizer into a proof); `.CoverPre.comp`, `.Cover.comp` — composition; `.CoverPre.of_comp_right`,
  `.Cover.of_comp_right` — a right factor of a cover is a cover; `.cover_of_isIso` — an
  isomorphism is a cover, its inverse being a section on the nose.

## The covers are exactly the regular epimorphisms

* `Realizability.ExReg.regularEpiOfEpiComp` — a general categorical step: if `f ≫ g` is a regular
  epimorphism and `f` is an epimorphism, then `g` is a regular epimorphism, the coequalizer
  diagram of `f ≫ g` being transported along `f`.
* `Realizability.ExReg.quot_comp_imgFac` — the canonical cover of the image *is* the canonical
  cover of the source followed by the first factor of the image factorization: both are the
  identity on points.
* `Realizability.ExReg.regularEpi_imgFac` — **the first factor of the image factorization is a
  regular epimorphism**, by the two previous items and `Realizability.ExReg.regularEpi_quot`.
  This was the first thing the task asked for.
* `Realizability.ExReg.coverPre_imgFacPre` — that first factor is also a cover.
* `Realizability.ExReg.invImgPre`, `.isIso_imgIncl_of_cover` — for a cover, the section is a
  pre-morphism from the target *to the image*, and it inverts the second factor: the two
  composites are homotopic to the identities, the homotopies being read off the section data.
* `Realizability.ExReg.isRegularEpi_of_cover` — a cover is a regular epimorphism: its image
  factorization is a regular epimorphism followed by an isomorphism.
* `Realizability.ExReg.cover_of_isRegularEpi` — conversely a regular epimorphism is strong, so
  the monomorphism of its image factorization is invertible, and the cover data is read off the
  inverse.
* `Realizability.ExReg.cover_iff_isRegularEpi` — **the regular epimorphisms of the completion are
  exactly its covers.**

## Stability under base change

* `Realizability.ExReg.liftPre` — the base of an object, with equality, is projective for the
  covers: given a cover `q` with section `(gs, s)` and any `pf` into the same target, the
  assignment `x ↦ gs (pf x)` is a pre-morphism out of `eqERel X.base`, because from a realizer
  of `x` one computes a realizer of `pf x`, then the section computes a realizer of
  `gs (pf x)`, and reflexivity turns it into a proof.
* `Realizability.ExReg.liftPre_comp` — composed with the cover it is the canonical cover of `X`
  followed by `pf`, the homotopy being the second component of the section data.
* `Realizability.ExReg.cover_of_isPullback` — **a cover pulled back along any morphism is a
  cover**: the lift and the canonical cover of `X` factor through the pullback, so the canonical
  cover of `X` factors through the pulled-back leg, and a right factor of a cover is a cover.
* `Realizability.ExReg.regularEpi_isStableUnderBaseChange` — the same statement for
  `MorphismProperty.regularEpi`.

## Coequalizers of kernel pairs, and regularity

* `Realizability.ExReg.hasCoequalizer_of_isKernelPair` — the kernel pair of a morphism has a
  coequalizer: the kernel pair of `f = imgFac ≫ imgIncl` is the kernel pair of `imgFac` because
  `imgIncl` is a monomorphism, and a regular epimorphism is the coequalizer of its kernel pair.
* `Realizability.ExReg.isKernelPair_and_isColimit_of_isKernelPair` — kernel pairs are effective:
  the kernel pair of a morphism is the kernel pair of its own coequalizer.
* `Realizability.ExReg.instRegular` — **the completion is a regular category**, in the sense of
  `CategoryTheory.Regular`: finite limits, coequalizers of kernel pairs, and regular
  epimorphisms stable under base change.

## Coequalizers of internal equivalence relations

`Start/AsmExRegCoeq.lean` builds the other half of exactness.

* `Realizability.ExReg.Coeq.EqvData` — the computational data of an internal equivalence
  relation `f₁, f₂ : R ⟶ E`, read on pre-morphisms: a diagonal, a swap, and a composite for two
  maps into `R` with matching middle endpoints; `.eqvData_of_isInternalEquiv` — an internal
  equivalence relation in the sense of `Realizability.ExReg.NotExact.IsInternalEquiv` carries
  that data, on any representatives of its legs.
* `Realizability.ExReg.Coeq.compERel` — the object of **composable pairs**: pairs of points of
  `R` whose middle endpoints are related, realized by their two realizers together with a proof
  of that relation, with projections `.compFst`, `.compSnd` and the composability homotopy
  `.compHomotopic`.  It is what the transitivity of the relation is applied to.
* `Realizability.ExReg.Coeq.coeqObj` — the quotient: the base of `E` with the coarser relation
  whose proofs are a point `r` of the base of `R`, a realizer of it, and proofs in `E` that
  `f₁ r` is related to `x` and `f₂ r` to `y`.  Reflexivity is the diagonal, symmetry the swap,
  and transitivity the composite of the composable pair built from the two middle proofs.
* `Realizability.ExReg.Coeq.coeqPre` — the map onto the quotient, the identity on points;
  `.epi_coeqPre` — it is an epimorphism, the quotient having the same base with the same
  realizers; `.coeq_homotopic` — it identifies the two legs, a realizer of `r` being the datum
  of a proof that `f₁ r` and `f₂ r` are related.
* `Realizability.ExReg.Coeq.descPre` — a map out of `E` that identifies the two legs descends:
  the descent is the same function, tracked by chaining the transported proof of `f₁ r ~ x`,
  the homotopy at `r`, and the transported proof of `f₂ r ~ y`.
* `Realizability.ExReg.Coeq.coeqCoforkIsColimit`, `.hasCoequalizer_of_isInternalEquiv` —
  **every internal equivalence relation of the completion has a coequalizer.**

## Exactness fails

`Start/AsmExRegNotExact.lean` settles the remaining question in the negative.

* `Realizability.ExReg.NotExact.IsInternalEquiv` — a jointly monic parallel pair with a
  diagonal, a swap and composites; `.isInternalEquiv_of_isKernelPair` — every kernel pair is
  one, so the notion is the standard one.
* The counterexample.  A morphism of the completion picks one point per point of the source
  *and* computes a realizer of the chosen point from a realizer of the source point, uniformly.
  Attach to each element `s` of the algebra two witnesses `cw s false`, `cw s true` that the
  element `s` itself cannot normalize — possible by a three-point pigeonhole
  (`.exists_pair_not_normalized`), since application is single-valued and no element maps three
  pairwise distinct elements into a single one of them (`.Blocking`, `.exists_blocking`).  The
  object `X` (`.xERel`) has two points `(s, false)`, `(s, true)` per element, each realized by
  `s` alone; the object `R` (`.rERel`) has over each such pair one point per witness, realized
  by the pair of `s` and an element computing the constant function at that witness.
* `.isInternalEquiv_p` — the two endpoint maps `.p₁`, `.p₂` are jointly monic (`.jointly_mono`)
  and carry a diagonal (`.deltaPre`), a swap (`.sigmaPre`) and a composition (`.transPre`).
* `.not_isKernelPair` — they are the kernel pair of no morphism.  The test object maps into `X`
  twice; the two maps become equal after any candidate `k`, because their difference is covered
  by the cross points (`.nPre`, `.piPre`, which is an epimorphism); a lift into `R` would have
  to choose one witness per index `s` and to compute a realizer of the chosen cross point from
  `s`, and at the index `s = t`, with `t` the tracker of the lift, that is exactly what the
  blocking property forbids.
* `.exists_internalEquiv_not_kernelPair` — **over any algebra with three distinct elements the
  completion carries an internal equivalence relation that is not a kernel pair**;
  `.kleene_exReg_not_exact` — in particular over Kleene's first algebra.

## Boundary

The completion of *all* assemblies is regular but not exact, and that is now proved in both
directions.  What is left of the programme is the completion with bases restricted to the
regular projectives — the partitioned assemblies of `Start/AssemblyProjective.lean` — where
exactness is expected to hold, together with the universal property among exact categories, the
topos structure, and the identification with the effective topos.
