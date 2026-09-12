# M12-EFF-EXREG — the exact completion of the assemblies

`Start/AsmExReg.lean`, `Start/AsmExRegProd.lean`, `Start/AsmExRegEq.lean` and
`Start/AsmExRegQuot.lean` build the category out of which the effective topos is made: the exact
completion of the regular category of assemblies of `Start/AssemblyRegular.lean`.

## The objects and the morphisms

* `Realizability.ExReg.ERel` — a **pseudo-equivalence relation** over the assemblies: an assembly
  `base`, a family `Prf a x y` of proofs realized by elements of the algebra, with the two
  endpoints of a proof computable from it (`ends`) and reflexivity, symmetry and transitivity
  each witnessed by an element of the algebra (`refl'`, `symm'`, `trans'`, the last a binary
  tracker).  This is exactly an internal equivalence relation on `base`: a subobject of
  `base × base` whose realizability relation may be finer than the inherited one, which is why a
  strong subobject would not do.
* `Realizability.ExReg.ERel.rel`, `.equivalence_rel` — the underlying relation, an equivalence
  relation; `.exists_fstTracker`, `.exists_sndTracker` — the endpoints of a proof are computable.
* `Realizability.ExReg.Pre` — a **pre-morphism**: a function on the bases with an element of the
  algebra transporting proofs.  `Realizability.ExReg.Pre.trackedBase` — it is in particular a
  morphism of assemblies (apply reflexivity, transport, read the first endpoint).
* `Realizability.ExReg.Homotopic` — two pre-morphisms are homotopic when an element of the
  algebra turns a realizer of `x` into a proof that the two values are related; it is an
  equivalence relation and compatible with composition (`.whiskerLeft`, `.whiskerRight`).
* `Realizability.ExReg.Hom`, `.instCategory` — the hom-sets are the pre-morphisms up to homotopy,
  and this is a category.

## The embedding of the assemblies

* `Realizability.ExReg.eqERel` — an assembly with equality, a proof that `x = y` being a realizer
  of `x`; `Realizability.ExReg.emb` — the resulting functor `Asm(A) ⥤ ExReg(A)`.
* `Realizability.ExReg.instFullEmb`, `.instFaithfulEmb` — **the embedding is full and faithful**.
  Fullness is the observation that a pre-morphism between equality relations is tracked as a map
  of assemblies (apply it to the reflexivity proof); faithfulness is that a homotopy between such
  maps carries, as its second component, the equation itself.

## Finite limits

* `Realizability.ExReg.termERel`, `.isTerminalTerm` — the terminal object.
* `Realizability.ExReg.prodERel`, `.prodFanIsLimit` — binary products: the product of the bases,
  a proof being the Church pair of a proof on each side.  Every combinator needed — the endpoints
  of a pair of proofs, the uniform reflexivity, symmetry and transitivity of the product, the
  pairing of two morphisms — is assembled from the pairing combinator of the algebra
  (`Realizability.ExReg.exists_pairOf`, `.exists_binPair`, `.exists_binOf`).
* `Realizability.ExReg.eqObj`, `.eqForkIsLimit` — equalizers.  A point of the equalizer is a
  point where the two maps are related; the *proofs* carry, besides a proof `x ~ y` in `E`, a
  witness at each endpoint that the maps agree there.  Carrying those witnesses as data is what
  keeps the endpoints of a proof computable, and it is what makes the realizer of a point of the
  equalizer the pair of a realizer of the point and of a witness.
* `Realizability.ExReg.instHasFiniteLimits` — **the completion has all finite limits**.
* `Realizability.ExReg.embProdIso`, `.embTermIso` — the embedding preserves the terminal object
  and binary products: a realizer of a pair *is* a Church pair of realizers, so the identity is
  tracked both ways.

## Every object is a quotient of an assembly

* `Realizability.ExReg.quot` — the canonical map from the base of a relation, with equality, to
  the relation; `Realizability.ExReg.epi_quot` — it is an epimorphism, because a homotopy out of
  the base *is* a homotopy out of the relation.
* `Realizability.ExReg.prfAsm` — the assembly of proofs of a relation: the related pairs, with
  the proofs as their realizers; `.relFst`, `.relSnd` — its two endpoints.
* `Realizability.ExReg.quotIsColimit` — **`quot E` is the coequalizer of the two endpoints**.
  The descent is the identity on functions: a map out of the base that identifies the two
  endpoints of every proof is precisely a map that transports proofs, i.e. a morphism out of the
  relation, and the homotopy witnessing the coequalizing condition *is* its proof tracker.
* `Realizability.ExReg.regularEpi_quot` — hence every object of the completion is a **regular**
  quotient of an assembly.

## Image factorizations

* `Realizability.ExReg.imgObj` — the image of a pre-morphism: the base of the source with the
  relation pulled back along the map, a proof carrying in addition a realizer of each of its
  endpoints, which is what keeps the endpoints computable.
* `Realizability.ExReg.imgFac_comp_imgIncl` — **every morphism factors** as the identity on
  points followed by the map itself; `Realizability.ExReg.epi_imgFac` and `.mono_imgIncl` — the
  first factor is an epimorphism (the image has the same base, with the same realizers, as the
  source) and the second a monomorphism (two maps into the image that agree after it are
  homotopic, the missing realizers being supplied by their own trackers).

## Boundary

What is built here is the completion as a category with finite limits, the embedding, and the
covers.  Regularity is proved in `Start/AsmExRegRegular.lean`
(`Realizability.ExReg.instRegular`), and the exactness question is now settled, in both
directions:

* `Realizability.ExReg.Coeq.hasCoequalizer_of_isInternalEquiv` — **every internal equivalence
  relation of the completion has a coequalizer**, the base of the object with the relation
  generated by the two legs (`Start/AsmExRegCoeq.lean`);
* `Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair` and
  `.kleene_exReg_not_exact` — **the completion is not exact**: over any algebra with three
  distinct elements, in particular over Kleene's first algebra, an internal equivalence relation
  of the completion need not be the kernel pair of any morphism
  (`Start/AsmExRegNotExact.lean`).  The obstruction is that a morphism into an object of the
  completion must choose one point per point of the source and compute a realizer of the chosen
  point uniformly, which fails when the points lying over a related pair carry unrelated
  realizers.

What has since been done, in `Start/AsmExRegProj.lean` and `Start/AsmExRegEffective.lean` (task
`M12-EXREG-PROJ-EXACT`): **restricting the bases to the regular projectives repairs exactness.**
On the full subcategory `Realizability.ExReg.ExRegP` of the objects whose base is a partitioned
assembly — the regular projectives of `Asm(A)` — every internal equivalence relation is effective:
the quotient map above is its coequalizer and the relation is that map's kernel pair
(`Realizability.ExReg.ExRegP.exists_effective_quotient`,
`.isKernelPair_of_isInternalEquiv`).  The two ingredients are joint monicity read as an element of
the algebra (`Realizability.ExReg.jmTracker_of_jointlyMono`) and the lifting that the single
realizer of a point of a partitioned assembly makes possible
(`Realizability.ExReg.exists_liftPre`) — the very step the counterexample blocks over a general
base.

Not done, in order of dependence:

* the regularity of that restricted subcategory as a category in its own right: the finite limits
  of `Start/AsmExRegEq.lean` and the image factorizations stay inside it only up to isomorphism,
  since the limits carry witnesses in their realizers;
* the universal property — that a regular functor out of `Asm(A)` extends, uniquely up to
  isomorphism, to an exact functor out of the completion;
* the topos structure: a subobject classifier and exponentials;
* the identification with the effective topos.
