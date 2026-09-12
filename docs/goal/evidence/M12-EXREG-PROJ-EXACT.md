# M12-EXREG-PROJ-EXACT — exactness of the completion on the regular projective bases

`Start/AsmExRegNotExact.lean` settles the exactness of the exact completion `ExReg(A)` of the
assemblies in the negative: over any partial combinatory algebra with three distinct elements, in
particular over Kleene's first algebra, there is an internal equivalence relation of the
completion which is the kernel pair of no morphism.  The obstruction is uniformity: a morphism
into an object of the completion has to pick one point per point of the source *and* compute a
realizer of the chosen point from a realizer of the source point, by one element of the algebra.

`Start/AsmExRegProj.lean` and `Start/AsmExRegEffective.lean` prove that the obstruction disappears
exactly where it is expected to: on the **regular projectives**.

## The subcategory

* `Realizability.ExReg.ProjBase`, `Realizability.ExReg.ExRegP` — the objects of the completion
  whose base is a partitioned assembly, and the full subcategory they span.
* `Realizability.ExReg.ExRegP.regularProjective_base` — those bases are regular projectives of
  `Asm(A)`; by `Realizability.Assembly.regularProjective_iff` the regular projectives are exactly
  the assemblies isomorphic to partitioned ones, so this is the restriction the classical
  comparison of the ex/reg and ex/lex completions asks for.
* `Realizability.ExReg.ExRegP.embP`, `.isInternalEquiv_id` — the subcategory is inhabited and the
  hypothesis of the main theorem is not vacuous.

## Probes

Everything rests on objects whose points *are* their realizers, so that a tracker out of them may
read off whatever data the points carry.

* `Realizability.ExReg.PairData`, `.pairERel` — a probe: a set of tuples, each realized by itself,
  carrying two points of a fixed object `R`, two tuples being related when their two points are
  related in `R`, a proof carrying in addition the realizers of its endpoints (which is what keeps
  those endpoints computable).
* `Realizability.ExReg.partitioned_pairERel` — a probe has a partitioned base, so it is a legal
  test object for the universal properties of the subcategory.
* `Realizability.ExReg.homotopic_pair`, `.pairFst`, `.pairSnd` — its two projections, and the
  criterion for maps out of it to be homotopic.

## Joint monicity, read computationally

* `Realizability.ExReg.jmData` — the probe of tuples consisting of two points of `R`, realizers of
  them, and proofs that their images under the two legs are related.
* `Realizability.ExReg.JMTracker`, `.jmTracker_of_jointlyMono` — probing a jointly monic pair with
  it yields **one element of the algebra** which manufactures a proof that two points of `R` are
  related from their realizers and from proofs that their images agree.

## The quotient over weaker data

* `Realizability.ExReg.compData` — the probe of composable pairs: two points of `R`, realizers of
  them, and a proof that the second endpoint of the first is related to the first endpoint of the
  second.  Being a probe, it is projective, so composites of maps out of it are available inside
  the subcategory.
* `Realizability.ExReg.EqvDataP`, `.eqvDataP_of_isInternalEquiv` — the data of an internal
  equivalence relation of the subcategory: a diagonal, a swap, and composites of maps out of
  objects *with partitioned base* only.  This is weaker than `Realizability.ExReg.Coeq.EqvData`,
  and it is all the subcategory supplies.
* `Realizability.ExReg.coeqObjP`, `.coeqPreP`, `.coeqCoforkPIsColimit` — the quotient of
  `Start/AsmExRegCoeq.lean`, rebuilt over that weaker data: the base of `E` with the relation the
  two legs generate, and the map onto it, which is again an epimorphism and is the coequalizer.

## The lifting, and the conclusion

* `Realizability.ExReg.exists_liftPre` — two maps out of an object with **partitioned** base which
  become homotopic in the quotient factor through the relation.  The single realizer of a point
  of the source determines the point of `R` to be chosen *and* a realizer of it, which is
  precisely what the counterexample shows to be impossible over an arbitrary base.
* `Realizability.ExReg.homotopic_of_jmTracker`, `.existsUnique_lift` — the factorization is
  unique, by joint monicity.
* `Realizability.ExReg.ExRegP.exists_effective_quotient` — **the conclusion**: every internal
  equivalence relation of the subcategory is effective — the quotient map is its coequalizer and
  the relation is that map's kernel pair; `.isKernelPair_of_isInternalEquiv` is the kernel pair
  half on its own.

`#print axioms` on the headline results reports only `propext`, `Classical.choice`, `Quot.sound`.

## Boundary

What is *not* claimed here: that the restricted subcategory is regular as a category in its own
right (that finite limits and image factorizations stay inside it — they do so only up to
isomorphism, since the limits built in `Start/AsmExRegEq.lean` carry witnesses in their
realizers), the universal property of the completion among exact categories, the topos structure
(subobject classifier and exponentials), and the identification with the effective topos.
