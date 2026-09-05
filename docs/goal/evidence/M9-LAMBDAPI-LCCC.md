# M9-LAMBDAPI-LCCC

**Status:** BACKEND_PARTIAL

Modules `Start/LambdaPi.lean`, `Start/LambdaPiTyping.lean`, `Start/LambdaPiBound.lean`,
`Start/LambdaPiCat.lean`, `Start/LambdaPiCwa.lean`, `Start/Cwa.lean`, `Start/CwaType.lean`,
`Start/Lccc.lean`, `Start/LcccType.lean`, `Start/CwaCodePi.lean`, `Start/CwaTypeModel.lean`,
`Start/CwaCodeSigma.lean`, `Start/CwaTypeModelSigma.lean`, `Start/LambdaPiInterp.lean`,
`Start/LambdaPiInterpFun.lean`, `Start/LambdaPiInterpSub.lean`, `Start/LambdaPiInterpConv.lean`,
`Start/LambdaPiInterpTotal.lean`, `Start/LambdaPiInterpHom.lean` and `Start/LambdaPiInitial.lean`,
all imported by `Start.lean`.  They build without `sorry` and without
linter warnings.

This is the layer above `M9-STLC-CCC`.  There the correspondence was "simply typed lambda
calculus ⟺ cartesian closed category"; here types may depend on terms, so a type lives in a
context and the two quantifiers `Σ` and `Π` become the two adjoints of substitution between
slice categories.

## The object language — `Start/LambdaPi.lean`, `Start/LambdaPiTyping.lean`

`Tm` is the raw syntax of `λΠ` (de Bruijn variables, the sorts `∗` and `□`, application,
abstraction and dependent products), with a full parallel-substitution calculus: `rename`,
`subst`, `up`, `scons`, `inst` (`t[a]`) and `shift`, together with the four composition laws
(`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`).  `Step`, `Red` and `Conv` are
β-reduction, its reflexive–transitive closure and conversion, with all congruence rules and
stability under renaming and substitution.

**`LambdaPi.church_rosser`** is proved by Takahashi's method: parallel reduction `Par` with its
complete development `rho`, the triangle property, hence the diamond property and confluence.
Its standard consequences are recorded: `Conv.church_rosser`, injectivity of the product former
(`pi_inj_left`, `pi_inj_right`), `sort_conv_inj` and `not_conv_sort_pi`.

`Start/LambdaPiTyping.lean` gives the pure-type-system presentation: `Ctx`, `Lookup`, the axiom
`∗ : □` and the rules `(∗,∗)`, `(∗,□)`, the judgement `Typing` and well-formed contexts `Wf`.
The metatheory is complete for this fragment:

* `Typing.rename`, `Typing.weaken` — renaming and weakening;
* `Typing.substs`, `Typing.inst` — the substitution lemma;
* `Typing.sort_inv`, `var_inv`, `pi_inv`, `lam_inv`, `app_inv` — the five inversion lemmas;
* `Typing.validity`, `Typing.typeTypable` — every type is a sort or is itself typable;
* `CtxConvOk`, `Typing.ctxConv` — conversion of contexts;
* **`Typing.step`, `Typing.red`** — subject reduction.

`Start/LambdaPiBound.lean` adds the variable-occurrence analysis (`Bnd k t`, `Typing.bnd_of_wf`,
`conv_subst_congr`) that the syntactic category needs.

## The interface — `Start/Cwa.lean` and the standard model — `Start/CwaType.lean`

`Cwa C` is a category with attributes: a strict presheaf of types `Ty` with substitution, context
extension `ext Γ A` with its display map `disp A`, and the requirement that the extension squares
are pullbacks.  `Cwa.Tm` are the sections of a display map, `Cwa.tmSub` their substitution, and
`Cwa.PiStruct` a dependent-product structure with the `lam`/`app` bijection.

`CwaType.families` is the standard model: contexts are types, a type in context `Γ` is a family
`Γ → Type u`, context extension is the sigma type.  `CwaType.secEquiv` shows its terms are exactly
the dependent functions `∀ x, A x`, and `CwaType.piStruct` is its Π-structure
`Pi A B x = (a : A x) → B ⟨x, a⟩`, for which the Beck–Chevalley condition holds definitionally.

## The categorical side — `Start/Lccc.lean`, `Start/LcccType.lean`

Mathlib has the two halves of local cartesian closure (`ChosenPullbacksAlong`,
`ExponentiableMorphism`) but no class bundling them and no naming of the quantifiers.
`CategoryTheory.LocallyCartesianClosed` supplies that, with `Sigma f = Over.map f`,
`Pullback f` and `Pi f` and the adjoint chain `Σ_f ⊣ f* ⊣ Π_f`
(`sigmaPullbackAdj`, `pullbackPiAdj`) and the two currying bijections.

`Start/LcccType.lean` builds the motivating instance by hand, with representatives that compute:
the pullback of `A` along `f` has total space `Σ y, Fib A (f y)` and the pushforward of `B` has
total space `Σ x, ∀ y ∈ f⁻¹(x), Fib B y`.  Both adjunctions are proved directly
(`LcccType.mapPullbackAdj`, `LcccType.pullbackPushforwardAdj`), giving
**`LcccType.instLocallyCartesianClosedType`**.

The two sides are then welded together: **`LcccType.piIso`** proves that pushing a family `B`
forward along the display map of `A` is isomorphic, in the slice over the context, to the family
`fun x => (a : A x) → B ⟨x, a⟩`, i.e. to `CwaType.piStruct.Pi A B`.  `LcccType.piFibEquiv` is the
fibrewise form and `LcccType.famFibEquiv` the identification of the fibre of a display map with
the family it comes from.

## The syntactic category — `Start/LambdaPiCat.lean`

Objects are well-formed contexts; a morphism `Δ ⟶ Γ` is a well-typed substitution taking the
variables of `Γ` to terms over `Δ`, identified when convertible at every variable of `Γ`.
Composition is substitution and the category laws hold on the nose.  Well-definedness of
composition is exactly where `Typing.bnd_of_wf` and `conv_subst_congr` are used.

* `LambdaPiCat.emptyIsTerminal` — the empty context is terminal;
* `LambdaPiCat.disp`, `LambdaPiCat.extend` — weakening out of an extended context, and the action
  of a substitution on an extended context;
* **`LambdaPiCat.isPullback_extend`** — the context-extension square is a pullback.  This is the
  universal property a category with attributes demands, and the precise sense in which "a
  substitution into `A :: Γ` is a substitution into `Γ` together with a term of `A`";
* **`LambdaPiCat.secEquiv`** — the categorical notion of a term reproduces the syntactic one:
  sections of the display map of `A` over `Γ` correspond exactly to well-typed `λΠ` terms of type
  `A` in `Γ`, taken up to conversion;
* `LambdaPiCat.lamTm`, `LambdaPiCat.appTm`, **`LambdaPiCat.appTm_lamTm`** — the Π-former of the
  calculus, on terms modulo conversion: abstraction, application in generic-argument form, and
  the β-law.

## The syntactic category with attributes — `Start/LambdaPiCwa.lean`

The syntactic pieces are assembled into the interface of `Start/Cwa.lean`.

* `LambdaPiCwa.TyQ Γ` — the *small types* of a context, that is the terms of sort `∗`, taken up to
  conversion; `LambdaPiCwa.tySubQ` is the action of a substitution on them, strictly functorial
  because substitution of raw terms is.
* `LambdaPiCwa.syntactic : Cwa LambdaPiCat.Ob` — **the syntactic category of `λΠ` is a category
  with attributes.**  Context extension is `A :: Γ` for a chosen representative `A` of the
  conversion class, the display map is weakening, and the extension squares are pullbacks: the
  square for a chosen representative is `LambdaPiCat.isPullback_extend`, and it is transported to
  the representative that `ext` picks along the isomorphism `LambdaPiCwa.convIso`, which is the
  identity substitution between extensions by convertible types.
* `LambdaPiCwa.weakPi : Cwa.WeakPiStruct syntactic` — **the dependent product of `λΠ` is a weak
  Π-structure**: `LambdaPiCwa.piQ_sub` is the Beck–Chevalley condition and `LambdaPiCwa.appQ_lamQ`
  is the β-law.  Types are restricted to sort `∗` precisely because the rules of `λΠ` form a
  product only over a term of `∗`.
* `LambdaPiCwa.not_piStruct_weakPi` — **η genuinely fails**: in the context `α : ∗, f : Π x:α. α`,
  `λ x. f x` is not β-convertible to `f` (`LambdaPiCwa.lamQ_appQ_ne`, from Church–Rosser and the
  fact that a reduct of an abstraction is an abstraction), so no `Cwa.PiStruct` on the syntactic
  category has the abstraction and application of the calculus.  A weak Π-structure is therefore
  the best possible on a β-only calculus.

## Strictification — `Start/CwaLocalUniverse.lean`

The coherence problem on the semantic side is solved by presenting types rather than taking them
to be slice objects.  A type in context `Γ` is a **local universe**: a morphism
`proj : total ⟶ base` of `C` together with a classifying map `cls : Γ ⟶ base` (`LuTy`).
Substitution acts on the classifying map alone,

```lean
def sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) : LuTy Δ := ⟨A.base, A.total, A.proj, σ ≫ A.cls⟩
```

so the two strictness laws `tySub (𝟙 Γ) A = A` and `tySub (τ ≫ σ) A = tySub τ (tySub σ A)` are
just the identity and associativity laws of `C` — which is exactly what the codomain fibration
fails to give, pullback along a composite agreeing with the composite of pullbacks only up to
canonical isomorphism.  Context extension is the pullback of `proj` along `cls`, the display map
is its first projection, and the extension squares are pullbacks by the pasting lemma
(`LuTy.isPullback_extend`).  Hence

```lean
noncomputable def Cwa.ofPullbacks (C : Type u) [Category.{v} C] [HasPullbacks C] :
    Cwa.{u, v, max u v} C
```

— **every category with pullbacks is a category with attributes**.  Nothing is lost by moving to
presentations: every slice object `p : Y ⟶ Γ` is presented by the type `LuTy.ofHom p`, whose
extended context is identified with `Y` over `Γ` (`LuTy.isoExtOfHom`, `LuTy.isoExtOfHom_disp`).

## The dependent product and sum of the strictified model — `Start/CwaPi.lean`

The local universes of `Start/CwaLocalUniverse.lean` give contexts and types; this file gives the
two quantifiers.  A locally cartesian closed structure relative to the pullbacks the category
already has is packaged as `LcccPullbacks C`: a right adjoint `pushforward f` to `Over.pullback f`
for every morphism `f` (`LcccPullbacks.ofLocallyCartesianClosed` derives it from the class of
`Start/Lccc.lean`, the two pullback functors being right adjoints of the same functor).

The difficulty is coherence again.  A dependent product of local universes must have a base and a
total space that do not mention the context, since substitution acts on the classifying map alone.
Both are therefore built *generically*:

* `LuTy.piBase A B` is the pushforward along `A.proj` of the constant family over `A.total` with
  fibre `B.base`.  By the adjunction, a map `Γ ⟶ piBase A B` over `A.base` is exactly a classifying
  map `Γ.A ⟶ B.base`, so this object classifies the data of a Π-type; `LuTy.piCls` is the
  transpose of the pair `(A.cls, B.cls)`.
* Over that base sit the generic copies `LuTy.piGenA`, `LuTy.piGenB` of `A` and `B` — the second
  classified by the counit — and `LuTy.piW`, the pushforward of the display map of `piGenB` along
  the display map of `piGenA`, is the generic dependent product.  `LuTy.piTy A B` is the local
  universe assembled from these.

* **`LuTy.piTy_sub`** — Beck–Chevalley *strictly*: `tySub σ (Pi A B) = Pi (tySub σ A) (…)` on the
  nose, because transposition is natural in the context (`LuTy.piCls_sub`).
* **`LuTy.tmEquivPi`** — terms of `piTy A B` in `Γ` are exactly terms of `B` in `Γ.A`.  The
  bijection chains the adjunction with the identification `LuTy.piCtxIso` of `Γ.A` with the
  pullback of the generic extended context along the transpose, which is a pullback by
  `LuTy.isPullback_piGenMap`; the computation rule `LuTy.piGenMap_cls` says the generic classifier
  pulls back to `B.cls`.
* **`Cwa.piStructOfLccc`** — hence a `Cwa.PiStruct`: since `lam` and `app` are the two legs of one
  bijection, **both β and η hold**.
* **`Cwa.sigmaStructOfLccc`** — the dependent sum on the same model.  Its base is the same
  classifier, its total space the generic two-step extension, and the pairing isomorphism
  `LuTy.sigPair` comes from the pasting of the two pullback squares (`LuTy.isPullback_sigTy`).

`Start/CwaPiType.lean` checks that the hypothesis is inhabited: `Type u` is locally cartesian
closed relative to its own pullbacks, so `LcccType.luPiStruct` and `LcccType.luSigmaStruct` are the
Π- and Σ-structures of its local-universe model.

## Naturality of the dependent product (`Start/CwaPiSub.lean`)

The interface `Cwa.PiStruct` of `Start/Cwa.lean` requires the *type former* to be stable under
substitution, but says nothing about abstraction and application.  For the model to be sound for a
calculus with substitution one also needs the equation `(λ b)[σ] = λ (b[σ⁺])`, and that is proved
here.

Terms are compared through their **code** `LuTy.code`, the composite of a section with the generic
element of the local universe presenting its type: a term is determined by its code
(`LuTy.code_injective`) and substitution acts on codes by precomposition (`LuTy.code_tmSub`).

* **`LuTy.piTranspose_sub`** — the transposition is natural in the context.  All the *generic* data
  of the dependent product (`piBase`, `piGenA`, `piGenB`, `piW`) depends on the local universes
  alone and not on their classifying maps, so substitution leaves it literally unchanged; only the
  classifying map moves, and the equation is `Adjunction.homEquiv_naturality_left` applied to the
  morphism `LuTy.piSubMor` of the slice, once the two comparison maps are matched
  (`LuTy.extend_piGenMap`, `LuTy.piCtxIso_hom_sub`, `LuTy.piBodyMor_sub`).
* **`LuTy.code_lam_sub`, `LuTy.lam_sub`** — abstraction commutes with substitution; the second form
  is written with the transport along `LuTy.piTy_sub`.
* **`LuTy.code_app_sub`, `LuTy.code_app_tmSub`** — application commutes with substitution.
* **`LuTy.extend_sigGenMap`** — the same for the dependent sum: the comparison map underlying the
  pairing isomorphism commutes with substitution.
* **`Cwa.naturalPiStructOfLccc`** — the naturality is packaged into the interface
  `Cwa.NaturalPiStruct` of `Start/Cwa.lean`, a Π-structure with β, η *and* the substitution law
  for abstraction, which the strictified model of a locally cartesian closed category satisfies.

## Comparisons between models — `Start/CwaMor.lean`

`Start/Cwa.lean` defines the models one at a time; nothing there relates two of them, so the
biequivalence could not even be stated.  `Cwa.Mor T S` is the missing notion: a functor on contexts,
an action on types commuting *strictly* with substitution, and an identification `Cwa.Mor.extIso` of
the image of an extended context with the extended context of the image, lying over the base context
(`extIso_disp`) and compatible with the action of a substitution on extended contexts
(`extIso_extend`).

* `Cwa.Mor.tmMap` — a morphism acts on terms, a section of a display map being carried to a section
  of the image display map;
* **`Cwa.Mor.tmMap_tmSub`** — that action commutes with substitution.  Both sides are sections of
  the display map of the substituted type, hence maps into a pullback, so it is enough to compare
  them with the two legs of the extension square; this is the law that makes a morphism a map of
  *models* and not merely of the underlying data;
* `Cwa.Mor.id`, `Cwa.Mor.comp`, `Cwa.Mor.tmMap_id`, `Cwa.Mor.tmMap_comp` — there is an identity
  morphism and morphisms compose, functorially on terms.

The example is the strictification itself.  A type of `Cwa.ofPullbacks C` is presented by a morphism
of `C`, and a functor transports such a presentation (`Cwa.luMap`); substitution acts on the
classifying map alone, so it is preserved *on the nose* (`Cwa.luMap_sub`) — the coherence problem
does not reappear.  If moreover `F` preserves pullbacks then it preserves extended contexts
(`Cwa.luExtIso`, from `IsPullback.map` and the uniqueness of pullbacks), compatibly with the display
maps and with substitution (`Cwa.luExtIso_hom_disp`, `Cwa.luExtIso_extend`).  Hence
**`Cwa.morOfPullbackPreserving`: the strictified model is functorial in pullback-preserving
functors** (`Cwa.morOfPreservesPullbacks` is the same statement for a functor preserving all
pullbacks).

## Universes of small types — `Start/CwaUniverse.lean`

A category with attributes with a Π-structure is *not* a model of `λΠ`: the types of `λΠ` are its
terms of sort `∗`, so a model must have a type whose terms name types.  That structure is now
formalized.

* `Cwa.Universe T` — a **universe à la Tarski**: a type `U Γ` in every context with
  `tySub σ (U Γ) = U Δ` on the nose, a decoding `El` of its terms as types, and `El_sub`, the
  decoding being strictly stable under substitution as well.  `Cwa.Universe.sub` is substitution on
  codes and `Cwa.Universe.extHom`, `Cwa.Universe.isPullback_extHom` give the extension square of a
  decoded type written with the substituted *code*.
* `Cwa.Universe.SmallPi` — a **dependent product over the small types**: `Pi a B` for a code `a`
  and an arbitrary type `B` over the decoded domain, with Beck–Chevalley, abstraction, application
  and β.  This is exactly the shape of the rules `(∗,∗)` and `(∗,□)`: the domain must be small, the
  body need not be.
* `Cwa.Universe.PiClosed` — **closure**: a code `code a b` for the product of two small types, with
  `El (code a b) = Pi a (El b)`.
* `Cwa.Universe.smallPiOfWeakPi` — a model whose product is defined over all types has in
  particular products over the small ones; only closure is extra.
* Two auxiliary facts about the interface itself: `Cwa.tmSub_eq_of` (a term substitution is the
  unique section with the expected composite) and `Cwa.tmSub_extend`.

## The syntactic model with all types — `Start/LambdaPiFull.lean`, `Start/LambdaPiUniv.lean`

`LambdaPiCwa.syntactic` takes the *small* types as its types, which is too small to hold `∗`
itself.  `LambdaPiFull.syntactic : Cwa LambdaPiCat.Ob` is the same construction with **all** types
of `λΠ`: a type in a context is a term typable by a sort, taken up to conversion and remembering
that sort (the sort is recorded because uniqueness of sorts is not part of the metatheory developed
here; a type of the model is then a conversion class together with the sort it lives at, and
substitution preserves it).  Everything it needs from `Start/LambdaPiCat.lean` — `cons`, the display
map, `isPullback_extend` — is already stated for an arbitrary sort.

On top of it, `Start/LambdaPiUniv.lean`:

* **`LambdaPiUniv.tmSub_tmEquiv_symm`** — the categorical substitution of terms, defined by the
  universal property of context extension, *is* the substitution of the calculus.  This is what
  makes the decoding stable under substitution; the proof identifies the pullback lift with the
  section read off the substituted representative.
* **`LambdaPiUniv.univ : Cwa.Universe LambdaPiFull.syntactic`** — the sort `∗` is a universe.  It is
  stable under substitution because it is a closed term, and `LambdaPiUniv.elQ` decodes a term of
  `∗` as the small type it is.
* **`LambdaPiUniv.smallTyEquiv`** — the terms of `∗` in a context are exactly the small types of
  that context, i.e. the types of `LambdaPiCwa.syntactic`; `LambdaPiUniv.elQ_injective` records that
  a small type has exactly one code.
* **`LambdaPiUniv.smallPi`** — the product rules of `λΠ` are a `SmallPi` structure: `piQ_sub` is
  Beck–Chevalley (the comparison of the two extended contexts goes through `eqToHom`, computed by
  `LambdaPiUniv.extHom_out_conv`), and `appQ_lamQ` is β.
* **`LambdaPiUniv.piClosed`** — the universe is closed under products, by the rule `(∗,∗)`.

## Universes on the semantic side — `Start/CwaUnivLocal.lean`

* `CwaUniv.codeOf` — a term of a type of the strictified model, composed with the generic element,
  is a map into the total space of the presentation; it is stable under substitution
  (`CwaUniv.codeOf_tmSub`).
* **`CwaUniv.universeOfHom`** — in a category with pullbacks and a terminal object, *every* morphism
  `p : E ⟶ 𝒰` is a universe in `Cwa.ofPullbacks C`: the codes in `Γ` are the maps `Γ ⟶ 𝒰` and a code
  decodes to the family it classifies.  Substitution acts by composition on both, so the decoding is
  strictly stable — the coherence problem does not reappear, because substitution in the strictified
  model touches the classifying map alone.
* **`CwaUniv.typeUniverse`** — the motivating instance: the generic family of small types
  `Σ A : Type u, A ⟶ Type u` is a universe in the strictified model of `Type (u+1)`.
* `CwaUniv.smallPiOfLccc` — in a locally cartesian closed category that universe carries a product
  over its small types, by `Cwa.Universe.smallPiOfWeakPi`.

## Functoriality of the substitution of terms — `Start/CwaSubFunctorial.lean`, `Start/LambdaPiCoherent.lean`

A category with attributes asks substitution to be strictly functorial on *types*; the substitution
of *terms* is then defined by the universal property of context extension, and nothing in the axioms
forces it to be functorial — an automorphism of an extended context over its base makes the
extension square of the identity substitution a pullback just as well, and the substitution of terms
along the identity is then that automorphism.

* **`Cwa.ExtCoherent`** isolates the missing law: the identity substitution acts on an extended
  context by the transport along `tySub_id`, and a composite acts by the composite of the actions,
  up to the transport along `tySub_comp`.
* **`Cwa.ExtCoherent.tmSub_id`**, **`Cwa.ExtCoherent.tmSub_comp`** — from it, the substitution of
  terms is functorial; `Cwa.Universe.sub_id` and `Cwa.Universe.sub_comp` say the same for the codes
  of a universe.
* **`Cwa.extCoherent_ofPullbacks`** — the strictified model of a category with pullbacks satisfies
  the law: `LuTy.extend` is a map into a pullback, and both sides of each equation are computed by
  the two legs.
* **`LambdaPiFull.extCoherent_syntactic`** — so does the syntactic model of `λΠ`: the action of a
  substitution on an extended context is the lifting `up` of the calculus
  (`LambdaPiFull.extendQ_id`, `LambdaPiFull.extendQ_comp`).  Hence `tmSub_id_syntactic` and
  `tmSub_comp_syntactic`: the categorical substitution of terms in the syntax agrees with the
  syntactic one on the nose.

## Comparisons of models with a universe — `Start/CwaMorUniv.lean`

`Cwa.Mor` compares two models but says nothing about their universes, which is what an
interpretation of `λΠ` has to respect.

* **`Cwa.Mor.PreservesUniverse`** — a morphism carrying the type of codes to the type of codes and
  commuting with decoding; **`Cwa.Mor.PreservesUniverse.codeMap_sub`** — the induced action on codes
  commutes with substitution, and `extElIso` transports the extension square of a decoded type.
* **`Cwa.Mor.PreservesSmallPi`**, **`Cwa.Mor.PreservesPiClosed`** — preservation of the products
  over the small types and of the codes for them.
* All three are closed under the identity and composition (`.id`, `.comp`), so the models of `λΠ`
  with a universe, its products and its codes form a category; the closure statements for the codes
  use the coherence law above.

## The category of models — `Start/CwaCat.lean`

`Start/CwaMor.lean` gives an identity morphism and a composite but not the laws.  `Cwa.Mor.ext`
is the extensionality principle — a morphism is determined by its functor, its action on types and
its comparison of extended contexts, the other fields being propositions — and with it
`Cwa.Mor.id_comp`, `Cwa.Mor.comp_id` and `Cwa.Mor.assoc` hold, so bundling a model as `Cwa.Model`
gives an honest category instance `Cwa.Model.instCategory`.

## Functors preserve the universes they present — `Start/CwaUnivMorLocal.lean`

`Start/CwaUnivLocal.lean` turns a morphism `p : E ⟶ 𝒰` of a category with pullbacks and a terminal
object into a universe of the strictified model, and `Start/CwaMor.lean` turns a
pullback-preserving functor into a morphism of strictified models.

* **`CwaUniv.preservesUniverseOfHom`** — a pullback-preserving functor `F` which carries the
  terminal object to the terminal object *on the nose* is a universe-preserving morphism from the
  universe presented by `p` to the universe presented by `F.map p`.  Strictness at the terminal
  object is needed because the type of codes is presented over the terminal object, so the
  comparison of the two universes is an equality of presentations
  (`CwaUniv.luMap_uTy`), and decoding commutes with it (`CwaUniv.luMap_elTy`).

## The small fragment of a model with a universe — `Start/CwaSmall.lean`

A model of `λΠ` is not a theory of all the types of a category with attributes: its types are the
*terms of `∗`*.  This module extracts that theory from a model with a universe.

* **`Cwa.Universe.smallCwa`** — the **small fragment**: the category with attributes on the same
  contexts whose types in `Γ` are the codes `Tm Γ (U Γ)`, whose substitution is the substitution of
  codes and whose extension of a code is the extension by its decoding.  Substitution is strictly
  functorial because `Cwa.ExtCoherent` makes the substitution of terms functorial, and the
  extension squares are `Cwa.Universe.isPullback_extHom`; its terms are literally the terms of the
  decoded type (`Cwa.Universe.smallCwa_Tm`).
* **`Cwa.Universe.smallMor`** — the inclusion of the small fragment into the ambient model, a
  morphism of categories with attributes which is the identity on contexts and decoding on types.
* **`Cwa.Universe.smallMorOfPreserves`** — a comparison of models preserving the universes
  (`Cwa.Mor.PreservesUniverse`) restricts to a comparison of the small fragments, acting on types
  by its action on codes.  (The categorical functoriality laws of this restriction are not
  claimed.)
* **`Cwa.Universe.NaturalPiClosed`** — the closure of the universe under the small products
  together with the law the codes need: the code of a product is stable under substitution.
  `Cwa.Universe.PiClosed` alone does not say this, and Beck–Chevalley for the product of the small
  fragment is exactly it.
* **`Cwa.Universe.smallWeakPi`** — with that law the small fragment carries a dependent product
  with the β-rule: the product of two codes is their code.

Two instances keep this from being vacuous.

* Semantically, **`CwaUniv.smallCwaOfHom`** is the model presented by a universe object
  `p : E ⟶ 𝒰` — the small fragment of the strictified model for `CwaUniv.universeOfHom p` — and
  **`CwaUniv.smallTyEquivHom`** identifies its types in a context `Γ` with the maps `Γ ⟶ 𝒰`.
* Syntactically, **`LambdaPiUniv.codeQ_sub`** proves the naturality law for `λΠ` (the code of a
  product is stable under substitution, `LambdaPiUniv.codeTm_sub` being the corresponding fact for
  codes in general), so **`LambdaPiUniv.naturalPiClosed`** upgrades the product rules `(∗,∗)` and
  `(∗,□)`, and **`LambdaPiUniv.smallSyntactic`** with **`LambdaPiUniv.smallSyntacticPi`** is the
  small fragment of the syntactic model of `Start/LambdaPiFull.lean` with its dependent product.
  `LambdaPiUniv.smallSyntactic_Ty_equiv` records that its types are exactly the small types of
  `λΠ`, i.e. the types of `Start/LambdaPiCwa.lean`.

## The two syntactic models are compared — `Start/LambdaPiSmallCompare.lean`

The development now has two syntactic models of `λΠ` built from the same contexts: the model of
`Start/LambdaPiCwa.lean`, whose types in a context are the small types (the terms of `∗` read as
types), and the small fragment `LambdaPiUniv.smallSyntactic` of the model of
`Start/LambdaPiFull.lean`, whose types are the terms of the universe `∗`.  This module shows that
they are the same model:

* **`LambdaPiUniv.smallToCwa`** is a morphism of categories with attributes
  `smallSyntactic ⟶ LambdaPiCwa.syntactic` in the sense of `Start/CwaMor.lean`.  It is the identity
  functor on contexts, its action on types is the bijection `LambdaPiUniv.smallTyEquiv`, and its
  comparison of extended contexts is the identity substitution, read through
  `LambdaPiFull.convIso` as an isomorphism between extensions by convertible types;
* **`LambdaPiUniv.smallToCwa_tyMap_bijective`** records that its action on types is a bijection in
  every context, so the comparison is an isomorphism on types and the identity on contexts;
* **`LambdaPiUniv.cwaToSmall`** is the morphism in the other direction, coding a small type as a
  term of `∗`, and **`LambdaPiUniv.smallToCwa_comp_cwaToSmall`** and
  **`LambdaPiUniv.cwaToSmall_comp_smallToCwa`** prove the two composites to be the identity
  morphisms;
* **`LambdaPiUniv.smallModelIso`** therefore exhibits the two syntactic models as **isomorphic**
  objects of the category of models `Cwa.Model` of `Start/CwaCat.lean`.  The extensionality that
  this needs — a comparison of extended contexts is determined, heterogeneously, by its transport
  along an equality of types — is `Cwa.heq_iso_ext`, added to `Start/CwaCat.lean`.

The work is in the last axiom of a morphism, the compatibility with the action of a substitution on
extended contexts.  Both sides are morphisms of the syntactic category, hence conversion classes of
substitutions, and both are shown to act at every variable as the lifting `up` of the calculus; the
helper lemmas `LambdaPiUniv.subst_out_ids_conv`, `convIso_out_conv`, `hom_ext_out` and
`cwaExtendQ_out_conv` isolate the pieces.

## A set-theoretic model of `λΠ` — `Start/CwaCodePi.lean`, `Start/CwaTypeModel.lean`

The models above are the syntactic one and the strictified model of an arbitrary category with
pullbacks.  These two modules add the *standard* model: contexts are types of `Type (u + 1)`, a
type in a context `Γ` is a family `Γ → Type u` of small types, and the dependent product is the
dependent function type.

`Start/CwaCodePi.lean` first isolates exactly what the small fragment of a model with a universe
needs in order to interpret the product:

* **`Cwa.Universe.CodePi`** — a code for the product of two *codes*, stable under substitution,
  together with `lam`, `app` and the β-rule `app_lam`.  This is weaker than `SmallPi` together with
  `PiClosed`: nothing is required about the product of arbitrary types of the ambient model, nor
  about the decoding of the code of a product;
* **`Cwa.Universe.smallWeakPiOfCodePi`** — such data already gives the small fragment a dependent
  product with the β-rule, `Cwa.WeakPiStruct (smallCwa co Un)`;
* **`Cwa.Universe.CodePiEta`** and **`Cwa.Universe.CodePiNatural`** — the same data with the η-law,
  and with the naturality of abstraction, give the small fragment a `Cwa.PiStruct`
  (**`Cwa.Universe.smallPiOfCodePiEta`**) and a `Cwa.NaturalPiStruct`
  (**`Cwa.Universe.smallNaturalPiOfCodePiNatural`**).  The law about substitution of terms that the
  last one states is made explicit by **`Cwa.Universe.smallCwa_tmSub`**: substitution in the small
  fragment is substitution in the ambient model, read through the decoding of the substituted
  code;
* **`Cwa.Universe.codePiOfNaturalPiClosed`** and **`Cwa.Universe.smallWeakPi_eq_ofCodePi`** — the
  earlier interface implies the new one, and the two products it yields agree, so nothing is lost.

`Start/CwaTypeModel.lean` builds the model.  The size discipline is what makes it work.  A universe
of small types cannot be a family of types of the model — `Type u` is not an element of `Type u` —
so the naive model of families of `Start/CwaType.lean` has no universe at all.  In the strictified
model a type is a *presentation*, a classifying map into a local universe, so the universe object
may be the large object `Type u : Type (u + 1)`; the product of two codes is the pointwise
dependent function type, which is small again *on the nose*.

* **`CwaUniv.tmSectionEquiv`** — in the strictified model of any category with pullbacks a term is
  a section of the generic family of its presentation, i.e. its code; `CwaUniv.codeOf_universeSub`,
  `extHom_gen` and `extHom_disp` compute the action of a substitution on codes and on extended
  contexts;
* **`CwaTypeModel.extIso`** — the extended context of a code is the total space `Σ x : Γ, a x` of
  the family `a` it names, and **`CwaTypeModel.extIso_extHom`** identifies the action of a
  substitution on it with reindexing of total spaces;
* **`CwaTypeModel.famSectionEquiv`**, **`CwaTypeModel.elTmEquiv`** — sections of the generic family
  are dependent functions, so the terms of a code are the dependent functions of the family;
* **`CwaTypeModel.piCode`** and **`CwaTypeModel.piCode_sub`** — the code `x ↦ (y : a x) → b ⟨x, y⟩`
  of a dependent product, and its stability under substitution; hence
  **`CwaTypeModel.codePi`**: *the universe of small types is closed under dependent products*;
* **`CwaTypeModel.piLam_sub`** — abstraction commutes with substitution;
* **`CwaTypeModel.model`**, **`CwaTypeModel.modelPi`**, **`CwaTypeModel.modelPiEta`** and
  **`CwaTypeModel.modelPiNatural`** — therefore a set-theoretic model of `λΠ`, a category with
  attributes with a dependent product satisfying the β-rule, the η-rule and the naturality of
  abstraction;
* **`CwaTypeModel.modelTyEquiv`**, **`CwaTypeModel.modelTmEquiv`**,
  **`CwaTypeModel.fam_modelPi_Pi`** — the model computed: its types in `Γ` are the maps
  `Γ ⟶ Type u`, its terms are the dependent functions, and its product is the dependent function
  type.

`Start/CwaCodeSigma.lean` and `Start/CwaTypeModelSigma.lean` do the same for the dependent sum.
**`Cwa.Universe.CodeSigma`** asks for a code for the sum of two codes, stable under substitution,
whose extended context is the twice-extended context lying over the base, and
**`Cwa.Universe.smallSigmaOfCodeSigma`** turns that into a `Cwa.SigmaStruct` on the small
fragment.  In the standard model the sum of `a` and `b` is `x ↦ (y : a x) × b ⟨x, y⟩`
(**`CwaTypeModel.sigCode`**, stable under substitution by **`CwaTypeModel.sigCode_sub`**), the
pairing isomorphism is the associativity of the total spaces (**`CwaTypeModel.pairIso`**,
**`CwaTypeModel.pairIso_disp`**), and so **`CwaTypeModel.codeSigma`** and
**`CwaTypeModel.modelSigma`**: *the universe of small types is closed under dependent sums*, and
the set-theoretic model has them.

## Initiality: the syntax is interpreted in every model — `Start/LambdaPiInterp.lean`,
`Start/LambdaPiInterpFun.lean`, `Start/LambdaPiInterpSub.lean`, `Start/LambdaPiInterpConv.lean`,
`Start/LambdaPiInterpTotal.lean`, `Start/LambdaPiInterpHom.lean`, `Start/LambdaPiInitial.lean`

**`LambdaPi.Model C`** is what a category of contexts must carry to interpret `λΠ`: a category with
attributes with coherent substitution of terms, a universe `Un` of small types, dependent products
over the small types with abstraction and application natural in the context, codes for those
products and a terminal object for the empty context.

Because a *raw* expression need not denote anything, the interpretation is defined as a pair of
relations by mutual induction on the syntax: **`LambdaPi.TyI s t A`** ("the expression `t` denotes
the type `A`") and **`LambdaPi.TmI s t A x`** ("`t` denotes the term `x` of type `A`"), where `s` is
a *semantic context* (`LambdaPi.SemCtx`), the list of types by which the object was built, which is
what reading de Bruijn indices requires.  Those relations are then shown to be a partial function
that is total on derivations:

* **`LambdaPi.functional_of_piInj`** — a model whose product former is injective
  (`LambdaPi.Model.PiInj`) interprets *single-valuedly*.  The hypothesis is needed for the
  application rule only: `λΠ` writes applications without annotation, so `f g` does not record the
  domain of the type of `f`, and two derivations could otherwise name the same semantic product by
  different codes.  A calculus with annotated applications would not need it;
* **`LambdaPi.TyI.ren`, `TmI.ren`, `TyI.subst`, `TmI.subst`, `TyI.inst`, `TmI.inst`** — the
  interpretation commutes with renaming, with parallel substitution and with instantiation of the
  last variable, the semantic side being substitution along a morphism of contexts.  The model laws
  used are exactly the naturality laws: Beck–Chevalley for the product, naturality of abstraction
  and of application, and stability of the codes;
* **`LambdaPi.Step.interp_preserves`, `Red.interp_preserves`, `TyI.conv_eq`, `TmI.conv_eq`** —
  β-reduction preserves what an expression denotes, hence convertible expressions denote the same
  thing (pass to a common reduct by Church–Rosser, then use functionality).  This is what the
  conversion rule of the typing judgement needs;
* **`LambdaPi.Typing.interp_total`** with **`TyI.total`, `TmI.total`, `CtxI.total`** — the
  interpretation is *total on derivations*, by induction on the derivation;
* **`LambdaPi.interp_exists_unique`** — putting the two halves together: a derivable term denotes
  **exactly one** term of the model, of exactly one type;
* **`LambdaPi.subI_exists_unique`** — and a well-typed substitution from `Δ` to `Γ` is carried by
  exactly one morphism between the interpreting objects.  The categorical ingredient, proved along
  the way, is **`Cwa.hom_eq_of_val_sub_var`**: a morphism into an extended context is determined by
  its composite with the display map together with the value it gives to the generic term.

`Start/LambdaPiInitial.lean` chooses the interpretation once and for all — `LambdaPiInitial.obj` and
`sem` by recursion on the context, `tyMap` on types — and assembles it:

* **`LambdaPiInitial.functor : LambdaPiCat.Ob ⥤ C`** — the interpretation *is a functor* on the
  syntactic category; preservation of identities and of composites is exactly the uniqueness of the
  interpretation of a substitution;
* **`LambdaPiInitial.tyMap_sub`** — the interpretation of a type is stable under substitution, on
  the nose, and **`homMap_dispQ`**, **`homMap_extendQ`** identify the display maps and the action on
  extended contexts;
* **`LambdaPiInitial.mor : Cwa.Mor LambdaPiFull.syntactic M.T`** — **the comparison morphism of
  categories with attributes** out of the syntactic model, for any model with injective products.
  Its action on terms and the compatibility of that action with substitution come for free from
  `Start/CwaMor.lean`.

A morphism of categories with attributes only compares the *types* of the two models, and the types
of `λΠ` are the terms of the sort `∗`; `Start/LambdaPiInitialUniv.lean` therefore checks that the
comparison respects the rest of the structure of a model of `λΠ`:

* **`LambdaPiInitial.tmMap_spec`** — the missing half of `tyMap_spec`: the term of the model that
  the comparison assigns to a term of the syntactic model is what the representative of that term
  denotes.  It is proved from the uniqueness of the interpretation of a *substitution*, a term
  being a section of the display map;
* **`LambdaPiInitial.mor_preservesUniverse`** — **the comparison preserves the universe**
  (`Cwa.Mor.PreservesUniverse`): the sort `∗` is carried to the universe of the model
  (`tyMap_uQ`) and a decoded code to the decoding of its image (`tyMap_elQ`);
* **`LambdaPiInitial.mor_preservesSmallPi`** — **it preserves the dependent products over the small
  types** (`Cwa.Mor.PreservesSmallPi`), by `tyMap_piQ`;
* **`LambdaPiInitial.mor_preservesPiClosed`** — **it preserves the codes for those products**
  (`Cwa.Mor.PreservesPiClosed`), by `codeMap_codeQ`.

So the comparison morphism compares the syntactic model with an arbitrary model *as models of
`λΠ`*, and not merely as categories with attributes.

## Boundary

What is **not** claimed is the *equivalence* between models of `λΠ` and locally cartesian closed
categories.  Both sides are built, and the syntax is now compared with an arbitrary model, but:

* no comparison in the inverse direction, from an arbitrary model back to the syntax, is proved, so
  the biequivalence itself is not formalized.  (The isomorphism `LambdaPiUniv.smallModelIso` above
  compares the two *syntactic* models with one another);
* the interpretation is built for models with injective products (`LambdaPi.Model.PiInj`), which is
  the price of unannotated application, as explained above;
* the universe of a *general* strictified model is still not shown to be closed under the
  pushforward product (`Cwa.Universe.PiClosed`).  For the code of a product to decode to the
  pushforward on the nose, the generic product data would have to be the universe object itself;
  this is a further requirement on the universe object, not a consequence of local cartesian
  closure.  What is proved is the corresponding closure for the standard model
  (`CwaTypeModel.codePi`), in the weaker but sufficient sense of `Cwa.Universe.CodePi`.

## Closure under the product is genuine extra structure

That last point is now made precise, in `Start/CwaUnivNotClosed.lean`: closure of a universe under
the dependent product is **not** a consequence of the ambient model having all dependent products.

**`CwaTypeNotClosed.twoUniverse`** is the universe of the standard model of families of types whose
codes in a context `Γ` are the families of booleans `Γ → Bool`, a code naming `Bool` where it is
`true` and the empty type where it is `false` (`CwaTypeNotClosed.dec`); stability of the decoding
under substitution is `El_sub`.  It has dependent products over its small types
(**`CwaTypeNotClosed.twoSmallPi`**, obtained from the Π-structure of the ambient model by
`Cwa.Universe.smallPiOfWeakPi`), and those products are the dependent function types
(`twoSmallPi_Pi`).  Nevertheless:

* **`CwaTypeNotClosed.not_piClosed`** — there is *no* `Cwa.Universe.PiClosed` structure on it.  The
  product of the code for `Bool` with itself over a one-point context is `Bool → Bool`, of
  cardinality four, whereas every code decodes to a type of cardinality at most two;
* **`CwaTypeNotClosed.not_codePi`** — it does not even carry the weaker product-of-codes data
  `Cwa.Universe.CodePi`.  There, abstraction is only required to be a section of application, but
  the β-law already makes it injective, so it would embed the four functions `Bool → Bool` into the
  at most two terms of the type named by any code; three pairwise distinct functions are exhibited
  and mapped into a two-element type.

* **`CwaTypeNotClosed.not_codeSigma`** — nor the sum-of-codes data `Cwa.Universe.CodeSigma`: its
  pairing isomorphism would identify the context extended twice by `Bool`, four points, with the
  context extended by a single code, of at most two points.

So `Cwa.Universe.PiClosed`, `Cwa.Universe.CodePi` and `Cwa.Universe.CodeSigma` are genuine
requirements on the universe
object of a model, independent of local cartesian closure of the ambient category — which is why
`CwaTypeModel.codePi` has to be verified for the specific universe of small types rather than
derived from the product structure.

## Update (the 2-categorical shadow of the comparison)

The comparison with locally cartesian closed categories is still not a biequivalence, and the
obstruction analysed in `M10-CWA-STRICT-RIGID` and `M10-CWA-STRICT-FULL` is unchanged: with strict
morphisms and strict 2-cells, strictification is not 2-functorial at all and is not full on the
nose.  What has changed is the two-dimensional side of the weakening it forces.  With the lax
2-cells the comparison of types is a map over the base rather than an equality, and that datum
turns out to be *uniquely determined* by the underlying natural transformation
(`M10-CWA-LAX-RIGID`, `Cwa.LaxTwoCell.equivNatTrans`).  Hence the interchange law holds
(`M10-CWA-LAX-INTERCHANGE`), both sides of the comparison are strict bicategories
(`M10-CWA-LAX-BICAT`: `Cwa.LaxCModel.instBicategory` and `Cwa.PbCat.instBicategory`), and
strictification carries whiskering to whiskering on either side
(`Cwa.laxTwoCellOfNatTrans_whiskerLeft`, `Cwa.laxTwoCellOfNatTrans_whiskerRight`) as well as
identities and vertical composition.

Still missing, and the reason this task stays open: strictification is not packaged as a mathlib
`Pseudofunctor` between those two bicategories, no functor is built in the opposite direction, and
no biequivalence is claimed.
