# M23-GROUPOID-MODEL and M23-UIP-INDEPENDENT — the Hofmann–Streicher groupoid model

Status: M23-GROUPOID-MODEL is **DONE_WEAK** (gap row M23-GROUPOID-PI: Π-types).
M23-UIP-INDEPENDENT is **DONE_STRONG**: its exit criteria need only the identity types.

## Modules

| module | content |
| --- | --- |
| `Start/GrpdGrothendieck.lean` | the Grothendieck construction `GObj A` of `A : Γ ⥤ Grpd` (objects `(γ, a)`, morphisms `(f, φ : A.map f a ⟶ b)`), its category and **groupoid** instance, the projection `disp`, the functor `extend σ A` induced by a substitution, `functor_ext`, sections `secOf`, `reindex`, `liftG` |
| `Start/CwaGroupoid.lean` | `grpdExt`, `dispG`, `extendG`, `isPullbackG` (the comprehension square is a pullback: `IsPullback.of_isLimit` with an explicit cone `PullbackCone.IsLimit.mk`, lift `liftG`, uniqueness `liftG_uniq`), and `GrpdModel.grpdCwa : Cwa.{u+1,u,u+1} Grpd.{u,u}` |
| `Start/GrpdIdTypes.lean` | transport along a fibre morphism (`transportAlong`) and its laws; the identity type `IdT A` over `ext2 Γ A`; `diagT`, `reflT`, `rhoT`; the eliminator `Jexp` with `Jexp_comp` and `Jexp_sub` |
| `Start/CwaGroupoidId.lean` | `GrpdModel.grpdIdStruct : IdStruct grpdCwa`: `IdC`, `grpdRefl`, `grpdJ'`, and the four laws `J_comp`, `Id_sub`, `refl_sub`, `J_sub` |
| `Start/CwaGroupoidUIP.lean` | `LoopG`, `unitG`, `loopTy`, `GrpdModel.grpdIdStruct_not_UIP`, `GrpdModel.uip_independent` |

## A1. The category with attributes

* `Ty Γ := Γ ⥤ Grpd`, `tySub σ A := σ ⋙ A`; `tySub_id` and `tySub_comp` hold by `rfl`
  (functor composition is strictly associative and unital).
* `ext Γ A := Grpd.of (GObj A)`, the Grothendieck construction.  Mathlib's `Grothendieck` is a
  category, not a groupoid; the groupoid instance is proved in `GrpdGrothendieck.lean` (`GObj.groupoid`:
  the inverse of `(f, φ)` is built from `f⁻¹` and the inverse of `A.map f⁻¹ φ`, up to `eqToHom`).
* `disp` is the first projection and `extend σ A : ext Δ (σ ⋙ A) ⟶ ext Γ A` maps `(δ, a)` to
  `(σ δ, a)`.
* `isPullback`: proved through an explicit limit cone.  Mathlib has no pullback lemma for the
  Grothendieck construction; given `F : W ⥤ ∫A` and `G : W ⥤ Δ` with
  `F ⋙ disp A = G ⋙ σ`, the lift is `liftG σ A F G h := (secOf F ⋙ reindex _) ⋙ extend G (σ ⋙ A)`
  (the section of `F` over `F ⋙ disp A`, reindexed along `h`), and uniqueness (`liftG_uniq`) uses `functor_ext` (a functor into `GObj` is determined by
  its two components, up to `eqToHom`).

## A2. Identity types

`Id A` at a point `(γ, a, b)` of `ext2 Γ A` is the discrete groupoid on the fibre morphisms
`A.map (𝟙 γ) a ⟶ b` (transported along the action of the context morphisms, `IdT`); `refl` is the
identity morphism; `J` is transport along the morphism, which exists because the fibre is a
groupoid.  The definitions are chosen so that `J_comp`, `Id_sub`, `refl_sub` and `J_sub` are
**equalities that hold strictly** as `IdStruct` states them; the hardest is `J_sub`
(`grpdJ'_sub`, compiled with a raised heartbeat bound).

## A3. UIP fails

`LoopG` is the one-object groupoid whose automorphism group is `ℤ/2` (`Bool` under `xor`, i.e.
`Multiplicative (ZMod 2)` up to isomorphism); `loopTy` is the constant type with value `LoopG` over
the terminal groupoid `unitG`.  At the base point, `Id x x` has two distinct elements (the two
loops), and `Id (Id A)` between them is empty (the fibre of `Id` is discrete), so no section as
required by `UIP` exists.

```lean
theorem grpdIdStruct_not_UIP : ¬ grpdIdStruct.{u}.UIP
```

## A4. Independence

```lean
theorem uip_independent :
    CwaType.idStruct.{u}.UIP ∧ ¬ grpdIdStruct.{u}.UIP ∧
    (∃ (C : Type (u + 1)) (_ : Category.{u} C) (T : Cwa.{u + 1, u, u + 1} C) (I : IdStruct T),
      I.UIP) ∧
    (∃ (C : Type (u + 1)) (_ : Category.{u} C) (T : Cwa.{u + 1, u, u + 1} C) (I : IdStruct T),
      ¬ I.UIP)
```

The set model satisfies UIP and the groupoid model refutes it, so neither UIP nor its negation follows
from the rules of `Cwa.IdStruct`.

## A5. Π-types — not done (gap row M23-GROUPOID-PI)

First missing construction:

```lean
def grpdPiStruct : Cwa.PiStruct grpdCwa
```

`Π A B` at `γ` is the groupoid of sections of `B` over the fibre `A γ` (functors
`s : A γ ⥤ ∫B|_{A γ}` over the inclusion, with natural transformations as morphisms), with the
action of `γ ⟶ γ'` by conjugation.  What has to be proved is the strict functoriality of this
action and the strict `λ`/`app`/β/η equations of `PiStruct`; the same transport lemmas
(`transportAlong`, `functor_ext`) are the tools.

## Axioms

See `M23-GROUPOID-MODEL-axioms.txt` and `M23-UIP-INDEPENDENT-axioms.txt`: all four results use
only `[propext, Classical.choice, Quot.sound]`.

## Round 3 — Π: the Π-groupoid and its functoriality (row M23-GROUPOID-PI, still open)

`Start/GrpdSect.lean`. For a family `F : D ⥤ Grpd`, `Sect F` is the groupoid of its sections. An
object is a choice `s a ∈ F a` with morphism maps compatible with identities and composition. A
morphism is a natural family. The instance is `Sect.groupoid`, with `toFunctor`/`ofOver`
relating sections to functors over `D`. Transport along a natural transformation
`θ : K ⋙ I ⟶ I'` is `GrpdModel.trans B K I I' θ : Sect (I ⋙ B) ⥤ Sect (I' ⋙ B)`, with the strict
laws `trans_id`, `trans_comp` and `trans_congr`.

`Start/GrpdPi.lean`. `fibI A γ : A γ ⥤ ∫ A` (inclusion of a fibre);
`piTheta A g : A(g⁻¹) ⋙ fibI A γ ⟶ fibI A γ'`; and

```lean
def PiF : Γ ⥤ Grpd.{u, u}   -- obj γ := Grpd.of (Sect (fibI A γ ⋙ B)), map g := piMap A B g
```

with `map_id` and `map_comp` proved strictly.

Still open: `def GrpdModel.grpdPiStruct : Cwa.PiStruct grpdCwa`. First missing lemma:

```lean
theorem PiF_sub (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd) (B : GObj A ⥤ Grpd) :
    σ ⋙ PiF A B = PiF (σ ⋙ A) (extend σ A ⋙ B)
```

It does not hold by `rfl`. The functor `fibI (σ ⋙ A) δ ⋙ extend σ A` has base morphism
`σ.map (𝟙 δ)` rather than `𝟙 (σ.obj δ)`, so the fibres agree only after a transport along
`Functor.map_id σ` (through `trans_congr`). This has not been attempted in Lean, so we do not
know whether it fails. After it come `lam`/`app`: a bijection between sections of `B` over `∫ A`
and sections of `PiF A B` over `Γ`, given by an evaluation functor, together with `app_lam` and
`lam_app`. Σ (`grpdSigmaStruct`) was not started.

## Round 4 — the Beck–Chevalley law for Π (`Start/GrpdPiSub.lean`)

Proved (axioms at most `[propext, Classical.choice, Quot.sound]`):

```lean
theorem GrpdModel.fibI_extend (δ : Δ) : fibI (σ ⋙ A) δ ⋙ extend σ A = fibI A (σ.obj δ)
theorem GrpdModel.trans_reindex ...   -- transport commutes with reindexing the family
theorem GrpdModel.trans_hcongr ...    -- transport along heterogeneously equal data
theorem GrpdModel.PiF_sub : σ ⋙ PiF A B = PiF (σ ⋙ A) (extend σ A ⋙ B)
```

`fibI_extend` is `Functor.ext`: objects agree by `rfl`, morphisms up to `eqToHom` through
`Functor.map_id σ`.  `PiF_sub` is `Functor.hext`: on objects, rewriting with `fibI_extend`
inside `Sect (· ⋙ B)`; on morphisms, a `HEq` of transports, by `trans_reindex` and then
`trans_hcongr` (`map_groupoidInv` identifies `σ.map (inv g)` with `inv (σ.map g)`).  So the `Pi_sub` field of
`Cwa.PiStruct grpdCwa` is available.

Still open: `def GrpdModel.grpdPiStruct : Cwa.PiStruct grpdCwa`.  **First missing construction:**
`lam`/`app`, i.e. the currying bijection between terms of `B` over the extended context and terms
of `PiF A B`,

```lean
def GrpdModel.piLam (t : Tm (ext Γ A) B) : Tm Γ (PiF A B)   -- a section of Sect (fibI A γ ⋙ B) at each γ
def GrpdModel.piApp (f : Tm Γ (PiF A B)) : Tm (ext Γ A) B   -- evaluation at (γ, a)
```

with `app_lam`, `lam_app` and then `lam_sub` (`NaturalPiStruct`).  The first equation that has to
be proved for `piLam` is functoriality of the section family in `γ`: for `g : γ ⟶ γ'`,
`(PiF A B).map g (piLam t γ) = piLam t γ'`, a transport identity of the same shape as `PiF_sub`'s
morphism part.  Σ (`grpdSigmaStruct`) not started.

## Round 5 — terms are sections; currying and abstraction (`Start/GrpdPiLam.lean`)

Proved (`lake build --wfail`):

* `GrpdModel.tmEquivSect X F : grpdCwa.Tm X F ≃ Sect F` — a term of the groupoid model (a functor
  `X ⥤ ∫ F` strictly over `𝟭 X`) is a section.
* `GrpdModel.Sect.restrict`, `GrpdModel.curryObj`, `GrpdModel.curryMap`, `piTheta_id_heq`,
  `piTheta_comp_heq`.
* **`GrpdModel.curry : Sect B → Sect (PiF A B)`** (with `map_id`, `map_comp`) and
  **`GrpdModel.grpdLam : grpdCwa.Tm (grpdCwa.ext Γ A) B → grpdCwa.Tm Γ (PiF A B)`**.

Finding on the suggested first equation.  `(PiF A B).map g (lam t γ) = lam t γ'` is **not an
equation** of the model: at `a : A γ'` the two sides are `B(θ_a)(t(γ, A(g⁻¹) a))` and `t(γ', a)`,
different objects of `B(γ', a)` in general.  The naturality of the section family `γ ↦ t|γ` is the
morphism `curryMap t g : (PiF A B).map g (t|γ) ⟶ t|γ'` of `Sect (fibI A γ' ⋙ B)` with components
`t.map (piTheta A g a)`; `curry` packages it as the morphism part of the section of `PiF A B`.

Open: `def GrpdModel.grpdPiStruct : Cwa.PiStruct grpdCwa`.  **First missing construction**:
application, the inverse `uncurry : Sect (PiF A B) → Sect B`, with object part
`(γ, a) ↦ (σ γ).obj a` and morphism part, for `f = fibI ψ ≫ θ_y : (γ, a) ⟶ (γ', a')`,
`eqToHom ≫ (B.map θ_y).map ((σ γ).map ψ) ≫ (σ.map g).app y`; the first failing equation is its
`map_comp` (the functoriality of evaluation `ev : ∫ (PiF A B) ×_Γ ∫ A ⥤ ∫ B`).  Then `app_lam`
and `lam_app` follow by making `curry`/`uncurry` an equivalence; `lam_sub` (NaturalPiStruct) and
`grpdSigmaStruct` are not started.

## Round 6 — application, β, η and the Π-structure (`Start/GrpdPiApp.lean`)

`lake build --wfail`; axioms `propext, Classical.choice, Quot.sound` (`M23-GROUPOID-PI-axioms.txt`).

* `GrpdModel.fibTil`, `GrpdModel.fibI_fibTil`, `GrpdModel.fibTil_unique`, `GrpdModel.fibTil_eq` —
  every morphism `m : (γ, a) ⟶ (γ', a')` of `∫ A` factors uniquely as a fibre morphism followed by
  the fibre comparison: `m = ι_γ(φ̃) ≫ θ_g(a')`.
* Following the suggested route, the morphism part of application on `m` is the composite of the
  **fibre part** `GrpdModel.appPhi σ γ` (the functor `A γ ⥤ ∫ B` given by the section `σ γ`) on
  `φ̃`, and the **transport part** `GrpdModel.appPsi σ g a'` (the morphism of `∫ B` over
  `θ_g(a')` given by the section's own morphism part `(σ.map g).app a'`).
* `GrpdModel.appPsi_comp` (from `σ.map_comp` and `piTheta_comp_heq`, i.e. the strict laws
  trans_comp/trans_congr), `GrpdModel.appPsi_nat` (naturality of `σ.map g`: the interchange of the
  two parts), `GrpdModel.fibTil_comp`, hence `GrpdModel.umap_comp` (**the `map_comp` that failed in
  round 5**) and `GrpdModel.umap_id`.
* `GrpdModel.uncurryF σ : GObj A ⥤ GObj B` with `GrpdModel.uncurryF_disp` (it lies over `∫ A`), and
  `GrpdModel.grpdApp : grpdCwa.Tm Γ (PiF A B) → grpdCwa.Tm (grpdCwa.ext Γ A) B`.
* `GrpdModel.uncurryF_curry` (β on functors), `GrpdModel.umap_fibI`, `GrpdModel.umap_theta`;
  β and η through `tmEquivSect`: `GrpdModel.grpd_app_lam : grpdApp A B (grpdLam A B b) = b` and
  `GrpdModel.grpd_lam_app : grpdLam A B (grpdApp A B f) = f`.
* **The terminal definition**:

```lean
def GrpdModel.grpdPiStruct : Cwa.PiStruct grpdCwa where
  Pi A B := PiF A B
  Pi_sub σ A B := PiF_sub σ A B
  lam {_} {A} {B} b := grpdLam A B b
  app {_} {A} {B} f := grpdApp A B f
  app_lam {_} {A} {B} b := grpd_app_lam A B b
  lam_app {_} {A} {B} f := grpd_lam_app A B f
```

Status: M23-GROUPOID-PI and M23-GROUPOID-MODEL are `DONE_STRONG` (the CwA, the identity types and
Π-types).  Not done this round (new row M23-GROUPOID-PI-NATURAL, not a gap of either row): the
substitution law of abstraction (`Cwa.NaturalPiStruct`, first missing lemma `grpdLam_sub`) and
`grpdSigmaStruct`.

## Round 7 — natural Π (`Start/GrpdPiNatural.lean`, row M23-GROUPOID-PI-NATURAL)

```lean
theorem GrpdModel.sectOfTm_tmSub    -- substitution of terms is restriction of sections
theorem GrpdModel.curry_restrict    -- currying commutes with restriction along σ : Δ ⥤ Γ
theorem GrpdModel.grpdLam_sub (b : grpdCwa.Tm (grpdCwa.ext Γ A) B) :
    Cwa.tmCast (PiF_sub σ A B) (grpdCwa.tmSub σ (grpdLam A B b)) =
      grpdLam (σ ⋙ A) (extend σ A ⋙ B) (grpdCwa.tmSub (extendG σ A) b)
def GrpdModel.grpdNaturalPiStruct : Cwa.NaturalPiStruct grpdCwa
```

Axioms: `M23-GROUPOID-PI-NATURAL-axioms.txt` (`propext, Classical.choice, Quot.sound`).

**Σ: not done.**  The interface exists (`Cwa.SigmaStruct` in `Start/Cwa.lean`: `Sig`, `Sig_sub`,
the pairing isomorphism `ext (ext Γ A) B ≅ ext Γ (Sig A B)` and `pair_disp`), so no new interface
was defined.  First missing construction: the functor `SigF A B : Γ ⥤ Grpd` sending `γ` to the
Grothendieck construction of `fibI A γ ⋙ B`, with its `map_comp` (functoriality of the
Grothendieck construction in the base), then the pairing isomorphism of groupoids over `Γ`.
Gap row M23-GROUPOID-SIGMA; M23-GROUPOID-PI-NATURAL is DONE_WEAK.
