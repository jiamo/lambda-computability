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
