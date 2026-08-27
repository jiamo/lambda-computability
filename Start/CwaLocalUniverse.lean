/-
**Strictification: a category with pullbacks is a category with attributes.**

`Start/Cwa.lean` demands that substitution act on types *strictly*: `tySub (𝟙 Γ) A = A` and
`tySub (τ ≫ σ) A = tySub τ (tySub σ A)` on the nose.  The naive reading of "a type in context `Γ`
is an object of the slice `C/Γ`, and substitution is pullback" does **not** satisfy this: pullback
along a composite agrees with the composite of pullbacks only up to canonical isomorphism, so the
codomain fibration is only pseudo-functorial.  This is the coherence problem that separates
locally cartesian closed categories from models of dependent type theory.

The standard cure is to replace a type by a *presentation* of it.  A type in context `Γ` is taken
here to be a **local universe**: a morphism `proj : total ⟶ base` of `C` together with a
classifying map `cls : Γ ⟶ base`.  Substitution acts on the classifying map only,
`tySub σ A = ⟨A.proj, σ ≫ A.cls⟩`, and is therefore strictly functorial — the two laws are the
identity and associativity laws of `C`.  The context extension `Γ.A` is the pullback of `A.proj`
along `A.cls`, and the extension squares are pullbacks by the pasting lemma.

Nothing is lost: every object `p : Y ⟶ Γ` of the slice is presented by a type, whose display map
is isomorphic to `p` over `Γ` (`LuTy.ofHom`, `LuTy.isoExtOfHom`, `LuTy.isoExtOfHom_disp`).

Main definitions:

* `LuTy` — types as local universes, with `LuTy.sub`, `LuTy.ext`, `LuTy.disp`, `LuTy.extend`;
* `Cwa.ofPullbacks` — **the category with attributes of a category with pullbacks**.

Main results:

* `LuTy.isPullback_extend` — the extension squares are pullbacks;
* `LuTy.isoExtOfHom_disp` — every slice object is presented by a type.
-/

import Start.Cwa
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- A **type in context `Γ`, presented by a local universe**: a morphism `proj : total ⟶ base`
of `C` together with a classifying map `cls : Γ ⟶ base`.  The type it presents is the pullback of
`proj` along `cls`. -/
structure LuTy (Γ : C) where
  /-- The base of the local universe. -/
  base : C
  /-- The total space of the local universe. -/
  total : C
  /-- The generic family. -/
  proj : total ⟶ base
  /-- The classifying map of the type. -/
  cls : Γ ⟶ base

namespace LuTy

/-- Substitution acts on the classifying map only, hence strictly. -/
@[reducible, simps] def sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) : LuTy Δ :=
  ⟨A.base, A.total, A.proj, σ ≫ A.cls⟩

@[simp] theorem sub_id {Γ : C} (A : LuTy Γ) : sub (𝟙 Γ) A = A := by
  cases A; simp [sub]

theorem sub_comp {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : LuTy Γ) :
    sub (τ ≫ σ) A = sub τ (sub σ A) := by
  cases A; simp [sub]

variable [HasPullbacks C]

/-- The extended context `Γ.A`: the pullback of the generic family along the classifying map. -/
noncomputable def ext (Γ : C) (A : LuTy Γ) : C := Limits.pullback A.cls A.proj

/-- The display map (weakening) out of an extended context. -/
noncomputable def disp {Γ : C} (A : LuTy Γ) : ext Γ A ⟶ Γ := pullback.fst A.cls A.proj

/-- The generic element of the extended context. -/
noncomputable def gen {Γ : C} (A : LuTy Γ) : ext Γ A ⟶ A.total := pullback.snd A.cls A.proj

theorem disp_cls {Γ : C} (A : LuTy Γ) : disp A ≫ A.cls = gen A ≫ A.proj :=
  pullback.condition

/-- The square exhibiting the extended context as a pullback. -/
theorem isPullback_gen {Γ : C} (A : LuTy Γ) :
    IsPullback (gen A) (disp A) A.proj A.cls :=
  (IsPullback.of_hasPullback A.cls A.proj).flip

/-- The action of a substitution on extended contexts. -/
noncomputable def extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) : ext Δ (sub σ A) ⟶ ext Γ A :=
  pullback.lift (disp (sub σ A) ≫ σ) (gen (sub σ A))
    (by rw [Category.assoc]; exact disp_cls (sub σ A))

@[simp] theorem extend_disp {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    extend σ A ≫ disp A = disp (sub σ A) ≫ σ :=
  pullback.lift_fst _ _ _

@[simp] theorem extend_gen {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    extend σ A ≫ gen A = gen (sub σ A) :=
  pullback.lift_snd _ _ _

/-- **The extension squares are pullbacks**, by the pasting lemma: the square of `σ` is the left
half of the pullback square of `sub σ A`, whose right half is the square of `A`. -/
theorem isPullback_extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    IsPullback (extend σ A) (disp (sub σ A)) (disp A) σ := by
  refine IsPullback.of_right ?_ (extend_disp σ A) (isPullback_gen A)
  have h : extend σ A ≫ gen A = gen (sub σ A) := extend_gen σ A
  rw [h]
  exact isPullback_gen (sub σ A)

/-! ### Every slice object is presented by a type -/

/-- The type presented by a morphism `p : Y ⟶ Γ` of `C`, taking the local universe to be `p`
itself and the classifying map to be the identity. -/
@[simps] def ofHom {Γ Y : C} (p : Y ⟶ Γ) : LuTy Γ := ⟨Γ, Y, p, 𝟙 Γ⟩

/-- The extended context of the type presented by `p : Y ⟶ Γ` is `Y`. -/
noncomputable def isoExtOfHom {Γ Y : C} (p : Y ⟶ Γ) : Y ≅ ext Γ (ofHom p) :=
  (IsPullback.of_id_fst (f := p)).flip.isoPullback

/-- The identification of `Y` with the extended context is an identification over `Γ`: the display
map of the type presented by `p` is `p`. -/
@[simp] theorem isoExtOfHom_disp {Γ Y : C} (p : Y ⟶ Γ) :
    (isoExtOfHom p).hom ≫ disp (ofHom p) = p := by
  exact IsPullback.isoPullback_hom_fst _

end LuTy

/-- **A category with pullbacks is a category with attributes.**  Types are local universes, so
substitution — which acts on the classifying map alone — is strictly functorial, which is what the
codomain fibration itself fails to be.  This is the strictification that turns the semantics of
dependent types into an honest model. -/
@[reducible] noncomputable def Cwa.ofPullbacks (C : Type u) [Category.{v} C] [HasPullbacks C] :
    Cwa.{u, v, max u v} C where
  Ty := LuTy
  tySub := LuTy.sub
  tySub_id := LuTy.sub_id
  tySub_comp := LuTy.sub_comp
  ext := LuTy.ext
  disp := LuTy.disp
  extend := LuTy.extend
  isPullback := LuTy.isPullback_extend
