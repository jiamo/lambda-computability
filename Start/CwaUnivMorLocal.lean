/-
**A functor preserving pullbacks and the terminal object preserves universes.**

`Start/CwaUnivLocal.lean` makes every morphism `p : E ⟶ 𝒰` of a category with pullbacks and a
terminal object into a universe of small types in the strictified model, and `Start/CwaMor.lean`
makes a pullback-preserving functor into a morphism of strictified models.  This file puts the two
together: such a functor carries the universe presented by `p` to the universe presented by
`F.map p`, provided it takes the terminal object to the terminal object *on the nose* — the codes
of a universe are terms of a type whose base is the terminal object, so the comparison is an
equality of presentations and strictness there is needed.

Main results:

* `CwaUniv.preservesUniverseOfHom` — **a pullback-preserving functor which preserves the terminal
  object strictly is a universe-preserving morphism of the strictified models.**
-/

import Start.CwaUnivLocal
import Start.CwaMorUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v'

open CategoryTheory Limits

namespace CwaUniv

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A local universe is determined by its four fields, up to the transports along the equalities
of the base and of the total space. -/
theorem luTy_ext {Γ : C} {A B : LuTy Γ} (hb : A.base = B.base) (ht : A.total = B.total)
    (hp : A.proj ≫ eqToHom hb = eqToHom ht ≫ B.proj) (hc : A.cls ≫ eqToHom hb = B.cls) :
    A = B := by
  obtain ⟨b₁, t₁, p₁, c₁⟩ := A
  obtain ⟨b₂, t₂, p₂, c₂⟩ := B
  cases hb
  cases ht
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hp hc
  cases hp
  cases hc
  rfl

variable (F : C ⥤ D) [HasPullbacks C] [HasPullbacks D] [HasTerminal C] [HasTerminal D]
  [∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F]

omit [HasPullbacks C] [HasPullbacks D]
  [∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F] in
/-- The image of the type of codes is the type of codes, when the terminal object is preserved
strictly. -/
theorem luMap_uTy (hT : F.obj (⊤_ C) = ⊤_ D) (U : C) (Γ : C) :
    Cwa.luMap F (uTy U Γ) = uTy (F.obj U) (F.obj Γ) := by
  refine luTy_ext hT rfl ?_ ?_
  · exact terminal.hom_ext _ _
  · exact terminal.hom_ext _ _

/-- The image of a decoded code is the decoding of the image of the code. -/
theorem luMap_elTy (hT : F.obj (⊤_ C) = ⊤_ D) {E U : C} (p : E ⟶ U) {Γ : C}
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ (uTy U Γ)) :
    Cwa.luMap F (elTy p a)
      = elTy (F.map p)
          (Cwa.tmCast (luMap_uTy F hT U Γ)
            ((Cwa.morOfPullbackPreserving F).tmMap a)) := by
  have hcast := codeOf_tmCast (luMap_uTy F hT U Γ) ((Cwa.morOfPullbackPreserving F).tmMap a)
  have hmain : F.map (codeOf a) = codeOf ((Cwa.morOfPullbackPreserving F).tmMap a) := by
    rw [codeOf, codeOf, Cwa.Mor.tmMap_val, Category.assoc, F.map_comp]
    exact congrArg (fun g => F.map a.1 ≫ g) (Cwa.luExtIso_hom_gen F (uTy U Γ)).symm
  have hcode : F.map (codeOf a)
      = codeOf (Cwa.tmCast (luMap_uTy F hT U Γ)
          ((Cwa.morOfPullbackPreserving F).tmMap a)) := by
    rw [hcast]
    exact hmain.trans (Category.comp_id _).symm
  exact congrArg (fun c => (⟨F.obj U, F.obj E, F.map p, c⟩ : LuTy (F.obj Γ))) hcode

/-- **A pullback-preserving functor which preserves the terminal object strictly preserves the
universes** of the strictified models. -/
theorem preservesUniverseOfHom (hT : F.obj (⊤_ C) = ⊤_ D) {E U : C} (p : E ⟶ U) :
    (Cwa.morOfPullbackPreserving F).PreservesUniverse (universeOfHom p)
      (universeOfHom (F.map p)) where
  U_map Γ := luMap_uTy F hT U Γ
  El_map a := luMap_elTy F hT p a

end CwaUniv
