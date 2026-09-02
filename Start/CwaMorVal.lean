/-
**Values under a morphism of categories with attributes.**

A *value* (`Cwa.Val`) is a pair of a type and a term of it; it is what a de Bruijn variable denotes
in a semantic context (`Start/CwaVar.lean`, `Start/LambdaPiInterp.lean`).  A morphism of categories
with attributes acts on values, and this module proves the two laws that action satisfies:

* `Cwa.Mor.valMap` — the action of a morphism on values;
* `Cwa.Mor.valMap_sub` — **the action commutes with substitution**;
* `Cwa.Mor.valMap_var` — **the generic term is carried to the generic term**, along the comparison
  of extended contexts.  This is the law that makes a morphism of models compatible with the de
  Bruijn reading of a context, and it is proved from the universal property of context extension:
  both sides are terms of the same type, and their induced morphisms into the extended context
  agree.
-/

import Start.LambdaPiInterpHom

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

/-- The action of a morphism of categories with attributes on values. -/
noncomputable def Mor.valMap (F : Mor T S) {Γ : C} (p : Val T Γ) : Val S (F.fnc.obj Γ) :=
  ⟨F.tyMap p.1, F.tmMap p.2⟩

@[simp] theorem Mor.valMap_mk (F : Mor T S) {Γ : C} (A : T.Ty Γ) (x : T.Tm Γ A) :
    F.valMap (⟨A, x⟩ : Val T Γ) = ⟨F.tyMap A, F.tmMap x⟩ := rfl

/-- **The action on values commutes with substitution.** -/
theorem Mor.valMap_sub (F : Mor T S) {Γ Δ : C} (σ : Δ ⟶ Γ) (p : Val T Γ) :
    F.valMap (Val.sub σ p) = Val.sub (F.fnc.map σ) (F.valMap p) := by
  rw [Val.sub, Mor.valMap, Mor.valMap, Val.sub,
    Val.mk_tmCast (F.tyMap_sub σ p.1) (F.tmMap (T.tmSub σ p.2)), F.tmMap_tmSub σ p.2]

/-- **A morphism of categories with attributes carries the generic term to the generic term**,
along its comparison of extended contexts. -/
theorem Mor.valMap_var (F : Mor T S) (co : ExtCoherent S) {Γ : C} (A : T.Ty Γ) :
    F.valMap (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A))
      = Val.sub (F.extIso A).hom
          (⟨S.tySub (S.disp (F.tyMap A)) (F.tyMap A), Cwa.var (F.tyMap A)⟩ :
            Val S (S.ext (F.fnc.obj Γ) (F.tyMap A))) := by
  have hd : (F.extIso A).hom ≫ S.disp (F.tyMap A) = F.fnc.map (T.disp A) := F.extIso_disp A
  -- the right-hand side is the value of a term of the substituted type
  obtain ⟨y, hy, hval⟩ := exists_tm_of_hom co (F.extIso A).hom hd
  rw [hval, Mor.valMap, Val.mk_tmCast (F.tyMap_sub (T.disp A) A) (F.tmMap (Cwa.var A))]
  refine congrArg _ (tm_ext_of_extend (F.fnc.map (T.disp A)) (F.tyMap A) ?_)
  rw [hy, tmCast_val, Category.assoc]
  have hext := F.extIso_extend (T.disp A) A
  rw [Mor.tmMap_val]
  rw [Category.assoc, ← hext, ← Category.assoc, ← F.fnc.map_comp, var_extend, F.fnc.map_id,
    Category.id_comp]

/-- **Transport of the action on extended contexts along an equality of types**, with arbitrary
coherence isomorphisms: this is the shape in which the comparison of a morphism of models with the
action of a substitution is checked. -/
theorem extend_eqToHom_gen {X Y : C} (σ : X ⟶ Y) {A A' : T.Ty Y} (h : A = A')
    {P : C} (p : P = T.ext X (T.tySub σ A)) (q : P = T.ext X (T.tySub σ A'))
    (r : T.ext Y A' = T.ext Y A) :
    eqToHom p ≫ T.extend σ A = eqToHom q ≫ T.extend σ A' ≫ eqToHom r := by
  cases h
  have hr : r = rfl := rfl
  subst hr
  simp

end Cwa
