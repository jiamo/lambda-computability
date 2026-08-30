/-
**Initiality: the syntax of `λΠ` maps to every model.**

`Start/LambdaPiInterpTotal.lean` and `Start/LambdaPiInterpHom.lean` interpret the contexts, the
types, the terms and the substitutions of `λΠ` in an arbitrary model, and prove that each of these
interpretations exists and is unique.  This module packages them: it builds, out of that data, a
**morphism of categories with attributes** from the syntactic model of `Start/LambdaPiFull.lean` to
the underlying category with attributes of any model with injective products.

* `LambdaPiInitial.obj`, `LambdaPiInitial.sem` — the object and the semantic context interpreting a
  well-formed context, chosen once and for all by recursion on the context;
* `LambdaPiInitial.homMap` — the morphism interpreting a substitution;
* `LambdaPiInitial.functor : LambdaPiCat.Ob ⥤ C` — **the interpretation is a functor**; that it
  preserves identities and composites is exactly the uniqueness of the interpretation of a
  substitution;
* `LambdaPiInitial.tyMap` — the type of the model interpreting a syntactic type, and
  `LambdaPiInitial.tyMap_sub` its stability under substitution;
* `LambdaPiInitial.mor : Cwa.Mor LambdaPiFull.syntactic M.T` — **the comparison morphism of
  categories with attributes**.  Its action on terms (`Cwa.Mor.tmMap`) and the compatibility of
  that action with substitution come for free from `Start/CwaMor.lean`.

Everything rests on uniqueness: two morphisms of the model carrying the same substitution are
equal, so each equation to be checked reduces to computing which raw substitution the two sides
carry.
-/

import Start.LambdaPiInterpHom
import Start.LambdaPiUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### Two more ways of carrying a substitution -/

/-- **Weakening is carried by the display map.** -/
theorem SubI.weaken {Γ' : C} (s : SemCtx M Γ') (A' : M.T.Ty Γ') :
    SubI s (s.cons A') (M.T.disp A') (fun n => Tm.var (n + 1)) := by
  intro n p hp
  exact TmI.var (by simp [SemCtx.varVal, hp])

/-- **Lifting a substitution under a binder is carried by the action on extended contexts.**  This
is `LambdaPi.SubI.up` for an arbitrary type of the model in place of a decoded code. -/
theorem SubI.upTy {Γ' Δ' : C} {s : SemCtx M Γ'} {r : SemCtx M Δ'} {σ : Δ' ⟶ Γ'} {f : ℕ → Tm}
    (h : SubI s r σ f) (A' : M.T.Ty Γ') :
    SubI (s.cons A') (r.cons (M.T.tySub σ A')) (M.T.extend σ A') (LambdaPi.up f) := by
  intro n p hp
  cases n with
  | zero =>
      simp only [SemCtx.varVal, Option.some.injEq] at hp
      subst hp
      exact TmI.var (by rw [SemCtx.varVal, M.co.val_sub_var σ A'])
  | succ m =>
      simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine TmI.cast_val ((h m q hq).weaken (M.T.tySub σ A')) ?_
      change Cwa.Val.sub (M.T.disp (M.T.tySub σ A')) (Cwa.Val.sub σ q)
          = Cwa.Val.sub (M.T.extend σ A') (Cwa.Val.sub (M.T.disp A') q)
      rw [M.co.val_sub_comp, M.co.val_sub_comp, (M.T.isPullback σ A').w]

/-! ### Transporting a carried substitution along an identification of semantic contexts -/

/-- Transporting the target of a carried substitution. -/
theorem SubI.congr_tgt {Γ₁ Γ₂ Δ' : C} {s₁ : SemCtx M Γ₁} {s₂ : SemCtx M Γ₂} {r : SemCtx M Δ'}
    (h : (⟨Γ₁, s₁⟩ : (X : C) × SemCtx M X) = ⟨Γ₂, s₂⟩) {σ : Δ' ⟶ Γ₁} {f : ℕ → Tm}
    (hσ : SubI s₁ r σ f) : SubI s₂ r (σ ≫ eqToHom (congrArg Sigma.fst h)) f := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  cases eq_of_heq h2
  simpa using hσ

/-- Transporting the source of a carried substitution. -/
theorem SubI.congr_src {Γ' Δ₁ Δ₂ : C} {s : SemCtx M Γ'} {r₁ : SemCtx M Δ₁} {r₂ : SemCtx M Δ₂}
    (h : (⟨Δ₁, r₁⟩ : (X : C) × SemCtx M X) = ⟨Δ₂, r₂⟩) {σ : Δ₁ ⟶ Γ'} {f : ℕ → Tm}
    (hσ : SubI s r₁ σ f) : SubI s r₂ (eqToHom (congrArg Sigma.fst h).symm ≫ σ) f := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  subst h1
  cases eq_of_heq h2
  simpa using hσ

end LambdaPi

namespace LambdaPiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### The interpretation of a context -/

/-- The interpretation of a well-formed context, chosen once and for all by recursion on it: an
object of the model together with the semantic context reading its de Bruijn variables. -/
noncomputable def ctxAux (hinj : M.PiInj) :
    (Γ : Ctx) → Wf Γ → {p : (Γ' : C) × SemCtx M Γ' // CtxI Γ p.2}
  | [], _ => ⟨⟨M.emp, SemCtx.nil⟩, CtxI.nil⟩
  | A :: Γ, h =>
      let r := ctxAux hinj Γ (by cases h with | cons hΓ _ => exact hΓ)
      let e : ∃ A' : M.T.Ty r.1.1, TyI r.1.2 A A' := by
        cases h with | cons _ hA => exact TyI.total hinj hA r.2
      ⟨⟨M.T.ext r.1.1 e.choose, r.1.2.cons e.choose⟩, CtxI.cons r.2 e.choose_spec⟩

variable (hinj : M.PiInj)

/-- The object of the model interpreting a context. -/
noncomputable def obj (Γ : Ob) : C := (ctxAux hinj Γ.ctx Γ.wf).1.1

/-- The semantic context interpreting a context. -/
noncomputable def sem (Γ : Ob) : SemCtx M (obj hinj Γ) := (ctxAux hinj Γ.ctx Γ.wf).1.2

/-- The chosen interpretation of a context is an interpretation of it. -/
theorem sem_spec (Γ : Ob) : CtxI Γ.ctx (sem hinj Γ) := (ctxAux hinj Γ.ctx Γ.wf).2

/-! ### The interpretation of a type -/

/-- The type of the model interpreting a syntactic type. -/
noncomputable def tyMap {Γ : Ob} (A : TyQ Γ) : M.T.Ty (obj hinj Γ) :=
  (TyI.total hinj A.rep.ok (sem_spec hinj Γ)).choose

/-- The chosen interpretation of a type is an interpretation of it. -/
theorem tyMap_spec {Γ : Ob} (A : TyQ Γ) : TyI (sem hinj Γ) A.rep.ty (tyMap hinj A) :=
  (TyI.total hinj A.rep.ok (sem_spec hinj Γ)).choose_spec

/-- Any interpretation of a syntactic type is the chosen one. -/
theorem tyMap_eq {Γ : Ob} (A : TyQ Γ) {A' : M.T.Ty (obj hinj Γ)} {t : Tm} (hc : Conv A.rep.ty t)
    (h : TyI (sem hinj Γ) t A') : tyMap hinj A = A' :=
  TyI.conv_eq hinj hc (tyMap_spec hinj A) h

/-- **The interpretation of an extended context is the extension by the interpretation of the new
type.** -/
theorem ctxI_ext {Γ : Ob} (A : TyQ Γ) :
    (⟨obj hinj (extOb Γ A), sem hinj (extOb Γ A)⟩ : (X : C) × SemCtx M X)
      = ⟨M.T.ext (obj hinj Γ) (tyMap hinj A), (sem hinj Γ).cons (tyMap hinj A)⟩ :=
  CtxI.unique (functional_of_piInj hinj) (sem_spec hinj (extOb Γ A))
    (CtxI.cons (sem_spec hinj Γ) (tyMap_spec hinj A))

/-- The object interpreting an extended context. -/
theorem objExt {Γ : Ob} (A : TyQ Γ) :
    obj hinj (extOb Γ A) = M.T.ext (obj hinj Γ) (tyMap hinj A) :=
  congrArg Sigma.fst (ctxI_ext hinj A)

/-! ### The interpretation of a substitution -/

/-- The morphism of the model interpreting a substitution. -/
noncomputable def homMap {Δ Γ : Ob} (σ : Δ ⟶ Γ) : obj hinj Δ ⟶ obj hinj Γ :=
  (SubI.total hinj (sem_spec hinj Γ) (sem_spec hinj Δ) σ.out.ok).choose

/-- The chosen interpretation of a substitution carries it. -/
theorem homMap_spec {Δ Γ : Ob} (σ : Δ ⟶ Γ) :
    SubI (sem hinj Γ) (sem hinj Δ) (homMap hinj σ) σ.out.sub :=
  (SubI.total hinj (sem_spec hinj Γ) (sem_spec hinj Δ) σ.out.ok).choose_spec

/-- Any morphism carrying a substitution convertible to `σ` is the interpretation of `σ`. -/
theorem homMap_eq {Δ Γ : Ob} (σ : Δ ⟶ Γ) {u : obj hinj Δ ⟶ obj hinj Γ} {f : ℕ → Tm}
    (hconv : ∀ n, n < Γ.ctx.length → Conv (σ.out.sub n) (f n))
    (hu : SubI (sem hinj Γ) (sem hinj Δ) u f) : homMap hinj σ = u :=
  SubI.conv_eq hinj (sem_spec hinj Γ) hconv (homMap_spec hinj σ) hu

/-- **The interpretation of contexts and substitutions is a functor.** -/
noncomputable def functor : Ob ⥤ C where
  obj := obj hinj
  map σ := homMap hinj σ
  map_id Γ := homMap_eq hinj (𝟙 Γ) (fun _ hn => id_out_conv (𝟙 Γ) rfl hn) (SubI.id _)
  map_comp f g :=
    homMap_eq hinj (f ≫ g) (fun _ hn => comp_out_conv f g hn)
      ((homMap_spec hinj g).comp (homMap_spec hinj f))

@[simp] theorem functor_obj (Γ : Ob) : (functor hinj).obj Γ = obj hinj Γ := rfl

@[simp] theorem functor_map {Δ Γ : Ob} (σ : Δ ⟶ Γ) :
    (functor hinj).map σ = homMap hinj σ := rfl

/-! ### The comparison is a morphism of categories with attributes -/

/-- **The interpretation of a type is stable under substitution**, on the nose. -/
theorem tyMap_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    tyMap hinj (tySubQ σ A) = M.T.tySub (homMap hinj σ) (tyMap hinj A) :=
  tyMap_eq hinj (tySubQ σ A) (tySubQ_rep_conv σ A)
    ((tyMap_spec hinj A).subst (homMap_spec hinj σ))

/-- **The display map of the syntax is interpreted by the display map of the model.** -/
theorem homMap_dispQ {Γ : Ob} (A : TyQ Γ) :
    homMap hinj (dispQ A) = eqToHom (objExt hinj A) ≫ M.T.disp (tyMap hinj A) := by
  have hu : SubI (sem hinj Γ) (sem hinj (extOb Γ A))
      (eqToHom (objExt hinj A) ≫ M.T.disp (tyMap hinj A)) (fun n => Tm.var (n + 1)) := by
    have h := SubI.congr_src (ctxI_ext hinj A).symm (SubI.weaken (sem hinj Γ) (tyMap hinj A))
    simpa using h
  exact homMap_eq hinj (dispQ A) (fun _ hn => hom_out_conv (g := dispRaw Γ A.rep.ok) rfl hn) hu

/-- **The action of a substitution on extended contexts is interpreted by the action of the model
on extended contexts.** -/
theorem homMap_extendQ {Γ Δ : Ob} (σ : Δ ⟶ Γ) (A : TyQ Γ) :
    homMap hinj (extendQ σ A)
      = eqToHom ((objExt hinj (tySubQ σ A)).trans
            (congrArg (M.T.ext (obj hinj Δ)) (tyMap_sub hinj σ A)))
          ≫ M.T.extend (homMap hinj σ) (tyMap hinj A) ≫ eqToHom (objExt hinj A).symm := by
  have hsrc : (⟨obj hinj (extOb Δ (tySubQ σ A)), sem hinj (extOb Δ (tySubQ σ A))⟩ :
        (X : C) × SemCtx M X)
      = ⟨M.T.ext (obj hinj Δ) (M.T.tySub (homMap hinj σ) (tyMap hinj A)),
          (sem hinj Δ).cons (M.T.tySub (homMap hinj σ) (tyMap hinj A))⟩ := by
    rw [ctxI_ext hinj (tySubQ σ A), tyMap_sub hinj σ A]
  have hu := SubI.congr_src hsrc.symm
    (SubI.congr_tgt (ctxI_ext hinj A).symm ((homMap_spec hinj σ).upTy (tyMap hinj A)))
  refine homMap_eq hinj (extendQ σ A) (fun _ hn => extendQ_out_conv σ A hn) ?_
  simpa using hu

/-- Cancelling a pair of inverse coherence isomorphisms on the right of a composite. -/
private theorem eqToHom_cancel_right {X Y V W : C} (p : X = Y) (h : W = V) (g : Y ⟶ V) :
    (eqToHom p ≫ g ≫ eqToHom h.symm) ≫ eqToHom h = eqToHom p ≫ g := by
  cases p; cases h; simp

/-- Splitting a coherence isomorphism along a composite of equalities. -/
private theorem eqToHom_trans_comp {X Y Z W : C} (p₁ : X = Y) (p₂ : Y = Z) (g : Z ⟶ W) :
    eqToHom (p₁.trans p₂) ≫ g = eqToHom p₁ ≫ eqToHom p₂ ≫ g := by
  cases p₁; cases p₂; simp

/-- **The comparison morphism of categories with attributes**: the syntax of `λΠ` is interpreted in
any model with injective products, compatibly with substitution and context extension. -/
noncomputable def mor : Cwa.Mor LambdaPiFull.syntactic M.T where
  fnc := functor hinj
  tyMap A := tyMap hinj A
  tyMap_sub σ A := tyMap_sub hinj σ A
  extIso A := eqToIso (objExt hinj A)
  extIso_disp A := by
    rw [functor_map, homMap_dispQ hinj A]
    rfl
  extIso_extend σ A := by
    simp only [functor_map]
    rw [homMap_extendQ hinj σ A]
    exact (eqToHom_cancel_right _ (objExt hinj A) _).trans
      (eqToHom_trans_comp (objExt hinj (tySubQ σ A)) _ _)

end LambdaPiInitial
