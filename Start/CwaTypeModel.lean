/-
**A set-theoretic model of `λΠ`.**

`Start/CwaCodePi.lean` isolates what the small fragment of a model with a universe needs in order
to interpret the dependent product of `λΠ`: a code for the product of two small types, stable
under substitution, whose terms are the terms of the body in the extended context.  This module
builds the model that satisfies it, and it is the *standard* one:

* contexts are types of `Type (u + 1)`;
* a type in a context `Γ` is a family `Γ → Type u` of **small** types, presented as a map into the
  universe object `Type u`;
* the extended context is the total space `Σ x : Γ, A x`, and a term is a dependent function;
* the product of `a` and `b` is the family `x ↦ (y : a x) → b ⟨x, y⟩`.

The size discipline is what makes this work.  A universe of small types cannot be a *family of
types* of the model — `Type u` is not an element of `Type u` — so the naive model of families
(`Start/CwaType.lean`) has no universe at all.  In the strictified model of
`Start/CwaLocalUniverse.lean` a type is a *presentation*, a classifying map into a local universe,
so the universe object may be the large object `Type u : Type (u + 1)`; decoding a code is taking
a pullback, and the total space of a small family over a large context is again large.  The
product of two codes is then the pointwise dependent function type, which is small again *on the
nose* — no lifting is needed, and the coherence problem does not reappear.

Main definitions and results:

* `CwaUniv.tmSectionEquiv` — in the strictified model of any category with pullbacks, a term is a
  section of the generic family of the presentation, i.e. its code;
* `CwaTypeModel.extIso` — the extended context of a code is the total space of the family it
  names, and `CwaTypeModel.extIso_extHom` computes the action of a substitution on it;
* `CwaTypeModel.elTmEquiv` — the terms of a code are the dependent functions;
* `CwaTypeModel.codePi` — **the universe of small types is closed under dependent products**, in
  the sense of `Cwa.Universe.CodePi`;
* `CwaTypeModel.piLam_sub` — **abstraction commutes with substitution**;
* `CwaTypeModel.model`, `CwaTypeModel.modelPi`, `CwaTypeModel.modelPiEta`,
  `CwaTypeModel.modelPiNatural` — hence **a set-theoretic model of `λΠ`**: the category with
  attributes whose types in `Γ` are the maps `Γ ⟶ Type u`, with a dependent product satisfying the
  β-rule, the η-rule and the naturality of abstraction;
* `CwaTypeModel.modelTyEquiv`, `CwaTypeModel.modelTmEquiv`, `CwaTypeModel.fam_modelPi_Pi` — the
  model computed: its types are the small families, its terms are the dependent functions, and its
  product is the dependent function type.
-/

import Start.CwaCodePi
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

/-- Equal morphisms of the category of types agree pointwise. -/
theorem types_hom_congr_fun.{w} {X Y : Type w} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : X → Y)) h) x

/-- Morphisms of the category of types that agree pointwise are equal. -/
theorem types_hom_ext.{w} {X Y : Type w} {f g : X ⟶ Y} (h : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext f g h

/-! ### Terms of the strictified model are sections of the generic family -/

namespace CwaUniv

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **A term of the strictified model is a section of the generic family**: it is determined by
its code, a map into the total space of the presentation lying over the classifying map. -/
noncomputable def tmSectionEquiv {Γ : C} (A : LuTy Γ) :
    Cwa.Tm (Cwa.ofPullbacks C) Γ A ≃ {f : Γ ⟶ A.total // f ≫ A.proj = A.cls} where
  toFun a := ⟨codeOf a, by
    rw [codeOf, Category.assoc, ← LuTy.disp_cls, ← Category.assoc, a.2, Category.id_comp]⟩
  invFun f := ⟨pullback.lift (𝟙 Γ) f.1 (by rw [Category.id_comp, f.2]), pullback.lift_fst _ _ _⟩
  left_inv a := by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans a.2.symm
    · exact pullback.lift_snd _ _ _
  right_inv f := Subtype.ext (pullback.lift_snd _ _ _)

@[simp] theorem tmSectionEquiv_apply_coe {Γ : C} (A : LuTy Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ A) : ((tmSectionEquiv A) a : Γ ⟶ A.total) = codeOf a := rfl

omit [HasPullbacks C] in
/-- Transport of the generic element along an equality of presentations. -/
theorem eqToHom_gen {Γ : C} {A A' : LuTy Γ} (h : A = A') [HasPullbacks C] :
    eqToHom (congrArg (LuTy.ext Γ) h).symm ≫ LuTy.gen A
      = LuTy.gen A' ≫ eqToHom (congrArg LuTy.total h).symm := by
  cases h; simp

variable [HasTerminal C]

/-- The code of a substituted code is the substituted code. -/
theorem codeOf_universeSub {E U : C} (p : E ⟶ U) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ ((universeOfHom p).U Γ)) :
    codeOf ((universeOfHom p).sub σ a) = σ ≫ codeOf a := by
  simp only [Cwa.Universe.sub, codeOf_tmCast]
  exact Eq.trans (Category.comp_id _) (codeOf_tmSub σ a)

/-- The action of a substitution on an extended context preserves the generic element. -/
theorem extHom_gen {E U : C} (p : E ⟶ U) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ ((universeOfHom p).U Γ)) :
    (universeOfHom p).extHom σ a ≫ LuTy.gen ((universeOfHom p).El a)
      = LuTy.gen ((universeOfHom p).El ((universeOfHom p).sub σ a)) := by
  simp only [Cwa.Universe.extHom, Category.assoc]
  rw [LuTy.extend_gen]
  exact (eqToHom_gen (Cwa.Universe.El_sub' (universeOfHom p) σ a)).trans (Category.comp_id _)

/-- The action of a substitution on an extended context lies over the substitution. -/
theorem extHom_disp {E U : C} (p : E ⟶ U) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) Γ ((universeOfHom p).U Γ)) :
    (universeOfHom p).extHom σ a ≫ LuTy.disp ((universeOfHom p).El a)
      = LuTy.disp ((universeOfHom p).El ((universeOfHom p).sub σ a)) ≫ σ :=
  ((universeOfHom p).isPullback_extHom σ a).w

end CwaUniv

/-! ### The model -/

namespace CwaTypeModel

open CwaUniv

/-- The universe object: the type of small types. -/
abbrev Uob : Type (u + 1) := Type u

/-- Its total space: the pointed small types. -/
abbrev Eob : Type (u + 1) := Σ A : Type u, A

/-- The generic family of small types. -/
abbrev genHom : Eob.{u} ⟶ Uob.{u} := ↾CwaUniv.genFam

/-- The ambient strictified model: the category with attributes of `Type (u + 1)`. -/
noncomputable abbrev amb : Cwa (Type (u + 1)) := Cwa.ofPullbacks (Type (u + 1))

/-- The universe of small types in the ambient model. -/
noncomputable abbrev un : Cwa.Universe amb.{u} := universeOfHom genHom.{u}

/-- **The set-theoretic model of `λΠ`**: the category with attributes on `Type (u + 1)` whose
types in a context are the codes for small types, i.e. the families of small types. -/
noncomputable def model : Cwa (Type (u + 1)) := smallCwaOfHom genHom.{u}

variable {Γ Δ : Type (u + 1)}

/-- The small family named by a code. -/
noncomputable abbrev fam (a : Cwa.Tm amb Γ (un.U Γ)) : Γ ⟶ Uob.{u} := codeOf a

/-! #### The extended context is the total space -/

/-- The total space of a small family. -/
abbrev sigObj (ca : Γ ⟶ Uob.{u}) : Type (u + 1) := (Σ x : Γ, ca x : Type (u + 1))

/-- The point of the generic family named by a point of the total space. -/
abbrev sigTot (ca : Γ ⟶ Uob.{u}) : sigObj ca → Eob.{u} := fun z => ⟨ca z.1, z.2⟩

theorem isPullback_sig (ca : Γ ⟶ Uob.{u}) :
    IsPullback (↾sigTot ca) (↾(Sigma.fst : sigObj ca → Γ)) genHom ca := by
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨h₁, h₂⟩
    cases h₂
    simpa using h₁
  · rintro ⟨A, y⟩ x hx
    subst hx
    exact ⟨⟨x, y⟩, rfl, rfl⟩

/-- **The extended context of a code is the total space of the family it names.** -/
noncomputable def extIso (a : Cwa.Tm amb Γ (un.U Γ)) : sigObj (fam a) ≅ amb.ext Γ (un.El a) :=
  IsPullback.isoIsPullback _ _ (isPullback_sig (fam a)) (LuTy.isPullback_gen (un.El a))

theorem extIso_hom_gen (a : Cwa.Tm amb Γ (un.U Γ)) :
    (extIso a).hom ≫ LuTy.gen (un.El a) = ↾sigTot (fam a) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

theorem extIso_hom_disp (a : Cwa.Tm amb Γ (un.U Γ)) :
    (extIso a).hom ≫ LuTy.disp (un.El a) = ↾(Sigma.fst : sigObj (fam a) → Γ) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

theorem sigma_cast_eta {A : Type u} (z : Eob.{u}) (h : z.1 = A) :
    (⟨A, cast h z.2⟩ : Eob.{u}) = z := by
  obtain ⟨B, y⟩ := z
  cases h
  rfl

theorem fam_sub (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ)) :
    fam (un.sub σ a) = σ ≫ fam a := codeOf_universeSub genHom σ a

/-- Reindexing a point of a total space along a substitution. -/
noncomputable abbrev sigShift (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ)) :
    sigObj (fam (un.sub σ a)) ⟶ sigObj (fam a) :=
  ↾fun z => (⟨σ z.1, cast (types_hom_congr_fun (fam_sub σ a) z.1) z.2⟩ : sigObj (fam a))

/-- **The action of a substitution on the extended context, computed on total spaces.** -/
theorem extIso_extHom (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ)) :
    (extIso (un.sub σ a)).hom ≫ un.extHom σ a = sigShift σ a ≫ (extIso a).hom := by
  have e1 : (extIso (un.sub σ a)).hom ≫ un.extHom σ a ≫ LuTy.gen (un.El a)
      = ↾sigTot (fam (un.sub σ a)) := by
    rw [extHom_gen]
    exact extIso_hom_gen _
  have e2 : (extIso (un.sub σ a)).hom ≫ un.extHom σ a ≫ LuTy.disp (un.El a)
      = ↾(Sigma.fst : sigObj (fam (un.sub σ a)) → Δ) ≫ σ := by
    rw [extHom_disp, ← Category.assoc, extIso_hom_disp]
  refine (LuTy.isPullback_gen (un.El a)).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, e1, extIso_hom_gen]
    refine types_hom_ext fun z => ?_
    exact (sigma_cast_eta (⟨_, z.2⟩ : Eob.{u}) (types_hom_congr_fun (fam_sub σ a) z.1)).symm
  · rw [Category.assoc, Category.assoc, e2, extIso_hom_disp]
    rfl

/-- The action of a substitution on the extended context, at a point. -/
theorem extHom_apply (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ))
    (z : sigObj (fam (un.sub σ a))) :
    (un.extHom σ a) ((extIso (un.sub σ a)).hom z)
      = (extIso a).hom ⟨σ z.1, cast (types_hom_congr_fun (fam_sub σ a) z.1) z.2⟩ := by
  have h := types_hom_congr_fun (extIso_extHom σ a) z
  simp only [types_comp_apply] at h
  exact h

/-! #### Terms are dependent functions -/

/-- **Sections of the generic family are dependent functions.** -/
def famSectionEquiv (c : Γ ⟶ Uob.{u}) :
    {f : Γ ⟶ Eob.{u} // f ≫ genHom = c} ≃ ∀ x : Γ, c x where
  toFun f := fun x => cast (types_hom_congr_fun f.2 x) (f.1 x).2
  invFun g := ⟨↾fun x => ⟨c x, g x⟩, rfl⟩
  left_inv f := by
    refine Subtype.ext (types_hom_ext fun x => ?_)
    have h : (f.1 x).1 = c x := types_hom_congr_fun f.2 x
    exact sigma_cast_eta (f.1 x) h
  right_inv g := by funext x; rfl

/-- **The terms of a code are the dependent functions of the family it names.** -/
noncomputable def elTmEquiv (a : Cwa.Tm amb Γ (un.U Γ)) :
    Cwa.Tm amb Γ (un.El a) ≃ ∀ x : Γ, fam a x :=
  (tmSectionEquiv (un.El a)).trans (famSectionEquiv (fam a))

/-- The codes in a context are the maps into the universe object. -/
noncomputable def codeEquiv (Γ : Type (u + 1)) : Cwa.Tm amb Γ (un.U Γ) ≃ (Γ ⟶ Uob.{u}) :=
  smallTyEquivHom genHom Γ

@[simp] theorem codeEquiv_apply (a : Cwa.Tm amb Γ (un.U Γ)) : codeEquiv Γ a = fam a := rfl

@[simp] theorem fam_codeEquiv_symm (f : Γ ⟶ Uob.{u}) : fam ((codeEquiv Γ).symm f) = f :=
  (codeEquiv Γ).apply_symm_apply f

theorem code_ext {a a' : Cwa.Tm amb Γ (un.U Γ)} (h : fam a = fam a') : a = a' :=
  (codeEquiv Γ).injective h

/-! #### The universe of small types is closed under dependent products -/

/-- Equality of dependent function types, from an equality of domains and of bodies. -/
theorem pi_type_congr {A A' : Type u} (h : A = A') {B : A → Type u} {B' : A' → Type u}
    (hB : ∀ y : A, B y = B' (cast h y)) : ((y : A) → B y) = ((y : A') → B' y) := by
  cases h
  exact congrArg (fun F : A → Type u => ((y : A) → F y)) (funext hB)

/-- Transport of a dependent function along an equality of arguments. -/
theorem cast_dep {α : Type (u + 1)} {F : α → Type u} (g : ∀ z, F z) {z z' : α} (e : z = z') :
    cast (congrArg F e) (g z) = g z' := by
  cases e; rfl

/-- The family of dependent function types: the product of a code `a` and a code `b` over its
total space. -/
noncomputable abbrev piFam (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) : Γ ⟶ Uob.{u} :=
  ↾fun x => ((y : fam a x) → fam b ((extIso a).hom ⟨x, y⟩))

/-- The code of the dependent product of two codes. -/
noncomputable def piCode (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    Cwa.Tm amb Γ (un.U Γ) := (codeEquiv Γ).symm (piFam a b)

@[simp] theorem fam_piCode (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    fam (piCode a b) = piFam a b := fam_codeEquiv_symm _

/-- The terms of the product code are the dependent functions of two arguments. -/
noncomputable def piTmEquiv (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    Cwa.Tm amb Γ (un.El (piCode a b))
      ≃ ∀ x : Γ, (y : fam a x) → fam b ((extIso a).hom ⟨x, y⟩) :=
  (elTmEquiv (piCode a b)).trans (Equiv.cast (by rw [fam_piCode]; try rfl))

/-- **The code of a product is stable under substitution.** -/
theorem piCode_sub (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    un.sub σ (piCode a b) = piCode (un.sub σ a) (un.sub (un.extHom σ a) b) := by
  refine code_ext ?_
  rw [fam_sub]
  simp only [fam_piCode]
  refine types_hom_ext fun x => ?_
  refine pi_type_congr (types_hom_congr_fun (fam_sub σ a) x).symm fun y => ?_
  set y' : fam (un.sub σ a) x := cast (types_hom_congr_fun (fam_sub σ a) x).symm y
  have hb : fam (un.sub (un.extHom σ a) b) = un.extHom σ a ≫ fam b :=
    fam_sub (un.extHom σ a) b
  have h1 := types_hom_congr_fun hb ((extIso (un.sub σ a)).hom ⟨x, y'⟩)
  have h2 := extHom_apply σ a ⟨x, y'⟩
  simp only [types_comp_apply] at h1
  rw [h1, h2]
  refine congrArg (ConcreteCategory.hom (fam b)) ?_
  refine congrArg (ConcreteCategory.hom (extIso a).hom) ?_
  refine Sigma.ext rfl ?_
  exact ((cast_heq _ _).trans (cast_heq _ _)).symm

/-- Abstraction: a dependent function of two arguments is a term of the product code. -/
noncomputable def piLam (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (x : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.El b)) :
    Cwa.Tm amb Γ (un.El (piCode a b)) :=
  (piTmEquiv a b).symm fun p y => (elTmEquiv b) x ((extIso a).hom ⟨p, y⟩)

/-- Application to the generic argument: a term of the product code is a term of the body in the
extended context. -/
noncomputable def piApp (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (f : Cwa.Tm amb Γ (un.El (piCode a b))) :
    Cwa.Tm amb (amb.ext Γ (un.El a)) (un.El b) :=
  (elTmEquiv b).symm fun w =>
    cast (congrArg (fun w' => fam b w') (types_hom_congr_fun (extIso a).inv_hom_id w))
      ((piTmEquiv a b) f ((extIso a).inv w).1 ((extIso a).inv w).2)

/-- **β** for the product of codes. -/
theorem piApp_piLam (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (x : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.El b)) : piApp a b (piLam a b x) = x := by
  refine (elTmEquiv b).injective ?_
  refine funext fun w => ?_
  rw [piApp, piLam, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact cast_dep (fun w' => (elTmEquiv b) x w') (types_hom_congr_fun (extIso a).inv_hom_id w)

/-- **η** for the product of codes: a term of the product code is its own η-expansion. -/
theorem piLam_piApp (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (f : Cwa.Tm amb Γ (un.El (piCode a b))) : piLam a b (piApp a b f) = f := by
  refine (piTmEquiv a b).injective ?_
  rw [piLam, Equiv.apply_symm_apply]
  refine funext fun p => funext fun y => ?_
  rw [piApp]
  simp only [Equiv.apply_symm_apply]
  exact cast_dep (fun z : sigObj (fam a) => (piTmEquiv a b) f z.1 z.2)
    (types_hom_congr_fun (extIso a).hom_inv_id (⟨p, y⟩ : sigObj (fam a)))

/-! #### Substitution -/

/-- Applying a transported dependent function. -/
theorem cast_pi_apply {α : Type (u + 1)} {B B' : α → Type u} (hB : B = B') (g : ∀ z, B z)
    (p : α) (hT : (∀ z, B z) = (∀ z, B' z)) (h : B p = B' p) : cast hT g p = cast h (g p) := by
  cases hB; rfl

/-- Two transported dependent functions agree if they agree pointwise. -/
theorem cast_pi_ext {A A' : Type u} (hA : A = A') {B : A → Type u} {B' : A' → Type u}
    (hB : ∀ y : A, B y = B' (cast hA y)) (g : (y : A) → B y) (g' : (y : A') → B' y)
    (hg : ∀ y : A, cast (hB y) (g y) = g' (cast hA y))
    (hT : ((y : A) → B y) = ((y : A') → B' y)) : cast hT g = g' := by
  cases hA
  have hBB : B = B' := funext hB
  cases hBB
  exact funext hg

/-- Transport along an equality of types is injective. -/
theorem cast_left_cancel {X Y : Type u} (h : X = Y) {v w : X} (hvw : cast h v = cast h w) :
    v = w := by cases h; exact hvw

/-- Transporting back and forth is the identity. -/
theorem cast_symm_cast {X Y : Type u} (h : X = Y) (v : X) : cast h.symm (cast h v) = v := by
  cases h; rfl

theorem fam_piCode_apply (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) (p : Γ) :
    (fam (piCode a b)) p = ((y : fam a p) → fam b ((extIso a).hom ⟨p, y⟩)) := by
  rw [fam_piCode]
  try rfl

theorem fam_piCode_fun (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    (fun p => (fam (piCode a b)) p)
      = fun p => ((y : fam a p) → fam b ((extIso a).hom ⟨p, y⟩)) := by
  rw [fam_piCode]
  try rfl

/-- **An abstraction is the dependent function it abstracts**, read through the identification of
the family named by the product code with the dependent function type. -/
theorem elTmEquiv_piLam_apply (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (x : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.El b)) (p : Γ)
    (h : (fam (piCode a b)) p = ((y : fam a p) → fam b ((extIso a).hom ⟨p, y⟩))) :
    cast h ((elTmEquiv (piCode a b)) (piLam a b x) p)
      = fun y => (elTmEquiv b) x ((extIso a).hom ⟨p, y⟩) := by
  have hF : (piTmEquiv a b) (piLam a b x) = fun p y => (elTmEquiv b) x ((extIso a).hom ⟨p, y⟩) := by
    rw [piLam, Equiv.apply_symm_apply]
  rw [← cast_pi_apply (fam_piCode_fun a b) ((elTmEquiv (piCode a b)) (piLam a b x)) p
      (congrArg (fun F : Γ → Type u => ∀ z, F z) (fam_piCode_fun a b)) h]
  exact congrFun hF p

/-- The code of a substituted term is the substituted code. -/
theorem codeOf_model_tmSub (σ : Δ ⟶ Γ) {a : model.Ty Γ} (x : Cwa.Tm model Γ a) :
    codeOf (Cwa.tmSub (T := model) σ x) = σ ≫ codeOf x := by
  have h : Cwa.tmSub (T := model) σ x
      = Cwa.tmCast (T := amb) (un.El_sub' σ a) (Cwa.tmSub (T := amb) σ x) :=
    Cwa.Universe.smallCwa_tmSub (Cwa.extCoherent_ofPullbacks _) un σ x
  refine Eq.trans (congrArg codeOf h) ?_
  refine Eq.trans (codeOf_tmCast (un.El_sub' σ a) (Cwa.tmSub (T := amb) σ x)) ?_
  exact Eq.trans (Category.comp_id _) (codeOf_tmSub σ x)

/-- **Substituting in a term precomposes the dependent function it denotes.** -/
theorem elTmEquiv_model_tmSub (σ : Δ ⟶ Γ) (a : model.Ty Γ) (x : Cwa.Tm model Γ a) (d : Δ) :
    (elTmEquiv (un.sub σ a)) (Cwa.tmSub (T := model) σ x) d
      = cast (types_hom_congr_fun (fam_sub σ a) d).symm ((elTmEquiv a) x (σ d)) := by
  have hx : codeOf x ≫ genHom = fam a := ((tmSectionEquiv (un.El a)) x).2
  have hpf : (σ ≫ codeOf x) ≫ genHom = fam (un.sub σ a) :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun t => σ ≫ t) hx) (fam_sub σ a).symm)
  have hc : (tmSectionEquiv (un.El (un.sub σ a))) (Cwa.tmSub (T := model) σ x)
      = ⟨σ ≫ codeOf x, hpf⟩ := Subtype.ext (codeOf_model_tmSub σ x)
  change (famSectionEquiv (fam (un.sub σ a)))
      ((tmSectionEquiv (un.El (un.sub σ a))) (Cwa.tmSub (T := model) σ x)) d = _
  rw [hc]
  exact (cast_cast _ _ _).symm

/-- Transporting a term along an equality of codes transports the dependent function it
denotes. -/
theorem elTmEquiv_model_tmCast {a a' : model.Ty Γ} (h : a = a') (x : Cwa.Tm model Γ a) (d : Γ) :
    (elTmEquiv a') (Cwa.tmCast (T := model) h x) d
      = cast (congrArg (fun c : model.Ty Γ => (fam c) d) h) ((elTmEquiv a) x d) := by
  cases h; rfl

/-- **Abstraction commutes with substitution.** -/
theorem piLam_sub (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (x : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.El b)) :
    Cwa.tmCast (T := model) (piCode_sub σ a b) (Cwa.tmSub (T := model) σ (piLam a b x))
      = piLam (un.sub σ a) (un.sub (un.extHom σ a) b)
          (Cwa.tmSub (T := model) (un.extHom σ a) x) := by
  refine (elTmEquiv (piCode (un.sub σ a) (un.sub (un.extHom σ a) b))).injective
    (funext fun p => ?_)
  refine cast_left_cancel (fam_piCode_apply (un.sub σ a) (un.sub (un.extHom σ a) b) p) ?_
  rw [elTmEquiv_piLam_apply (un.sub σ a) (un.sub (un.extHom σ a) b)
      (Cwa.tmSub (T := model) (un.extHom σ a) x) p
      (fam_piCode_apply (un.sub σ a) (un.sub (un.extHom σ a) b) p)]
  rw [elTmEquiv_model_tmCast (piCode_sub σ a b) (Cwa.tmSub (T := model) σ (piLam a b x)) p,
    elTmEquiv_model_tmSub σ (piCode a b) (piLam a b x) p]
  have hV : (elTmEquiv (piCode a b)) (piLam a b x) (σ p)
      = cast (fam_piCode_apply a b (σ p)).symm
          (fun y => (elTmEquiv b) x ((extIso a).hom ⟨σ p, y⟩)) := by
    refine Eq.trans (cast_symm_cast (fam_piCode_apply a b (σ p)) _).symm ?_
    exact congrArg (cast (fam_piCode_apply a b (σ p)).symm)
      (elTmEquiv_piLam_apply a b x (σ p) (fam_piCode_apply a b (σ p)))
  rw [hV]
  refine Eq.trans (cast_cast _ _ _)
    (Eq.trans (cast_cast _ _ _) (Eq.trans (cast_cast _ _ _) ?_))
  set hA : fam a (σ p) = fam (un.sub σ a) p :=
    (types_hom_congr_fun (fam_sub σ a) p).symm with hAdef
  have hstep : ∀ y : fam a (σ p),
      (un.extHom σ a) ((extIso (un.sub σ a)).hom ⟨p, cast hA y⟩)
        = (extIso a).hom ⟨σ p, y⟩ := by
    intro y
    rw [extHom_apply]
    refine congrArg (ConcreteCategory.hom (extIso a).hom) (Sigma.ext rfl ?_)
    exact (cast_heq _ _).trans (cast_heq _ _)
  have hB : ∀ y : fam a (σ p), fam b ((extIso a).hom ⟨σ p, y⟩)
      = fam (un.sub (un.extHom σ a) b) ((extIso (un.sub σ a)).hom ⟨p, cast hA y⟩) := by
    intro y
    exact ((types_hom_congr_fun (fam_sub (un.extHom σ a) b)
      ((extIso (un.sub σ a)).hom ⟨p, cast hA y⟩)).trans
      (congrArg (fun w => fam b w) (hstep y))).symm
  have hg : ∀ y : fam a (σ p),
      cast (hB y) ((elTmEquiv b) x ((extIso a).hom ⟨σ p, y⟩))
        = (elTmEquiv (un.sub (un.extHom σ a) b))
            (Cwa.tmSub (T := model) (un.extHom σ a) x)
            ((extIso (un.sub σ a)).hom ⟨p, cast hA y⟩) := by
    intro y
    rw [elTmEquiv_model_tmSub (un.extHom σ a) b x ((extIso (un.sub σ a)).hom ⟨p, cast hA y⟩)]
    rw [← cast_dep (fun w => (elTmEquiv b) x w) (hstep y)]
    exact cast_cast _ _ _
  exact cast_pi_ext hA hB
    (fun y => (elTmEquiv b) x ((extIso a).hom ⟨σ p, y⟩))
    (fun y'' => (elTmEquiv (un.sub (un.extHom σ a) b))
      (Cwa.tmSub (T := model) (un.extHom σ a) x) ((extIso (un.sub σ a)).hom ⟨p, y''⟩))
    hg _

/-- **The universe of small types is closed under dependent products.** -/
noncomputable def codePi : Cwa.Universe.CodePi un.{u} where
  code a b := piCode a b
  code_sub σ a b := piCode_sub σ a b
  lam {_Γ a b} x := piLam a b x
  app {_Γ a b} f := piApp a b f
  app_lam {_Γ a b} x := piApp_piLam a b x

/-- **The dependent product of the set-theoretic model satisfies η as well**: abstraction and
application are mutually inverse, because a dependent function is its own η-expansion. -/
noncomputable def codePiEta : Cwa.Universe.CodePiEta un.{u} where
  toCodePi := codePi
  lam_app {_Γ a b} f := piLam_piApp a b f

/-- **The dependent product of the set-theoretic model is natural in the context**: abstraction
commutes with substitution. -/
noncomputable def codePiNatural :
    Cwa.Universe.CodePiNatural (Cwa.extCoherent_ofPullbacks (Type (u + 1))) un.{u} where
  toCodePiEta := codePiEta
  lam_sub σ a b x := piLam_sub σ a b x

/-! #### The model -/

/-- **The model interprets the dependent product of `λΠ`**, with the β-rule, the η-rule and the
naturality of abstraction in the context. -/
noncomputable def modelPiNatural : Cwa.NaturalPiStruct model.{u} :=
  Cwa.Universe.smallNaturalPiOfCodePiNatural (Cwa.extCoherent_ofPullbacks _) un codePiNatural

/-- **The model interprets the dependent product of `λΠ`**, with the β- and the η-rule. -/
noncomputable def modelPiEta : Cwa.PiStruct model.{u} := modelPiNatural.toPiStruct

/-- **The model interprets the dependent product of `λΠ`**, with the β-rule. -/
noncomputable def modelPi : Cwa.WeakPiStruct model.{u} := modelPiEta.toWeakPiStruct

/-- The types of the model in a context `Γ` are the families of small types over `Γ`. -/
noncomputable def modelTyEquiv (Γ : Type (u + 1)) : model.Ty Γ ≃ (Γ ⟶ Uob.{u}) := codeEquiv Γ

/-- The terms of the model are the dependent functions. -/
noncomputable def modelTmEquiv (Γ : Type (u + 1)) (a : model.Ty Γ) :
    model.Tm Γ a ≃ ∀ x : Γ, fam a x := elTmEquiv a

/-- **The dependent product of the model is the dependent function type.** -/
theorem fam_modelPi_Pi (a : model.Ty Γ) (b : model.Ty (model.ext Γ a)) :
    fam (modelPi.Pi a b) = ↾fun x => ((y : fam a x) → fam b ((extIso a).hom ⟨x, y⟩)) :=
  fam_piCode a b

end CwaTypeModel
