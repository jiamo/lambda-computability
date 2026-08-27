/-
**The small fragment of a model with a universe.**

`Start/CwaUniverse.lean` equips a category with attributes `T` with a universe `Un` of small
types: a type `U Γ` of codes in every context, and a decoding `El` of its terms as types of `T`.
The calculus `λΠ` is not a theory of *all* the types of such a model — it is a theory of the small
ones, its types being exactly the terms of `∗`.  This module makes that precise by building, out of
`T` and `Un`, a second category with attributes on the *same* category of contexts whose types are
the codes:

* `Cwa.Universe.smallCwa` — **the small fragment**: `Ty Γ` is `T.Tm Γ (U Γ)`, substitution is the
  substitution of codes, and the context extension of a code is the extension of `T` by its
  decoding.  Substitution is strictly functorial because the substitution of terms is
  (`Cwa.ExtCoherent`), and the extension squares are the squares of the decoded types
  (`Cwa.Universe.isPullback_extHom`).  Its terms are literally the terms of the decoded type
  (`Cwa.Universe.smallCwa_Tm`);
* `Cwa.Universe.smallMor` — **the inclusion of the small fragment into the model**: the identity
  functor on contexts, decoding on types.  This is a morphism of categories with attributes in the
  sense of `Start/CwaMor.lean`, i.e. an honest comparison of models;
* `Cwa.Universe.smallMorOfPreserves` — a comparison of models preserving the universes restricts
  to a comparison of the small fragments, acting on types by its action on codes;
* `Cwa.Universe.NaturalPiClosed` — closure of the universe under the small products, with the
  naturality law the codes need: the code of a product is stable under substitution.  `PiClosed`
  by itself does not say this, and without it the product of the small fragment would not satisfy
  Beck–Chevalley;
* `Cwa.Universe.smallWeakPi` — **the small fragment is a model of `λΠ`**: a natural closure of the
  universe under products makes the codes into a dependent product on `smallCwa`, with β.

Two instances are given.  Semantically, `CwaUniv.smallCwaOfHom` is the model whose types in a
context are the maps into a universe object, the strictification that a universe object gives on
the nose (`CwaUniv.smallTyEquivHom`).  Syntactically, `LambdaPiUniv.naturalPiClosed` upgrades the
product rules `(∗,∗)`/`(∗,□)` of `λΠ` to the naturality law, so the small fragment of the syntactic
model of `Start/LambdaPiFull.lean` is a model of `λΠ` whose types are the terms of `∗`.
-/

import Start.CwaMorUniv
import Start.CwaSubFunctorial
import Start.CwaUnivLocal
import Start.LambdaPiCoherent
import Start.LambdaPiUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

namespace Universe

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- **The small fragment of a model with a universe**: the category with attributes on the same
contexts whose types are the codes of the universe.  Substitution of codes is strictly functorial
by `Cwa.ExtCoherent`, and the extension square of a code is the extension square of its
decoding. -/
@[reducible]
noncomputable def smallCwa (co : ExtCoherent T) (Un : Universe T) : Cwa.{u, v, v} C where
  Ty Γ := T.Tm Γ (Un.U Γ)
  tySub σ a := Un.sub σ a
  tySub_id a := Universe.sub_id co Un a
  tySub_comp σ τ a := (Universe.sub_comp co Un σ τ a).symm
  ext Γ a := T.ext Γ (Un.El a)
  disp a := T.disp (Un.El a)
  extend σ a := Un.extHom σ a
  isPullback σ a := Un.isPullback_extHom σ a

@[simp] theorem smallCwa_Ty (co : ExtCoherent T) (Un : Universe T) (Γ : C) :
    (smallCwa co Un).Ty Γ = T.Tm Γ (Un.U Γ) := rfl

@[simp] theorem smallCwa_tySub (co : ExtCoherent T) (Un : Universe T) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : T.Tm Γ (Un.U Γ)) : (smallCwa co Un).tySub σ a = Un.sub σ a := rfl

@[simp] theorem smallCwa_ext (co : ExtCoherent T) (Un : Universe T) {Γ : C}
    (a : T.Tm Γ (Un.U Γ)) : (smallCwa co Un).ext Γ a = T.ext Γ (Un.El a) := rfl

/-- **The terms of the small fragment are the terms of the decoded type.** -/
theorem smallCwa_Tm (co : ExtCoherent T) (Un : Universe T) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    (smallCwa co Un).Tm Γ a = T.Tm Γ (Un.El a) := rfl

/-- **The inclusion of the small fragment into the model**: the identity on contexts, decoding on
types. -/
noncomputable def smallMor (co : ExtCoherent T) (Un : Universe T) : Mor (smallCwa co Un) T where
  fnc := 𝟭 C
  tyMap a := Un.El a
  tyMap_sub σ a := (Un.El_sub' σ a).symm
  extIso _ := Iso.refl _
  extIso_disp _ := Category.id_comp _
  extIso_extend σ a := by
    simp only [Functor.id_obj, Functor.id_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

section Functorial

variable {D : Type u} [Category.{v} D] {S : Cwa.{u, v, w} D}

/-- The action of a substitution on extended contexts commutes with transport along an equality
of types. -/
theorem _root_.Cwa.extend_eqToHom {Γ Δ : C} (σ : Δ ⟶ Γ) {A A' : T.Ty Γ} (e : A = A') :
    T.extend σ A ≫ eqToHom (congrArg (T.ext Γ) e)
      = eqToHom (congrArg (T.ext Δ) (congrArg (T.tySub σ) e)) ≫ T.extend σ A' := by
  cases e
  simp

/-- **A universe-preserving comparison of models restricts to the small fragments**: a morphism
that carries the universe to the universe and commutes with decoding induces a morphism of the
small fragments, acting on types by its action on codes. -/
noncomputable def smallMorOfPreserves (coT : ExtCoherent T) (coS : ExtCoherent S)
    {Un : Universe T} {Vn : Universe S} {F : Mor T S} (h : F.PreservesUniverse Un Vn) :
    Mor (smallCwa coT Un) (smallCwa coS Vn) where
  fnc := F.fnc
  tyMap a := h.codeMap a
  tyMap_sub σ a := h.codeMap_sub σ a
  extIso a := h.extElIso a
  extIso_disp a := h.extElIso_hom_disp a
  extIso_extend σ a := by
    have hF := F.extIso_extend σ (Un.El a)
    simp only [smallCwa, Universe.extHom, Mor.PreservesUniverse.extElIso, Iso.trans_hom,
      eqToIso.hom, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (F.fnc.map (T.extend σ (Un.El a))), hF]
    simp only [Category.assoc]
    rw [Cwa.extend_eqToHom (F.fnc.map σ) (h.El_map' a)]
    rw [← Category.assoc (F.fnc.map (eqToHom _)),
      Mor.extIso_eqToHom F (Un.El_sub' σ a).symm]
    simp only [Category.assoc, eqToHom_trans_assoc]

/-- The restriction of the identity comparison acts as the identity on types. -/
theorem smallMorOfPreserves_id_tyMap (co : ExtCoherent T) (Un : Universe T) {Γ : C}
    (a : (smallCwa co Un).Ty Γ) :
    (smallMorOfPreserves co co (Mor.PreservesUniverse.id Un)).tyMap a = a := by
  change tmCast rfl ((Mor.id T).tmMap a) = a
  rw [tmCast_rfl, Mor.tmMap_id]

/-- The restriction of a composite acts on types as the composite of the restrictions. -/
theorem smallMorOfPreserves_comp_tyMap {E : Type u} [Category.{v} E] {R : Cwa.{u, v, w} E}
    (coT : ExtCoherent T) (coS : ExtCoherent S) (coR : ExtCoherent R)
    {Un : Universe T} {Vn : Universe S} {Wn : Universe R} {F : Mor T S} {G : Mor S R}
    (h : F.PreservesUniverse Un Vn) (h' : G.PreservesUniverse Vn Wn) {Γ : C}
    (a : (smallCwa coT Un).Ty Γ) :
    (smallMorOfPreserves coT coR (h.comp h')).tyMap a
      = (smallMorOfPreserves coS coR h').tyMap ((smallMorOfPreserves coT coS h).tyMap a) :=
  h.codeMap_comp h' a

end Functorial

/-- **Closure of the universe under the small products, naturally**: `Cwa.Universe.PiClosed`
together with the law that the code of a product is stable under substitution.  The bare `PiClosed`
gives a code and its decoding but says nothing about substitution, and Beck–Chevalley for the
product of the small fragment is exactly this naturality. -/
structure NaturalPiClosed (Un : Universe T) (P : SmallPi Un) extends PiClosed Un P where
  /-- The code of a product is stable under substitution. -/
  code_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (a : T.Tm Γ (Un.U Γ))
      (b : T.Tm (T.ext Γ (Un.El a)) (Un.U (T.ext Γ (Un.El a)))),
      Un.sub σ (toPiClosed.code a b)
        = toPiClosed.code (Un.sub σ a) (Un.sub (Un.extHom σ a) b)

/-- **The small fragment is a model of `λΠ`.**  The dependent product of two codes is their code,
its Beck–Chevalley condition is the naturality law, and abstraction and application are those of
the ambient product transported along `El_code`. -/
noncomputable def smallWeakPi (co : ExtCoherent T) (Un : Universe T) (P : SmallPi Un)
    (Pc : NaturalPiClosed Un P) : WeakPiStruct (smallCwa co Un) where
  Pi a b := Pc.code a b
  Pi_sub σ a b := Pc.code_sub σ a b
  lam {_Γ _a _b} x := tmCast (T := T) (Pc.El_code _ _).symm (P.lam x)
  app {_Γ _a _b} f := P.app (tmCast (T := T) (Pc.El_code _ _) f)
  app_lam {_Γ a b} x := by
    have h : tmCast (T := T) (Pc.El_code a b)
        (tmCast (T := T) (Pc.El_code a b).symm (P.lam x)) = P.lam x := by
      rw [tmCast_trans]
      rfl
    change P.app (tmCast (T := T) (Pc.El_code a b)
      (tmCast (T := T) (Pc.El_code a b).symm (P.lam x))) = x
    rw [h]
    exact P.app_lam x

end Universe

end Cwa

/-! ### The semantic instance: the types are the maps into a universe object -/

namespace CwaUniv

open Cwa

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C]

/-- **The model presented by a universe object**: the small fragment of the strictified model of
`Start/CwaLocalUniverse.lean` for the universe of `Start/CwaUnivLocal.lean`.  A type in context `Γ`
is a code, i.e. a map `Γ ⟶ 𝒰`, and the extended context is the pullback of the generic family. -/
@[reducible] noncomputable def smallCwaOfHom {E U : C} (p : E ⟶ U) : Cwa.{u, v, v} C :=
  Cwa.Universe.smallCwa (Cwa.extCoherent_ofPullbacks C) (universeOfHom p)

omit [HasPullbacks C] in
/-- The condition making a map into the universe object a code: the two composites into the
terminal object agree. -/
theorem uTy_lift_cond (U : C) {Γ : C} (f : Γ ⟶ U) :
    𝟙 Γ ≫ (uTy U Γ).cls = f ≫ (uTy U Γ).proj :=
  terminal.hom_ext _ _

/-- The types of that model are exactly the maps into the universe object: a code is a term of the
type of codes, and `codeOf` reads off the classifying map. -/
noncomputable def smallTyEquivHom {E U : C} (p : E ⟶ U) (Γ : C) :
    (smallCwaOfHom p).Ty Γ ≃ (Γ ⟶ U) where
  toFun a := codeOf a
  invFun f :=
    ⟨pullback.lift (𝟙 Γ) f (uTy_lift_cond U f), pullback.lift_fst (𝟙 Γ) f _⟩
  left_inv a := by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst (𝟙 Γ) (codeOf a) (uTy_lift_cond U (codeOf a))).trans a.2.symm
    · exact pullback.lift_snd (𝟙 Γ) (codeOf a) (uTy_lift_cond U (codeOf a))
  right_inv f := pullback.lift_snd (𝟙 Γ) f _

end CwaUniv

/-! ### The syntactic instance: the small fragment of the syntactic model of `λΠ` -/

namespace LambdaPiUniv

open LambdaPi LambdaPiCat LambdaPiFull

/-- **The code of a substituted term is the substitution of its code.** -/
theorem codeTm_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ)) :
    Conv (codeTm (univ.sub σ a)) (subst σ.out.sub (codeTm a)) := by
  have h : codeTm (univ.sub σ a)
      = (tmEquiv (tySubQ σ (uQ Γ)) (Cwa.tmSub (T := syntactic) σ a)).out.tm :=
    codeTm_cast (uQ_sub σ) _
  rw [h]
  exact tmEquiv_tmSub_conv σ (uQ Γ) a

/-- **The code of a product is stable under substitution**: the product rule `(∗,∗)` of `λΠ`
commutes with substitution, because substitution of a product is the product of the
substitutions. -/
theorem codeQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ))
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) (uQ (extOb Γ (elQ a)))) :
    univ.sub σ (codeQ a b) = codeQ (univ.sub σ a) (univ.sub (univ.extHom σ a) b) := by
  refine eq_of_codeTm_conv ?_
  refine (codeTm_sub σ (codeQ a b)).trans ?_
  refine Conv.trans ((codeTm_symm _).subst σ.out.sub) ?_
  refine Conv.trans ?_ (codeTm_symm _).symm
  rw [subst_pi]
  refine Conv.pi ?_ ?_
  · have h := tySubQ_rep_conv σ (elQ a)
    rw [elQ_sub σ a] at h
    exact h.symm
  · refine Conv.trans ?_ (codeTm_sub (univ.extHom σ a) b).symm
    refine conv_subst_congr ((codeTm_ok b).bnd_of_wf (extOb Γ (elQ a)).wf).1 ?_
    intro n hn
    exact (extHom_out_conv σ a hn).symm

/-- **The universe `∗` is closed under products, naturally.**  This is what makes the small
fragment of the syntactic model — the model whose types are the terms of `∗` — a model of `λΠ`. -/
noncomputable def naturalPiClosed : Cwa.Universe.NaturalPiClosed univ smallPi where
  toPiClosed := piClosed
  code_sub σ a b := codeQ_sub σ a b

/-- **The small fragment of the syntactic model of `λΠ`**: the category with attributes on the
contexts of `λΠ` whose types in a context are the terms of `∗`. -/
noncomputable def smallSyntactic : Cwa.{0, 0, 0} Ob :=
  Cwa.Universe.smallCwa extCoherent_syntactic univ

/-- **The small fragment of the syntactic model carries the dependent product of `λΠ`.** -/
noncomputable def smallSyntacticPi : Cwa.WeakPiStruct smallSyntactic :=
  Cwa.Universe.smallWeakPi extCoherent_syntactic univ smallPi naturalPiClosed

/-- The types of the small fragment of the syntactic model are exactly the small types of `λΠ`,
i.e. the types of `Start/LambdaPiCwa.lean`. -/
noncomputable def smallSyntactic_Ty_equiv (Γ : Ob) :
    smallSyntactic.Ty Γ ≃ LambdaPiCwa.TyQ Γ := smallTyEquiv Γ

end LambdaPiUniv
