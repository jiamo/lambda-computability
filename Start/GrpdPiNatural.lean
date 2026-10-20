/-
**Natural Π-types in the groupoid model** (task `M23-GROUPOID-PI-NATURAL`, round 7).

* `GrpdModel.sectOfTm_tmSub` — substitution of terms is restriction of sections:
  `sectOfTm (t[ρ]) = Sect.restrict ρ (sectOfTm t)`;
* `GrpdModel.curry_restrict` — **currying commutes with restriction along `σ : Δ ⥤ Γ`**:
  `(curry A B τ)|σ` and `curry (σ ⋙ A) (extend σ A ⋙ B) (τ|extend σ A)` agree (heterogeneously,
  along Beck–Chevalley `PiF_sub`);
* `GrpdModel.grpdLam_sub` — abstraction is stable under substitution:
  `tmCast (PiF_sub σ A B) ((λ b)[σ]) = λ (b[σ⁺])`;
* `GrpdModel.grpdNaturalPiStruct : Cwa.NaturalPiStruct grpdCwa` — **the groupoid model has
  natural Π-types**.
-/

import Start.GrpdPiApp

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

/-! ### Heterogeneous extensionality -/

section HExt

variable {X : Type u} [Category.{u} X]

theorem Sect.hext_of_eq {F F' : X ⥤ Grpd.{u, u}} (hF : F = F') {s : Sect F} {t : Sect F'}
    (ho : ∀ x, HEq (s.obj x) (t.obj x))
    (hm : ∀ {x y : X} (f : x ⟶ y), HEq (s.map f) (t.map f)) : HEq s t := by
  subst hF
  exact heq_of_eq (Sect.hext (funext fun x => eq_of_heq (ho x)) hm)

theorem SectHom.hext_of_eq {F F' : X ⥤ Grpd.{u, u}} (hF : F = F') {s t : Sect F}
    {s' t' : Sect F'} (hs : HEq s s') (ht : HEq t t') {α : s ⟶ t} {β : s' ⟶ t'}
    (h : ∀ x, HEq (α.app x) (β.app x)) : HEq α β := by
  subst hF
  cases hs
  cases ht
  exact heq_of_eq (Sect.hom_ext fun x => eq_of_heq (h x))

theorem Sect.restrict_hcongr {Y E : Type u} [Category.{u} Y] [Category.{u} E]
    {B : E ⥤ Grpd.{u, u}} {i i' : Y ⥤ E} (h : i = i') (τ : Sect B) :
    HEq (Sect.restrict i τ) (Sect.restrict i' τ) := by
  subst h; rfl

theorem grpd_obj_hcongr {C D C' D' : Grpd.{u, u}} (hC : C = C') (hD : D = D') {f : C ⟶ D}
    {f' : C' ⟶ D'} (hf : HEq f f') {x : C} {x' : C'} (hx : HEq x x') :
    HEq (f.obj x) (f'.obj x') := by
  subst hC hD
  cases hf
  cases hx
  rfl

theorem GHom.fib_hcongr {Γ : Type u} [Category.{u} Γ] {A : Γ ⥤ Grpd.{u, u}} {p q p' q' : GObj A}
    (hp : p = p') (hq : q = q') {f : p ⟶ q} {g : p' ⟶ q'} (h : HEq f g) : HEq f.fib g.fib := by
  subst hp hq
  cases h
  rfl

end HExt

/-! ### Substitution of terms is restriction of sections -/

section TmSub

variable {Δ Γ : Grpd.{u, u}} (ρ : Δ ⟶ Γ) {F : Γ ⥤ Grpd.{u, u}}

theorem tmSub_fst (t : grpdCwa.Tm Γ F) :
    (grpdCwa.tmSub ρ t).1 ⋙ extend ρ F = ρ ⋙ t.1 :=
  (grpdCwa.isPullback ρ F).lift_fst _ _ _

theorem sectOfTm_obj_heq {X : Grpd.{u, u}} {G : X ⥤ Grpd.{u, u}} (s : grpdCwa.Tm X G) (x : X) :
    HEq ((sectOfTm s).obj x) (s.1.obj x).fib :=
  Sect.cast_obj_heq (congrArg (· ⋙ G) s.2) _ x

theorem sectOfTm_map_heq {X : Grpd.{u, u}} {G : X ⥤ Grpd.{u, u}} (s : grpdCwa.Tm X G) {x y : X}
    (f : x ⟶ y) : HEq ((sectOfTm s).map f) (s.1.map f).fib :=
  Sect.cast_map_heq (congrArg (· ⋙ G) s.2) _ f

/-- **Substitution of terms is restriction of sections.** -/
theorem sectOfTm_tmSub (t : grpdCwa.Tm Γ F) :
    sectOfTm (grpdCwa.tmSub ρ t) = Sect.restrict ρ (sectOfTm t) := by
  have hfst := tmSub_fst ρ t
  refine Sect.hext (funext fun δ => eq_of_heq ?_) fun {δ δ'} f => ?_
  · refine (sectOfTm_obj_heq _ δ).trans ?_
    refine (congr_arg_heq GObj.fib (Functor.congr_obj hfst δ)).trans ?_
    exact (sectOfTm_obj_heq t _).symm
  · refine (sectOfTm_map_heq _ f).trans ?_
    refine (GHom.fib_hcongr (Functor.congr_obj hfst δ) (Functor.congr_obj hfst δ')
      (Functor.hcongr_hom hfst f)).trans ?_
    exact (sectOfTm_map_heq t _).symm

theorem sectOfTm_tmCast {X : Grpd.{u, u}} {G G' : X ⥤ Grpd.{u, u}} (h : G = G')
    (s : grpdCwa.Tm X G) : HEq (sectOfTm (Cwa.tmCast h s)) (sectOfTm s) := by
  subst h; rfl

end TmSub

/-! ### Currying commutes with restriction -/

section CurryRestrict

variable {Δ Γ : Type u} [Groupoid.{u} Δ] [Groupoid.{u} Γ] (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{u, u})
  (B : GObj A ⥤ Grpd.{u, u})

theorem curryObj_restrict (τ : Sect B) (δ : Δ) :
    HEq (curryObj A B τ (σ.obj δ))
      (curryObj (σ ⋙ A) (extend σ A ⋙ B) (Sect.restrict (extend σ A) τ) δ) :=
  Sect.restrict_hcongr (fibI_extend σ A δ).symm τ

/-- **Currying commutes with restriction along `σ : Δ ⥤ Γ`.** -/
theorem curry_restrict (τ : Sect B) :
    HEq (Sect.restrict σ (curry A B τ))
      (curry (σ ⋙ A) (extend σ A ⋙ B) (Sect.restrict (extend σ A) τ)) := by
  refine Sect.hext_of_eq (PiF_sub σ A B) (fun δ => curryObj_restrict σ A B τ δ) ?_
  intro δ δ' g
  have hF : fibI A (σ.obj δ') ⋙ B = fibI (σ ⋙ A) δ' ⋙ extend σ A ⋙ B := by
    rw [← Functor.assoc, fibI_extend]
  refine SectHom.hext_of_eq hF ?_ (curryObj_restrict σ A B τ δ') ?_
  · exact grpd_obj_hcongr (Functor.congr_obj (PiF_sub σ A B) δ)
      (Functor.congr_obj (PiF_sub σ A B) δ') (Functor.hcongr_hom (PiF_sub σ A B) g)
      (curryObj_restrict σ A B τ δ)
  · intro a
    show HEq (τ.map ((piTheta A (σ.map g)).app a))
      (τ.map ((extend σ A).map ((piTheta (σ ⋙ A) g).app a)))
    have hp : (A.map (Groupoid.inv (σ.map g))).obj a =
        (A.map (σ.map (Groupoid.inv g))).obj a := by
      rw [map_groupoidInv]
    refine τ.map_hcongr (x := ⟨σ.obj δ, (A.map (Groupoid.inv (σ.map g))).obj a⟩)
      (x' := ⟨σ.obj δ, (A.map (σ.map (Groupoid.inv g))).obj a⟩)
      (GObj.ext' rfl (heq_of_eq hp)) rfl ?_
    refine GHom.hext' (p := ⟨σ.obj δ, (A.map (Groupoid.inv (σ.map g))).obj a⟩)
      (p' := ⟨σ.obj δ, (A.map (σ.map (Groupoid.inv g))).obj a⟩)
      (GObj.ext' rfl (heq_of_eq hp)) rfl HEq.rfl ?_
    dsimp only [piTheta, extend]
    exact eqToHom_heq_eqToHom _ _ (congrArg (A.map (σ.map g)).obj hp) rfl

end CurryRestrict

/-! ### Abstraction is stable under substitution -/

section LamSub

variable {Δ Γ : Grpd.{u, u}} (σ : Δ ⟶ Γ) (A : grpdCwa.Ty Γ) (B : grpdCwa.Ty (grpdCwa.ext Γ A))

/-- **Abstraction commutes with substitution in the groupoid model.** -/
theorem grpdLam_sub (b : grpdCwa.Tm (grpdCwa.ext Γ A) B) :
    Cwa.tmCast (PiF_sub σ A B) (grpdCwa.tmSub σ (grpdLam A B b)) =
      grpdLam (σ ⋙ A) (extend σ A ⋙ B) (grpdCwa.tmSub (extendG σ A) b) := by
  have h1 := sectOfTm_tmCast (PiF_sub σ A B) (grpdCwa.tmSub σ (grpdLam A B b))
  have h2 : sectOfTm (grpdCwa.tmSub σ (grpdLam A B b)) =
      Sect.restrict σ (curry A B (sectOfTm b)) := by
    rw [sectOfTm_tmSub]
    exact congrArg (Sect.restrict σ) ((tmEquivSect Γ (PiF A B)).right_inv _)
  have h3 : sectOfTm (grpdLam (σ ⋙ A) (extend σ A ⋙ B) (grpdCwa.tmSub (extendG σ A) b)) =
      curry (σ ⋙ A) (extend σ A ⋙ B) (Sect.restrict (extend σ A) (sectOfTm b)) := by
    have := (tmEquivSect Δ (PiF (σ ⋙ A) (extend σ A ⋙ B))).right_inv
      (curry (σ ⋙ A) (extend σ A ⋙ B) (sectOfTm (grpdCwa.tmSub (extendG σ A) b)))
    refine this.trans ?_
    exact congrArg (curry (σ ⋙ A) (extend σ A ⋙ B)) (sectOfTm_tmSub (extendG σ A) b)
  refine (tmEquivSect Δ _).injective (eq_of_heq ?_)
  refine h1.trans ?_
  refine (heq_of_eq h2).trans ?_
  refine (curry_restrict σ A B (sectOfTm b)).trans ?_
  exact heq_of_eq h3.symm

/-- **The groupoid model has natural Π-types.** -/
def grpdNaturalPiStruct : Cwa.NaturalPiStruct grpdCwa where
  toPiStruct := grpdPiStruct
  lam_sub := fun {_} {_} σ {A} {B} b => grpdLam_sub σ A B b

end LamSub

end GrpdModel
