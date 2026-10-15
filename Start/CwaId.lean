/-
**Identity types for categories with attributes.**

Task `M23-ID-TYPES`.

For a category with attributes `T` (`Start/Cwa.lean`):

* `Cwa.wk A`, `Cwa.ext2 Γ A` — the weakening `A⁺ = A[p]` and the context `Γ.A.A⁺` of two
  variables of type `A`; `Cwa.diag A : Γ.A ⟶ Γ.A.A⁺` — the diagonal (the generic term `var A`);
  `Cwa.liftLift σ A : Δ.A[σ].A[σ]⁺ ⟶ Γ.A.A⁺` — a substitution `σ` extended past both variables.
* `Cwa.IdStruct T` — an **identity-type structure**: formation `Id A` over `Γ.A.A⁺`,
  reflexivity `refl A` over the diagonal, the eliminator `J` (for a motive `C` over
  `Γ.A.A⁺.Id A` and a term over reflexivity) with its computation rule `J_comp`, and stability of
  all three under substitution (`Id_sub`, `refl_sub`, `J_sub`).
* `Cwa.IdStruct.UIP` — **uniqueness of identity proofs** as a property of such a structure: in the
  context `Γ, x y : A, q r : Id x y` the type `Id q r` (the identity type of `Id A`) has a term.
* The standard model: `CwaType.idStruct` — the families model `CwaType.families` carries an
  identity-type structure, `Id A ⟨⟨x, a⟩, b⟩ = (a = b)`, and `CwaType.idStruct_UIP` — it
  satisfies UIP.
-/

import Start.CwaType

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] (T : Cwa.{u, v, w} C)

/-- The weakening `A⁺` of `A` to the context `Γ.A`. -/
abbrev wk {Γ : C} (A : T.Ty Γ) : T.Ty (T.ext Γ A) := T.tySub (T.disp A) A

/-- The context `Γ.A.A⁺`: two variables of type `A`. -/
abbrev ext2 (Γ : C) (A : T.Ty Γ) : C := T.ext (T.ext Γ A) (T.wk A)

variable {T}

/-- The diagonal `Γ.A ⟶ Γ.A.A⁺`, `x ↦ (x, x)`. -/
noncomputable def diag {Γ : C} (A : T.Ty Γ) : T.ext Γ A ⟶ T.ext2 Γ A := (var A).1

/-- A substitution `σ : Δ ⟶ Γ` extended past two variables of type `A`. -/
noncomputable def liftLift {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) :
    T.ext2 Δ (T.tySub σ A) ⟶ T.ext2 Γ A :=
  (T.isPullback (T.disp A) A).lift
    (T.extend (T.disp (T.tySub σ A)) (T.tySub σ A) ≫ T.extend σ A)
    (T.disp (T.wk (T.tySub σ A)) ≫ T.extend σ A) (by
      rw [Category.assoc, (T.isPullback σ A).w, ← Category.assoc,
        (T.isPullback (T.disp (T.tySub σ A)) (T.tySub σ A)).w, Category.assoc, Category.assoc,
        (T.isPullback σ A).w])

/-- The substitution along a term `r` of `I[diag]`, read as a map `Γ.A ⟶ Γ.A.A⁺.I`. -/
noncomputable def reflMap {Γ : C} {A : T.Ty Γ} {I : T.Ty (T.ext2 Γ A)}
    (r : T.Tm (T.ext Γ A) (T.tySub (diag A) I)) : T.ext Γ A ⟶ T.ext (T.ext2 Γ A) I :=
  r.1 ≫ T.extend (diag A) I

variable (T)

/-- An **identity-type structure** on a category with attributes. -/
structure IdStruct where
  /-- Formation: `Γ, x y : A ⊢ Id x y`. -/
  Id : {Γ : C} → (A : T.Ty Γ) → T.Ty (T.ext2 Γ A)
  /-- Reflexivity: `Γ, x : A ⊢ refl x : Id x x`. -/
  refl : {Γ : C} → (A : T.Ty Γ) → T.Tm (T.ext Γ A) (T.tySub (diag A) (Id A))
  /-- The eliminator `J`: a motive over `Γ, x y : A, p : Id x y` with a term over reflexivity
  gives a term of the motive. -/
  J : {Γ : C} → {A : T.Ty Γ} → (M : T.Ty (T.ext (T.ext2 Γ A) (Id A))) →
      T.Tm (T.ext Γ A) (T.tySub (reflMap (refl A)) M) → T.Tm (T.ext (T.ext2 Γ A) (Id A)) M
  /-- The computation rule: `J M d` at reflexivity is `d`. -/
  J_comp : ∀ {Γ : C} {A : T.Ty Γ} (M : T.Ty (T.ext (T.ext2 Γ A) (Id A)))
      (d : T.Tm (T.ext Γ A) (T.tySub (reflMap (refl A)) M)),
      T.tmSub (reflMap (refl A)) (J M d) = d
  /-- Formation is stable under substitution. -/
  Id_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ),
      T.tySub (liftLift σ A) (Id A) = Id (T.tySub σ A)
  /-- Reflexivity is stable under substitution. -/
  refl_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ),
      reflMap (refl (T.tySub σ A)) ≫
          (eqToHom (congrArg (T.ext _) (Id_sub σ A).symm) ≫ T.extend (liftLift σ A) (Id A)) =
        T.extend σ A ≫ reflMap (refl A)
  /-- `J` is stable under substitution. -/
  J_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) (M : T.Ty (T.ext (T.ext2 Γ A) (Id A)))
      (d : T.Tm (T.ext Γ A) (T.tySub (reflMap (refl A)) M)),
      (J (T.tySub (eqToHom (congrArg (T.ext _) (Id_sub σ A).symm) ≫
            T.extend (liftLift σ A) (Id A)) M)
          (tmCast (by rw [← T.tySub_comp, ← T.tySub_comp, refl_sub σ A])
            (T.tmSub (T.extend σ A) d))).1 ≫
        T.extend (eqToHom (congrArg (T.ext _) (Id_sub σ A).symm) ≫
          T.extend (liftLift σ A) (Id A)) M =
      (eqToHom (congrArg (T.ext _) (Id_sub σ A).symm) ≫ T.extend (liftLift σ A) (Id A)) ≫
        (J M d).1

namespace IdStruct

variable {T}

/-- **Uniqueness of identity proofs**: in the context `Γ, x y : A, q r : Id x y`, the identity
type `Id q r` of `Id A` has a term. -/
def UIP (I : IdStruct T) : Prop :=
  ∀ {Γ : C} (A : T.Ty Γ),
    Nonempty (T.Tm (T.ext2 (T.ext2 Γ A) (I.Id A)) (I.Id (I.Id A)))

end IdStruct

end Cwa

namespace CwaType

open Cwa

theorem eqToHom_apply' {X Y : Type u} (h : X = Y) (x : X) : (eqToHom h : X ⟶ Y) x = cast h x := by
  subst h
  rfl

/-- Substitution of terms in the families model is precomposition. -/
theorem tmSub_eq {Γ Δ : Type u} (σ : Δ ⟶ Γ) {A : Γ → Type u} (a : families.Tm Γ A) :
    families.tmSub σ a = (secEquiv (fun d => A (σ d))).symm (fun d => secEquiv A a (σ d)) := by
  apply Subtype.ext
  refine (families.isPullback σ A).hom_ext ?_ ?_
  · change (families.isPullback σ A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_fst]
    refine ConcreteCategory.hom_ext _ _ fun d => ?_
    exact (sigma_mk_eq (a.1 (σ d)) (σ d) (tm_base a (σ d))).symm
  · change (families.isPullback σ A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_snd]
    rfl

theorem secEquiv_tmSub {Γ Δ : Type u} (σ : Δ ⟶ Γ) {A : Γ → Type u} (a : families.Tm Γ A) :
    secEquiv _ (families.tmSub σ a) = fun d => secEquiv A a (σ d) := by
  rw [tmSub_eq]
  exact Equiv.apply_symm_apply _ _

theorem diag_eq {Γ : Type u} (A : Γ → Type u) :
    diag (T := families) A = ↾fun p : Total A => (⟨p, p.2⟩ : Total fun q : Total A => A q.1) := by
  refine (families.isPullback (families.disp A) A).hom_ext ?_ ?_
  · change (families.isPullback (families.disp A) A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_fst]
    rfl
  · change (families.isPullback (families.disp A) A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_snd]
    rfl

theorem diag_apply {Γ : Type u} (A : Γ → Type u) (p : Total A) :
    diag (T := families) A p = ⟨p, p.2⟩ := by
  rw [diag_eq]
  rfl

theorem liftLift_eq {Γ Δ : Type u} (σ : Δ ⟶ Γ) (A : Γ → Type u) :
    liftLift (T := families) σ A =
      ↾fun p : Total (fun q : Total (fun d => A (σ d)) => A (σ q.1)) =>
        (⟨⟨σ p.1.1, p.1.2⟩, p.2⟩ : Total fun q : Total A => A q.1) := by
  refine (families.isPullback (families.disp A) A).hom_ext ?_ ?_
  · change (families.isPullback (families.disp A) A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_fst]
    rfl
  · change (families.isPullback (families.disp A) A).lift _ _ _ ≫ _ = _
    rw [IsPullback.lift_snd]
    rfl

theorem liftLift_apply {Γ Δ : Type u} (σ : Δ ⟶ Γ) (A : Γ → Type u)
    (p : Total (fun q : Total (fun d => A (σ d)) => A (σ q.1))) :
    liftLift (T := families) σ A p = ⟨⟨σ p.1.1, p.1.2⟩, p.2⟩ := by
  rw [liftLift_eq]
  rfl

/-- The identity type of the families model: `Id A ⟨⟨x, a⟩, b⟩ = (a = b)`. -/
def idTy {Γ : Type u} (A : Γ → Type u) (p : Total fun q : Total A => A q.1) : Type u :=
  ULift.{u} (PLift (p.1.2 = p.2))

instance {Γ : Type u} (A : Γ → Type u) (p : Total fun q : Total A => A q.1) :
    Subsingleton (idTy A p) :=
  ⟨fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl⟩

theorem idTy_diag {Γ : Type u} (A : Γ → Type u) (p : Total A) :
    (diag (T := families) A p).1.2 = (diag (T := families) A p).2 := by
  have key : ∀ q : Total fun q : Total A => A q.1, q = ⟨p, p.2⟩ → q.1.2 = q.2 := by
    rintro q rfl
    rfl
  exact key _ (diag_apply A p)

/-- Reflexivity in the families model. -/
noncomputable def reflTm {Γ : Type u} (A : Γ → Type u) :
    families.Tm (Total A) (families.tySub (diag (T := families) A) (idTy A)) :=
  (secEquiv _).symm fun p => ⟨⟨idTy_diag A p⟩⟩

theorem total_idTy_ext {Γ : Type u} {A : Γ → Type u} {e₁ e₂ : Total (idTy A)} (h : e₁.1 = e₂.1) :
    e₁ = e₂ := by
  obtain ⟨r₁, v₁⟩ := e₁
  obtain ⟨r₂, v₂⟩ := e₂
  simp only at h
  subst h
  rw [Subsingleton.elim v₁ v₂]

theorem reflMap_apply {Γ : Type u} (A : Γ → Type u) (p : Total A) :
    reflMap (reflTm A) p = (⟨⟨p, p.2⟩, ⟨⟨rfl⟩⟩⟩ : Total (idTy A)) := by
  apply total_idTy_ext
  exact diag_apply A p

theorem reflMap_fst {Γ : Type u} (A : Γ → Type u) (p : Total A) :
    (reflMap (reflTm A) p).1 = diag (T := families) A p := rfl

theorem reflMap_eq_of {Γ : Type u} {A : Γ → Type u} (e : Total (idTy A)) :
    reflMap (reflTm A) e.1.1 = e := by
  apply total_idTy_ext
  rw [reflMap_fst, diag_apply]
  exact Sigma.ext rfl (heq_of_eq e.2.down.down)

/-- The eliminator of the families model, pointwise. -/
noncomputable def jFun {Γ : Type u} {A : Γ → Type u} (M : Total (idTy A) → Type u)
    (dd : ∀ p : Total A, M (reflMap (reflTm A) p)) (e : Total (idTy A)) : M e :=
  cast (congrArg M (reflMap_eq_of e)) (dd e.1.1)

/-- The eliminator of the families model. -/
noncomputable def jTm {Γ : Type u} {A : Γ → Type u} (M : Total (idTy A) → Type u)
    (d : families.Tm (Total A) (families.tySub (reflMap (reflTm A)) M)) :
    families.Tm (Total (idTy A)) M :=
  (secEquiv M).symm (jFun M (secEquiv _ d))

theorem fst_eqToHom {X : Type u} {B B' : X → Type u} (h : B = B') (e : Total B) :
    ((eqToHom (congrArg (families.ext X) h) : Total B ⟶ Total B') e).1 = e.1 := by
  subst h
  rfl

theorem secEquiv_tmCast_heq {X : Type u} {B B' : X → Type u} (h : B = B') (a : families.Tm X B)
    (x : X) : HEq (secEquiv B' (tmCast h a) x) (secEquiv B a x) := by
  subst h
  rfl

theorem idTy_sub {Γ Δ : Type u} (σ : Δ ⟶ Γ) (A : Γ → Type u) :
    families.tySub (liftLift (T := families) σ A) (idTy A) = idTy (families.tySub σ A) := by
  funext p
  change idTy A (liftLift (T := families) σ A p) = _
  rw [liftLift_apply]
  rfl

theorem fst_extend {X Y : Type u} (τ : Y ⟶ X) (B : X → Type u) (x : Total fun y => B (τ y)) :
    (families.extend τ B x).1 = τ x.1 := rfl

/-- **The families model carries an identity-type structure**, with `Id A ⟨⟨x, a⟩, b⟩` the
type `a = b`. -/
noncomputable def idStruct : IdStruct families.{u} where
  Id A := idTy A
  refl A := reflTm A
  J M d := jTm M d
  J_comp M d := by
    apply (secEquiv _).injective
    rw [secEquiv_tmSub]
    funext p
    simp only [jTm, Equiv.apply_symm_apply, jFun]
    have h : (reflMap (reflTm _) p).1.1 = p := by rw [reflMap_fst, diag_apply]
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq (secEquiv _ d) h))
  Id_sub σ A := idTy_sub σ A
  refl_sub σ A := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    apply total_idTy_ext
    rw [types_comp_apply, types_comp_apply, types_comp_apply, fst_extend, fst_eqToHom,
      reflMap_fst, reflMap_fst, diag_apply, diag_apply, liftLift_apply]
    · rfl
    · exact (idTy_sub σ A).symm
  J_sub σ A M d := by
    refine ConcreteCategory.hom_ext _ _ fun e => ?_
    rw [types_comp_apply, types_comp_apply]
    refine Sigma.ext rfl ?_
    have hq : ((eqToHom (congrArg (families.ext _) (idTy_sub σ A).symm) ≫
        families.extend (liftLift (T := families) σ A) (idTy A)) e).1.1 =
        families.extend σ A e.1.1 := by
      rw [types_comp_apply, fst_extend, fst_eqToHom, liftLift_apply]
      · rfl
      · exact (idTy_sub σ A).symm
    change HEq (jFun _ _ e) (jFun M _ _)
    unfold jFun
    refine (cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
    refine (secEquiv_tmCast_heq _ _ _).trans ?_
    rw [secEquiv_tmSub]
    exact congr_arg_heq (secEquiv _ d) hq.symm

/-- **UIP holds in the families model.** -/
theorem idStruct_UIP : idStruct.{u}.UIP := by
  intro Γ A
  exact ⟨(secEquiv _).symm fun p => ⟨⟨@Subsingleton.elim (idTy A p.1.1) _ _ _⟩⟩⟩

end CwaType
