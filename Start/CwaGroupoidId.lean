/-
**Identity types in the groupoid model** — tasks
`M23-GROUPOID-MODEL` and `M23-UIP-INDEPENDENT`.

* `GrpdModel.grpdIdStruct : Cwa.IdStruct grpdCwa` — the Hofmann–Streicher identity types: `Id A`
  at `(γ, a, b)` is the discrete groupoid on the morphisms `a ⟶ b` of the fibre, `refl` is the
  identity morphism, and `J` is transport along the morphism `(x, x, refl) ⟶ (x, y, p)`
  (`Start/GrpdIdTypes.lean`).  All of `J_comp`, `Id_sub`, `refl_sub` and `J_sub` hold strictly.
* `Start/CwaGroupoidUIP.lean` uses it to show that UIP fails in the groupoid model and is
  therefore independent of the identity-type rules.
-/

import Start.CwaGroupoid
import Start.GrpdIdTypes

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Cwa

namespace GrpdModel

section Generic

variable {C : Type*} [Category C] {T : Cwa C}

theorem tmSub_eq_of {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} (a : T.Tm Γ A) (b : T.Tm Δ (T.tySub σ A))
    (h : b.1 ≫ T.extend σ A = σ ≫ a.1) : T.tmSub σ a = b := by
  apply Subtype.ext
  symm
  apply (T.isPullback σ A).hom_ext
  · rw [h]; exact ((T.isPullback σ A).lift_fst _ _ _).symm
  · rw [b.2]; exact ((T.isPullback σ A).lift_snd _ _ _).symm

end Generic

section Glue

variable {Γ : Grpd.{u, u}} (A : grpdCwa.Ty Γ)

/-- The identity type, as a type of the category with attributes `grpdCwa`. -/
def IdC : grpdCwa.Ty (grpdCwa.ext2 Γ A) := IdT A

theorem diag_eq : diag (T := grpdCwa) A = diagT A := by
  refine ((grpdCwa.isPullback (grpdCwa.disp A) A).hom_ext ?_ ?_).symm
  · change _ = (grpdCwa.isPullback (grpdCwa.disp A) A).lift _ _ _ ≫ _
    rw [IsPullback.lift_fst]; rfl
  · change _ = (grpdCwa.isPullback (grpdCwa.disp A) A).lift _ _ _ ≫ _
    rw [IsPullback.lift_snd]; rfl

theorem liftLift_eq {Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ) : liftLift (T := grpdCwa) σ A = llT σ A := by
  refine ((grpdCwa.isPullback (grpdCwa.disp A) A).hom_ext ?_ ?_).symm
  · change _ = (grpdCwa.isPullback (grpdCwa.disp A) A).lift _ _ _ ≫ _
    rw [IsPullback.lift_fst]; rfl
  · change _ = (grpdCwa.isPullback (grpdCwa.disp A) A).lift _ _ _ ≫ _
    rw [IsPullback.lift_snd]; rfl

/-- Reflexivity over the explicit diagonal. -/
def reflTm : grpdCwa.Tm (grpdCwa.ext Γ A) (grpdCwa.tySub (diagT A) (IdC A)) := ⟨reflT A, rfl⟩

/-- Reflexivity in the groupoid model: the identity morphism. -/
noncomputable def grpdRefl :
    grpdCwa.Tm (grpdCwa.ext Γ A) (grpdCwa.tySub (diag (T := grpdCwa) A) (IdC A)) :=
  tmCast (congrArg (fun D => grpdCwa.tySub D (IdC A)) (diag_eq A).symm) (reflTm A)

theorem reflMap_eq : reflMap (grpdRefl A) = rhoT A := by
  have key : ∀ (D : grpdCwa.ext Γ A ⟶ grpdCwa.ext2 Γ A) (hD : diagT A = D)
      (h : grpdCwa.tySub (diagT A) (IdC A) = grpdCwa.tySub D (IdC A)),
      (tmCast h (reflTm A)).1 ≫
        grpdCwa.extend D (IdC A) = rhoT A := by
    intro D hD h
    subst hD
    rfl
  exact key _ (diag_eq A).symm _

theorem xi_eq {Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ)
    (h : grpdCwa.tySub (liftLift (T := grpdCwa) σ A) (IdC A) = IdT (grpdCwa.tySub σ A)) :
    eqToHom (congrArg (grpdCwa.ext _) h.symm) ≫ grpdCwa.extend (liftLift σ A) (IdC A) =
      xiT σ A := by
  have key : ∀ (L : grpdCwa.ext2 Δ (grpdCwa.tySub σ A) ⟶ grpdCwa.ext2 Γ A) (hL : llT σ A = L)
      (h : grpdCwa.tySub L (IdC A) = IdT (grpdCwa.tySub σ A)),
      eqToHom (congrArg (grpdCwa.ext _) h.symm) ≫ grpdCwa.extend L (IdC A) = xiT σ A := by
    intro L hL h
    subst hL
    rw [eqToHom_refl, Category.id_comp]
    rfl
  exact key _ (liftLift_eq A σ).symm h

/-- The eliminator, for any presentation `R` of the map `x ↦ (x, x, refl x)`. -/
def grpdJ' (M : grpdCwa.Ty (grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)))
    (R : grpdCwa.ext Γ A ⟶ grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)) (hR : R = rhoT A)
    (d : grpdCwa.Tm (grpdCwa.ext Γ A) (grpdCwa.tySub R M)) :
    grpdCwa.Tm (grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)) M :=
  ⟨Jexp A M (tmCast (congrArg (fun R => grpdCwa.tySub R M) hR) d).1
    (tmCast (congrArg (fun R => grpdCwa.tySub R M) hR) d).2, rfl⟩

theorem grpdJ'_comp (M : grpdCwa.Ty (grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)))
    (R : grpdCwa.ext Γ A ⟶ grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)) (hR : R = rhoT A)
    (d : grpdCwa.Tm (grpdCwa.ext Γ A) (grpdCwa.tySub R M)) :
    grpdCwa.tmSub R (grpdJ' A M R hR d) = d := by
  subst hR
  refine tmSub_eq_of _ _ _ ?_
  exact (Jexp_comp A M _ d.2).symm

set_option maxHeartbeats 4000000 in
theorem grpdJ'_sub {Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ)
    (M : grpdCwa.Ty (grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)))
    (ξ : grpdCwa.ext (grpdCwa.ext2 Δ (grpdCwa.tySub σ A)) (IdC (grpdCwa.tySub σ A)) ⟶
      grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)) (hξ : ξ = xiT σ A)
    (R : grpdCwa.ext Γ A ⟶ grpdCwa.ext (grpdCwa.ext2 Γ A) (IdC A)) (hR : R = rhoT A)
    (R' : grpdCwa.ext Δ (grpdCwa.tySub σ A) ⟶ grpdCwa.ext (grpdCwa.ext2 Δ (grpdCwa.tySub σ A)) (IdC (grpdCwa.tySub σ A)))
    (hR' : R' = rhoT (grpdCwa.tySub σ A)) (d : grpdCwa.Tm (grpdCwa.ext Γ A) (grpdCwa.tySub R M))
    (hc : grpdCwa.tySub (grpdCwa.extend σ A) (grpdCwa.tySub R M) =
      grpdCwa.tySub R' (grpdCwa.tySub ξ M)) :
    (grpdJ' (grpdCwa.tySub σ A) (grpdCwa.tySub ξ M) R' hR'
        (tmCast hc (grpdCwa.tmSub (grpdCwa.extend σ A) d))).1 ≫ grpdCwa.extend ξ M =
      ξ ≫ (grpdJ' A M R hR d).1 := by
  subst hξ hR hR'
  have hdd : (grpdCwa.tmSub (grpdCwa.extend σ A) d).1 ≫
      grpdCwa.extend (grpdCwa.extend σ A) (grpdCwa.tySub (rhoT A) M) =
      grpdCwa.extend σ A ≫ d.1 := (grpdCwa.isPullback _ _).lift_fst _ _ _
  exact Jexp_sub σ A M d.1 d.2 _ (grpdCwa.tmSub (grpdCwa.extend σ A) d).2 hdd

end Glue

theorem grpd_Id_sub {Γ Δ : Grpd.{u, u}} (σ : Δ ⟶ Γ) (A : grpdCwa.Ty Γ) :
    grpdCwa.tySub (liftLift σ A) (IdC A) = IdC (grpdCwa.tySub σ A) :=
  congrArg (fun L => grpdCwa.tySub L (IdC A)) (liftLift_eq A σ)

/-- **The identity-type structure of the groupoid model.** -/
noncomputable def grpdIdStruct : IdStruct grpdCwa.{u} where
  Id A := IdC A
  refl A := grpdRefl A
  J {_ A} M d := grpdJ' A M _ (reflMap_eq A) d
  J_comp {_ A} M d := grpdJ'_comp A M _ (reflMap_eq A) d
  Id_sub σ A := grpd_Id_sub σ A
  refl_sub σ A := by
    rw [xi_eq A σ (grpd_Id_sub σ A), reflMap_eq,
      reflMap_eq]
    rfl
  J_sub σ A M d := grpdJ'_sub A σ M
    (eqToHom (congrArg (grpdCwa.ext _) (grpd_Id_sub σ A).symm) ≫
      grpdCwa.extend (liftLift σ A) (IdC A))
    (xi_eq A σ (grpd_Id_sub σ A)) _ (reflMap_eq A) _ (reflMap_eq _) d _

end GrpdModel
