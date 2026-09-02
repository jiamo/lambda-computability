/-
**2-cells transport the structure of a model of `λΠ`.**

`Start/CwaMorUniv.lean` says what it means for a morphism of categories with attributes to
preserve a universe, the dependent products over the small types, and the codes for them — the
structure an interpretation of `λΠ` has to respect.  `Start/CwaTwoCell.lean` adds 2-cells between
morphisms.  This module connects the two: **the three preservation properties are invariant under
2-cells**, so they only depend on the isomorphism class of a 1-cell.

The engine is a single lemma about terms.  A 2-cell `θ : F ⟹ G` identifies the type `F.tyMap A`
with `G.tyMap A` substituted along its component; the same then holds one level down, for the
*terms*: `F.tmMap a` is `G.tmMap a` substituted along the component
(`Cwa.TwoCell.tmMap_eq`).  This is proved from the pullback characterisation of term substitution
together with the naturality of the component, and it is what makes the action on codes — and
hence decoding, products and their codes — transportable.

The consequence for the syntax of `λΠ` is a **necessary condition** for a 1-cell out of the
syntactic model to be the canonical interpretation: any 1-cell isomorphic to it preserves the
universe, the small products and their codes, and sends the empty context to a terminal object
(`LambdaPiBiInitial.preservesUniverse_of_twoCell`,
`LambdaPiBiInitial.isTerminal_empty_of_iso` and the summary
`LambdaPiBiInitial.iso_mor_necessary`).  Together with
`LambdaPiBiInitial.nonempty_iso_mor_iff` this pins the criterion down from both sides: the
comparison with the canonical interpretation can only exist for structure-preserving pointed
1-cells.

Main results:

* `Cwa.TwoCell.tmMap_eq` — **a 2-cell transports the action on terms**;
* `Cwa.TwoCell.codeMap_eq` — hence the action on codes;
* `Cwa.TwoCell.preservesUniverse`, `Cwa.TwoCell.preservesSmallPi`,
  `Cwa.TwoCell.preservesPiClosed` — **the preservation properties are invariant under 2-cells**;
* `LambdaPiBiInitial.iso_mor_necessary` — a 1-cell out of the syntactic model of `λΠ` isomorphic
  to the canonical interpretation preserves the universe, the small products and their codes, and
  sends the empty context to a terminal object.
-/

import Start.CwaTwoCell
import Start.CwaMorUniv
import Start.CwaBiInitial
import Start.LambdaPiInitialUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {F G : Mor T S}

namespace TwoCell

/-- **A 2-cell transports the action on terms**: the term `F.tmMap a` is the term `G.tmMap a`
substituted along the component of the 2-cell.  Both sides are sections of the same display map,
and a section into a context extension is determined by its composite with the extension square,
which the naturality of the component computes. -/
theorem tmMap_eq (θ : TwoCell F G) {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) :
    tmCast (θ.tySub_app A) (S.tmSub (θ.nat.app Γ) (G.tmMap a)) = F.tmMap a := by
  have key : S.tmSub (θ.nat.app Γ) (G.tmMap a)
      = tmCast (θ.tySub_app A).symm (F.tmMap a) := by
    refine (tmSub_eq_of (θ.nat.app Γ) (G.tmMap a) (tmCast (θ.tySub_app A).symm (F.tmMap a)) ?_).symm
    have hsub : (tmCast (θ.tySub_app A).symm (F.tmMap a)).1 ≫ S.extend (θ.nat.app Γ) (G.tyMap A)
        = (F.tmMap a).1 ≫ S.substCompare (θ.nat.app Γ) (θ.tySub_app A) := by
      rw [tmCast_val, substCompare, Category.assoc]
    rw [hsub, Mor.tmMap_val, Category.assoc, θ.extend_app A, ← Category.assoc,
      θ.nat.naturality a.1, Category.assoc, Mor.tmMap_val]
  rw [key, tmCast_trans]
  simp

/-- A 2-cell transports the action on codes of a universe-preserving morphism. -/
theorem codeMap_eq (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    (h : G.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ))
    (hU : F.tyMap (Un.U Γ) = Vn.U (F.fnc.obj Γ)) :
    tmCast hU (F.tmMap a) = Vn.sub (θ.nat.app Γ) (h.codeMap a) := by
  simp only [Universe.sub, Mor.PreservesUniverse.codeMap, tmSub_tmCast, ← θ.tmMap_eq a,
    tmCast_trans]

/-- The canonical map out of an extended context does not change when the type it is substituted
from is replaced by an equal one. -/
theorem _root_.Cwa.substCompare_congr_ty {Γ Δ : D} (σ : Δ ⟶ Γ) {B B' : S.Ty Γ} (hB : B = B')
    {A : S.Ty Δ} (e : S.tySub σ B = A) (e' : S.tySub σ B' = A) :
    S.substCompare σ e ≫ eqToHom (congrArg (S.ext Γ) hB) = S.substCompare σ e' := by
  cases hB
  simp

/-- The canonical map out of an extended context does not change when the substituted type is
replaced by an equal one. -/
theorem _root_.Cwa.substCompare_eqToHom_left {Γ Δ : D} (σ : Δ ⟶ Γ) {B : S.Ty Γ} {A A' : S.Ty Δ}
    (hA : A = A') (e : S.tySub σ B = A) (e' : S.tySub σ B = A') :
    eqToHom (congrArg (S.ext Δ) hA) ≫ S.substCompare σ e' = S.substCompare σ e := by
  cases hA
  simp

/-- The action of a substitution on a context extended by a decoded type is the canonical map. -/
theorem _root_.Cwa.Universe.extHom_eq_substCompare (Vn : Universe S) {Γ Δ : D} (σ : Δ ⟶ Γ)
    (c : S.Tm Γ (Vn.U Γ)) :
    Vn.extHom σ c = S.substCompare σ (Vn.El_sub' σ c) := by
  simp [Universe.extHom, substCompare]

/-- **Universe preservation is invariant under 2-cells.** -/
theorem preservesUniverse (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    (h : G.PreservesUniverse Un Vn) : F.PreservesUniverse Un Vn where
  U_map Γ := by
    rw [← θ.tySub_app (Un.U Γ), h.U_map Γ, Vn.U_sub]
  El_map a := by
    rw [← θ.tySub_app (Un.El a), h.El_map a, Vn.El_sub']
    exact (congrArg Vn.El (θ.codeMap_eq h a _)).symm

/-- A 2-cell transports the action on codes of a universe-preserving morphism, in the form in
which the transported universe preservation of `Cwa.TwoCell.preservesUniverse` records it. -/
theorem codeMap_preservesUniverse (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    (h : G.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    (θ.preservesUniverse h).codeMap a = Vn.sub (θ.nat.app Γ) (h.codeMap a) :=
  θ.codeMap_eq h a _

/-- **A 2-cell transports the comparison of the contexts extended by a decoded type.** -/
theorem extElIso_hom_twoCell (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    (h : G.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    θ.nat.app (T.ext Γ (Un.El a)) ≫ (h.extElIso a).hom
      = ((θ.preservesUniverse h).extElIso a).hom
          ≫ eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c))
              (θ.codeMap_preservesUniverse h a))
          ≫ Vn.extHom (θ.nat.app Γ) (h.codeMap a) := by
  have e' : S.tySub (θ.nat.app Γ) (Vn.El (h.codeMap a)) = F.tyMap (Un.El a) := by
    rw [← h.El_map' a, θ.tySub_app]
  have hL : θ.nat.app (T.ext Γ (Un.El a)) ≫ (h.extElIso a).hom
      = (F.extIso (Un.El a)).hom ≫ S.substCompare (θ.nat.app Γ) e' := by
    rw [Mor.PreservesUniverse.extElIso]
    simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, ← θ.extend_app (Un.El a)]
    rw [Category.assoc,
      substCompare_congr_ty (θ.nat.app Γ) (h.El_map' a) (θ.tySub_app (Un.El a)) e']
  have hR : ((θ.preservesUniverse h).extElIso a).hom
        ≫ eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c))
            (θ.codeMap_preservesUniverse h a))
        ≫ Vn.extHom (θ.nat.app Γ) (h.codeMap a)
      = (F.extIso (Un.El a)).hom ≫ S.substCompare (θ.nat.app Γ) e' := by
    rw [Mor.PreservesUniverse.extElIso, Vn.extHom_eq_substCompare]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc]
    rw [substCompare_eqToHom_left (θ.nat.app Γ)
      (show F.tyMap (Un.El a) = Vn.El (Vn.sub (θ.nat.app Γ) (h.codeMap a)) by
        rw [← e', Vn.El_sub'])
      e' (Vn.El_sub' (θ.nat.app Γ) (h.codeMap a))]
  rw [hL, hR]

/-- The inverse form of `Cwa.TwoCell.extElIso_hom_twoCell`. -/
theorem extElIso_inv_twoCell (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    (h : G.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    ((θ.preservesUniverse h).extElIso a).inv ≫ θ.nat.app (T.ext Γ (Un.El a))
      = eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c))
            (θ.codeMap_preservesUniverse h a))
          ≫ Vn.extHom (θ.nat.app Γ) (h.codeMap a) ≫ (h.extElIso a).inv := by
  calc ((θ.preservesUniverse h).extElIso a).inv ≫ θ.nat.app (T.ext Γ (Un.El a))
      = ((θ.preservesUniverse h).extElIso a).inv
          ≫ (θ.nat.app (T.ext Γ (Un.El a)) ≫ (h.extElIso a).hom) ≫ (h.extElIso a).inv := by
        simp
    _ = ((θ.preservesUniverse h).extElIso a).inv
          ≫ (((θ.preservesUniverse h).extElIso a).hom
            ≫ eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c))
                (θ.codeMap_preservesUniverse h a))
            ≫ Vn.extHom (θ.nat.app Γ) (h.codeMap a)) ≫ (h.extElIso a).inv := by
        rw [θ.extElIso_hom_twoCell h a]
    _ = eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c))
            (θ.codeMap_preservesUniverse h a))
          ≫ Vn.extHom (θ.nat.app Γ) (h.codeMap a) ≫ (h.extElIso a).inv := by
        simp

/-- **Preservation of the dependent products over the small types is invariant under 2-cells.** -/
theorem preservesSmallPi (θ : TwoCell F G) {Un : Universe T} {Vn : Universe S}
    {h : G.PreservesUniverse Un Vn} {P : Universe.SmallPi Un} {Q : Universe.SmallPi Vn}
    (hP : G.PreservesSmallPi h P Q) : F.PreservesSmallPi (θ.preservesUniverse h) P Q where
  Pi_map := fun {Γ} a B => by
    have hc := θ.codeMap_preservesUniverse h a
    have hbody : S.tySub ((θ.preservesUniverse h).extElIso a).inv (F.tyMap B)
        = S.tySub (eqToHom (congrArg (fun c => S.ext (F.fnc.obj Γ) (Vn.El c)) hc))
            (S.tySub (Vn.extHom (θ.nat.app Γ) (h.codeMap a) ≫ (h.extElIso a).inv)
              (G.tyMap B)) := by
      rw [← θ.tySub_app B, ← S.tySub_comp, θ.extElIso_inv_twoCell h a, ← S.tySub_comp]
    rw [← θ.tySub_app (P.Pi a B), hP.Pi_map a B, Q.Pi_sub, ← S.tySub_comp, hbody]
    exact (Universe.SmallPi.Pi_congr Q hc.symm _).symm

/-- **Preservation of the codes for the products is invariant under 2-cells**, for a universe
whose codes for products are stable under substitution (`hcs`, the Beck–Chevalley condition of
`Cwa.Universe.CodePi.code_sub`, which `Cwa.Universe.PiClosed` does not itself demand). -/
theorem preservesPiClosed (θ : TwoCell F G) (co : ExtCoherent S) {Un : Universe T}
    {Vn : Universe S} {h : G.PreservesUniverse Un Vn} {P : Universe.SmallPi Un}
    {Q : Universe.SmallPi Vn} {C₀ : Universe.PiClosed Un P} {C₁ : Universe.PiClosed Vn Q}
    (hcs : ∀ {Γ Δ : D} (σ : Δ ⟶ Γ) (a : S.Tm Γ (Vn.U Γ))
      (b : S.Tm (S.ext Γ (Vn.El a)) (Vn.U (S.ext Γ (Vn.El a)))),
      Vn.sub σ (C₁.code a b) = C₁.code (Vn.sub σ a) (Vn.sub (Vn.extHom σ a) b))
    (hC : G.PreservesPiClosed h C₀ C₁) :
    F.PreservesPiClosed (θ.preservesUniverse h) C₀ C₁ where
  code_map := fun {Γ} a b => by
    have hc := θ.codeMap_preservesUniverse h a
    have hb := θ.codeMap_preservesUniverse h b
    rw [θ.codeMap_preservesUniverse h (C₀.code a b), hC.code_map a b, hcs,
      Universe.sub_comp co Vn (h.extElIso a).inv (Vn.extHom (θ.nat.app Γ) (h.codeMap a))
        (h.codeMap b),
      hb, Universe.sub_comp co Vn, θ.extElIso_inv_twoCell h a]
    conv_rhs => rw [← Universe.sub_comp co Vn]
    exact (Mor.PreservesPiClosed.code_congr co C₁ hc.symm _ _ rfl).symm

end TwoCell

end Cwa

/-! ### The necessary conditions for a 1-cell out of the syntax of `λΠ` -/

namespace LambdaPiBiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv Cwa

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- **A 1-cell out of the syntactic model receiving a 2-cell from the canonical interpretation
preserves the universe.**  The sort `∗` is carried to the universe of the model, because the
universe is stable under substitution and the 2-cell identifies the two images up to substituting
along its component. -/
theorem preservesUniverse_of_twoCell (hinj : M.PiInj) {F : Cwa.Mor syntactic M.T}
    (θ : Cwa.TwoCell F (LambdaPiInitial.mor hinj)) :
    F.PreservesUniverse univ M.Un :=
  θ.preservesUniverse (LambdaPiInitial.mor_preservesUniverse hinj)

/-- The component at the empty context of an isomorphism in the hom-category is an isomorphism of
the two images of the empty context. -/
noncomputable def isoObjEmpty (hinj : M.PiInj) {F : Cwa.Mor syntactic M.T}
    (i : @Iso _ (morCategory (T := syntactic) M.co) F (LambdaPiInitial.mor hinj)) :
    F.fnc.obj empty ≅ (LambdaPiInitial.mor hinj).fnc.obj empty := by
  let _ := morCategory (T := syntactic) M.co
  exact
    { hom := i.hom.nat.app empty
      inv := i.inv.nat.app empty
      hom_inv_id := by
        have h : (i.hom.vcomp M.co i.inv).nat.app empty = 𝟙 (F.fnc.obj empty) := by
          rw [show i.hom.vcomp M.co i.inv = TwoCell.id M.co F from i.hom_inv_id]
          rfl
        exact h
      inv_hom_id := by
        have h : (i.inv.vcomp M.co i.hom).nat.app empty
            = 𝟙 ((LambdaPiInitial.mor hinj).fnc.obj empty) := by
          rw [show i.inv.vcomp M.co i.hom = TwoCell.id M.co (LambdaPiInitial.mor hinj) from
            i.inv_hom_id]
          rfl
        exact h }

/-- **A 1-cell out of the syntactic model isomorphic to the canonical interpretation sends the
empty context to a terminal object**, the canonical interpretation sending it to the terminal
object of the model. -/
noncomputable def isTerminal_empty_of_iso (hinj : M.PiInj) {F : Cwa.Mor syntactic M.T}
    (i : @Iso _ (morCategory (T := syntactic) M.co) F (LambdaPiInitial.mor hinj)) :
    IsTerminal (F.fnc.obj empty) :=
  IsTerminal.ofIso (isTerminal_mor_empty hinj) (isoObjEmpty hinj i).symm

/-- **The necessary conditions.**  A 1-cell out of the syntactic model of `λΠ` isomorphic to the
canonical interpretation preserves the universe and sends the empty context to a terminal object.
Both conditions are therefore forced, and the second is exactly the hypothesis under which
`LambdaPiBiInitial.nonempty_iso_mor_iff` reduces the comparison to the existence of 2-cells. -/
theorem iso_mor_necessary (hinj : M.PiInj) {F : Cwa.Mor syntactic M.T}
    (i : @Iso _ (morCategory (T := syntactic) M.co) F (LambdaPiInitial.mor hinj)) :
    F.PreservesUniverse univ M.Un ∧ Nonempty (IsTerminal (F.fnc.obj empty)) := by
  let _ := morCategory (T := syntactic) M.co
  exact ⟨preservesUniverse_of_twoCell hinj i.hom, ⟨isTerminal_empty_of_iso hinj i⟩⟩

end LambdaPiBiInitial
