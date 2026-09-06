/-
**A non-syntactic model of `λΠ`, on the pointed sets.**

`Start/PointedCwa.lean` builds a category with attributes on the category of pointed sets.  This
module equips it with everything the calculus `λΠ` asks of a model — a universe of small types,
products over the small types, codes for the products of two small types, and a terminal object —
and checks that its product former is *injective*, which is the hypothesis under which the syntax
of `λΠ` is initial.  Up to now the only model of `λΠ` in the library was the syntactic one, so this
is also the first proof that the notion is not vacuous outside the syntax.

The model is about the smallest one that can have an injective product former.  The universe of
small types is `ℕ`, every code decodes to a one-point type, and the code of a product is the Cantor
pairing of the codes of its domain and its body — injective, and with `Nat.pair 0 0 = 0`, so that
the code `0` is preserved by the product former.  That last equation is what allows the model to
live on *pointed* sets, which is what `Start/CwaLaxNotUnique.lean` needs.

Main definitions:

* `PointedModel.ptUniverse` — the universe of small types;
* `PointedModel.ptSmallPi` — the products over the small types;
* `PointedModel.ptPiClosed` — the codes for the products of two small types;
* `PointedModel.ptModel` — **the model of `λΠ` on the pointed sets**.

Main results:

* `PointedModel.ptModel_piInj` — **the product former of the model is injective**, so the syntax of
  `λΠ` is interpreted in it;
* `PointedModel.isTerminal_unitPt` — the one-point set is terminal.
-/

import Start.PointedCwa
import Start.LambdaPiInterpFun

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace PointedModel

/-! ### Generalities -/

/-- The one-point pointed set. -/
def unitPt : Pointed := ⟨PUnit, PUnit.unit⟩

/-- **The one-point set is terminal** in the pointed sets. -/
def isTerminal_unitPt : IsTerminal unitPt :=
  IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, rfl⟩)
    (fun _ _ => Pointed.Hom.ext (funext fun _ => rfl))

/-- **A term is determined by its values, up to a change of type.** -/
theorem tmCast_eq_of_val {Γ : Pointed} {A A' : ptCwa.Ty Γ} (h : A = A') {a : ptCwa.Tm Γ A}
    {a' : ptCwa.Tm Γ A'} (hv : ∀ γ, HEq (val a γ) (val a' γ)) : Cwa.tmCast h a = a' := by
  cases h
  exact val_injective (funext fun γ => eq_of_heq (hv γ))

/-- Transporting a term along an equality of types does not change its values. -/
theorem val_tmCast {Γ : Pointed} {A A' : ptCwa.Ty Γ} (h : A = A') (a : ptCwa.Tm Γ A) (γ : Γ.X) :
    HEq (val (Cwa.tmCast h a) γ) (val a γ) := by
  cases h
  rfl

/-- The values of a term at equal points agree. -/
theorem val_heq_congr {Γ : Pointed} {A : ptCwa.Ty Γ} (a : ptCwa.Tm Γ A) {γ γ' : Γ.X}
    (h : γ = γ') : HEq (val a γ) (val a γ') := by
  cases h
  rfl

/-! ### The universe of small types -/

/-- **The universe of small types**: the codes are the natural numbers, and every code decodes to a
one-point type. -/
@[reducible] def ptUniverse : Cwa.Universe ptCwa where
  U _ := fun _ => uE
  U_sub _ := rfl
  El a := fun γ => elE (val a γ)
  El_sub σ a := funext fun δ => congrArg elE (val_tmSub σ a δ).symm

/-- The value of a substituted code. -/
theorem val_sub {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (a : ptCwa.Tm Γ (ptUniverse.U Γ)) (δ : Δ.X) :
    val (ptUniverse.sub σ a) δ = val a (σ.toFun δ) :=
  val_tmSub σ a δ

/-- **The action of a substitution on a context extended by a small type**: since the fibres are
one-point sets it is the substitution on the base. -/
theorem extHom_toFun {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (a : ptCwa.Tm Γ (ptUniverse.U Γ))
    (p : extCarrier Δ (ptUniverse.El (ptUniverse.sub σ a))) :
    (ptUniverse.extHom σ a).toFun p = ⟨σ.toFun p.1, PUnit.unit⟩ :=
  extCarrier_ext (congrFun (congrArg Pointed.Hom.toFun
    (ptUniverse.isPullback_extHom σ a).w) p) rfl

/-! ### Products over the small types -/

variable {Γ Δ : Pointed}

/-- The dependent product over a small type: since the domain is a one-point set the product is the
body itself, with the code of the domain recorded in its tag. -/
def piTy (a : ptCwa.Tm Γ (ptUniverse.U Γ)) (B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))) :
    ptCwa.Ty Γ :=
  fun γ => piE (val a γ) (B ⟨γ, PUnit.unit⟩)

/-- Abstraction: a term of the body is a term of the product. -/
def lamTm {a : ptCwa.Tm Γ (ptUniverse.U Γ)} {B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))}
    (b : ptCwa.Tm (ptCwa.ext Γ (ptUniverse.El a)) B) : ptCwa.Tm Γ (piTy a B) :=
  mkTm _ (fun γ => val b ⟨γ, PUnit.unit⟩) (val_point b)

/-- Application: a term of the product is a term of the body. -/
def appTm {a : ptCwa.Tm Γ (ptUniverse.U Γ)} {B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))}
    (f : ptCwa.Tm Γ (piTy a B)) : ptCwa.Tm (ptCwa.ext Γ (ptUniverse.El a)) B :=
  mkTm _ (fun p => val f p.1) (val_point f)

@[simp] theorem val_lamTm {a : ptCwa.Tm Γ (ptUniverse.U Γ)}
    {B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))} (b : ptCwa.Tm (ptCwa.ext Γ (ptUniverse.El a)) B)
    (γ : Γ.X) : val (lamTm b) γ = val b ⟨γ, PUnit.unit⟩ := rfl

@[simp] theorem val_appTm {a : ptCwa.Tm Γ (ptUniverse.U Γ)}
    {B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))} (f : ptCwa.Tm Γ (piTy a B))
    (p : extCarrier Γ (ptUniverse.El a)) : val (appTm f) p = val f p.1 := rfl

/-- The product former is stable under substitution. -/
theorem piTy_sub (σ : Δ ⟶ Γ) (a : ptCwa.Tm Γ (ptUniverse.U Γ))
    (B : ptCwa.Ty (ptCwa.ext Γ (ptUniverse.El a))) :
    ptCwa.tySub σ (piTy a B)
      = piTy (ptUniverse.sub σ a) (ptCwa.tySub (ptUniverse.extHom σ a) B) := by
  funext δ
  change piE (val a (σ.toFun δ)) (B ⟨σ.toFun δ, PUnit.unit⟩)
      = piE (val (ptUniverse.sub σ a) δ) (B ((ptUniverse.extHom σ a).toFun ⟨δ, PUnit.unit⟩))
  rw [val_sub, extHom_toFun]

/-- **The products over the small types.** -/
@[reducible] def ptSmallPi : Cwa.Universe.SmallPi ptUniverse where
  Pi := piTy
  Pi_sub := piTy_sub
  lam := lamTm
  app := appTm
  app_lam _ := val_injective (funext fun _ => rfl)

/-- The code of the product of two small types: the Cantor pairing of the codes of its domain and
its body. -/
def codeTm (a : ptCwa.Tm Γ (ptUniverse.U Γ))
    (b : ptCwa.Tm (ptCwa.ext Γ (ptUniverse.El a))
      (ptUniverse.U (ptCwa.ext Γ (ptUniverse.El a)))) :
    ptCwa.Tm Γ (ptUniverse.U Γ) :=
  mkTm _ (fun γ => Nat.pair (val a γ) (val b ⟨γ, PUnit.unit⟩))
    (by
      have ha := val_point a
      have hb := val_point b
      change Nat.pair (val a Γ.point) (val b (extPt Γ (ptUniverse.El a)).point)
          = pt (ptUniverse.U Γ Γ.point)
      rw [ha, hb]
      rfl)

@[simp] theorem val_codeTm (a : ptCwa.Tm Γ (ptUniverse.U Γ))
    (b : ptCwa.Tm (ptCwa.ext Γ (ptUniverse.El a))
      (ptUniverse.U (ptCwa.ext Γ (ptUniverse.El a)))) (γ : Γ.X) :
    val (codeTm a b) γ = Nat.pair (val a γ) (val b ⟨γ, PUnit.unit⟩) := rfl

/-- **The universe is closed under the products of two small types**: the code of a product is the
Cantor pairing of the codes of its domain and its body. -/
def ptPiClosed : Cwa.Universe.NaturalPiClosed ptUniverse ptSmallPi where
  code := codeTm
  El_code _ _ := rfl
  code_sub σ a b := by
    refine val_injective (funext fun δ => ?_)
    have h : val (ptUniverse.sub (ptUniverse.extHom σ a) b) ⟨δ, PUnit.unit⟩
        = val b ⟨σ.toFun δ, PUnit.unit⟩ :=
      (val_sub (ptUniverse.extHom σ a) b ⟨δ, PUnit.unit⟩).trans
        (congrArg (val b) (extHom_toFun σ a ⟨δ, PUnit.unit⟩))
    have hl : val (ptUniverse.sub σ (codeTm a b)) δ
        = Nat.pair (val a (σ.toFun δ)) (val b ⟨σ.toFun δ, PUnit.unit⟩) :=
      (val_sub σ (codeTm a b) δ).trans (val_codeTm a b (σ.toFun δ))
    have hr : val (codeTm (ptUniverse.sub σ a) (ptUniverse.sub (ptUniverse.extHom σ a) b)) δ
        = Nat.pair (val a (σ.toFun δ)) (val b ⟨σ.toFun δ, PUnit.unit⟩) :=
      (val_codeTm _ _ δ).trans (congr (congrArg Nat.pair (val_sub σ a δ)) h)
    exact hl.trans hr.symm

/-! ### The model -/

/-- **The model of `λΠ` on the pointed sets.** -/
def ptModel : LambdaPi.Model.{1, 0, 0} Pointed where
  T := ptCwa
  co := ptExtCoherent
  Un := ptUniverse
  SP := ptSmallPi
  PC := ptPiClosed
  emp := unitPt
  empIsTerminal := isTerminal_unitPt
  lam_sub σ a B b := by
    refine tmCast_eq_of_val _ (fun δ => ?_)
    have h1 : HEq (val (ptCwa.tmSub σ (lamTm b)) δ) (val b ⟨σ.toFun δ, PUnit.unit⟩) :=
      heq_of_eq ((val_tmSub σ (lamTm b) δ).trans (val_lamTm b (σ.toFun δ)))
    have h2 : HEq (val (lamTm (ptCwa.tmSub (ptUniverse.extHom σ a) b)) δ)
        (val b ⟨σ.toFun δ, PUnit.unit⟩) := by
      refine HEq.trans (heq_of_eq (val_tmSub (ptUniverse.extHom σ a) b ⟨δ, PUnit.unit⟩)) ?_
      exact val_heq_congr b (extHom_toFun σ a ⟨δ, PUnit.unit⟩)
    exact h1.trans h2.symm
  app_sub σ a B f := by
    refine val_injective (funext fun p => ?_)
    have h1 : HEq (val (ptCwa.tmSub (ptUniverse.extHom σ a) (appTm f)) p)
        (val f (σ.toFun p.1)) := by
      refine HEq.trans (heq_of_eq (val_tmSub (ptUniverse.extHom σ a) (appTm f) p)) ?_
      refine HEq.trans (heq_of_eq (val_appTm f ((ptUniverse.extHom σ a).toFun p))) ?_
      exact val_heq_congr f (congrArg Sigma.fst (extHom_toFun σ a p))
    have h2 : HEq (val (appTm (Cwa.tmCast (piTy_sub σ a B) (ptCwa.tmSub σ f))) p)
        (val f (σ.toFun p.1)) := by
      refine HEq.trans (heq_of_eq (val_appTm _ p)) ?_
      refine HEq.trans (val_tmCast (piTy_sub σ a B) (ptCwa.tmSub σ f) p.1) ?_
      exact heq_of_eq (val_tmSub σ f p.1)
    exact eq_of_heq (h1.trans h2.symm)

/-- **The product former of the model is injective.** -/
theorem ptModel_piInj : ptModel.PiInj := by
  intro Γ a a' B B' h
  have hval : ∀ γ : Γ.X, val a γ = val a' γ ∧ B ⟨γ, PUnit.unit⟩ = B' ⟨γ, PUnit.unit⟩ :=
    fun γ => piE_injective (congrFun h γ)
  have haa : a = a' := val_injective (funext fun γ => (hval γ).1)
  subst haa
  have hBB : B = B' := funext fun p => (hval p.1).2
  subst hBB
  rfl

end PointedModel
