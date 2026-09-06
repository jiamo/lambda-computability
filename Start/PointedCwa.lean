/-
**A category with attributes on the pointed sets.**

Every model of `λΠ` in the library so far is the syntactic one.  This module builds a genuinely
semantic one, on the category `Pointed` of pointed sets, and it is built to be as degenerate as a
model of `λΠ` can be while still having an *injective* product former: the universe of small types
is `ℕ`, every small type decodes to a one-point set, and the code of a product of two small types
is the Cantor pairing of their codes.  Because `Nat.pair 0 0 = 0` the code `0` is a base point of
the universe, which is what lets the whole structure live on *pointed* sets.

The point of working over the pointed sets is `Start/CwaLaxNotUnique.lean`: the constant map to the
base point is a natural endomorphism of the identity functor of `Pointed`, so *every* functor into
`Pointed` — in particular the interpretation of the syntax of `λΠ` — has a natural endomorphism
besides the identity.

A *type* over a pointed set `Γ` is here a function `Γ → Bool × ℕ`: the boolean says whether the
type decodes to `ℕ` (that is the universe) or to a one-point set (that is a small type), and the
natural number is a tag which the product former uses to stay injective.  Keeping the decoding a
function of the boolean alone is what makes the equation `El (code a b) = Pi a (El b)` — the law
that a universe closed under products has to satisfy *on the nose* — hold by definition.

Main definitions:

* `PointedModel.TyE` — the type expressions of the model, `PointedModel.dec` their decoding and
  `PointedModel.pt` its base point;
* `PointedModel.piE` — the product former on type expressions;
* `PointedModel.ptCwa` — **the category with attributes** of pointed families;
* `PointedModel.val`, `PointedModel.mkTm` — the terms of the model as pointed dependent functions.

Main results:

* `PointedModel.piE_injective` — the product former on type expressions is injective;
* `PointedModel.isPullback_extend` — the context extension squares are pullbacks;
* `PointedModel.val_injective` — a term is determined by the function it denotes;
* `PointedModel.val_tmSub` — substitution of terms is composition;
* `PointedModel.ptExtCoherent` — the model is coherent, so its 1-cells have 2-cells.
-/

import Start.CwaSmall
import Start.CwaSubFunctorial
import Mathlib.CategoryTheory.Category.Pointed

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace PointedModel

/-! ### Type expressions and their decoding -/

/-- A **type expression** of the model: a boolean saying which set the type decodes to, and a
natural number tag.  The tag is what makes the product former injective; the decoding ignores
it. -/
abbrev TyE : Type := Bool × ℕ

/-- The decoding of the boolean part of a type expression: `true` is the universe of codes, `false`
a small type. -/
def decB : Bool → Type
  | true => ℕ
  | false => PUnit

/-- The base point of a decoded type expression. -/
def ptB : (b : Bool) → decB b
  | true => (0 : ℕ)
  | false => PUnit.unit

/-- The decoding of a type expression as a set. -/
def dec (t : TyE) : Type := decB t.1

/-- The base point of the decoding of a type expression. -/
def pt (t : TyE) : dec t := ptB t.1

/-- The type expression of the universe of codes: it decodes to `ℕ`. -/
def uE : TyE := (true, 0)

/-- The type expression of the small type named by the code `c`: it decodes to a one-point set. -/
def elE (c : ℕ) : TyE := (false, c)

/-- **The product former on type expressions**: the product of a body over the small type named by
`c` decodes exactly as the body does, and records `c` in its tag by Cantor pairing. -/
def piE (c : ℕ) (B : TyE) : TyE := (B.1, Nat.pair c B.2)

@[simp] theorem dec_piE (c : ℕ) (B : TyE) : dec (piE c B) = dec B := rfl

@[simp] theorem pt_piE (c : ℕ) (B : TyE) : pt (piE c B) = pt B := rfl

@[simp] theorem dec_elE (c : ℕ) : dec (elE c) = PUnit := rfl

@[simp] theorem dec_uE : dec uE = ℕ := rfl

/-- The code of the product of two small types, as a type expression. -/
theorem piE_elE (c d : ℕ) : piE c (elE d) = elE (Nat.pair c d) := rfl

/-- **The product former is injective**: it determines the code of its domain and its body. -/
theorem piE_injective {c c' : ℕ} {B B' : TyE} (h : piE c B = piE c' B') : c = c' ∧ B = B' := by
  have h1 : (piE c B).1 = (piE c' B').1 := by rw [h]
  have h2 : (piE c B).2 = (piE c' B').2 := by rw [h]
  simp only [piE] at h1 h2
  obtain ⟨hc, hB⟩ := Nat.pair_eq_pair.mp h2
  exact ⟨hc, Prod.ext h1 hB⟩

/-! ### Extended contexts -/

/-- The underlying set of a context extended by a type. -/
abbrev extCarrier (Γ : Pointed) (A : Γ.X → TyE) : Type := Σ γ : Γ.X, dec (A γ)

/-- Transport in a fibre along an equality of points. -/
def tr {Γ : Pointed} (A : Γ.X → TyE) {γ γ' : Γ.X} (h : γ = γ') (x : dec (A γ)) : dec (A γ') :=
  h ▸ x

@[simp] theorem tr_refl {Γ : Pointed} (A : Γ.X → TyE) {γ : Γ.X} (h : γ = γ) (x : dec (A γ)) :
    tr A h x = x := rfl

/-- Transport carries the base point to the base point. -/
@[simp] theorem tr_pt {Γ : Pointed} (A : Γ.X → TyE) {γ γ' : Γ.X} (h : γ = γ') :
    tr A h (pt (A γ)) = pt (A γ') := by
  cases h
  rfl

/-- Transport along a substituted equality. -/
theorem tr_map {Γ Δ : Pointed} (A : Γ.X → TyE) (σ : Δ ⟶ Γ) {δ δ' : Δ.X} (h : δ = δ')
    (x : dec (A (σ.toFun δ))) :
    tr (fun d => A (σ.toFun d)) h x = tr A (congrArg σ.toFun h) x := by
  cases h
  rfl

/-- Reassembling a point of an extended context from its transported fibre component. -/
theorem mk_tr {Γ : Pointed} {A : Γ.X → TyE} (p : extCarrier Γ A) {γ : Γ.X} (h : p.1 = γ) :
    (⟨γ, tr A h p.2⟩ : extCarrier Γ A) = p := by
  obtain ⟨g, x⟩ := p
  cases h
  rfl

/-- Two points of an extended context agree when their first components do and their fibre
components agree after transport. -/
theorem extCarrier_ext {Γ : Pointed} {A : Γ.X → TyE} {p q : extCarrier Γ A} (h : p.1 = q.1)
    (h' : tr A h p.2 = q.2) : p = q := by
  rw [← mk_tr p h, h']

/-- Equal points of an extended context have equal transported fibre components. -/
theorem tr_congr {Γ : Pointed} {A : Γ.X → TyE} {p q : extCarrier Γ A} (hpq : p = q) {γ : Γ.X}
    (h : p.1 = γ) (h' : q.1 = γ) : tr A h p.2 = tr A h' q.2 := by
  cases hpq
  rfl

/-- The context `Γ` extended by the type `A`, as a pointed set. -/
def extPt (Γ : Pointed) (A : Γ.X → TyE) : Pointed :=
  ⟨extCarrier Γ A, ⟨Γ.point, pt (A Γ.point)⟩⟩

@[simp] theorem extPt_point (Γ : Pointed) (A : Γ.X → TyE) :
    (extPt Γ A).point = (⟨Γ.point, pt (A Γ.point)⟩ : extCarrier Γ A) := rfl

/-- The display map of a type: the first projection out of the extended context. -/
def dispPt {Γ : Pointed} (A : Γ.X → TyE) : extPt Γ A ⟶ Γ :=
  ⟨Sigma.fst, rfl⟩

@[simp] theorem dispPt_toFun {Γ : Pointed} (A : Γ.X → TyE) (p : extCarrier Γ A) :
    (dispPt A).toFun p = p.1 := rfl

/-- The action of a substitution on extended contexts. -/
def extendPt {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (A : Γ.X → TyE) :
    extPt Δ (fun δ => A (σ.toFun δ)) ⟶ extPt Γ A :=
  ⟨fun p => ⟨σ.toFun p.1, p.2⟩,
    congrArg (fun γ => (⟨γ, pt (A γ)⟩ : extCarrier Γ A)) σ.map_point⟩

@[simp] theorem extendPt_toFun {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (A : Γ.X → TyE)
    (p : extCarrier Δ fun δ => A (σ.toFun δ)) :
    (extendPt σ A).toFun p = ⟨σ.toFun p.1, p.2⟩ := rfl

/-- **The context extension squares are pullbacks.**  A map into the extended context is a map into
the context together with an element of the fibre, and the fibre over a point is the fibre over its
image. -/
theorem isPullback_extend {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (A : Γ.X → TyE) :
    IsPullback (extendPt σ A) (dispPt (fun δ => A (σ.toFun δ))) (dispPt A) σ := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (W := extPt Δ fun δ => A (σ.toFun δ))
    (by ext p; rfl) (fun s => ?lift) (fun s => ?fac₁) (fun s => ?fac₂) (fun s m h₁ h₂ => ?uniq))
  case lift =>
    have hx : ∀ x, ((PullbackCone.fst s).toFun x).1 = σ.toFun ((PullbackCone.snd s).toFun x) :=
      fun x => congrFun (congrArg Pointed.Hom.toFun s.condition) x
    refine ⟨fun x => ⟨(PullbackCone.snd s).toFun x, tr A (hx x) ((PullbackCone.fst s).toFun x).2⟩,
      ?_⟩
    have h₀ : (PullbackCone.fst s).toFun s.pt.point = (extPt Γ A).point :=
      (PullbackCone.fst s).map_point
    have h₁ : (PullbackCone.snd s).toFun s.pt.point = Δ.point := (PullbackCone.snd s).map_point
    have hval : tr A (hx s.pt.point) ((PullbackCone.fst s).toFun s.pt.point).2
        = pt (A (σ.toFun ((PullbackCone.snd s).toFun s.pt.point))) := by
      rw [tr_congr h₀ (hx s.pt.point) (h₀ ▸ hx s.pt.point)]
      exact tr_pt A _
    refine Eq.trans ?_ (congrArg
      (fun d => (⟨d, pt (A (σ.toFun d))⟩ : extCarrier Δ fun δ => A (σ.toFun δ))) h₁)
    exact congrArg (fun x => (⟨(PullbackCone.snd s).toFun s.pt.point, x⟩ :
      extCarrier Δ fun δ => A (σ.toFun δ))) hval
  case fac₁ =>
    refine Pointed.Hom.ext (funext fun x => ?_)
    exact mk_tr ((PullbackCone.fst s).toFun x) _
  case fac₂ => exact Pointed.Hom.ext (funext fun _ => rfl)
  case uniq =>
    refine Pointed.Hom.ext (funext fun x => ?_)
    have h₂' : (m.toFun x).1 = (PullbackCone.snd s).toFun x :=
      congrFun (congrArg Pointed.Hom.toFun h₂) x
    have h₁' : (⟨σ.toFun (m.toFun x).1, (m.toFun x).2⟩ : extCarrier Γ A)
        = (PullbackCone.fst s).toFun x :=
      congrFun (congrArg Pointed.Hom.toFun h₁) x
    refine extCarrier_ext h₂' ?_
    rw [tr_map A σ h₂']
    exact tr_congr h₁' _ _

/-- **The category with attributes of pointed families.** -/
@[reducible] def ptCwa : Cwa.{1, 0, 0} Pointed where
  Ty Γ := Γ.X → TyE
  tySub σ A := fun δ => A (σ.toFun δ)
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  ext := extPt
  disp := dispPt
  extend := extendPt
  isPullback := isPullback_extend

@[simp] theorem ptCwa_tySub {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (A : ptCwa.Ty Γ) :
    ptCwa.tySub σ A = fun δ => A (σ.toFun δ) := rfl

@[simp] theorem ptCwa_ext (Γ : Pointed) (A : ptCwa.Ty Γ) : ptCwa.ext Γ A = extPt Γ A := rfl

@[simp] theorem ptCwa_disp {Γ : Pointed} (A : ptCwa.Ty Γ) : ptCwa.disp A = dispPt A := rfl

@[simp] theorem ptCwa_extend {Γ Δ : Pointed} (σ : Δ ⟶ Γ) (A : ptCwa.Ty Γ) :
    ptCwa.extend σ A = extendPt σ A := rfl

/-- **The model is coherent**: the action of a substitution on extended contexts is functorial. -/
theorem ptExtCoherent : Cwa.ExtCoherent ptCwa where
  extend_id _ := rfl
  extend_comp _ _ _ := rfl

/-! ### Terms -/

variable {Γ Δ : Pointed}

/-- The first component of the value of a term is the point it was taken at. -/
theorem tm_fst (A : ptCwa.Ty Γ) (a : ptCwa.Tm Γ A) (γ : Γ.X) : (a.1.toFun γ).1 = γ :=
  congrFun (congrArg Pointed.Hom.toFun a.2) γ

/-- **The dependent function denoted by a term.** -/
def val {A : ptCwa.Ty Γ} (a : ptCwa.Tm Γ A) (γ : Γ.X) : dec (A γ) :=
  tr A (tm_fst A a γ) (a.1.toFun γ).2

/-- The underlying map of a term, computed from the function it denotes. -/
theorem tm_toFun {A : ptCwa.Ty Γ} (a : ptCwa.Tm Γ A) (γ : Γ.X) :
    a.1.toFun γ = ⟨γ, val a γ⟩ :=
  (mk_tr (a.1.toFun γ) (tm_fst A a γ)).symm

/-- **A term out of a pointed dependent function.** -/
def mkTm (A : ptCwa.Ty Γ) (f : (γ : Γ.X) → dec (A γ)) (hf : f Γ.point = pt (A Γ.point)) :
    ptCwa.Tm Γ A :=
  ⟨⟨fun γ => ⟨γ, f γ⟩, congrArg (fun x => (⟨Γ.point, x⟩ : extCarrier Γ A)) hf⟩,
    Pointed.Hom.ext (funext fun _ => rfl)⟩

@[simp] theorem val_mkTm (A : ptCwa.Ty Γ) (f : (γ : Γ.X) → dec (A γ))
    (hf : f Γ.point = pt (A Γ.point)) : val (mkTm A f hf) = f := rfl

/-- **A term is determined by the function it denotes.** -/
theorem val_injective {A : ptCwa.Ty Γ} {a b : ptCwa.Tm Γ A} (h : val a = val b) : a = b := by
  refine Subtype.ext (Pointed.Hom.ext (funext fun γ => ?_))
  rw [tm_toFun a γ, tm_toFun b γ, h]

/-- The function denoted by a term carries the base point to the base point. -/
theorem val_point {A : ptCwa.Ty Γ} (a : ptCwa.Tm Γ A) : val a Γ.point = pt (A Γ.point) := by
  have h : a.1.toFun Γ.point = (extPt Γ A).point := a.1.map_point
  have := tr_congr h (tm_fst A a Γ.point) (h ▸ tm_fst A a Γ.point)
  rw [val, this]
  exact tr_pt A _

/-- **Substitution of terms is composition.** -/
theorem val_tmSub {A : ptCwa.Ty Γ} (σ : Δ ⟶ Γ) (a : ptCwa.Tm Γ A) (δ : Δ.X) :
    val (ptCwa.tmSub σ a) δ = val a (σ.toFun δ) := by
  have hext := Cwa.tmSub_extend (T := ptCwa) σ a
  have h := congrFun (congrArg Pointed.Hom.toFun hext) δ
  have hl : (extendPt σ A).toFun ((ptCwa.tmSub σ a).1.toFun δ)
      = ⟨σ.toFun δ, val (ptCwa.tmSub σ a) δ⟩ := by
    rw [tm_toFun (ptCwa.tmSub σ a) δ]
    rfl
  have hr : a.1.toFun (σ.toFun δ) = ⟨σ.toFun δ, val a (σ.toFun δ)⟩ := tm_toFun a _
  have h' : (⟨σ.toFun δ, val (ptCwa.tmSub σ a) δ⟩ : extCarrier Γ A)
      = ⟨σ.toFun δ, val a (σ.toFun δ)⟩ := by
    rw [← hl, ← hr]
    exact h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h').2

end PointedModel
