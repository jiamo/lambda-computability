/-
The syntactic category of the simply typed lambda calculus, and the Lambek half of the
Curry–Howard–Lambek correspondence: **types are objects, terms are morphisms, and the resulting
category is cartesian closed**.

Objects are the types of `Start/Stlc.lean`; a morphism `A ⟶ B` is a term with a single free
variable of type `A`, taken up to βη-conversion; composition is substitution.

* `Stlc.category` — the syntactic category;
* `Stlc.isTerminalUnit`, `Stlc.prodCone` — the unit type is terminal and the product type is a
  binary product, so the syntactic category has finite products;
* `Stlc.cartesianMonoidal` — the resulting `CartesianMonoidalCategory` structure, whose monoidal
  product is the product type;
* `Stlc.closed`, `Stlc.monoidalClosed` — the function type is an exponential: `- × A ⊣ A ⇒ -`,
  by β and η.  Together with the previous item this says exactly that the syntactic category is
  cartesian closed in the sense of Mathlib.
-/

import Start.Stlc
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Stlc

open CategoryTheory Limits MonoidalCategory

------------------------------------------------------------------------
-- Substitution of the unique variable
------------------------------------------------------------------------

/-- The substitution of the unique variable of a one-variable context by a term. -/
def one {Δ : Ctx} {A : Ty} (f : Tm Δ A) : Sub [A] Δ := fun _ v =>
  match v with
  | Var.zero => f
  | Var.succ v => nomatch v

theorem one_var_zero (A : Ty) : one (Tm.var (Var.zero (Γ := []) (A := A))) = Sub.id [A] := by
  funext B v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

theorem one_comp {Δ : Ctx} {A B : Ty} (f : Tm Δ A) (g : Tm [A] B) :
    Sub.comp (one f) (one g) = one (sub (one f) g) := by
  funext C v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

/-- Composition of one-variable terms is substitution. -/
def cmp {A B C : Ty} (g : Tm [B] C) (f : Tm [A] B) : Tm [A] C := sub (one f) g

theorem cmp_id_left {A B : Ty} (f : Tm [A] B) : cmp (Tm.var Var.zero) f = f := rfl

theorem cmp_id_right {A B : Ty} (f : Tm [A] B) : cmp f (Tm.var Var.zero) = f := by
  change sub (one (Tm.var Var.zero)) f = f
  rw [one_var_zero, sub_id]

theorem cmp_assoc {A B C D : Ty} (h : Tm [C] D) (g : Tm [B] C) (f : Tm [A] B) :
    cmp (cmp h g) f = cmp h (cmp g f) := by
  change sub (one f) (sub (one g) h) = sub (one (sub (one f) g)) h
  rw [sub_sub, one_comp]

theorem cmp_congr {A B C : Ty} {g g' : Tm [B] C} {f f' : Tm [A] B} (hg : Conv g g')
    (hf : Conv f f') : Conv (cmp g f) (cmp g' f') := by
  refine Conv.trans (hg.sub (one f)) (Conv.subCongr g' ?_)
  intro D v
  cases v with
  | zero => exact hf
  | succ v => exact nomatch v

------------------------------------------------------------------------
-- The syntactic category
------------------------------------------------------------------------

/-- Morphisms of the syntactic category: terms with one free variable, modulo conversion. -/
def Hom (A B : Ty) : Type := Quotient (convSetoid [A] B)

/-- The morphism represented by a term. -/
def hom {A B : Ty} (t : Tm [A] B) : Hom A B := Quotient.mk _ t

theorem hom_eq {A B : Ty} {t u : Tm [A] B} (h : Conv t u) : hom t = hom u := Quotient.sound h

@[elab_as_elim]
theorem Hom.ind {A B : Ty} {motive : Hom A B → Prop} (h : ∀ t : Tm [A] B, motive (hom t))
    (f : Hom A B) : motive f := Quotient.ind h f

/-- Composition in the syntactic category. -/
def homComp {A B C : Ty} (f : Hom A B) (g : Hom B C) : Hom A C :=
  Quotient.map₂ (fun (f : Tm [A] B) (g : Tm [B] C) => cmp g f)
    (fun _ _ hf _ _ hg => cmp_congr hg hf) f g

@[simp] theorem homComp_hom {A B C : Ty} (f : Tm [A] B) (g : Tm [B] C) :
    homComp (hom f) (hom g) = hom (cmp g f) := rfl

/-- **The syntactic category of the simply typed lambda calculus**: objects are types, morphisms
are terms with one free variable modulo βη-conversion, composition is substitution. -/
instance category : Category Ty where
  Hom := Hom
  id _ := hom (Tm.var Var.zero)
  comp := homComp
  id_comp f := by
    induction f using Hom.ind with
    | _ t =>
      change hom (cmp t (Tm.var Var.zero)) = hom t
      rw [cmp_id_right]
  comp_id f := by
    induction f using Hom.ind with
    | _ t =>
      change hom (cmp (Tm.var Var.zero) t) = hom t
      rw [cmp_id_left]
  assoc f g h := by
    induction f using Hom.ind with
    | _ f =>
      induction g using Hom.ind with
      | _ g =>
        induction h using Hom.ind with
        | _ h => exact congrArg hom (cmp_assoc h g f).symm

theorem id_def (A : Ty) : 𝟙 A = hom (Tm.var (Var.zero (Γ := []) (A := A))) := rfl

theorem comp_def {A B C : Ty} (f : Tm [A] B) (g : Tm [B] C) :
    (hom f ≫ hom g : A ⟶ C) = hom (cmp g f) := rfl

------------------------------------------------------------------------
-- Finite products
------------------------------------------------------------------------

/-- Every morphism into the unit type is the constant `⋆`. -/
theorem hom_unit_eq {A : Ty} (f : A ⟶ Ty.unit) : f = hom Tm.star := by
  induction f using Hom.ind with
  | _ t => exact hom_eq (Conv.unit_eta t)

/-- The unit type is a terminal object. -/
def isTerminalUnit : IsTerminal (Ty.unit : Ty) :=
  IsTerminal.ofUniqueHom (fun _ => hom Tm.star) (fun _ f => hom_unit_eq f)

/-- The chosen terminal cone. -/
def terminalCone : LimitCone (Functor.empty.{0} Ty) where
  cone := asEmptyCone (Ty.unit : Ty)
  isLimit := isTerminalUnit

/-- The first projection. -/
def projFst (A B : Ty) : Ty.prod A B ⟶ A := hom (Tm.fst (Tm.var Var.zero))

/-- The second projection. -/
def projSnd (A B : Ty) : Ty.prod A B ⟶ B := hom (Tm.snd (Tm.var Var.zero))

/-- The pairing of two morphisms. -/
def pairHom {C A B : Ty} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ Ty.prod A B :=
  Quotient.map₂ (fun (f : Tm [C] A) (g : Tm [C] B) => Tm.pair f g)
    (fun _ _ hf _ _ hg => Conv.pair hf hg) f g

@[simp] theorem pairHom_hom {C A B : Ty} (f : Tm [C] A) (g : Tm [C] B) :
    pairHom (hom f) (hom g) = hom (Tm.pair f g) := rfl

@[simp] theorem pairHom_fst {C A B : Ty} (f : C ⟶ A) (g : C ⟶ B) :
    pairHom f g ≫ projFst A B = f := by
  induction f using Hom.ind with
  | _ f =>
    induction g using Hom.ind with
    | _ g => exact hom_eq (Conv.fst_pair f g)

@[simp] theorem pairHom_snd {C A B : Ty} (f : C ⟶ A) (g : C ⟶ B) :
    pairHom f g ≫ projSnd A B = g := by
  induction f using Hom.ind with
  | _ f =>
    induction g using Hom.ind with
    | _ g => exact hom_eq (Conv.snd_pair f g)

theorem pairHom_unique {C A B : Ty} (f : C ⟶ A) (g : C ⟶ B) (m : C ⟶ Ty.prod A B)
    (h1 : m ≫ projFst A B = f) (h2 : m ≫ projSnd A B = g) : m = pairHom f g := by
  subst h1; subst h2
  induction m using Hom.ind with
  | _ m => exact (hom_eq (Conv.pair_eta m)).symm

/-- The product type is a binary product. -/
def prodCone (A B : Ty) : LimitCone (pair A B) where
  cone := BinaryFan.mk (projFst A B) (projSnd A B)
  isLimit :=
    BinaryFan.IsLimit.mk _ (fun f g => pairHom f g) (fun f g => pairHom_fst f g)
      (fun f g => pairHom_snd f g)
      (fun f g m h1 h2 => pairHom_unique f g m h1 h2)

/-- The syntactic category is cartesian monoidal: the monoidal product is the product type and
the unit is the unit type. -/
instance cartesianMonoidal : CartesianMonoidalCategory Ty :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone (fun A B => prodCone A B)

------------------------------------------------------------------------
-- Substitution lemmas for the one-variable calculus
------------------------------------------------------------------------

theorem comp_one {Γ Δ : Ctx} {A : Ty} (σ : Sub Γ Δ) (t : Tm Γ A) :
    Sub.comp σ (one t) = one (sub σ t) := by
  funext C v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

theorem sub_sub_one {Γ Δ : Ctx} {A B : Ty} (σ : Sub Γ Δ) (t : Tm Γ A) (u : Tm [A] B) :
    sub σ (sub (one t) u) = sub (one (sub σ t)) u := by
  rw [sub_sub, comp_one]

/-- Instantiating a term that was weakened under a binder by the variable `0`. -/
theorem sub_single_var_ren {Γ : Ctx} {A B : Ty} (t : Tm (A :: Γ) B) :
    sub (Sub.single (Tm.var Var.zero)) (ren ((Ren.wk A).lift A) t) = t := by
  rw [sub_ren]
  have h : (Sub.single (Tm.var (Var.zero (Γ := Γ) (A := A)))).compRen ((Ren.wk A).lift A)
      = Sub.id (A :: Γ) := by
    funext C v
    cases v with
    | zero => rfl
    | succ v => rfl
  rw [h, sub_id]

/-- η for a weakened abstraction. -/
theorem conv_app_wk_lam {X Y Z : Ty} (b : Tm [X, Y] Z) :
    Conv (Tm.app (wk X (Tm.lam b)) (Tm.var Var.zero)) b := by
  have h : wk X (Tm.lam b) = Tm.lam (ren ((Ren.wk X).lift X) b) := rfl
  rw [h]
  refine Conv.trans (Conv.beta _ _) ?_
  rw [show inst (ren ((Ren.wk X).lift X) b) (Tm.var Var.zero)
      = sub (Sub.single (Tm.var Var.zero)) (ren ((Ren.wk X).lift X) b) from rfl,
    sub_single_var_ren]

------------------------------------------------------------------------
-- The exponential functor
------------------------------------------------------------------------

/-- The application of the second variable to the first, `fun (x : X) (f : X ⇒ B) => f x`. -/
def appVar (X B : Ty) : Tm [X, Ty.arrow X B] B :=
  Tm.app (Tm.var (Var.succ Var.zero)) (Tm.var Var.zero)

/-- Post-composition with `g`, as a term `(X ⇒ B) → (X ⇒ B')`. -/
def expTm {X B B' : Ty} (g : Tm [B] B') : Tm [Ty.arrow X B] (Ty.arrow X B') :=
  Tm.lam (sub (one (appVar X B)) g)

theorem expTm_congr {X B B' : Ty} {g g' : Tm [B] B'} (h : Conv g g') :
    Conv (expTm (X := X) g) (expTm g') :=
  Conv.lam (h.sub _)

/-- Post-composition, as a morphism of the syntactic category. -/
def expHom (X : Ty) {B B' : Ty} (g : B ⟶ B') : Ty.arrow X B ⟶ Ty.arrow X B' :=
  Quotient.map (fun (g : Tm [B] B') => expTm (X := X) g) (fun _ _ h => expTm_congr h) g

@[simp] theorem expHom_hom (X : Ty) {B B' : Ty} (g : Tm [B] B') :
    expHom X (hom g) = hom (expTm g) := rfl

theorem expTm_id (X B : Ty) : Conv (expTm (X := X) (Tm.var (Var.zero (Γ := []) (A := B))))
    (Tm.var Var.zero) := by
  have h : expTm (X := X) (Tm.var (Var.zero (Γ := []) (A := B)))
      = Tm.lam (Tm.app (wk X (Tm.var Var.zero)) (Tm.var Var.zero)) := rfl
  rw [h]
  exact (Conv.eta (Tm.var Var.zero)).symm

theorem expTm_comp (X : Ty) {B₀ B₁ B₂ : Ty} (g₁ : Tm [B₀] B₁) (g₂ : Tm [B₁] B₂) :
    Conv (expTm (X := X) (cmp g₂ g₁)) (cmp (expTm (X := X) g₂) (expTm (X := X) g₁)) := by
  have hl : expTm (X := X) (cmp g₂ g₁)
      = Tm.lam (sub (one (sub (one (appVar X B₀)) g₁)) g₂) := by
    change Tm.lam (sub (one (appVar X B₀)) (sub (one g₁) g₂)) = _
    rw [sub_sub_one]
  have hr : cmp (expTm (X := X) g₂) (expTm (X := X) g₁)
      = Tm.lam (sub (one (Tm.app (wk X (expTm (X := X) g₁)) (Tm.var Var.zero))) g₂) := by
    change Tm.lam (sub ((one (expTm (X := X) g₁)).lift X) (sub (one (appVar X B₁)) g₂)) = _
    rw [sub_sub_one]
    rfl
  rw [hl, hr]
  refine Conv.lam (Conv.subCongr g₂ ?_)
  intro C v
  cases v with
  | zero => exact (conv_app_wk_lam _).symm
  | succ v => exact nomatch v

/-- The exponential functor `X ⇒ -`. -/
def expFunctor (X : Ty) : Ty ⥤ Ty where
  obj B := Ty.arrow X B
  map g := expHom X g
  map_id B := by
    change expHom X (hom (Tm.var Var.zero)) = hom (Tm.var Var.zero)
    exact hom_eq (expTm_id X B)
  map_comp {B₀ B₁ B₂} g₁ g₂ := by
    induction g₁ using Hom.ind with
    | _ g₁ =>
      induction g₂ using Hom.ind with
      | _ g₂ => exact hom_eq (expTm_comp X g₁ g₂)

------------------------------------------------------------------------
-- Currying
------------------------------------------------------------------------

theorem fst_eq (X Y : Ty) : CartesianMonoidalCategory.fst X Y = projFst X Y := rfl

theorem snd_eq (X Y : Ty) : CartesianMonoidalCategory.snd X Y = projSnd X Y := rfl

theorem whiskerLeft_eq (X : Ty) {Y Y' : Ty} (f : Y ⟶ Y') :
    (X ◁ f : X ⊗ Y ⟶ X ⊗ Y') = pairHom (projFst X Y) (projSnd X Y ≫ f) := by
  refine pairHom_unique _ _ _ ?_ ?_
  · exact CartesianMonoidalCategory.whiskerLeft_fst X f
  · exact CartesianMonoidalCategory.whiskerLeft_snd X f

/-- The pair of the two variables of a two-variable context. -/
def pairVar (X Y : Ty) : Tm [X, Y] (Ty.prod X Y) :=
  Tm.pair (Tm.var Var.zero) (Tm.var (Var.succ Var.zero))

/-- Currying, on terms. -/
def curryTm {X Y Z : Ty} (f : Tm [Ty.prod X Y] Z) : Tm [Y] (Ty.arrow X Z) :=
  Tm.lam (sub (one (pairVar X Y)) f)

/-- The unique variable of a one-variable context. -/
def v0 (A : Ty) : Tm [A] A := Tm.var Var.zero

/-- Uncurrying, on terms. -/
def uncurryTm {X Y Z : Ty} (g : Tm [Y] (Ty.arrow X Z)) : Tm [Ty.prod X Y] Z :=
  Tm.app (sub (one (Tm.snd (v0 (Ty.prod X Y)))) g) (Tm.fst (v0 (Ty.prod X Y)))

theorem curryTm_congr {X Y Z : Ty} {f f' : Tm [Ty.prod X Y] Z} (h : Conv f f') :
    Conv (curryTm f) (curryTm f') := Conv.lam (h.sub _)

theorem uncurryTm_congr {X Y Z : Ty} {g g' : Tm [Y] (Ty.arrow X Z)} (h : Conv g g') :
    Conv (uncurryTm g) (uncurryTm g') := Conv.app (h.sub _) (Conv.refl _)

/-- Weakening as a one-variable substitution. -/
theorem wk_eq_sub_one {X Y : Ty} {A : Ty} (g : Tm [Y] A) :
    wk X g = sub (one (Tm.var (Var.succ (B := X) (Var.zero (Γ := []) (A := Y))))) g := by
  rw [wk, ren_eq_sub]
  congr 1
  funext C v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

theorem uncurry_curry {X Y Z : Ty} (f : Tm [Ty.prod X Y] Z) :
    Conv (uncurryTm (curryTm f)) f := by
  have h1 : uncurryTm (curryTm (X := X) f)
      = Tm.app (Tm.lam (sub ((one (Tm.snd (v0 (Ty.prod X Y)))).lift X)
          (sub (one (pairVar X Y)) f))) (Tm.fst (v0 (Ty.prod X Y))) := rfl
  rw [h1]
  refine Conv.trans (Conv.beta _ _) ?_
  have h2 : inst (sub ((one (Tm.snd (v0 (Ty.prod X Y)))).lift X) (sub (one (pairVar X Y)) f))
      (Tm.fst (v0 (Ty.prod X Y)))
      = sub (one (Tm.pair (Tm.fst (v0 (Ty.prod X Y))) (Tm.snd (v0 (Ty.prod X Y))))) f := by
    change sub (Sub.single (Tm.fst (v0 (Ty.prod X Y))))
      (sub ((one (Tm.snd (v0 (Ty.prod X Y)))).lift X) (sub (one (pairVar X Y)) f)) = _
    rw [sub_sub_one, sub_sub_one]
    rfl
  rw [h2]
  have hc : Conv (sub (one (Tm.pair (Tm.fst (v0 (Ty.prod X Y))) (Tm.snd (v0 (Ty.prod X Y))))) f)
      (sub (Sub.id [Ty.prod X Y]) f) := by
    refine Conv.subCongr f ?_
    intro C v
    cases v with
    | zero => exact Conv.pair_eta _
    | succ v => exact nomatch v
  rwa [sub_id] at hc

theorem curry_uncurry {X Y Z : Ty} (g : Tm [Y] (Ty.arrow X Z)) :
    Conv (curryTm (uncurryTm g)) g := by
  have h1 : curryTm (uncurryTm (X := X) g)
      = Tm.lam (Tm.app (sub (one (Tm.snd (pairVar X Y))) g) (Tm.fst (pairVar X Y))) := by
    change Tm.lam (sub (one (pairVar X Y))
      (Tm.app (sub (one (Tm.snd (v0 (Ty.prod X Y)))) g) (Tm.fst (v0 (Ty.prod X Y))))) = _
    change Tm.lam (Tm.app (sub (one (pairVar X Y)) (sub (one (Tm.snd (v0 (Ty.prod X Y)))) g))
      (Tm.fst (sub (one (pairVar X Y)) (v0 (Ty.prod X Y))))) = _
    rw [sub_sub_one]
    rfl
  rw [h1]
  refine Conv.trans (Conv.lam (Conv.app ?_ (Conv.fst_pair _ _))) (Conv.eta g).symm
  rw [wk_eq_sub_one]
  refine Conv.subCongr g ?_
  intro C v
  cases v with
  | zero => exact Conv.snd_pair _ _
  | succ v => exact nomatch v

/-- Currying, as a bijection of morphisms. -/
def curryHom {X Y Z : Ty} (f : Ty.prod X Y ⟶ Z) : Y ⟶ Ty.arrow X Z :=
  Quotient.map (fun (f : Tm [Ty.prod X Y] Z) => curryTm f) (fun _ _ h => curryTm_congr h) f

/-- Uncurrying, as a bijection of morphisms. -/
def uncurryHom {X Y Z : Ty} (g : Y ⟶ Ty.arrow X Z) : Ty.prod X Y ⟶ Z :=
  Quotient.map (fun (g : Tm [Y] (Ty.arrow X Z)) => uncurryTm g) (fun _ _ h => uncurryTm_congr h) g

@[simp] theorem curryHom_hom {X Y Z : Ty} (f : Tm [Ty.prod X Y] Z) :
    curryHom (X := X) (hom f) = hom (curryTm f) := rfl

@[simp] theorem uncurryHom_hom {X Y Z : Ty} (g : Tm [Y] (Ty.arrow X Z)) :
    uncurryHom (X := X) (hom g) = hom (uncurryTm g) := rfl

/-- Currying is a bijection between `X × Y ⟶ Z` and `Y ⟶ (X ⇒ Z)`. -/
def curryEquiv (X Y Z : Ty) : (Ty.prod X Y ⟶ Z) ≃ (Y ⟶ Ty.arrow X Z) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv f := by
    induction f using Hom.ind with
    | _ f => exact hom_eq (uncurry_curry f)
  right_inv g := by
    induction g using Hom.ind with
    | _ g => exact hom_eq (curry_uncurry g)

------------------------------------------------------------------------
-- The exponential adjunction
------------------------------------------------------------------------

/-- Naturality of currying in the codomain. -/
theorem curryTm_cmp {X Y Z Z' : Ty} (f : Tm [Ty.prod X Y] Z) (g : Tm [Z] Z') :
    Conv (curryTm (X := X) (cmp g f)) (cmp (expTm (X := X) g) (curryTm f)) := by
  have hl : curryTm (X := X) (cmp g f) = Tm.lam (sub (one (sub (one (pairVar X Y)) f)) g) := by
    change Tm.lam (sub (one (pairVar X Y)) (sub (one f) g)) = _
    rw [sub_sub_one]
  have hr : cmp (expTm (X := X) g) (curryTm f)
      = Tm.lam (sub (one (Tm.app (wk X (curryTm (X := X) f)) (Tm.var Var.zero))) g) := by
    change Tm.lam (sub ((one (curryTm (X := X) f)).lift X) (sub (one (appVar X Z)) g)) = _
    rw [sub_sub_one]
    rfl
  rw [hl, hr]
  refine Conv.lam (Conv.subCongr g ?_)
  intro C v
  cases v with
  | zero => exact (conv_app_wk_lam _).symm
  | succ v => exact nomatch v

/-- Naturality of uncurrying in the domain. -/
theorem uncurryTm_cmp {X Y Y' Z : Ty} (f : Tm [Y] Y') (g : Tm [Y'] (Ty.arrow X Z)) :
    Conv (uncurryTm (X := X) (cmp g f))
      (cmp (uncurryTm g) (Tm.pair (Tm.fst (v0 (Ty.prod X Y)))
        (sub (one (Tm.snd (v0 (Ty.prod X Y)))) f))) := by
  set P : Tm [Ty.prod X Y] (Ty.prod X Y') :=
    Tm.pair (Tm.fst (v0 (Ty.prod X Y))) (sub (one (Tm.snd (v0 (Ty.prod X Y)))) f) with hP
  have hl : uncurryTm (X := X) (cmp g f)
      = Tm.app (sub (one (sub (one (Tm.snd (v0 (Ty.prod X Y)))) f)) g)
          (Tm.fst (v0 (Ty.prod X Y))) := by
    change Tm.app (sub (one (Tm.snd (v0 (Ty.prod X Y)))) (sub (one f) g))
      (Tm.fst (v0 (Ty.prod X Y))) = _
    rw [sub_sub_one]
  have hr : cmp (uncurryTm (X := X) g) P = Tm.app (sub (one (Tm.snd P)) g) (Tm.fst P) := by
    change Tm.app (sub (one P) (sub (one (Tm.snd (v0 (Ty.prod X Y')))) g))
      (Tm.fst (sub (one P) (v0 (Ty.prod X Y')))) = _
    rw [sub_sub_one]
    rfl
  rw [hl, hr]
  refine Conv.app (Conv.subCongr g ?_) (Conv.fst_pair _ _).symm
  intro C v
  cases v with
  | zero => exact (Conv.snd_pair _ _).symm
  | succ v => exact nomatch v

theorem tensorObj_eq (X Y : Ty) : (X ⊗ Y : Ty) = Ty.prod X Y := rfl

theorem tensorLeft_map (X : Ty) {Y Y' : Ty} (f : Y ⟶ Y') :
    (tensorLeft X).map f = (X ◁ f : X ⊗ Y ⟶ X ⊗ Y') := rfl

/-- Whiskering by `X` on the left, computed on terms. -/
theorem whiskerLeft_hom (X : Ty) {Y Y' : Ty} (f : Tm [Y] Y') :
    (X ◁ hom f : X ⊗ Y ⟶ X ⊗ Y')
      = hom (Tm.pair (Tm.fst (v0 (Ty.prod X Y))) (sub (one (Tm.snd (v0 (Ty.prod X Y)))) f)) := by
  rw [whiskerLeft_eq]
  rfl

/-- **Every type is exponentiable in the syntactic category**: `- × X ⊣ X ⇒ -`, by β and η. -/
instance closed (X : Ty) : Closed X where
  rightAdj := expFunctor X
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun Y Z => curryEquiv X Y Z
      homEquiv_naturality_left_symm := by
        intro Y' Y Z f g
        induction f using Hom.ind with
        | _ f =>
          induction g using Hom.ind with
          | _ g =>
            rw [tensorLeft_map, whiskerLeft_hom]
            exact hom_eq (uncurryTm_cmp f g)
      homEquiv_naturality_right := by
        intro Y Z Z' f g
        induction f using Hom.ind with
        | _ f =>
          induction g using Hom.ind with
          | _ g => exact hom_eq (curryTm_cmp f g) }

/-- **The syntactic category of the simply typed lambda calculus is cartesian closed.**  This is
the Lambek half of the Curry–Howard–Lambek correspondence: types are objects, terms modulo
βη-conversion are morphisms, the unit and product types give the finite products, and the function
type gives the exponential. -/
instance monoidalClosed : MonoidalClosed Ty where
  closed X := closed X

end Stlc
