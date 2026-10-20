/-
**A concrete class environment** — task `M25-TYPECLASS-DICT`.

The source calculus of `Start/TypeClassElab.lean` is instantiated with a small but genuine
environment, in the style of Haskell's prelude:

```haskell
class Eq a where eq :: a -> a -> a
class Eq a => Ord a where cmp :: a -> a -> a
instance Eq Base
instance Eq b => Eq (a -> b)       -- an instance with a context
instance Ord Base
```

* `TypeClass.exampleEnv` — the environment, with the dictionary of every instance;
* `TypeClass.exampleEnv_good` — **it is well formed**: every instance dictionary has the
  dictionary type of its head in the dictionary types of its instance context;
* `TypeClass.ent_eq_arrow` — the instance with a context at work: `Eq (Base → Base)` is
  entailed, by the arrow instance over `Eq Base`;
* `TypeClass.ent_eq_of_ord` — the superclass at work: `Ord Base` entails `Eq Base`;
* `TypeClass.example_elab` — a source program using a method elaborates to a strongly
  normalizing System F term of the translated type.
-/

import Start.TypeClassElab

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- The signature `a → a → a` of both example methods. -/
def binOp : Mty := Mty.arrow (Mty.var 0) (Mty.arrow (Mty.var 0) (Mty.var 0))

/-- `class Eq a where eq : a → a → a`. -/
def eqDecl : ClassDecl := ⟨none, [binOp]⟩

/-- `class Eq a => Ord a where cmp : a → a → a`. -/
def ordDecl : ClassDecl := ⟨some 0, [binOp]⟩

/-- The dictionary of `instance Eq Base`: the first projection. -/
def eqBaseDict : Lambda := recMk [Lambda.lam (Lambda.lam (Lambda.var 1))]

/-- The dictionary of `instance Eq b => Eq (a → b)`: `eq f g = λz. eq_b (f z) (g z)`. -/
def eqArrowDict : Lambda :=
  recMk [Lambda.lam (Lambda.lam (Lambda.lam
    (Lambda.app (Lambda.app (recProj 1 0 (Lambda.var 3)) (Lambda.app (Lambda.var 2) (Lambda.var 0)))
      (Lambda.app (Lambda.var 1) (Lambda.var 0)))))]

/-- The dictionary of `instance Ord Base`: the `Eq Base` dictionary and a method. -/
def ordBaseDict : Lambda := recMk [eqBaseDict, Lambda.lam (Lambda.lam (Lambda.var 1))]

/-- `instance Eq Base`. -/
def instEqBase : Inst := ⟨0, Mty.base, [], eqBaseDict⟩

/-- `instance Eq b => Eq (a → b)`. -/
def instEqArrow : Inst := ⟨0, Mty.arrow (Mty.var 0) (Mty.var 1), [⟨0, Mty.var 1⟩], eqArrowDict⟩

/-- `instance Ord Base`. -/
def instOrdBase : Inst := ⟨1, Mty.base, [], ordBaseDict⟩

/-- The example environment. -/
def exampleEnv : Env := ⟨[eqDecl, ordDecl], [instEqBase, instEqArrow, instOrdBase]⟩

theorem dictTy_eq_cls (τ : Mty) :
    dictTy exampleEnv 0 τ = recTy [mtyF (inst0 τ binOp)] := rfl

theorem dictTy_ord_cls (τ : Mty) :
    dictTy exampleEnv 1 τ = recTy [dictTy exampleEnv 0 τ, mtyF (inst0 τ binOp)] := rfl

theorem exampleEnv_ok : EnvOK exampleEnv where
  super_lt := by
    intro c D hc d hd
    match c with
    | 0 => simp [exampleEnv, eqDecl] at hc; subst hc; simp at hd
    | 1 => simp [exampleEnv, ordDecl] at hc; subst hc; simp at hd; omega
    | (n + 2) => simp [exampleEnv] at hc
  methods_mono := by
    intro c D hc m hm
    match c with
    | 0 =>
        simp [exampleEnv, eqDecl] at hc
        subst hc
        simp at hm
        subst hm
        exact ⟨rfl, rfl, rfl⟩
    | 1 =>
        simp [exampleEnv, ordDecl] at hc
        subst hc
        simp at hm
        subst hm
        exact ⟨rfl, rfl, rfl⟩
    | (n + 2) => simp [exampleEnv] at hc

/-- The constant-like method `λx y. x`. -/
theorem typing_fst (Γ : List FTy) (A : FTy) :
    Typing Γ (Lambda.lam (Lambda.lam (Lambda.var 1))) (FTy.arrow A (FTy.arrow A A)) :=
  Typing.lam (Typing.lam (Typing.var rfl))

theorem typing_eqBaseDict (Γ : List FTy) :
    Typing Γ eqBaseDict (dictTy exampleEnv 0 Mty.base) := by
  rw [dictTy_eq_cls]
  exact typing_recMk (List.Forall₂.cons (typing_fst Γ _) List.Forall₂.nil)

theorem typing_eqArrowDict :
    Typing ([⟨0, Mty.var 1⟩].map (dictTyC exampleEnv)) eqArrowDict
      (dictTy exampleEnv 0 (Mty.arrow (Mty.var 0) (Mty.var 1))) := by
  rw [dictTy_eq_cls]
  refine typing_recMk (List.Forall₂.cons ?_ List.Forall₂.nil)
  refine Typing.lam (Typing.lam (Typing.lam ?_))
  have hd : Typing [FTy.var 0, FTy.arrow (FTy.var 0) (FTy.var 1),
      FTy.arrow (FTy.var 0) (FTy.var 1), recTy [mtyF (inst0 (Mty.var 1) binOp)]]
      (Lambda.var 3) (recTy [mtyF (inst0 (Mty.var 1) binOp)]) := Typing.var rfl
  have hproj : Typing [FTy.var 0, FTy.arrow (FTy.var 0) (FTy.var 1),
      FTy.arrow (FTy.var 0) (FTy.var 1), recTy [mtyF (inst0 (Mty.var 1) binOp)]]
      (recProj 1 0 (Lambda.var 3))
      (FTy.arrow (FTy.var 1) (FTy.arrow (FTy.var 1) (FTy.var 1))) :=
    typing_recProj (As := [mtyF (inst0 (Mty.var 1) binOp)]) hd rfl
  exact Typing.app (Typing.app hproj (Typing.app (Typing.var rfl) (Typing.var rfl)))
    (Typing.app (Typing.var rfl) (Typing.var rfl))

theorem typing_ordBaseDict :
    Typing [] ordBaseDict (dictTy exampleEnv 1 Mty.base) := by
  rw [dictTy_ord_cls]
  exact typing_recMk (List.Forall₂.cons (typing_eqBaseDict [])
    (List.Forall₂.cons (typing_fst [] _) List.Forall₂.nil))

/-- **The example environment is well formed.** -/
theorem exampleEnv_good : EnvGood exampleEnv where
  toEnvOK := exampleEnv_ok
  insts_ok := by
    intro I hI
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl
    · exact typing_eqBaseDict _
    · exact typing_eqArrowDict
    · exact typing_ordBaseDict

/-! ### Entailment at work -/

/-- `Eq Base` holds, by the instance for the base type. -/
theorem ent_eq_base (P : List Cstr) : Ent exampleEnv P ⟨0, Mty.base⟩ := by
  have h := Ent.inst (E := exampleEnv) (P := P) (I := instEqBase) (s := fun _ => Mty.base)
    (by simp [exampleEnv]) (by simp [instEqBase])
  simpa [instEqBase, msubst] using h

/-- **The instance with a context at work**: `Eq (Base → Base)` holds. -/
theorem ent_eq_arrow (P : List Cstr) :
    Ent exampleEnv P ⟨0, Mty.arrow Mty.base Mty.base⟩ := by
  have h := Ent.inst (E := exampleEnv) (P := P) (I := instEqArrow) (s := fun _ => Mty.base)
    (by simp [exampleEnv]) (by
      intro C hC
      simp only [instEqArrow, List.mem_singleton] at hC
      subst hC
      simpa [Cstr.subst, msubst] using ent_eq_base P)
  simpa [instEqArrow, msubst] using h

/-- **The superclass at work**: a dictionary for `Ord Base` yields one for `Eq Base`. -/
theorem ent_eq_of_ord (P : List Cstr) (h : Ent exampleEnv P ⟨1, Mty.base⟩) :
    Ent exampleEnv P ⟨0, Mty.base⟩ :=
  Ent.sup (D := ordDecl) rfl rfl h

/-! ### A program -/

/-- `λx. eq x x`, at the type `(Base → Base) → (Base → Base)`. -/
def exampleProg : Sexp :=
  Sexp.lam (Sexp.app (Sexp.app (Sexp.method 0 0) (Sexp.var 0)) (Sexp.var 0))

theorem exampleProg_typing :
    STyping exampleEnv [] [] exampleProg
      (Mty.arrow (Mty.arrow Mty.base Mty.base) (Mty.arrow Mty.base Mty.base)) := by
  refine STyping.lam (STyping.app (STyping.app ?_ (STyping.var rfl)) (STyping.var rfl))
  have h : STyping exampleEnv [] [Mty.arrow Mty.base Mty.base] (Sexp.method 0 0)
      (inst0 (Mty.arrow Mty.base Mty.base) binOp) :=
    STyping.method (D := eqDecl) rfl rfl (ent_eq_arrow [])
  simpa [inst0, msubst, binOp] using h

/-- **The example program elaborates to a strongly normalizing System F term** of the translated
type. -/
theorem example_elab :
    ∃ t, Typing (tctx exampleEnv [] [])
        t (mtyF (Mty.arrow (Mty.arrow Mty.base Mty.base) (Mty.arrow Mty.base Mty.base))) ∧
      Lambda.SN t :=
  elab_sn exampleEnv_good exampleProg_typing

end TypeClass
