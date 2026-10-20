/-
**Type classes by dictionary passing** — task `M25-TYPECLASS-DICT` (part 1: records and
dictionary types).

The source calculus of single-parameter type classes (Wadler–Blott; Hall–Hammond–Peyton
Jones–Wadler) is elaborated into the Curry-style System F of `Start/SystemF.lean`.  A dictionary
is a record: the superclass dictionary, if the class has a superclass, followed by the methods.
Records are Church-encoded products.

* `TypeClass.recTy As` — the type `∀β. (A₁ → ⋯ → Aₙ → β) → β` of a record with fields `As`;
  `TypeClass.recMk`, `TypeClass.recProj` — its constructor and its projections, with their
  typing rules `typing_recMk` and `typing_recProj`;
* `TypeClass.Mty`, `TypeClass.Cstr` — source monotypes (a base type, type variables, arrows) and
  class constraints `C τ`; `TypeClass.mtyF` — their translation to System F types;
* `TypeClass.ClassDecl`, `TypeClass.Inst`, `TypeClass.Env` — class declarations (at most one
  superclass, a list of method signatures in the class variable) and instance declarations (a
  head, an instance context, and the dictionary the instance elaborates to);
* `TypeClass.dictTy E c τ` — **the dictionary type of the class `c` at the type `τ`**, and
  `TypeClass.dictTy_msubst` — it commutes with type substitution.
-/

import Start.SystemFSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-! ### Records in System F -/

/-- The type of a record with fields `As`: `∀β. (A₁ → ⋯ → Aₙ → β) → β`. -/
def recTy (As : List FTy) : FTy :=
  FTy.all (FTy.arrow (As.foldr (fun A B => FTy.arrow (tyShift A) B) (FTy.var 0)) (FTy.var 0))

/-- Iterated application. -/
def appsL : Lambda → List Lambda → Lambda
  | t, [] => t
  | t, u :: us => appsL (Lambda.app t u) us

/-- The record with fields `ts`: `λk. k t₁ ⋯ tₙ`. -/
def recMk (ts : List Lambda) : Lambda :=
  Lambda.lam (appsL (Lambda.var 0) (ts.map (Lambda.lift 1 0)))

/-- `lams n t` is `λ ⋯ λ t` with `n` abstractions. -/
def lams : ℕ → Lambda → Lambda
  | 0, t => t
  | n + 1, t => Lambda.lam (lams n t)

/-- The selector of the `j`-th field out of `n`: `λx₁ ⋯ xₙ. xⱼ`. -/
def sel (n j : ℕ) : Lambda := lams n (Lambda.var (n - 1 - j))

/-- The `j`-th projection of a record of `n` fields. -/
def recProj (n j : ℕ) (d : Lambda) : Lambda := Lambda.app d (sel n j)

theorem typing_appsL {Γ : List FTy} {h : Lambda} {ts : List Lambda} {As : List FTy} {R : FTy}
    (hts : List.Forall₂ (fun t A => Typing Γ t A) ts As)
    (hh : Typing Γ h (As.foldr FTy.arrow R)) : Typing Γ (appsL h ts) R := by
  induction hts generalizing h with
  | nil => exact hh
  | cons ht _ ih => exact ih (Typing.app hh ht)

theorem foldr_tyShift (As : List FTy) :
    As.foldr (fun A B => FTy.arrow (tyShift A) B) (FTy.var 0) =
      (As.map tyShift).foldr FTy.arrow (FTy.var 0) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [List.foldr, ih]

theorem forall₂_shiftTy {Γ : List FTy} {ts : List Lambda} {As : List FTy}
    (h : List.Forall₂ (fun t A => Typing Γ t A) ts As) :
    List.Forall₂ (fun t A => Typing (Γ.map tyShift) t A) ts (As.map tyShift) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons ht _ ih => exact List.Forall₂.cons (Typing.shiftTy ht) ih

theorem forall₂_lift_one {Δ : List FTy} (B : FTy) {ts : List Lambda} {As : List FTy}
    (h : List.Forall₂ (fun t A => Typing Δ t A) ts As) :
    List.Forall₂ (fun t A => Typing (B :: Δ) t A) (ts.map (Lambda.lift 1 0)) As := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons ht _ ih => exact List.Forall₂.cons (ht.lift_one _) ih

/-- **The typing rule of the record constructor.** -/
theorem typing_recMk {Γ : List FTy} {ts : List Lambda} {As : List FTy}
    (h : List.Forall₂ (fun t A => Typing Γ t A) ts As) : Typing Γ (recMk ts) (recTy As) := by
  refine Typing.tlam (Typing.lam ?_)
  rw [foldr_tyShift]
  exact typing_appsL (forall₂_lift_one _ (forall₂_shiftTy h)) (Typing.var rfl)

theorem tyInst_fold (A : FTy) (As : List FTy) :
    tyInst A (As.foldr (fun X B => FTy.arrow (tyShift X) B) (FTy.var 0)) =
      As.foldr FTy.arrow A := by
  induction As with
  | nil => rfl
  | cons X As ih =>
      show tySubst (tyScons A) (FTy.arrow (tyShift X) _) = _
      simp only [tySubst, List.foldr]
      rw [show tySubst (tyScons A) (tyShift X) = X from tyInst_tyShift A X]
      rw [show tySubst (tyScons A)
          (As.foldr (fun X B => FTy.arrow (tyShift X) B) (FTy.var 0)) = As.foldr FTy.arrow A
        from ih]

theorem typing_lams_var (Bs : List FTy) : ∀ (Γ Δ : List FTy) (A : FTy),
    Typing (Δ ++ A :: Γ) (lams Bs.length (Lambda.var (Bs.length + Δ.length)))
      (Bs.foldr FTy.arrow A) := by
  induction Bs with
  | nil =>
      intro Γ Δ A
      refine Typing.var ?_
      simp
  | cons Y Bs ih =>
      intro Γ Δ A
      refine Typing.lam ?_
      have := ih Γ (Y :: Δ) A
      simpa [lams, List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

theorem typing_sel_split : ∀ (As₁ : List FTy) (A : FTy) (As₂ : List FTy) (Γ : List FTy),
    Typing Γ (lams (As₁.length + 1 + As₂.length) (Lambda.var As₂.length))
      ((As₁ ++ A :: As₂).foldr FTy.arrow A) := by
  intro As₁
  induction As₁ with
  | nil =>
      intro A As₂ Γ
      simp only [List.length_nil, Nat.zero_add, List.nil_append, List.foldr]
      have h : 1 + As₂.length = As₂.length + 1 := by omega
      rw [h, lams]
      exact Typing.lam (by simpa using typing_lams_var As₂ Γ [] A)
  | cons X As₁ ih =>
      intro A As₂ Γ
      have h : As₁.length + 1 + 1 + As₂.length = (As₁.length + 1 + As₂.length) + 1 := by omega
      simp only [List.length_cons, h, lams, List.cons_append, List.foldr]
      exact Typing.lam (ih A As₂ (X :: Γ))

/-- The selector is typable. -/
theorem typing_sel {Γ : List FTy} {As : List FTy} {A : FTy} {j : ℕ} (hj : As[j]? = some A) :
    Typing Γ (sel As.length j) (As.foldr FTy.arrow A) := by
  obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hj
  have hsplit : As = As.take j ++ A :: As.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j As]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, hval]
  have hlen1 : (As.take j).length = j := by rw [List.length_take]; omega
  have hlen2 : (As.drop (j + 1)).length = As.length - 1 - j := by rw [List.length_drop]; omega
  have hkey := typing_sel_split (As.take j) A (As.drop (j + 1)) Γ
  rw [hlen1, hlen2, ← hsplit] at hkey
  have hl : j + 1 + (As.length - 1 - j) = As.length := by omega
  rw [hl] at hkey
  exact hkey

/-- **The typing rule of the record projections.** -/
theorem typing_recProj {Γ : List FTy} {d : Lambda} {As : List FTy} {A : FTy} {j : ℕ}
    (hd : Typing Γ d (recTy As)) (hj : As[j]? = some A) :
    Typing Γ (recProj As.length j d) A := by
  have h1 := Typing.tapp A hd
  have h2 : tyInst A (FTy.arrow (As.foldr (fun X B => FTy.arrow (tyShift X) B) (FTy.var 0))
        (FTy.var 0)) = FTy.arrow (As.foldr FTy.arrow A) A := by
    show tySubst (tyScons A) (FTy.arrow _ (FTy.var 0)) = _
    simp only [tySubst]
    rw [show tySubst (tyScons A)
        (As.foldr (fun X B => FTy.arrow (tyShift X) B) (FTy.var 0)) = As.foldr FTy.arrow A
      from tyInst_fold A As]
    rfl
  rw [h2] at h1
  exact Typing.app h1 (typing_sel hj)

/-! ### The source language of classes -/

/-- Source monotypes: a base type, type variables and arrows. -/
inductive Mty where
  /-- The base type. -/
  | base : Mty
  /-- A type variable. -/
  | var : ℕ → Mty
  /-- A function type. -/
  | arrow : Mty → Mty → Mty
  deriving DecidableEq

/-- Substitution of source type variables. -/
def msubst (s : ℕ → Mty) : Mty → Mty
  | Mty.base => Mty.base
  | Mty.var i => s i
  | Mty.arrow a b => Mty.arrow (msubst s a) (msubst s b)

/-- Monotypes use only the class variable `var 0`. -/
def Mono0 : Mty → Prop
  | Mty.base => True
  | Mty.var i => i = 0
  | Mty.arrow a b => Mono0 a ∧ Mono0 b

/-- Substituting the class variable by `τ`. -/
def inst0 (τ : Mty) : Mty → Mty := msubst (fun _ => τ)

theorem msubst_inst0 {m : Mty} (hm : Mono0 m) (s : ℕ → Mty) (τ : Mty) :
    msubst s (inst0 τ m) = inst0 (msubst s τ) m := by
  induction m with
  | base => rfl
  | var i => rfl
  | arrow a b iha ihb =>
      obtain ⟨ha, hb⟩ := hm
      have h1 := iha ha
      have h2 := ihb hb
      simp only [inst0, msubst] at h1 h2 ⊢
      rw [h1, h2]

/-- A class constraint `C τ`. -/
structure Cstr where
  /-- The class. -/
  cls : ℕ
  /-- The type it constrains. -/
  ty : Mty
  deriving DecidableEq

/-- Substitution in a constraint. -/
def Cstr.subst (s : ℕ → Mty) (C : Cstr) : Cstr := ⟨C.cls, msubst s C.ty⟩

/-- Source monotypes as System F types; the base type is the closed type `∀α. α`. -/
def mtyF : Mty → FTy
  | Mty.base => FTy.all (FTy.var 0)
  | Mty.var i => FTy.var i
  | Mty.arrow a b => FTy.arrow (mtyF a) (mtyF b)

/-- A source substitution as a System F type substitution. -/
def mtyS (s : ℕ → Mty) : ℕ → FTy := fun i => mtyF (s i)

theorem mtyF_msubst (s : ℕ → Mty) (τ : Mty) : mtyF (msubst s τ) = tySubst (mtyS s) (mtyF τ) := by
  induction τ with
  | base => rfl
  | var i => rfl
  | arrow a b iha ihb => simp [msubst, mtyF, tySubst, iha, ihb]

/-- A class declaration: at most one superclass and the method signatures, written in the class
variable `Mty.var 0`. -/
structure ClassDecl where
  /-- The superclass, if any. -/
  super : Option ℕ
  /-- The method signatures. -/
  methods : List Mty

/-- An instance declaration: the class, the head type, the instance context, and the System F
dictionary the instance elaborates to (its free variables are the context dictionaries). -/
structure Inst where
  /-- The class. -/
  cls : ℕ
  /-- The head type. -/
  head : Mty
  /-- The instance context. -/
  ctxt : List Cstr
  /-- The dictionary of the instance. -/
  dict : Lambda

/-- A class and instance environment. -/
structure Env where
  /-- The class declarations, indexed by class number. -/
  classes : List ClassDecl
  /-- The instance declarations. -/
  insts : List Inst

/-! ### Dictionary types -/

/-- The fields of the dictionary of a class: the superclass dictionary, then the methods. -/
def dictFields (rec : ℕ → Mty → FTy) (D : ClassDecl) (τ : Mty) : List FTy :=
  (match D.super with | none => [] | some d => [rec d τ]) ++
    D.methods.map (fun m => mtyF (inst0 τ m))

/-- The dictionary type, with fuel for the superclass chain. -/
def dictTyF (E : Env) : ℕ → ℕ → Mty → FTy
  | 0, _, _ => FTy.all (FTy.var 0)
  | n + 1, c, τ =>
      match E.classes[c]? with
      | none => FTy.all (FTy.var 0)
      | some D => recTy (dictFields (dictTyF E n) D τ)

/-- **The dictionary type of the class `c` at the type `τ`.** -/
def dictTy (E : Env) (c : ℕ) (τ : Mty) : FTy := dictTyF E (c + 1) c τ

/-- The dictionary type of a constraint. -/
def dictTyC (E : Env) (C : Cstr) : FTy := dictTy E C.cls C.ty

/-- Superclasses have smaller class numbers, and method signatures use only the class
variable. -/
structure EnvOK (E : Env) : Prop where
  /-- A superclass comes earlier. -/
  super_lt : ∀ {c : ℕ} {D : ClassDecl}, E.classes[c]? = some D → ∀ {d : ℕ}, D.super = some d →
    d < c
  /-- Method signatures mention only the class variable. -/
  methods_mono : ∀ {c : ℕ} {D : ClassDecl}, E.classes[c]? = some D → ∀ m ∈ D.methods, Mono0 m

theorem dictTyF_fuel {E : Env} (h : EnvOK E) :
    ∀ (n c : ℕ) (τ : Mty), c < n → dictTyF E n c τ = dictTy E c τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro c τ hc
      cases n with
      | zero => omega
      | succ n' =>
          cases hc' : E.classes[c]? with
          | none => simp [dictTy, dictTyF, hc']
          | some D =>
              simp only [dictTy, dictTyF, hc']
              cases hs : D.super with
              | none => simp [dictFields, hs]
              | some d =>
                  have hd : d < c := h.super_lt hc' hs
                  have h1 : dictTyF E n' d τ = dictTy E d τ := ih n' (by omega) d τ (by omega)
                  have h2 : dictTyF E c d τ = dictTy E d τ := ih c (by omega) d τ hd
                  simp [dictFields, hs, h1, h2]

/-- **The dictionary of a class is the record of its superclass dictionary and its methods.** -/
theorem dictTy_eq {E : Env} (h : EnvOK E) {c : ℕ} {D : ClassDecl} (hc : E.classes[c]? = some D)
    (τ : Mty) : dictTy E c τ = recTy (dictFields (dictTy E) D τ) := by
  simp only [dictTy, dictTyF, hc]
  cases hs : D.super with
  | none => simp [dictFields, hs]
  | some d =>
      have hd : d < c := h.super_lt hc hs
      simp [dictFields, hs, dictTyF_fuel h c d τ hd]

theorem dictTy_none {E : Env} {c : ℕ} (hc : E.classes[c]? = none) (τ : Mty) :
    dictTy E c τ = FTy.all (FTy.var 0) := by
  simp [dictTy, dictTyF, hc]

theorem tySubst_recTy (s : ℕ → FTy) (As : List FTy) :
    tySubst s (recTy As) = recTy (As.map (tySubst s)) := by
  simp only [recTy, tySubst, FTy.all.injEq, FTy.arrow.injEq]
  refine ⟨?_, rfl⟩
  induction As with
  | nil => rfl
  | cons A As ih =>
      simp only [List.foldr, List.map_cons, tySubst, ih, FTy.arrow.injEq, and_true]
      exact tySubst_tyShift s A

/-- **Dictionary types commute with type substitution.** -/
theorem dictTy_msubst {E : Env} (h : EnvOK E) (c : ℕ) (s : ℕ → Mty) (τ : Mty) :
    dictTy E c (msubst s τ) = tySubst (mtyS s) (dictTy E c τ) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      cases hc : E.classes[c]? with
      | none => simp [dictTy_none hc, tySubst, ups]
      | some D =>
          rw [dictTy_eq h hc, dictTy_eq h hc, tySubst_recTy]
          congr 1
          simp only [dictFields, List.map_append, List.map_map, Function.comp_def]
          refine congrArg₂ (· ++ ·) ?_ ?_
          · cases hs : D.super with
            | none => rfl
            | some d =>
                have hd : d < c := h.super_lt hc hs
                simp [ih d hd]
          · refine List.map_congr_left fun m hm => ?_
            rw [← msubst_inst0 (h.methods_mono hc m hm), mtyF_msubst]

theorem dictTyC_subst {E : Env} (h : EnvOK E) (s : ℕ → Mty) (C : Cstr) :
    dictTyC E (C.subst s) = tySubst (mtyS s) (dictTyC E C) :=
  dictTy_msubst h C.cls s C.ty

end TypeClass
