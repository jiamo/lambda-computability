import Start.PTSCube
import Start.SystemF

/-!
# Elaborating Curry-style System F into the System F corner of the cube

This module is this library's own (task `M23-PTS`).  `Start/SystemF.lean` presents System F in
Curry style: terms are untyped `Lambda` terms, type abstraction and type application leave no
trace in the term.  The `systemF` corner of `Start/PTSCube.lean` is Church style: type
abstractions `λX:∗. M` and type applications `M T` are explicit and term abstractions carry
their domain.  This module gives a **derivation-directed elaboration** from the former into the
latter, together with an **erasure theorem**.

* `PureTypeSystem.FElab.trTy` — System F types as cube types (`A → B` is the non-dependent
  product `Π_:A. B`, `∀X. A` is `ΠX:∗. A`), commuting with renaming and substitution;
* `PureTypeSystem.FElab.trTy_typed` — every translated type has sort `∗` in the `systemF` corner;
* `PureTypeSystem.FElab.erase` — erasure of annotated terms to untyped `Lambda` terms, driven by
  a map telling which variables are term variables (type abstractions, type applications and
  type annotations are deleted, variable indices are renumbered);
* `PureTypeSystem.FElab.elaborate` — the main lemma: by induction on a Curry derivation
  `SystemF.Typing Γ t A`, construct an annotated term `M` with a `systemF`-corner derivation of
  type `A` (under a typed interpretation of the type variables) and with `erase M = t`;
* `PureTypeSystem.FElab.elaborate_ctx` — the corollary for an arbitrary Curry context, free type
  variables being interpreted by the empty type `ΠX:∗. X`.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace FElab

open LambdaPi (Srt)
open SystemF (FTy Typing)

/-- The `systemF` corner of the cube. -/
abbrev F : Specification Srt := cubeSpec systemF

/-- System F types as types of the cube. -/
def trTy : FTy → Expr Srt
  | .var i => .var i
  | .arrow A B => .pi (trTy A) ((trTy B).rename Nat.succ)
  | .all A => .pi (.sort .star) (trTy A)

theorem liftRen_eq_upr (r : ℕ → ℕ) : Expr.liftRen r = SystemF.upr r := by
  funext n; cases n <;> rfl

theorem trTy_rename (A : FTy) (r : ℕ → ℕ) :
    trTy (SystemF.tyRename r A) = (trTy A).rename r := by
  induction A generalizing r with
  | var i => rfl
  | arrow A B ihA ihB =>
      simp only [SystemF.tyRename, trTy, Expr.rename, ihA, ihB, Expr.rename_comp]
      congr 2
  | all A ih =>
      simp only [SystemF.tyRename, trTy, Expr.rename, ih, liftRen_eq_upr]

theorem trTy_subst (A : FTy) (s : ℕ → FTy) :
    trTy (SystemF.tySubst s A) = (trTy A).subst (trTy ∘ s) := by
  induction A generalizing s with
  | var i => rfl
  | arrow A B ihA ihB =>
      simp only [SystemF.tySubst, trTy, Expr.subst, ihA, ihB, Expr.subst_rename,
        Expr.rename_subst]
      rfl
  | all A ih =>
      simp only [SystemF.tySubst, trTy, Expr.subst, ih]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          simp only [Function.comp_apply, SystemF.ups, SystemF.tyShift, trTy_rename,
            Expr.liftSub_succ]

theorem trTy_inst (B A : FTy) :
    trTy (SystemF.tyInst B A) = (trTy A).instantiate (trTy B) := by
  rw [SystemF.tyInst, trTy_subst, Expr.instantiate]
  congr 1
  funext n
  cases n <;> rfl

/-- The interpretation of a type under a valuation `θ` of its type variables. -/
def tr (θ : ℕ → Expr Srt) (A : FTy) : Expr Srt := (trTy A).subst θ

theorem tr_arrow (θ : ℕ → Expr Srt) (A B : FTy) :
    tr θ (.arrow A B) = .pi (tr θ A) ((tr θ B).rename Nat.succ) := by
  simp only [tr, trTy, Expr.subst, Expr.subst_rename, Expr.rename_subst]
  rfl

theorem tr_all (θ : ℕ → Expr Srt) (A : FTy) :
    tr θ (.all A) = .pi (.sort .star) (tr (Expr.liftSub θ) A) := rfl

theorem tr_inst (θ : ℕ → Expr Srt) (B A : FTy) :
    tr θ (SystemF.tyInst B A) = (tr (Expr.liftSub θ) A).instantiate (tr θ B) := by
  simp only [tr, trTy_inst, Expr.instantiate_subst]

theorem tr_shift (θ : ℕ → Expr Srt) (A : FTy) :
    tr (Expr.liftSub θ) (SystemF.tyShift A) = (tr θ A).rename Nat.succ := by
  simp only [tr, SystemF.tyShift, trTy_rename, Expr.subst_rename, Expr.rename_subst]
  rfl

theorem tr_rename (θ : ℕ → Expr Srt) (A : FTy) :
    tr (fun n => (θ n).rename Nat.succ) A = (tr θ A).rename Nat.succ := by
  simp only [tr, Expr.rename_subst]

/-- A valuation of the type variables by types of sort `∗`. -/
def TypedVal (Δ : List (Expr Srt)) (θ : ℕ → Expr Srt) : Prop :=
  ∀ i, HasType F Δ (θ i) (.sort .star)

theorem TypedVal.weaken {Δ : List (Expr Srt)} {θ : ℕ → Expr Srt} (hθ : TypedVal Δ θ)
    {D : Expr Srt} {s : Srt} (hD : HasType F Δ D (.sort s)) :
    TypedVal (D :: Δ) (fun n => (θ n).rename Nat.succ) :=
  fun i => by simpa only [Expr.rename] using HasType.weaken (hθ i) hD

theorem TypedVal.lift {Δ : List (Expr Srt)} {θ : ℕ → Expr Srt} (hθ : TypedVal Δ θ)
    (hΔ : ValidContext F Δ) : TypedVal (.sort .star :: Δ) (Expr.liftSub θ) := by
  have hs : HasType F Δ (.sort .star) (.sort .box) := cube_star_box _ hΔ
  intro i
  cases i with
  | zero => simpa only [Expr.liftSub_zero, Expr.rename] using HasType.var hs
  | succ i => simpa only [Expr.liftSub_succ, Expr.rename] using HasType.weaken (hθ i) hs

/-- **Translated types are well sorted**: under a typed valuation, `tr θ A : ∗`. -/
theorem trTy_typed (A : FTy) :
    ∀ {Δ : List (Expr Srt)} {θ : ℕ → Expr Srt}, ValidContext F Δ → TypedVal Δ θ →
      HasType F Δ (tr θ A) (.sort .star) := by
  induction A with
  | var i => intro Δ θ _ hθ; exact hθ i
  | arrow A B ihA ihB =>
      intro Δ θ hΔ hθ
      rw [tr_arrow]
      have hA := ihA hΔ hθ
      have hB := ihB (.cons hΔ hA) (hθ.weaken hA)
      rw [tr_rename] at hB
      exact .product hA hB ⟨rfl, trivial⟩
  | all A ih =>
      intro Δ θ hΔ hθ
      rw [tr_all]
      have hs : HasType F Δ (.sort .star) (.sort .box) := cube_star_box _ hΔ
      exact .product hs (ih (.cons hΔ hs) (hθ.lift hΔ)) ⟨rfl, rfl⟩

/-! ### Erasure -/

/-- Whether an annotated term is a type argument, given which variables are term variables
(`m n = some j`: PTS variable `n` is the term variable `j`; `none`: a type variable). -/
def isTy (m : ℕ → Option ℕ) : Expr Srt → Bool
  | .var n => (m n).isNone
  | .sort _ => true
  | .pi _ _ => true
  | .app _ _ => false
  | .lam _ _ => false

/-- Entering a term binder. -/
def mSome (m : ℕ → Option ℕ) : ℕ → Option ℕ
  | 0 => some 0
  | n + 1 => (m n).map Nat.succ

/-- Entering a type binder. -/
def mNone (m : ℕ → Option ℕ) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => m n

/-- **Erasure** of an annotated term: type abstractions (`λX:∗. b`), type applications and type
annotations are deleted, and variables are renumbered to count term variables only. -/
def erase : (ℕ → Option ℕ) → Expr Srt → Lambda
  | m, .var n => .var ((m n).getD 0)
  | _, .sort _ => .var 0
  | _, .pi _ _ => .var 0
  | m, .lam A b => if A = .sort .star then erase (mNone m) b else .lam (erase (mSome m) b)
  | m, .app f a => if isTy m a then erase m f else .app (erase m f) (erase m a)

theorem isTy_rename_some {m : ℕ → Option ℕ} {X : Expr Srt} (h : isTy m X = true) :
    isTy (mSome m) (X.rename Nat.succ) = true := by
  cases X with
  | var n => simpa [isTy, Expr.rename, mSome] using h
  | sort _ => rfl
  | pi _ _ => rfl
  | app _ _ => simp [isTy] at h
  | lam _ _ => simp [isTy] at h

theorem isTy_rename_none {m : ℕ → Option ℕ} {X : Expr Srt} (h : isTy m X = true) :
    isTy (mNone m) (X.rename Nat.succ) = true := by
  cases X with
  | var n => simpa [isTy, Expr.rename, mNone] using h
  | sort _ => rfl
  | pi _ _ => rfl
  | app _ _ => simp [isTy] at h
  | lam _ _ => simp [isTy] at h

theorem isTy_tr {m : ℕ → Option ℕ} {θ : ℕ → Expr Srt} (hθ : ∀ i, isTy m (θ i) = true)
    (B : FTy) : isTy m (tr θ B) = true := by
  cases B with
  | var i => exact hθ i
  | arrow _ _ => rfl
  | all _ => rfl

theorem app_type_eq (X a : Expr Srt) (θ : ℕ → Expr Srt) :
    ((X.rename Nat.succ).subst (Expr.liftSub θ)).instantiate a = X.subst θ := by
  simp only [Expr.instantiate, Expr.subst_rename, Expr.subst_subst]
  congr 1
  funext n
  simp only [Function.comp_apply, Expr.liftSub_succ, Expr.subst_lift_single]

/-! ### The elaboration -/

/-- **Derivation-directed elaboration of Curry-style System F.**  Given a Curry derivation
`Typing Γ t A`, a valid `systemF`-corner context `Δ`, a typed valuation `θ` of the type
variables (each `θ i` a type argument for the variable map `m`), and an assignment `ν` of the
term variables of `Γ` to variables of `Δ` of the translated types, there is an annotated term
`M` with `Δ ⊢ M : tr θ A` in the `systemF` corner whose erasure is `t` (and which is not itself
a type argument). -/
theorem elaborate {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ {Δ : List (Expr Srt)} {θ : ℕ → Expr Srt} {ν : ℕ → ℕ} {m : ℕ → Option ℕ},
      ValidContext F Δ → TypedVal Δ θ → (∀ i, isTy m (θ i) = true) →
      (∀ j B, Γ[j]? = some B → HasType F Δ (.var (ν j)) (tr θ B) ∧ m (ν j) = some j) →
      ∃ M, HasType F Δ M (tr θ A) ∧ erase m M = t ∧ isTy m M = false := by
  induction h with
  | @var Γ i B hi =>
      intro Δ θ ν m _ _ _ hν
      obtain ⟨hty, hm⟩ := hν i B hi
      exact ⟨.var (ν i), hty, by simp [erase, hm], by simp [isTy, hm]⟩
  | @app Γ a b A B _ _ iha ihb =>
      intro Δ θ ν m hΔ hθ hθm hν
      obtain ⟨M₁, h₁, e₁, -⟩ := iha hΔ hθ hθm hν
      obtain ⟨M₂, h₂, e₂, t₂⟩ := ihb hΔ hθ hθm hν
      refine ⟨.app M₁ M₂, ?_, by simp [erase, t₂, e₁, e₂], rfl⟩
      have := HasType.application (by simpa only [tr, trTy, Expr.subst] using h₁) h₂
      rwa [app_type_eq] at this
  | @lam Γ t A B _ ih =>
      intro Δ θ ν m hΔ hθ hθm hν
      have hA := trTy_typed A hΔ hθ
      have hΔ' : ValidContext F (tr θ A :: Δ) := .cons hΔ hA
      obtain ⟨M, hM, eM, -⟩ := ih (Δ := tr θ A :: Δ) (θ := fun n => (θ n).rename Nat.succ)
        (ν := Expr.liftRen ν) (m := mSome m) hΔ' (hθ.weaken hA)
        (fun i => isTy_rename_some (hθm i)) (by
          intro j C hj
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
              subst hj
              refine ⟨?_, rfl⟩
              rw [tr_rename]
              exact HasType.var hA
          | succ j =>
              simp only [List.getElem?_cons_succ] at hj
              obtain ⟨hty, hm⟩ := hν j C hj
              refine ⟨?_, by simp [mSome, Expr.liftRen, hm]⟩
              rw [tr_rename]
              exact HasType.weaken hty hA)
      rw [tr_rename] at hM
      have hpi := trTy_typed (.arrow A B) hΔ hθ
      rw [tr_arrow] at hpi
      have hne : tr θ A ≠ .sort .star := by
        intro he
        rw [he] at hA
        exact not_hasType_star_star _ hA
      refine ⟨.lam (tr θ A) M, ?_, by simp [erase, hne, eM], rfl⟩
      rw [tr_arrow]
      exact .abstraction hM hpi
  | @tlam Γ t A _ ih =>
      intro Δ θ ν m hΔ hθ hθm hν
      have hs : HasType F Δ (.sort .star) (.sort .box) := cube_star_box _ hΔ
      have hΔ' : ValidContext F (.sort .star :: Δ) := .cons hΔ hs
      obtain ⟨M, hM, eM, -⟩ := ih (Δ := .sort .star :: Δ) (θ := Expr.liftSub θ)
        (ν := fun j => ν j + 1) (m := mNone m) hΔ' (hθ.lift hΔ)
        (fun i => by
          cases i with
          | zero => rfl
          | succ i => exact isTy_rename_none (hθm i)) (by
          intro j C hj
          rw [List.getElem?_map] at hj
          obtain ⟨C₀, hC₀, rfl⟩ := Option.map_eq_some_iff.mp hj
          obtain ⟨hty, hm⟩ := hν j C₀ hC₀
          refine ⟨?_, by simp [mNone, hm]⟩
          rw [tr_shift]
          exact HasType.weaken hty hs)
      have hpi := trTy_typed (.all A) hΔ hθ
      refine ⟨.lam (.sort .star) M, ?_, by simp [erase, eM], rfl⟩
      rw [tr_all] at hpi ⊢
      exact .abstraction hM hpi
  | @tapp Γ t A B _ ih =>
      intro Δ θ ν m hΔ hθ hθm hν
      obtain ⟨M, hM, eM, -⟩ := ih hΔ hθ hθm hν
      have hB := trTy_typed B hΔ hθ
      refine ⟨.app M (tr θ B), ?_, by simp [erase, isTy_tr hθm B, eM], rfl⟩
      rw [tr_inst]
      rw [tr_all] at hM
      exact HasType.application hM hB

/-! ### Arbitrary Curry contexts -/

/-- The empty type `ΠX:∗. X`, interpreting free type variables. -/
def emptyTy : Expr Srt := .pi (.sort .star) (.var 0)

/-- The valuation sending every type variable to the empty type. -/
def θ₀ : ℕ → Expr Srt := fun _ => emptyTy

theorem emptyTy_typed {Δ : List (Expr Srt)} (hΔ : ValidContext F Δ) :
    HasType F Δ emptyTy (.sort .star) := by
  have hs := cube_star_box systemF hΔ
  exact .product hs (by simpa only [Expr.rename] using HasType.var hs) ⟨rfl, rfl⟩

theorem tr_θ₀_rename (A : FTy) (ρ : ℕ → ℕ) : (tr θ₀ A).rename ρ = tr θ₀ A := by
  simp only [tr, Expr.rename_subst]
  rfl

/-- The `systemF`-corner context interpreting a Curry context. -/
def ctx (Γ : List FTy) : List (Expr Srt) := Γ.map (tr θ₀)

theorem ctx_valid : ∀ Γ : List FTy, ValidContext F (ctx Γ)
  | [] => .nil
  | A :: Γ => .cons (ctx_valid Γ) (trTy_typed A (ctx_valid Γ) fun _ => emptyTy_typed (ctx_valid Γ))

theorem ctx_lookup : ∀ (Γ : List FTy) (j : ℕ) (B : FTy), Γ[j]? = some B →
    Lookup (ctx Γ) j (tr θ₀ B)
  | [], _, _, h => by simp at h
  | A :: Γ, 0, B, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have := Lookup.zero (tr θ₀ A) (ctx Γ)
      rwa [tr_θ₀_rename] at this
  | A :: Γ, j + 1, B, h => by
      simp only [List.getElem?_cons_succ] at h
      have := Lookup.succ (tr θ₀ A) (ctx_lookup Γ j B h)
      rwa [tr_θ₀_rename] at this

/-- **Elaboration of System F into the `systemF` corner, with erasure.**  Every Curry-style
System F derivation `Γ ⊢ t : A` yields an annotated term `M` with a `systemF`-corner derivation
`ctx Γ ⊢ M : tr θ₀ A` (free type variables read as the empty type) whose erasure is exactly `t`;
all variables of `ctx Γ` are term variables. -/
theorem elaborate_ctx {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∃ M, HasType F (ctx Γ) M (tr θ₀ A) ∧ erase some M = t := by
  obtain ⟨M, hM, eM, -⟩ := elaborate (ν := id) (m := some) h (ctx_valid Γ)
    (fun _ => emptyTy_typed (ctx_valid Γ)) (fun _ => rfl)
    (fun j B hj => ⟨HasType.lookup (ctx_valid Γ) (ctx_lookup Γ j B hj), rfl⟩)
  exact ⟨M, hM, eM⟩

/-- The elaboration lands in every corner with polymorphism (by the cube inclusions). -/
theorem elaborate_corner {f : CubeFeatures} (hf : systemF ≤ f) {Γ : List FTy} {t : Lambda}
    {A : FTy} (h : Typing Γ t A) :
    ∃ M, HasType (cubeSpec f) (ctx Γ) M (tr θ₀ A) ∧ erase some M = t := by
  obtain ⟨M, hM, eM⟩ := elaborate_ctx h
  exact ⟨M, cube_inclusion hf hM, eM⟩

/-- Example: the polymorphic self-application `λx. x x : (∀X. X → X) → (∀X. X → X)` of
`Start/SystemF.lean` has an annotated `systemF` elaboration. -/
example : ∃ M, HasType F ([]) M (tr θ₀ (.arrow SystemF.idTy SystemF.idTy)) ∧
    erase some M = SystemF.selfApp :=
  elaborate_ctx (SystemF.typing_selfApp [])

end FElab

end PureTypeSystem
