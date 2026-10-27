/-
**Martin-Löf type theory: type reduction and generic equality** — milestone M30
(`M30-MLTT-LR`).

* `MLTT.TyReds`, `MLTT.TyRedsT` — weak head reduction of types (`Γ ⊢ A ⇒* B`, a reduction in
  some universe at each step), with `TyReds.tyEq`, `TyReds.rename`, `TyReds.whnf_unique`;
* `MLTT.GenEq` — Abel, Öhman and Vezzosi's **generic equality**: three relations (types, terms,
  neutral terms) with the properties the logical relation needs.  The logical relation of
  `Start/MLTTLogRel.lean` is defined for any generic equality; instantiated with the
  declarative equality it gives normalization and the fundamental theorem, instantiated with
  the algorithmic equality it gives completeness of the conversion algorithm;
* `MLTT.declEq` — the declarative instance (`TyEq`, `DEq`, `DEq`).
-/

import Start.MLTTReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Type reduction -/

/-- Many-step weak head reduction of types. -/
inductive TyReds : Ctx → Tm → Tm → Prop
  | refl {Γ : Ctx} {A : Tm} : WfTy Γ A → TyReds Γ A A
  | step {Γ : Ctx} {A A' B : Tm} {l : ℕ} : TRed Γ A A' (univ l) → TyReds Γ A' B → TyReds Γ A B

theorem TyReds.tyEq {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) : TyEq Γ A B := by
  induction h with
  | refl hA => exact Der.reflT hA
  | step hs _ ih => exact Der.transT (Der.elEq hs.deq) ih

theorem TyReds.wfL {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) : WfTy Γ A := by
  cases h with
  | refl hA => exact hA
  | step hs _ => exact Der.el hs.tyLeft

theorem TyReds.trans {Γ : Ctx} {A B C : Tm} (h₁ : TyReds Γ A B) (h₂ : TyReds Γ B C) :
    TyReds Γ A C := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact TyReds.step hs (ih h₂)

theorem TyReds.rename {Γ Δ : Ctx} {A B : Tm} {ρ : ℕ → ℕ} (h : TyReds Γ A B) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TyReds Δ (MLTT.rename ρ A) (MLTT.rename ρ B) := by
  induction h with
  | refl hA => exact TyReds.refl (hA.rename hρ hΔ)
  | step hs _ ih => exact TyReds.step (hs.rename hρ hΔ) ih

theorem TyReds.of_whnf {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) (hA : Whnf A) : B = A := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hA.no_tred hs).elim

theorem TyReds.whnf_unique {Γ Γ' : Ctx} {A B C : Tm} (hB : TyReds Γ A B) (hC : TyReds Γ' A C)
    (hnB : Whnf B) (hnC : Whnf C) : B = C := by
  induction hB generalizing C with
  | refl => exact (hC.of_whnf hnB).symm
  | step hs _ ih =>
      cases hC with
      | refl => exact (hnC.no_tred hs).elim
      | step hs' hC' =>
          rw [TRed.det hs hs'] at ih
          exact ih hC' hnB hnC

/-- `Γ ⊢ A :⇒*: B`: a type reduction between well-formed types. -/
structure TyRedsT (Γ : Ctx) (A B : Tm) : Prop where
  wfL : WfTy Γ A
  wfR : WfTy Γ B
  red : TyReds Γ A B

theorem TyRedsT.refl {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : TyRedsT Γ A A := ⟨h, h, TyReds.refl h⟩

theorem TyRedsT.rename {Γ Δ : Ctx} {A B : Tm} {ρ : ℕ → ℕ} (h : TyRedsT Γ A B) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TyRedsT Δ (MLTT.rename ρ A) (MLTT.rename ρ B) :=
  ⟨h.wfL.rename hρ hΔ, h.wfR.rename hρ hΔ, h.red.rename hρ hΔ⟩

theorem TyRedsT.tyEq {Γ : Ctx} {A B : Tm} (h : TyRedsT Γ A B) : TyEq Γ A B := h.red.tyEq

theorem TyRedsT.whnf_unique {Γ : Ctx} {A B C : Tm} (hB : TyRedsT Γ A B) (hC : TyRedsT Γ A C)
    (hnB : Whnf B) (hnC : Whnf C) : B = C :=
  hB.red.whnf_unique hC.red hnB hnC

/-! ### Generic equality -/

/-- **A generic equality**: equality of types, of terms and of neutral terms, with the
properties the logical relation uses. -/
structure GenEq where
  /-- `Γ ⊢ A ≅ B`. -/
  ty : Ctx → Tm → Tm → Prop
  /-- `Γ ⊢ t ≅ u : A`. -/
  tm : Ctx → Tm → Tm → Tm → Prop
  /-- `Γ ⊢ n ~ m : A`. -/
  ne : Ctx → Tm → Tm → Tm → Prop
  ne_tm : ∀ {Γ k l A}, ne Γ k l A → tm Γ k l A
  ty_eq : ∀ {Γ A B}, ty Γ A B → TyEq Γ A B
  tm_eq : ∀ {Γ t u A}, tm Γ t u A → DEq Γ t u A
  ne_eq : ∀ {Γ k l A}, ne Γ k l A → DEq Γ k l A
  univ : ∀ {Γ A B l}, tm Γ A B (Tm.univ l) → ty Γ A B
  ty_symm : ∀ {Γ A B}, ty Γ A B → ty Γ B A
  ty_trans : ∀ {Γ A B C}, ty Γ A B → ty Γ B C → ty Γ A C
  tm_symm : ∀ {Γ t u A}, tm Γ t u A → tm Γ u t A
  tm_trans : ∀ {Γ t u v A}, tm Γ t u A → tm Γ u v A → tm Γ t v A
  ne_symm : ∀ {Γ k l A}, ne Γ k l A → ne Γ l k A
  ne_trans : ∀ {Γ k l m A}, ne Γ k l A → ne Γ l m A → ne Γ k m A
  tm_conv : ∀ {Γ t u A B}, tm Γ t u A → TyEq Γ A B → tm Γ t u B
  ne_conv : ∀ {Γ t u A B}, ne Γ t u A → TyEq Γ A B → ne Γ t u B
  ty_wk : ∀ {Γ Δ ρ A B}, RenOk ρ Γ Δ → WfCtx Δ → ty Γ A B → ty Δ (rename ρ A) (rename ρ B)
  tm_wk : ∀ {Γ Δ ρ t u A}, RenOk ρ Γ Δ → WfCtx Δ → tm Γ t u A →
    tm Δ (rename ρ t) (rename ρ u) (rename ρ A)
  ne_wk : ∀ {Γ Δ ρ t u A}, RenOk ρ Γ Δ → WfCtx Δ → ne Γ t u A →
    ne Δ (rename ρ t) (rename ρ u) (rename ρ A)
  ty_red : ∀ {Γ A A' B B'}, TyRedsT Γ A A' → TyRedsT Γ B B' → Whnf A' → Whnf B' → ty Γ A' B' →
    ty Γ A B
  tm_red : ∀ {Γ A B a a' b b'}, TyRedsT Γ A B → TRedsT Γ a a' B → TRedsT Γ b b' B → Whnf B →
    Whnf a' → Whnf b' → tm Γ a' b' B → tm Γ a b A
  univ_refl : ∀ {Γ} (l : ℕ), WfCtx Γ → ty Γ (Tm.univ l) (Tm.univ l)
  univU_refl : ∀ {Γ} (l : ℕ), WfCtx Γ → tm Γ (Tm.univ l) (Tm.univ l) (Tm.univ (l + 1))
  nat_refl : ∀ {Γ}, WfCtx Γ → ty Γ Tm.nat Tm.nat
  natU_refl : ∀ {Γ}, WfCtx Γ → tm Γ Tm.nat Tm.nat (Tm.univ 0)
  empty_refl : ∀ {Γ}, WfCtx Γ → ty Γ Tm.empty Tm.empty
  emptyU_refl : ∀ {Γ}, WfCtx Γ → tm Γ Tm.empty Tm.empty (Tm.univ 0)
  pi_cong : ∀ {Γ F H G E}, WfTy Γ F → ty Γ F H → ty (F :: Γ) G E → ty Γ (pi F G) (pi H E)
  piU_cong : ∀ {Γ F H G E i j}, HasTy Γ F (Tm.univ i) → tm Γ F H (Tm.univ i) →
    tm (F :: Γ) G E (Tm.univ j) → tm Γ (pi F G) (pi H E) (Tm.univ (max i j))
  zero_refl : ∀ {Γ}, WfCtx Γ → tm Γ Tm.zero Tm.zero Tm.nat
  succ_cong : ∀ {Γ m n}, tm Γ m n Tm.nat → tm Γ (succ m) (succ n) Tm.nat
  eta : ∀ {Γ f g F G}, WfTy Γ F → HasTy Γ f (pi F G) → HasTy Γ g (pi F G) → Whnf f → Whnf g →
    tm (F :: Γ) (app (shift f) (var 0)) (app (shift g) (var 0)) G → tm Γ f g (pi F G)
  var_refl : ∀ {Γ n A}, HasTy Γ (var n) A → ne Γ (var n) (var n) A
  app_cong : ∀ {Γ f g a b F G}, ne Γ f g (pi F G) → tm Γ a b F → ne Γ (app f a) (app g b) (G[a])
  natrec_cong : ∀ {Γ P P' z z' s s' n n'}, WfTy (Tm.nat :: Γ) P → ty (Tm.nat :: Γ) P P' →
    tm Γ z z' (P[Tm.zero]) → tm (P :: Tm.nat :: Γ) s s' (stepTy P) → ne Γ n n' Tm.nat →
    ne Γ (natrec P z s n) (natrec P' z' s' n') (P[n])
  emptyrec_cong : ∀ {Γ P P' e e'}, ty Γ P P' → ne Γ e e' Tm.empty →
    ne Γ (emptyrec P e) (emptyrec P' e') P

/-! ### The declarative instance -/

/-- **The declarative equality is a generic equality.** -/
def declEq : GenEq where
  ty := TyEq
  tm := DEq
  ne := DEq
  ne_tm := id
  ty_eq := id
  tm_eq := id
  ne_eq := id
  univ := Der.elEq
  ty_symm := Der.symmT
  ty_trans := Der.transT
  tm_symm := Der.symm
  tm_trans := Der.trans
  ne_symm := Der.symm
  ne_trans := Der.trans
  tm_conv := Der.eqConv
  ne_conv := Der.eqConv
  ty_wk := fun hρ hΔ h => h.rename hρ hΔ
  tm_wk := fun hρ hΔ h => h.rename hρ hΔ
  ne_wk := fun hρ hΔ h => h.rename hρ hΔ
  ty_red := fun hA hB _ _ h => Der.transT (Der.transT hA.tyEq h) (Der.symmT hB.tyEq)
  tm_red := fun hAB ha hb _ _ _ h =>
    Der.eqConv (Der.trans (Der.trans ha.red.deq h) (Der.symm hb.red.deq)) (Der.symmT hAB.tyEq)
  univ_refl := fun l hΓ => Der.reflT (Der.univT l hΓ)
  univU_refl := fun l hΓ => Der.refl (Der.univU l hΓ)
  nat_refl := fun hΓ => Der.reflT (Der.natT hΓ)
  natU_refl := fun hΓ => Der.refl (Der.natU hΓ)
  empty_refl := fun hΓ => Der.reflT (Der.emptyT hΓ)
  emptyU_refl := fun hΓ => Der.refl (Der.emptyU hΓ)
  pi_cong := fun hF hFH hGE => Der.piCongT hF hFH hGE
  piU_cong := fun hF hFH hGE => Der.piCongU hF hFH hGE
  zero_refl := fun hΓ => Der.refl (Der.zero hΓ)
  succ_cong := Der.succCong
  eta := fun hF hf hg _ _ h => Der.eta hF hf hg h
  var_refl := Der.refl
  app_cong := Der.appCong
  natrec_cong := fun hP hPP hz hs hn => Der.natrecCong hP hPP hz hs hn
  emptyrec_cong := Der.emptyrecCong

end MLTT
