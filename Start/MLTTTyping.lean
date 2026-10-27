/-
**Martin-Löf type theory: the declarative judgements** — milestone M30 (`M30-MLTT-DECL`).

The five judgements of Martin-Löf type theory with dependent functions, a predicative hierarchy
of universes, natural numbers and the empty type, in the style of Abel, Öhman and Vezzosi
(*Decidability of conversion for type theory in type theory*, POPL 2018), with their one universe
replaced by the hierarchy `U 0 : U 1 : U 2 : …`.  They form one inductive family `MLTT.Der`
over the judgement forms `MLTT.Jd`, so that one induction proves a property of all of them:

* `⊢ Γ` — well-formed contexts;
* `Γ ⊢ A` — well-formed types: the universes, `ℕ`, `⊥`, dependent products, and every term of a
  universe (`Der.el`);
* `Γ ⊢ t : A` — typing; the universes are Russell universes (`U l : U (l+1)`, and the type
  formers are terms of universes, `Π F G : U (max i j)` as in Agda, not cumulative);
* `Γ ⊢ A ≡ B` — type equality;
* `Γ ⊢ t ≡ u : A` — definitional equality of terms, with β and the extensionality rule for
  functions and the computation rules of `natrec`.

* `MLTT.Der.wf_ctx` — the context of a derivable judgement is well formed;
* `MLTT.Der.ren` — **weakening** for all five forms, under renamings between well-formed
  contexts (`MLTT.RenOk`).
-/

import Start.MLTTSyntax

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Contexts -/

/-- Contexts: a list of types, the type of the variable `0` first. -/
abbrev Ctx := List Tm

/-- `Lookup Γ n A` : the variable `n` has type `A` in `Γ` (the entry already weakened). -/
inductive Lookup : Ctx → ℕ → Tm → Prop
  | zero (Γ : Ctx) (A : Tm) : Lookup (A :: Γ) 0 (shift A)
  | succ {Γ : Ctx} {n : ℕ} {A : Tm} (B : Tm) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (shift A)

theorem Lookup.det {Γ : Ctx} {n : ℕ} {A B : Tm} (hA : Lookup Γ n A) (hB : Lookup Γ n B) : A = B := by
  induction hA generalizing B with
  | zero => cases hB; rfl
  | succ _ _ ih => cases hB with | succ _ h => rw [ih h]

/-! ### The judgements -/

/-- The judgement forms. -/
inductive Jd where
  /-- `⊢ Γ`. -/
  | wf (Γ : Ctx)
  /-- `Γ ⊢ A`. -/
  | tyWf (Γ : Ctx) (A : Tm)
  /-- `Γ ⊢ t : A`. -/
  | ty (Γ : Ctx) (t A : Tm)
  /-- `Γ ⊢ A ≡ B`. -/
  | tyEq (Γ : Ctx) (A B : Tm)
  /-- `Γ ⊢ t ≡ u : A`. -/
  | eq (Γ : Ctx) (t u A : Tm)

/-- **The derivable judgements of Martin-Löf type theory.** -/
inductive Der : Jd → Prop
  /- Contexts -/
  | nil : Der (.wf [])
  | cons {Γ : Ctx} {A : Tm} : Der (.wf Γ) → Der (.tyWf Γ A) → Der (.wf (A :: Γ))
  /- Types -/
  | univT {Γ : Ctx} (l : ℕ) : Der (.wf Γ) → Der (.tyWf Γ (univ l))
  | natT {Γ : Ctx} : Der (.wf Γ) → Der (.tyWf Γ nat)
  | emptyT {Γ : Ctx} : Der (.wf Γ) → Der (.tyWf Γ empty)
  | piT {Γ : Ctx} {F G : Tm} : Der (.tyWf Γ F) → Der (.tyWf (F :: Γ) G) → Der (.tyWf Γ (pi F G))
  | el {Γ : Ctx} {A : Tm} {l : ℕ} : Der (.ty Γ A (univ l)) → Der (.tyWf Γ A)
  /- Typing -/
  | var {Γ : Ctx} {n : ℕ} {A : Tm} : Der (.wf Γ) → Lookup Γ n A → Der (.ty Γ (var n) A)
  | univU {Γ : Ctx} (l : ℕ) : Der (.wf Γ) → Der (.ty Γ (univ l) (univ (l + 1)))
  | natU {Γ : Ctx} : Der (.wf Γ) → Der (.ty Γ nat (univ 0))
  | emptyU {Γ : Ctx} : Der (.wf Γ) → Der (.ty Γ empty (univ 0))
  | piU {Γ : Ctx} {F G : Tm} {i j : ℕ} : Der (.ty Γ F (univ i)) → Der (.ty (F :: Γ) G (univ j)) →
      Der (.ty Γ (pi F G) (univ (max i j)))
  | lam {Γ : Ctx} {F G b : Tm} : Der (.tyWf Γ F) → Der (.ty (F :: Γ) b G) →
      Der (.ty Γ (lam b) (pi F G))
  | app {Γ : Ctx} {f a F G : Tm} : Der (.ty Γ f (pi F G)) → Der (.ty Γ a F) →
      Der (.ty Γ (app f a) (G[a]))
  | zero {Γ : Ctx} : Der (.wf Γ) → Der (.ty Γ zero nat)
  | succ {Γ : Ctx} {n : Tm} : Der (.ty Γ n nat) → Der (.ty Γ (succ n) nat)
  | natrec {Γ : Ctx} {P z s n : Tm} : Der (.tyWf (nat :: Γ) P) →
      Der (.ty Γ z (P[zero])) → Der (.ty (P :: nat :: Γ) s (stepTy P)) → Der (.ty Γ n nat) →
      Der (.ty Γ (natrec P z s n) (P[n]))
  | emptyrec {Γ : Ctx} {P e : Tm} : Der (.tyWf Γ P) → Der (.ty Γ e empty) →
      Der (.ty Γ (emptyrec P e) P)
  | conv {Γ : Ctx} {t A B : Tm} : Der (.ty Γ t A) → Der (.tyEq Γ A B) → Der (.ty Γ t B)
  /- Type equality -/
  | reflT {Γ : Ctx} {A : Tm} : Der (.tyWf Γ A) → Der (.tyEq Γ A A)
  | symmT {Γ : Ctx} {A B : Tm} : Der (.tyEq Γ A B) → Der (.tyEq Γ B A)
  | transT {Γ : Ctx} {A B C : Tm} : Der (.tyEq Γ A B) → Der (.tyEq Γ B C) → Der (.tyEq Γ A C)
  | piCongT {Γ : Ctx} {F H G E : Tm} : Der (.tyWf Γ F) → Der (.tyEq Γ F H) →
      Der (.tyEq (F :: Γ) G E) → Der (.tyEq Γ (pi F G) (pi H E))
  | elEq {Γ : Ctx} {A B : Tm} {l : ℕ} : Der (.eq Γ A B (univ l)) → Der (.tyEq Γ A B)
  /- Term equality: an equivalence, with conversion of the type -/
  | refl {Γ : Ctx} {t A : Tm} : Der (.ty Γ t A) → Der (.eq Γ t t A)
  | symm {Γ : Ctx} {t u A : Tm} : Der (.eq Γ t u A) → Der (.eq Γ u t A)
  | trans {Γ : Ctx} {t u v A : Tm} : Der (.eq Γ t u A) → Der (.eq Γ u v A) → Der (.eq Γ t v A)
  | eqConv {Γ : Ctx} {t u A B : Tm} : Der (.eq Γ t u A) → Der (.tyEq Γ A B) → Der (.eq Γ t u B)
  /- Term equality: congruences -/
  | piCongU {Γ : Ctx} {F H G E : Tm} {i j : ℕ} : Der (.ty Γ F (univ i)) →
      Der (.eq Γ F H (univ i)) → Der (.eq (F :: Γ) G E (univ j)) →
      Der (.eq Γ (pi F G) (pi H E) (univ (max i j)))
  | appCong {Γ : Ctx} {f g a b F G : Tm} : Der (.eq Γ f g (pi F G)) → Der (.eq Γ a b F) →
      Der (.eq Γ (app f a) (app g b) (G[a]))
  | succCong {Γ : Ctx} {n m : Tm} : Der (.eq Γ n m nat) → Der (.eq Γ (succ n) (succ m) nat)
  | natrecCong {Γ : Ctx} {P P' z z' s s' n n' : Tm} : Der (.tyWf (nat :: Γ) P) →
      Der (.tyEq (nat :: Γ) P P') → Der (.eq Γ z z' (P[zero])) →
      Der (.eq (P :: nat :: Γ) s s' (stepTy P)) → Der (.eq Γ n n' nat) →
      Der (.eq Γ (natrec P z s n) (natrec P' z' s' n') (P[n]))
  | emptyrecCong {Γ : Ctx} {P P' e e' : Tm} : Der (.tyEq Γ P P') → Der (.eq Γ e e' empty) →
      Der (.eq Γ (emptyrec P e) (emptyrec P' e') P)
  /- Term equality: computation and extensionality -/
  | beta {Γ : Ctx} {F G b a : Tm} : Der (.tyWf Γ F) → Der (.ty (F :: Γ) b G) →
      Der (.ty Γ a F) → Der (.eq Γ (app (lam b) a) (b[a]) (G[a]))
  | eta {Γ : Ctx} {f g F G : Tm} : Der (.tyWf Γ F) → Der (.ty Γ f (pi F G)) →
      Der (.ty Γ g (pi F G)) →
      Der (.eq (F :: Γ) (app (shift f) (var 0)) (app (shift g) (var 0)) G) →
      Der (.eq Γ f g (pi F G))
  | natrecZero {Γ : Ctx} {P z s : Tm} : Der (.tyWf (nat :: Γ) P) →
      Der (.ty Γ z (P[zero])) → Der (.ty (P :: nat :: Γ) s (stepTy P)) →
      Der (.eq Γ (natrec P z s zero) z (P[zero]))
  | natrecSucc {Γ : Ctx} {P z s n : Tm} : Der (.tyWf (nat :: Γ) P) →
      Der (.ty Γ z (P[zero])) → Der (.ty (P :: nat :: Γ) s (stepTy P)) → Der (.ty Γ n nat) →
      Der (.eq Γ (natrec P z s (succ n)) (inst2 n (natrec P z s n) s) (P[succ n]))

/-- `⊢ Γ`. -/
abbrev WfCtx (Γ : Ctx) : Prop := Der (.wf Γ)

/-- `Γ ⊢ A`. -/
abbrev WfTy (Γ : Ctx) (A : Tm) : Prop := Der (.tyWf Γ A)

/-- `Γ ⊢ t : A`. -/
abbrev HasTy (Γ : Ctx) (t A : Tm) : Prop := Der (.ty Γ t A)

/-- `Γ ⊢ A ≡ B`. -/
abbrev TyEq (Γ : Ctx) (A B : Tm) : Prop := Der (.tyEq Γ A B)

/-- `Γ ⊢ t ≡ u : A`. -/
abbrev DEq (Γ : Ctx) (t u A : Tm) : Prop := Der (.eq Γ t u A)

/-! ### Well-formed contexts -/

/-- The context of a judgement. -/
def Jd.ctx : Jd → Ctx
  | .wf Γ => Γ
  | .tyWf Γ _ => Γ
  | .ty Γ _ _ => Γ
  | .tyEq Γ _ _ => Γ
  | .eq Γ _ _ _ => Γ

/-- **The context of a derivable judgement is well formed.** -/
theorem Der.wf_ctx {J : Jd} (h : Der J) : WfCtx J.ctx := by
  induction h with
  | nil => exact Der.nil
  | cons hΓ hA _ _ => exact Der.cons hΓ hA
  | univT _ hΓ => exact hΓ
  | natT hΓ => exact hΓ
  | emptyT hΓ => exact hΓ
  | piT _ _ ih _ => exact ih
  | el _ ih => exact ih
  | var hΓ _ => exact hΓ
  | univU _ hΓ => exact hΓ
  | natU hΓ => exact hΓ
  | emptyU hΓ => exact hΓ
  | piU _ _ ih _ => exact ih
  | lam _ _ ih _ => exact ih
  | app _ _ ih _ => exact ih
  | zero hΓ => exact hΓ
  | succ _ ih => exact ih
  | natrec _ _ _ _ _ _ _ ih => exact ih
  | emptyrec _ _ ih _ => exact ih
  | conv _ _ ih _ => exact ih
  | reflT _ ih => exact ih
  | symmT _ ih => exact ih
  | transT _ _ ih _ => exact ih
  | piCongT _ _ _ ih _ _ => exact ih
  | elEq _ ih => exact ih
  | refl _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | eqConv _ _ ih _ => exact ih
  | piCongU _ _ _ ih _ _ => exact ih
  | appCong _ _ ih _ => exact ih
  | succCong _ ih => exact ih
  | natrecCong _ _ _ _ _ _ _ _ _ ih => exact ih
  | emptyrecCong _ _ ih _ => exact ih
  | beta _ _ _ ihF _ _ => exact ihF
  | eta _ _ _ _ ihF _ _ _ => exact ihF
  | natrecZero _ _ _ _ ihz _ => exact ihz
  | natrecSucc _ _ _ _ _ _ _ ihn => exact ihn

theorem WfTy.wf {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : WfCtx Γ := Der.wf_ctx h
theorem HasTy.wf {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : WfCtx Γ := Der.wf_ctx h
theorem TyEq.wf {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : WfCtx Γ := Der.wf_ctx h
theorem DEq.wf {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) : WfCtx Γ := Der.wf_ctx h

/-! ### Weakening -/

/-- `ρ` renames the context `Γ` into the context `Δ`. -/
def RenOk (ρ : ℕ → ℕ) (Γ Δ : Ctx) : Prop := ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (rename ρ A)

theorem rename_upr_shift (ρ : ℕ → ℕ) (A : Tm) :
    rename (upr ρ) (shift A) = shift (rename ρ A) := by
  simp only [shift, rename_rename]
  exact rename_congr (fun _ => rfl) A

theorem RenOk.up {ρ : ℕ → ℕ} {Γ Δ : Ctx} (h : RenOk ρ Γ Δ) (A : Tm) :
    RenOk (upr ρ) (A :: Γ) (rename ρ A :: Δ) := by
  intro n B hB
  cases hB with
  | zero =>
      rw [rename_upr_shift]
      exact Lookup.zero _ _
  | @succ Γ' n' A' B' hB' =>
      rw [rename_upr_shift]
      exact Lookup.succ _ (h _ _ hB')

theorem RenOk.shift (Γ : Ctx) (A : Tm) : RenOk Nat.succ Γ (A :: Γ) := fun _ _ hB =>
  Lookup.succ _ hB

theorem RenOk.id (Γ : Ctx) : RenOk id Γ Γ := fun _ _ hB => by simpa using hB

theorem RenOk.comp {ρ ρ' : ℕ → ℕ} {Γ Δ Θ : Ctx} (h : RenOk ρ Γ Δ) (h' : RenOk ρ' Δ Θ) :
    RenOk (fun n => ρ' (ρ n)) Γ Θ := by
  intro n A hA
  have := h' _ _ (h _ _ hA)
  rwa [rename_rename] at this

/-- The statement of weakening, for each judgement form. -/
def Jd.Ren : Jd → Prop
  | .wf _ => True
  | .tyWf Γ A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ → WfTy Δ (rename ρ A)
  | .ty Γ t A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      HasTy Δ (rename ρ t) (rename ρ A)
  | .tyEq Γ A B => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      TyEq Δ (rename ρ A) (rename ρ B)
  | .eq Γ t u A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      DEq Δ (rename ρ t) (rename ρ u) (rename ρ A)

theorem rename_shift_var0 (ρ : ℕ → ℕ) (f : Tm) :
    rename (upr ρ) (app (shift f) (var 0)) = app (shift (rename ρ f)) (var 0) := by
  simp [rename_upr_shift]

/-- **Weakening**, for all judgement forms at once. -/
theorem Der.ren {J : Jd} (h : Der J) : J.Ren := by
  induction h with
  | nil => trivial
  | cons _ _ _ _ => trivial
  | univT l _ _ => intro Δ ρ hρ hΔ; exact Der.univT l hΔ
  | natT _ _ => intro Δ ρ hρ hΔ; exact Der.natT hΔ
  | emptyT _ _ => intro Δ ρ hρ hΔ; exact Der.emptyT hΔ
  | piT _ _ ihF ihG =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      exact Der.piT hF (ihG (hρ.up _) (Der.cons hΔ hF))
  | el _ ih => intro Δ ρ hρ hΔ; exact Der.el (ih hρ hΔ)
  | var _ hl _ => intro Δ ρ hρ hΔ; exact Der.var hΔ (hρ _ _ hl)
  | univU l _ _ => intro Δ ρ hρ hΔ; exact Der.univU l hΔ
  | natU _ _ => intro Δ ρ hρ hΔ; exact Der.natU hΔ
  | emptyU _ _ => intro Δ ρ hρ hΔ; exact Der.emptyU hΔ
  | piU _ _ ihF ihG =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      exact Der.piU hF (ihG (hρ.up _) (Der.cons hΔ (Der.el hF)))
  | lam _ _ ihF ihb =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      exact Der.lam hF (ihb (hρ.up _) (Der.cons hΔ hF))
  | app _ _ ihf iha =>
      intro Δ ρ hρ hΔ
      have := Der.app (ihf hρ hΔ) (iha hρ hΔ)
      rwa [← rename_inst] at this
  | zero _ _ => intro Δ ρ hρ hΔ; exact Der.zero hΔ
  | succ _ ih => intro Δ ρ hρ hΔ; exact Der.succ (ih hρ hΔ)
  | @natrec Γ P z s n _ _ _ _ ihP ihz ihs ihn =>
      intro Δ ρ hρ hΔ
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP := ihP (hρ.up Tm.nat) hN
      have hz := ihz hρ hΔ
      rw [rename_inst] at hz
      have hs := ihs ((hρ.up Tm.nat).up P) (Der.cons hN hP)
      rw [rename_stepTy] at hs
      have := Der.natrec hP hz hs (ihn hρ hΔ)
      rwa [← rename_inst] at this
  | emptyrec _ _ ihP ihe => intro Δ ρ hρ hΔ; exact Der.emptyrec (ihP hρ hΔ) (ihe hρ hΔ)
  | conv _ _ iht ihe => intro Δ ρ hρ hΔ; exact Der.conv (iht hρ hΔ) (ihe hρ hΔ)
  | reflT _ ih => intro Δ ρ hρ hΔ; exact Der.reflT (ih hρ hΔ)
  | symmT _ ih => intro Δ ρ hρ hΔ; exact Der.symmT (ih hρ hΔ)
  | transT _ _ ih₁ ih₂ => intro Δ ρ hρ hΔ; exact Der.transT (ih₁ hρ hΔ) (ih₂ hρ hΔ)
  | piCongT _ _ _ ihF ihFH ihGE =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      exact Der.piCongT hF (ihFH hρ hΔ) (ihGE (hρ.up _) (Der.cons hΔ hF))
  | elEq _ ih => intro Δ ρ hρ hΔ; exact Der.elEq (ih hρ hΔ)
  | refl _ ih => intro Δ ρ hρ hΔ; exact Der.refl (ih hρ hΔ)
  | symm _ ih => intro Δ ρ hρ hΔ; exact Der.symm (ih hρ hΔ)
  | trans _ _ ih₁ ih₂ => intro Δ ρ hρ hΔ; exact Der.trans (ih₁ hρ hΔ) (ih₂ hρ hΔ)
  | eqConv _ _ ih₁ ih₂ => intro Δ ρ hρ hΔ; exact Der.eqConv (ih₁ hρ hΔ) (ih₂ hρ hΔ)
  | piCongU _ _ _ ihF ihFH ihGE =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      exact Der.piCongU hF (ihFH hρ hΔ) (ihGE (hρ.up _) (Der.cons hΔ (Der.el hF)))
  | appCong _ _ ihf iha =>
      intro Δ ρ hρ hΔ
      have := Der.appCong (ihf hρ hΔ) (iha hρ hΔ)
      rwa [← rename_inst] at this
  | succCong _ ih => intro Δ ρ hρ hΔ; exact Der.succCong (ih hρ hΔ)
  | @natrecCong Γ P P' z z' s s' n n' _ _ _ _ _ ihP ihPP ihz ihs ihn =>
      intro Δ ρ hρ hΔ
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP := ihP (hρ.up Tm.nat) hN
      have hz := ihz hρ hΔ
      rw [rename_inst] at hz
      have hs := ihs ((hρ.up Tm.nat).up P) (Der.cons hN hP)
      rw [rename_stepTy] at hs
      have := Der.natrecCong hP (ihPP (hρ.up Tm.nat) hN) hz hs (ihn hρ hΔ)
      rwa [← rename_inst] at this
  | emptyrecCong _ _ ihP ihe => intro Δ ρ hρ hΔ; exact Der.emptyrecCong (ihP hρ hΔ) (ihe hρ hΔ)
  | beta _ _ _ ihF ihb iha =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      have := Der.beta hF (ihb (hρ.up _) (Der.cons hΔ hF)) (iha hρ hΔ)
      rwa [← rename_inst, ← rename_inst] at this
  | eta _ _ _ _ ihF ihf ihg ihe =>
      intro Δ ρ hρ hΔ
      have hF := ihF hρ hΔ
      have he := ihe (hρ.up _) (Der.cons hΔ hF)
      rw [rename_shift_var0, rename_shift_var0] at he
      exact Der.eta hF (ihf hρ hΔ) (ihg hρ hΔ) he
  | @natrecZero Γ P z s _ _ _ ihP ihz ihs =>
      intro Δ ρ hρ hΔ
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP := ihP (hρ.up Tm.nat) hN
      have hz := ihz hρ hΔ
      rw [rename_inst] at hz
      have hs := ihs ((hρ.up Tm.nat).up P) (Der.cons hN hP)
      rw [rename_stepTy] at hs
      have := Der.natrecZero hP hz hs
      simpa [rename_inst] using this
  | @natrecSucc Γ P z s n _ _ _ _ ihP ihz ihs ihn =>
      intro Δ ρ hρ hΔ
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP := ihP (hρ.up Tm.nat) hN
      have hz := ihz hρ hΔ
      rw [rename_inst] at hz
      have hs := ihs ((hρ.up Tm.nat).up P) (Der.cons hN hP)
      rw [rename_stepTy] at hs
      have := Der.natrecSucc hP hz hs (ihn hρ hΔ)
      simpa [rename_inst, rename_inst2] using this

theorem WfTy.rename {Γ Δ : Ctx} {A : Tm} {ρ : ℕ → ℕ} (h : WfTy Γ A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : WfTy Δ (rename ρ A) :=
  Der.ren h hρ hΔ

theorem HasTy.rename {Γ Δ : Ctx} {t A : Tm} {ρ : ℕ → ℕ} (h : HasTy Γ t A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : HasTy Δ (rename ρ t) (rename ρ A) :=
  Der.ren h hρ hΔ

theorem TyEq.rename {Γ Δ : Ctx} {A B : Tm} {ρ : ℕ → ℕ} (h : TyEq Γ A B) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TyEq Δ (rename ρ A) (rename ρ B) :=
  Der.ren h hρ hΔ

theorem DEq.rename {Γ Δ : Ctx} {t u A : Tm} {ρ : ℕ → ℕ} (h : DEq Γ t u A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : DEq Δ (rename ρ t) (rename ρ u) (rename ρ A) :=
  Der.ren h hρ hΔ

/-- Weakening by one type. -/
theorem HasTy.weaken {Γ : Ctx} {t A B : Tm} (h : HasTy Γ t A) (hB : WfCtx (B :: Γ)) :
    HasTy (B :: Γ) (shift t) (shift A) :=
  h.rename (RenOk.shift Γ B) hB

theorem WfTy.weaken {Γ : Ctx} {A B : Tm} (h : WfTy Γ A) (hB : WfCtx (B :: Γ)) :
    WfTy (B :: Γ) (shift A) :=
  h.rename (RenOk.shift Γ B) hB

theorem TyEq.weaken {Γ : Ctx} {A A' B : Tm} (h : TyEq Γ A A') (hB : WfCtx (B :: Γ)) :
    TyEq (B :: Γ) (shift A) (shift A') :=
  h.rename (RenOk.shift Γ B) hB

theorem DEq.weaken {Γ : Ctx} {t u A B : Tm} (h : DEq Γ t u A) (hB : WfCtx (B :: Γ)) :
    DEq (B :: Γ) (shift t) (shift u) (shift A) :=
  h.rename (RenOk.shift Γ B) hB

end MLTT
