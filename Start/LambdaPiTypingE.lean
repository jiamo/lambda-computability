/-
**`λΠ` with βη-conversion in the typing rules** — task `M23-LF-EQUIV-COMPLETE`.

The typing judgement `LambdaPi.Typing` of `Start/LambdaPiTyping.lean` converts types by β only, so
it is not closed under the η-rule of a declarative equality: `F (c (λy. g y))` is typable and
`F (c g)` is not (`Start/LambdaPiLFTEqTypeLevelCounter.lean`).  This module sets up the
judgement Harper and Pfenning's equality is about: the same rules, with **βη-conversion** in the
conversion rule, and its basic metatheory.

* `BetaEtaConv.rename`, `BetaEtaConv.subst`, `BetaEtaConv.substs`, `BetaEtaConv.instArg` —
  βη-conversion is stable under renaming and substitution, and substitution respects it;
* `LambdaPi.TypingE`, `LambdaPi.WfE` — the judgement and its well-formed contexts, with
  `Typing.toE` and `Wf.toE` (every β-derivation is a βη-derivation);
* `TypingE.rename`, `TypingE.weaken`, `TypingE.substs`, `TypingE.inst` — weakening and
  substitution;
* `TypingE.sort_inv`, `var_inv`, `pi_inv`, `lam_inv`, `app_inv` — inversion, with
  βη-conversions;
* `TypingE.validity` — the type of a typable term is `□` or typable by a sort;
* `TypingE.ctxConv` — conversion of the context;
* `TypingE.whStep`, `TypingE.whRed` — subject reduction for weak head reduction (product
  injectivity for βη-conversion, `betaEtaConv_pi_inv`);
* `teq_validityE_false` — the validity statement recorded as the first missing lemma,
  `TEq Γ M N A → Wf Γ → TypingE Γ M A ∧ TypingE Γ N A`, is false: `TEq.beta` accepts a kind as
  the domain of the abstraction, and `TypingE` cannot type `(λx:∗. x) (Πy:X. X)`.
-/

import Start.LambdaPiLFTEqIncomplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### βη-conversion under renaming and substitution -/

theorem EtaStep.subst {t t' : Tm} (h : EtaStep t t') (σ : ℕ → Tm) :
    EtaStep (LambdaPi.subst σ t) (LambdaPi.subst σ t') := by
  induction h generalizing σ with
  | eta A t =>
      have h := EtaStep.eta (LambdaPi.subst σ A) (LambdaPi.subst σ t)
      simpa [subst_up_shift] using h
  | appL a _ ih => exact EtaStep.appL _ (ih σ)
  | appR f _ ih => exact EtaStep.appR _ (ih σ)
  | lamL b _ ih => exact EtaStep.lamL _ (ih σ)
  | lamR A _ ih => exact EtaStep.lamR _ (ih (up σ))
  | piL B _ ih => exact EtaStep.piL _ (ih σ)
  | piR A _ ih => exact EtaStep.piR _ (ih (up σ))

theorem BetaEtaStep.rename {t t' : Tm} (h : BetaEtaStep t t') (ρ : ℕ → ℕ) :
    BetaEtaStep (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') :=
  h.imp (fun h => h.rename ρ) (fun h => h.rename ρ)

theorem BetaEtaStep.subst {t t' : Tm} (h : BetaEtaStep t t') (σ : ℕ → Tm) :
    BetaEtaStep (LambdaPi.subst σ t) (LambdaPi.subst σ t') :=
  h.imp (fun h => h.subst σ) (fun h => h.subst σ)

namespace BetaEtaConv

theorem rename {t t' : Tm} (h : BetaEtaConv t t') (ρ : ℕ → ℕ) :
    BetaEtaConv (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih => exact ih.step (hs.rename ρ)
  | stepInv _ hs ih => exact ih.stepInv (hs.rename ρ)

theorem subst {t t' : Tm} (h : BetaEtaConv t t') (σ : ℕ → Tm) :
    BetaEtaConv (LambdaPi.subst σ t) (LambdaPi.subst σ t') := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih => exact ih.step (hs.subst σ)
  | stepInv _ hs ih => exact ih.stepInv (hs.subst σ)

/-- β-conversion is a βη-conversion. -/
theorem ofConv {t u : Tm} (h : Conv t u) : BetaEtaConv t u := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih => exact ih.step (Or.inl hs)
  | stepInv _ hs ih => exact ih.stepInv (Or.inl hs)

theorem lamC {A A' b b' : Tm} (hb : BetaEtaConv b b') :
    BetaEtaConv (Tm.lam A b) (Tm.lam A' b') :=
  (BetaEtaConv.lamR A hb).trans (betaEtaConv_lam_annot A A' b')

theorem appC {f f' a a' : Tm} (hf : BetaEtaConv f f') (ha : BetaEtaConv a a') :
    BetaEtaConv (Tm.app f a) (Tm.app f' a') :=
  (BetaEtaConv.appL a hf).trans (BetaEtaConv.appR f' ha)

theorem piC {A A' B B' : Tm} (hA : BetaEtaConv A A') (hB : BetaEtaConv B B') :
    BetaEtaConv (Tm.pi A B) (Tm.pi A' B') :=
  (BetaEtaConv.piL B hA).trans (BetaEtaConv.piR A' hB)

theorem up {σ σ' : ℕ → Tm} (h : ∀ n, BetaEtaConv (σ n) (σ' n)) :
    ∀ n, BetaEtaConv (LambdaPi.up σ n) (LambdaPi.up σ' n)
  | 0 => BetaEtaConv.refl _
  | n + 1 => (h n).rename Nat.succ

/-- Substitutions that are pointwise βη-convertible give βη-convertible results. -/
theorem substs {σ σ' : ℕ → Tm} (h : ∀ n, BetaEtaConv (σ n) (σ' n)) (t : Tm) :
    BetaEtaConv (LambdaPi.subst σ t) (LambdaPi.subst σ' t) := by
  induction t generalizing σ σ' with
  | var n => exact h n
  | sort s => exact BetaEtaConv.refl _
  | app f a ihf iha =>
      simp only [subst_app]
      exact appC (ihf h) (iha h)
  | lam A b _ ihb =>
      simp only [subst_lam]
      exact lamC (ihb (up h))
  | pi A B ihA ihB =>
      simp only [subst_pi]
      exact piC (ihA h) (ihB (up h))

/-- Substituting βη-convertible arguments. -/
theorem instArg (t : Tm) {a a' : Tm} (h : BetaEtaConv a a') : BetaEtaConv (t[a]) (t[a']) := by
  apply substs
  intro n
  cases n with
  | zero => exact h
  | succ n => exact BetaEtaConv.refl _

end BetaEtaConv

/-! ### The judgement -/

/-- **The typing judgement of `λΠ` with βη-conversion.** -/
inductive TypingE : Ctx → Tm → Tm → Prop
  | ax (Γ : Ctx) : TypingE Γ (Tm.sort Srt.star) (Tm.sort Srt.box)
  | var {Γ : Ctx} {n : ℕ} {A : Tm} : Lookup Γ n A → TypingE Γ (Tm.var n) A
  | pi {Γ : Ctx} {A B : Tm} {s t : Srt} : Rule s t → TypingE Γ A (Tm.sort s) →
      TypingE (A :: Γ) B (Tm.sort t) → TypingE Γ (Tm.pi A B) (Tm.sort t)
  | lam {Γ : Ctx} {A B b : Tm} {s : Srt} : TypingE Γ (Tm.pi A B) (Tm.sort s) →
      TypingE (A :: Γ) b B → TypingE Γ (Tm.lam A b) (Tm.pi A B)
  | app {Γ : Ctx} {f a A B : Tm} : TypingE Γ f (Tm.pi A B) → TypingE Γ a A →
      TypingE Γ (Tm.app f a) (B[a])
  | conv {Γ : Ctx} {t A B : Tm} {s : Srt} : TypingE Γ t A → TypingE Γ B (Tm.sort s) →
      BetaEtaConv A B → TypingE Γ t B

/-- Well-formed contexts for `TypingE`. -/
inductive WfE : Ctx → Prop
  | nil : WfE []
  | cons {Γ : Ctx} {A : Tm} {s : Srt} : WfE Γ → TypingE Γ A (Tm.sort s) → WfE (A :: Γ)

/-- Every β-typing is a βη-typing. -/
theorem Typing.toE {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) : TypingE Γ t A := by
  induction h with
  | ax Γ => exact TypingE.ax Γ
  | var hA => exact TypingE.var hA
  | pi hr _ _ ihA ihB => exact TypingE.pi hr ihA ihB
  | lam _ _ ihP ihb => exact TypingE.lam ihP ihb
  | app _ _ ihf iha => exact TypingE.app ihf iha
  | conv _ _ hc iht ihB => exact TypingE.conv iht ihB (BetaEtaConv.ofConv hc)

theorem Wf.toE {Γ : Ctx} (h : Wf Γ) : WfE Γ := by
  induction h with
  | nil => exact WfE.nil
  | cons _ hA ih => exact WfE.cons ih hA.toE

/-! ### Renaming and weakening -/

theorem TypingE.rename {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) {Δ : Ctx} {ρ : ℕ → ℕ}
    (hρ : RenOk ρ Γ Δ) : TypingE Δ (LambdaPi.rename ρ t) (LambdaPi.rename ρ A) := by
  induction h generalizing Δ ρ with
  | ax Γ => exact TypingE.ax _
  | var hA => exact TypingE.var (hρ _ _ hA)
  | pi hr _ _ ihA ihB => exact TypingE.pi hr (ihA hρ) (ihB (hρ.up _))
  | lam _ _ ihP ihb => exact TypingE.lam (ihP hρ) (ihb (hρ.up _))
  | @app Γ f a A B _ _ ihf iha =>
      have hres := TypingE.app (ihf hρ) (iha hρ)
      rwa [← inst_rename] at hres
  | conv _ _ hc iht ihB => exact TypingE.conv (iht hρ) (ihB hρ) (hc.rename ρ)

/-- Weakening. -/
theorem TypingE.weaken {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) (B : Tm) :
    TypingE (B :: Γ) (shift t) (shift A) :=
  h.rename (RenOk.shift Γ B)

theorem WfE.tail {Γ : Ctx} {A : Tm} (h : WfE (A :: Γ)) : WfE Γ := by
  cases h with
  | cons hΓ _ => exact hΓ

theorem WfE.head {Γ : Ctx} {A : Tm} (h : WfE (A :: Γ)) : ∃ s : Srt, TypingE Γ A (Tm.sort s) := by
  cases h with
  | cons _ hA => exact ⟨_, hA⟩

/-- In a well-formed context every declared type is typable by a sort. -/
theorem WfE.lookup_typed {Γ : Ctx} (hΓ : WfE Γ) {n : ℕ} {A : Tm} (hA : Lookup Γ n A) :
    ∃ s : Srt, TypingE Γ A (Tm.sort s) := by
  induction hA with
  | zero Γ A =>
      cases hΓ with
      | cons _ hA => exact ⟨_, hA.weaken A⟩
  | succ B _ ih =>
      cases hΓ with
      | cons hΓ' _ =>
          obtain ⟨s, hs⟩ := ih hΓ'
          exact ⟨s, hs.weaken B⟩

/-! ### Substitution -/

/-- `σ` is a well-typed substitution from `Γ` to `Δ`. -/
def SubOkE (σ : ℕ → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ n A, Lookup Γ n A → TypingE Δ (σ n) (subst σ A)

theorem SubOkE.up {σ : ℕ → Tm} {Γ Δ : Ctx} (h : SubOkE σ Γ Δ) (A : Tm) :
    SubOkE (LambdaPi.up σ) (A :: Γ) (subst σ A :: Δ) := by
  intro n B hB
  cases hB with
  | zero =>
      rw [subst_up_shift]
      exact TypingE.var (Lookup.zero _ _)
  | @succ Γ' n' A' B' hB' =>
      rw [subst_up_shift]
      exact (h _ _ hB').weaken _

theorem TypingE.substs {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) {Δ : Ctx} {σ : ℕ → Tm}
    (hσ : SubOkE σ Γ Δ) : TypingE Δ (subst σ t) (subst σ A) := by
  induction h generalizing Δ σ with
  | ax Γ => exact TypingE.ax _
  | var hA => exact hσ _ _ hA
  | pi hr _ _ ihA ihB => exact TypingE.pi hr (ihA hσ) (ihB (hσ.up _))
  | lam _ _ ihP ihb => exact TypingE.lam (ihP hσ) (ihb (hσ.up _))
  | @app Γ f a A B _ _ ihf iha =>
      have hres := TypingE.app (ihf hσ) (iha hσ)
      rwa [← inst_subst] at hres
  | conv _ _ hc iht ihB => exact TypingE.conv (iht hσ) (ihB hσ) (hc.subst σ)

theorem SubOkE.inst {Γ : Ctx} {a A : Tm} (ha : TypingE Γ a A) :
    SubOkE (scons a ids) (A :: Γ) Γ := by
  intro n B hB
  cases hB with
  | zero =>
      have he : subst (scons a ids) (shift A) = A := inst_shift a A
      rw [he]
      exact ha
  | @succ Γ' n' A' B' hB' =>
      have he : subst (scons a ids) (shift A') = A' := inst_shift a A'
      rw [he]
      exact TypingE.var hB'

/-- Substitution of a single variable. -/
theorem TypingE.inst {Γ : Ctx} {A B b a : Tm} (hb : TypingE (A :: Γ) b B) (ha : TypingE Γ a A) :
    TypingE Γ (b[a]) (B[a]) :=
  hb.substs (SubOkE.inst ha)

/-! ### Inversion -/

theorem TypingE.sort_inv' {Γ : Ctx} {e C : Tm} (h : TypingE Γ e C) :
    ∀ {s : Srt}, e = Tm.sort s → s = Srt.star ∧ BetaEtaConv (Tm.sort Srt.box) C := by
  induction h with
  | ax Γ => intro s he; cases he; exact ⟨rfl, BetaEtaConv.refl _⟩
  | var _ => intro s he; cases he
  | pi _ _ _ _ _ => intro s he; cases he
  | lam _ _ _ _ => intro s he; cases he
  | app _ _ _ _ => intro s he; cases he
  | conv _ _ hc ih _ =>
      intro s he
      obtain ⟨hs, hconv⟩ := ih he
      exact ⟨hs, hconv.trans hc⟩

theorem TypingE.sort_inv {Γ : Ctx} {s : Srt} {C : Tm} (h : TypingE Γ (Tm.sort s) C) :
    s = Srt.star ∧ BetaEtaConv (Tm.sort Srt.box) C :=
  h.sort_inv' rfl

theorem TypingE.var_inv' {Γ : Ctx} {e C : Tm} (h : TypingE Γ e C) :
    ∀ {n : ℕ}, e = Tm.var n → ∃ A, Lookup Γ n A ∧ BetaEtaConv A C := by
  induction h with
  | ax Γ => intro n he; cases he
  | var hA => intro n he; cases he; exact ⟨_, hA, BetaEtaConv.refl _⟩
  | pi _ _ _ _ _ => intro n he; cases he
  | lam _ _ _ _ => intro n he; cases he
  | app _ _ _ _ => intro n he; cases he
  | conv _ _ hc ih _ =>
      intro n he
      obtain ⟨A, hA, hconv⟩ := ih he
      exact ⟨A, hA, hconv.trans hc⟩

theorem TypingE.var_inv {Γ : Ctx} {n : ℕ} {C : Tm} (h : TypingE Γ (Tm.var n) C) :
    ∃ A, Lookup Γ n A ∧ BetaEtaConv A C :=
  h.var_inv' rfl

theorem TypingE.pi_inv' {Γ : Ctx} {e C : Tm} (h : TypingE Γ e C) :
    ∀ {A B : Tm}, e = Tm.pi A B →
      ∃ s t, Rule s t ∧ TypingE Γ A (Tm.sort s) ∧ TypingE (A :: Γ) B (Tm.sort t) ∧
        BetaEtaConv (Tm.sort t) C := by
  induction h with
  | ax Γ => intro A B he; cases he
  | var _ => intro A B he; cases he
  | pi hr hA hB _ _ =>
      intro A B he
      cases he
      exact ⟨_, _, hr, hA, hB, BetaEtaConv.refl _⟩
  | lam _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | conv _ _ hc ih _ =>
      intro A B he
      obtain ⟨s, t, hr, hA, hB, hconv⟩ := ih he
      exact ⟨s, t, hr, hA, hB, hconv.trans hc⟩

theorem TypingE.pi_inv {Γ : Ctx} {A B C : Tm} (h : TypingE Γ (Tm.pi A B) C) :
    ∃ s t, Rule s t ∧ TypingE Γ A (Tm.sort s) ∧ TypingE (A :: Γ) B (Tm.sort t) ∧
      BetaEtaConv (Tm.sort t) C :=
  h.pi_inv' rfl

theorem TypingE.lam_inv' {Γ : Ctx} {e C : Tm} (h : TypingE Γ e C) :
    ∀ {A b : Tm}, e = Tm.lam A b →
      ∃ B s, TypingE Γ (Tm.pi A B) (Tm.sort s) ∧ TypingE (A :: Γ) b B ∧
        BetaEtaConv (Tm.pi A B) C := by
  induction h with
  | ax Γ => intro A b he; cases he
  | var _ => intro A b he; cases he
  | pi _ _ _ _ _ => intro A b he; cases he
  | lam hP hb _ _ =>
      intro A b he
      cases he
      exact ⟨_, _, hP, hb, BetaEtaConv.refl _⟩
  | app _ _ _ _ => intro A b he; cases he
  | conv _ _ hc ih _ =>
      intro A b he
      obtain ⟨B, s, hP, hb, hconv⟩ := ih he
      exact ⟨B, s, hP, hb, hconv.trans hc⟩

theorem TypingE.lam_inv {Γ : Ctx} {A b C : Tm} (h : TypingE Γ (Tm.lam A b) C) :
    ∃ B s, TypingE Γ (Tm.pi A B) (Tm.sort s) ∧ TypingE (A :: Γ) b B ∧
      BetaEtaConv (Tm.pi A B) C :=
  h.lam_inv' rfl

theorem TypingE.app_inv' {Γ : Ctx} {e C : Tm} (h : TypingE Γ e C) :
    ∀ {f a : Tm}, e = Tm.app f a →
      ∃ A B, TypingE Γ f (Tm.pi A B) ∧ TypingE Γ a A ∧ BetaEtaConv (B[a]) C := by
  induction h with
  | ax Γ => intro f a he; cases he
  | var _ => intro f a he; cases he
  | pi _ _ _ _ _ => intro f a he; cases he
  | lam _ _ _ _ => intro f a he; cases he
  | app hf ha _ _ =>
      intro f a he
      cases he
      exact ⟨_, _, hf, ha, BetaEtaConv.refl _⟩
  | conv _ _ hc ih _ =>
      intro f a he
      obtain ⟨A, B, hf, ha, hconv⟩ := ih he
      exact ⟨A, B, hf, ha, hconv.trans hc⟩

theorem TypingE.app_inv {Γ : Ctx} {f a C : Tm} (h : TypingE Γ (Tm.app f a) C) :
    ∃ A B, TypingE Γ f (Tm.pi A B) ∧ TypingE Γ a A ∧ BetaEtaConv (B[a]) C :=
  h.app_inv' rfl

/-- The top sort has no type. -/
theorem not_typingE_box {Γ : Ctx} {C : Tm} (h : TypingE Γ (Tm.sort Srt.box) C) : False := by
  obtain ⟨hs, -⟩ := h.sort_inv
  exact Srt.noConfusion hs

/-! ### Validity -/

/-- **Validity**: the type of a typable term is the top sort or is typable by a sort. -/
theorem TypingE.validity {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) :
    WfE Γ → A = Tm.sort Srt.box ∨ ∃ s : Srt, TypingE Γ A (Tm.sort s) := by
  induction h with
  | ax Γ => intro _; exact Or.inl rfl
  | var hA => intro hΓ; exact Or.inr (hΓ.lookup_typed hA)
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro _
      cases t with
      | star => exact Or.inr ⟨Srt.box, TypingE.ax _⟩
      | box => exact Or.inl rfl
  | @lam Γ A B b s hP hb ihP ihb => intro _; exact Or.inr ⟨s, hP⟩
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ
      rcases ihf hΓ with h₁ | ⟨s, hs⟩
      · exact absurd h₁ (by simp)
      · obtain ⟨s', t', hr, hA, hB, hconv⟩ := hs.pi_inv
        exact Or.inr ⟨t', hB.inst ha⟩
  | conv _ hB _ _ _ => intro _; exact Or.inr ⟨_, hB⟩

/-- A product type that is typable has a typable codomain. -/
theorem TypingE.pi_cod {Γ : Ctx} {f A B : Tm} (h : TypingE Γ f (Tm.pi A B)) (hΓ : WfE Γ) :
    ∃ s t, Rule s t ∧ TypingE Γ A (Tm.sort s) ∧ TypingE (A :: Γ) B (Tm.sort t) := by
  rcases h.validity hΓ with h₁ | ⟨s, hs⟩
  · exact absurd h₁ (by simp)
  · obtain ⟨s', t', hr, hA, hB, -⟩ := hs.pi_inv
    exact ⟨s', t', hr, hA, hB⟩

/-! ### Context conversion -/

/-- `Δ` is a well-typed βη-conversion of the context `Γ`. -/
def CtxConvOkE (Γ Δ : Ctx) : Prop :=
  ∀ n A, Lookup Γ n A → ∃ A' s, Lookup Δ n A' ∧ BetaEtaConv A A' ∧ TypingE Δ A (Tm.sort s)

theorem CtxConvOkE.refl {Γ : Ctx} (hΓ : WfE Γ) : CtxConvOkE Γ Γ := by
  intro n A hA
  obtain ⟨s, hs⟩ := hΓ.lookup_typed hA
  exact ⟨A, s, hA, BetaEtaConv.refl _, hs⟩

theorem CtxConvOkE.cons {Γ Δ : Ctx} (h : CtxConvOkE Γ Δ) {A : Tm} {s : Srt}
    (hA : TypingE Δ A (Tm.sort s)) : CtxConvOkE (A :: Γ) (A :: Δ) := by
  intro n B hB
  cases hB with
  | zero => exact ⟨shift A, s, Lookup.zero _ _, BetaEtaConv.refl _, hA.weaken A⟩
  | @succ Γ' n' A' B' hB' =>
      obtain ⟨B'', s'', hB'', hconv, hty⟩ := h _ _ hB'
      exact ⟨shift B'', s'', Lookup.succ _ hB'', hconv.rename Nat.succ, hty.weaken A⟩

/-- Converting the first entry of a context, given that the old entry stays typable. -/
theorem CtxConvOkE.consConv {Γ : Ctx} (hΓ : WfE Γ) {A A' : Tm} {s : Srt}
    (hA : TypingE Γ A (Tm.sort s)) (hconv : BetaEtaConv A A') : CtxConvOkE (A :: Γ) (A' :: Γ) := by
  intro n B hB
  cases hB with
  | zero =>
      exact ⟨shift A', s, Lookup.zero _ _, hconv.rename Nat.succ, hA.weaken A'⟩
  | @succ Γ' n' A'' B' hB' =>
      obtain ⟨s', hs'⟩ := hΓ.lookup_typed hB'
      exact ⟨shift A'', s', Lookup.succ _ hB', BetaEtaConv.refl _, hs'.weaken A'⟩

/-- Typing is stable under βη-conversion of the context. -/
theorem TypingE.ctxConv {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) {Δ : Ctx}
    (hΔ : CtxConvOkE Γ Δ) : TypingE Δ t A := by
  induction h generalizing Δ with
  | ax Γ => exact TypingE.ax _
  | var hA =>
      obtain ⟨A', s, hA', hconv, hty⟩ := hΔ _ _ hA
      exact (TypingE.var hA').conv hty hconv.symm
  | @pi Γ A B s t hr hA hB ihA ihB =>
      have hA' := ihA hΔ
      exact TypingE.pi hr hA' (ihB (hΔ.cons hA'))
  | @lam Γ A B b s hP hb ihP ihb =>
      have hP' := ihP hΔ
      obtain ⟨s', t', hr, hA', hB', hconv⟩ := hP'.pi_inv
      exact TypingE.lam hP' (ihb (hΔ.cons hA'))
  | app _ _ ihf iha => exact TypingE.app (ihf hΔ) (iha hΔ)
  | conv _ _ hc iht ihB => exact (iht hΔ).conv (ihB hΔ) hc

/-- Changing the first entry of a well-formed context to a βη-convertible one. -/
theorem TypingE.ctxConv₁ {Γ : Ctx} {A A' t T : Tm} {s : Srt} (h : TypingE (A :: Γ) t T)
    (hΓ : WfE Γ) (hA : TypingE Γ A (Tm.sort s)) (hconv : BetaEtaConv A A') :
    TypingE (A' :: Γ) t T := by
  refine h.ctxConv ?_
  intro n B hB
  cases hB with
  | zero =>
      exact ⟨shift A', s, Lookup.zero _ _, hconv.rename Nat.succ, hA.weaken A'⟩
  | @succ Γ' n' A'' B' hB' =>
      obtain ⟨s'', hs''⟩ := hΓ.lookup_typed hB'
      exact ⟨shift A'', s'', Lookup.succ _ hB', BetaEtaConv.refl _, hs''.weaken A'⟩

/-! ### Subject reduction for weak head reduction -/

/-- **Subject reduction for a weak head step.** -/
theorem TypingE.whStep {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) :
    WfE Γ → ∀ {t' : Tm}, WhStep t t' → TypingE Γ t' A := by
  induction h with
  | ax Γ => intro _ t' hst; cases hst
  | var _ => intro _ t' hst; cases hst
  | pi _ _ _ _ _ => intro _ t' hst; cases hst
  | lam _ _ _ _ => intro _ t' hst; cases hst
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ t' hst
      have hBa : ∃ s : Srt, TypingE Γ (B[a]) (Tm.sort s) := by
        obtain ⟨s', t', hr, hA, hB⟩ := hf.pi_cod hΓ
        exact ⟨t', hB.inst ha⟩
      cases hst with
      | beta A₀ b a =>
          obtain ⟨B₀, s₀, hP₀, hb₀, hconv₀⟩ := hf.lam_inv
          obtain ⟨s₁, t₁, hr₁, hA₀, hB₀, _⟩ := hP₀.pi_inv
          obtain ⟨hAA, hBB⟩ := betaEtaConv_pi_inv hconv₀
          have ha₀ : TypingE Γ a A₀ := ha.conv hA₀ hAA.symm
          have hsub : TypingE Γ (b[a]) (B₀[a]) := hb₀.inst ha₀
          obtain ⟨s₂, hs₂⟩ := hBa
          exact hsub.conv hs₂ (hBB.subst (scons a ids))
      | appL _ hf' => exact TypingE.app (ihf hΓ hf') ha
  | @conv Γ t A B s ht hB hc iht ihB =>
      intro hΓ t' hst
      exact (iht hΓ hst).conv hB hc

/-- Subject reduction for weak head reduction. -/
theorem TypingE.whRed {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) (hΓ : WfE Γ) {t' : Tm}
    (hred : WhRed t t') : TypingE Γ t' A := by
  induction hred with
  | refl => exact h
  | tail _ hs ih => exact ih.whStep hΓ hs

/-! ### The recorded validity statement for `TEq` is false -/

/-- `(λx:∗. x) (Πy:X. X)` has no βη-type either. -/
theorem ti_redex_untypedE (T : Tm) : ¬ TypingE tiΓ tiR T := by
  intro h
  obtain ⟨A, B, hf, -, -⟩ := h.app_inv
  obtain ⟨B₀, s₀, hP, -, -⟩ := hf.lam_inv
  obtain ⟨s, t, hr, hA, -, -⟩ := hP.pi_inv
  cases hr
  obtain ⟨-, hc⟩ := hA.sort_inv
  exact Srt.noConfusion (betaEtaConv_sort_inj hc)

/-- **The validity of `TEq` for βη-typing is false**: `TEq.beta` relates the untypable
`(λx:∗. x) (Πy:X. X)` to `Πy:X. X` in the well-formed context `X : ∗`. -/
theorem teq_validityE_false :
    ¬ ∀ (Γ : Ctx) (M N A : Tm), TEq Γ M N A → Wf Γ → TypingE Γ M A ∧ TypingE Γ N A := by
  intro h
  exact ti_redex_untypedE _ (h _ _ _ _ ti_teq_redex ti_wf).1

end LambdaPi
