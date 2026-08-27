/-
The typing judgement of the dependently typed lambda calculus `λΠ`, and its metatheory:
weakening, substitution, context conversion, type correctness (validity) and subject reduction.

The calculus is the pure type system with sorts `∗ : □` and the two rules `(∗,∗)` and `(∗,□)`,
i.e. the logical framework `LF` = `λΠ`.  A context is a list of types, the type of the de Bruijn
variable `0` first, and `Lookup Γ n A` says that the variable `n` has type `A` in `Γ` (the entry
already shifted).

* `LambdaPi.Typing` — the typing judgement `Γ ⊢ t : A`, and `LambdaPi.Wf` — well-formed contexts;
* `LambdaPi.Typing.rename`, `LambdaPi.Typing.weaken` — renaming and weakening;
* `LambdaPi.Typing.substs`, `LambdaPi.Typing.inst` — the substitution lemma, in parallel and in
  single-variable form; this is what makes the syntactic category of `Start/LambdaPiCwa.lean`
  work;
* `LambdaPi.Typing.pi_inv`, `LambdaPi.Typing.lam_inv`, `LambdaPi.Typing.app_inv`,
  `LambdaPi.Typing.var_inv`, `LambdaPi.Typing.sort_inv` — inversion of the typing rules;
* `LambdaPi.Typing.ctxConv` — conversion of the context;
* `LambdaPi.Typing.validity` — the type of a typable term is the top sort or is itself typable;
* `LambdaPi.Typing.step`, `LambdaPi.Typing.red` — **subject reduction**: typing is preserved by
  β-reduction.
-/

import Start.LambdaPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-- Contexts: a list of types, the type of the variable `0` first. -/
abbrev Ctx := List Tm

/-- `Lookup Γ n A` : the de Bruijn variable `n` has type `A` in `Γ`. -/
inductive Lookup : Ctx → ℕ → Tm → Prop
  | zero (Γ : Ctx) (A : Tm) : Lookup (A :: Γ) 0 (shift A)
  | succ {Γ : Ctx} {n : ℕ} {A : Tm} (B : Tm) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (shift A)

/-- The product rules of `λΠ`: a product may be formed over a *type* (a term of `∗`), and it
lands in the sort of its codomain.  This gives exactly the rules `(∗,∗)` and `(∗,□)`. -/
def Rule (s _t : Srt) : Prop := s = Srt.star

/-- The typing judgement of `λΠ`. -/
inductive Typing : Ctx → Tm → Tm → Prop
  | ax (Γ : Ctx) : Typing Γ (Tm.sort Srt.star) (Tm.sort Srt.box)
  | var {Γ : Ctx} {n : ℕ} {A : Tm} : Lookup Γ n A → Typing Γ (Tm.var n) A
  | pi {Γ : Ctx} {A B : Tm} {s t : Srt} : Rule s t → Typing Γ A (Tm.sort s) →
      Typing (A :: Γ) B (Tm.sort t) → Typing Γ (Tm.pi A B) (Tm.sort t)
  | lam {Γ : Ctx} {A B b : Tm} {s : Srt} : Typing Γ (Tm.pi A B) (Tm.sort s) →
      Typing (A :: Γ) b B → Typing Γ (Tm.lam A b) (Tm.pi A B)
  | app {Γ : Ctx} {f a A B : Tm} : Typing Γ f (Tm.pi A B) → Typing Γ a A →
      Typing Γ (Tm.app f a) (B[a])
  | conv {Γ : Ctx} {t A B : Tm} {s : Srt} : Typing Γ t A → Typing Γ B (Tm.sort s) →
      Conv A B → Typing Γ t B

/-- Well-formed contexts. -/
inductive Wf : Ctx → Prop
  | nil : Wf []
  | cons {Γ : Ctx} {A : Tm} {s : Srt} : Wf Γ → Typing Γ A (Tm.sort s) → Wf (A :: Γ)

/-! ### Renaming and weakening -/

/-- `ρ` renames the context `Γ` into the context `Δ`. -/
def RenOk (ρ : ℕ → ℕ) (Γ Δ : Ctx) : Prop := ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (rename ρ A)

theorem rename_upr_shift (ρ : ℕ → ℕ) (A : Tm) :
    rename (upr ρ) (shift A) = shift (rename ρ A) := by
  simp only [shift, rename_rename]
  exact rename_congr (by intro k; rfl) A

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

theorem Typing.rename {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) {Δ : Ctx} {ρ : ℕ → ℕ}
    (hρ : RenOk ρ Γ Δ) : Typing Δ (LambdaPi.rename ρ t) (LambdaPi.rename ρ A) := by
  induction h generalizing Δ ρ with
  | ax Γ => exact Typing.ax _
  | var hA => exact Typing.var (hρ _ _ hA)
  | pi hr _ _ ihA ihB => exact Typing.pi hr (ihA hρ) (ihB (hρ.up _))
  | lam _ _ ihP ihb => exact Typing.lam (ihP hρ) (ihb (hρ.up _))
  | @app Γ f a A B _ _ ihf iha =>
      have hres := Typing.app (ihf hρ) (iha hρ)
      rwa [← inst_rename] at hres
  | conv _ _ hc iht ihB => exact Typing.conv (iht hρ) (ihB hρ) (hc.rename ρ)

/-- Weakening: a judgement remains valid in a longer context. -/
theorem Typing.weaken {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (B : Tm) :
    Typing (B :: Γ) (shift t) (shift A) :=
  h.rename (RenOk.shift Γ B)

theorem Wf.tail {Γ : Ctx} {A : Tm} (h : Wf (A :: Γ)) : Wf Γ := by
  cases h with
  | cons hΓ _ => exact hΓ

/-- In a well-formed context every variable has a type that is typable by a sort. -/
theorem Wf.lookup_typed {Γ : Ctx} (hΓ : Wf Γ) {n : ℕ} {A : Tm} (hA : Lookup Γ n A) :
    ∃ s : Srt, Typing Γ A (Tm.sort s) := by
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

/-- `σ` is a well-typed substitution from the context `Γ` to the context `Δ`. -/
def SubOk (σ : ℕ → Tm) (Γ Δ : Ctx) : Prop := ∀ n A, Lookup Γ n A → Typing Δ (σ n) (subst σ A)

theorem subst_up_shift (σ : ℕ → Tm) (A : Tm) : subst (up σ) (shift A) = shift (subst σ A) := by
  simp only [shift, subst_rename, rename_subst]
  rfl

theorem SubOk.up {σ : ℕ → Tm} {Γ Δ : Ctx} (h : SubOk σ Γ Δ) (A : Tm) :
    SubOk (LambdaPi.up σ) (A :: Γ) (subst σ A :: Δ) := by
  intro n B hB
  cases hB with
  | zero =>
      rw [subst_up_shift]
      exact Typing.var (Lookup.zero _ _)
  | @succ Γ' n' A' B' hB' =>
      rw [subst_up_shift]
      exact (h _ _ hB').weaken _

theorem Typing.substs {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) {Δ : Ctx} {σ : ℕ → Tm}
    (hσ : SubOk σ Γ Δ) : Typing Δ (subst σ t) (subst σ A) := by
  induction h generalizing Δ σ with
  | ax Γ => exact Typing.ax _
  | var hA => exact hσ _ _ hA
  | pi hr _ _ ihA ihB => exact Typing.pi hr (ihA hσ) (ihB (hσ.up _))
  | lam _ _ ihP ihb => exact Typing.lam (ihP hσ) (ihb (hσ.up _))
  | @app Γ f a A B _ _ ihf iha =>
      have hres := Typing.app (ihf hσ) (iha hσ)
      rwa [← inst_subst] at hres
  | conv _ _ hc iht ihB => exact Typing.conv (iht hσ) (ihB hσ) (hc.subst σ)

/-- The substitution `scons a ids` substitutes `a` for the variable `0`. -/
theorem SubOk.inst {Γ : Ctx} {a A : Tm} (ha : Typing Γ a A) :
    SubOk (scons a ids) (A :: Γ) Γ := by
  intro n B hB
  cases hB with
  | zero =>
      have he : subst (scons a ids) (shift A) = A := inst_shift a A
      rw [he]
      exact ha
  | @succ Γ' n' A' B' hB' =>
      have he : subst (scons a ids) (shift A') = A' := inst_shift a A'
      rw [he]
      exact Typing.var hB'

/-- Substitution of a single variable. -/
theorem Typing.inst {Γ : Ctx} {A B b a : Tm} (hb : Typing (A :: Γ) b B) (ha : Typing Γ a A) :
    Typing Γ (b[a]) (B[a]) :=
  hb.substs (SubOk.inst ha)

/-! ### Inversion -/

theorem Typing.sort_inv' {Γ : Ctx} {e C : Tm} (h : Typing Γ e C) :
    ∀ {s : Srt}, e = Tm.sort s → s = Srt.star ∧ Conv (Tm.sort Srt.box) C := by
  induction h with
  | ax Γ => intro s he; cases he; exact ⟨rfl, Conv.refl _⟩
  | var _ => intro s he; cases he
  | pi _ _ _ _ _ => intro s he; cases he
  | lam _ _ _ _ => intro s he; cases he
  | app _ _ _ _ => intro s he; cases he
  | conv _ _ hc ih _ =>
      intro s he
      obtain ⟨hs, hconv⟩ := ih he
      exact ⟨hs, hconv.trans hc⟩

theorem Typing.sort_inv {Γ : Ctx} {s : Srt} {C : Tm} (h : Typing Γ (Tm.sort s) C) :
    s = Srt.star ∧ Conv (Tm.sort Srt.box) C :=
  h.sort_inv' rfl

theorem Typing.var_inv' {Γ : Ctx} {e C : Tm} (h : Typing Γ e C) :
    ∀ {n : ℕ}, e = Tm.var n → ∃ A, Lookup Γ n A ∧ Conv A C := by
  induction h with
  | ax Γ => intro n he; cases he
  | var hA => intro n he; cases he; exact ⟨_, hA, Conv.refl _⟩
  | pi _ _ _ _ _ => intro n he; cases he
  | lam _ _ _ _ => intro n he; cases he
  | app _ _ _ _ => intro n he; cases he
  | conv _ _ hc ih _ =>
      intro n he
      obtain ⟨A, hA, hconv⟩ := ih he
      exact ⟨A, hA, hconv.trans hc⟩

theorem Typing.var_inv {Γ : Ctx} {n : ℕ} {C : Tm} (h : Typing Γ (Tm.var n) C) :
    ∃ A, Lookup Γ n A ∧ Conv A C :=
  h.var_inv' rfl

theorem Typing.pi_inv' {Γ : Ctx} {e C : Tm} (h : Typing Γ e C) :
    ∀ {A B : Tm}, e = Tm.pi A B →
      ∃ s t, Rule s t ∧ Typing Γ A (Tm.sort s) ∧ Typing (A :: Γ) B (Tm.sort t) ∧
        Conv (Tm.sort t) C := by
  induction h with
  | ax Γ => intro A B he; cases he
  | var _ => intro A B he; cases he
  | pi hr hA hB _ _ =>
      intro A B he
      cases he
      exact ⟨_, _, hr, hA, hB, Conv.refl _⟩
  | lam _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | conv _ _ hc ih _ =>
      intro A B he
      obtain ⟨s, t, hr, hA, hB, hconv⟩ := ih he
      exact ⟨s, t, hr, hA, hB, hconv.trans hc⟩

theorem Typing.pi_inv {Γ : Ctx} {A B C : Tm} (h : Typing Γ (Tm.pi A B) C) :
    ∃ s t, Rule s t ∧ Typing Γ A (Tm.sort s) ∧ Typing (A :: Γ) B (Tm.sort t) ∧
      Conv (Tm.sort t) C :=
  h.pi_inv' rfl

theorem Typing.lam_inv' {Γ : Ctx} {e C : Tm} (h : Typing Γ e C) :
    ∀ {A b : Tm}, e = Tm.lam A b →
      ∃ B s, Typing Γ (Tm.pi A B) (Tm.sort s) ∧ Typing (A :: Γ) b B ∧ Conv (Tm.pi A B) C := by
  induction h with
  | ax Γ => intro A b he; cases he
  | var _ => intro A b he; cases he
  | pi _ _ _ _ _ => intro A b he; cases he
  | lam hP hb _ _ =>
      intro A b he
      cases he
      exact ⟨_, _, hP, hb, Conv.refl _⟩
  | app _ _ _ _ => intro A b he; cases he
  | conv _ _ hc ih _ =>
      intro A b he
      obtain ⟨B, s, hP, hb, hconv⟩ := ih he
      exact ⟨B, s, hP, hb, hconv.trans hc⟩

theorem Typing.lam_inv {Γ : Ctx} {A b C : Tm} (h : Typing Γ (Tm.lam A b) C) :
    ∃ B s, Typing Γ (Tm.pi A B) (Tm.sort s) ∧ Typing (A :: Γ) b B ∧ Conv (Tm.pi A B) C :=
  h.lam_inv' rfl

theorem Typing.app_inv' {Γ : Ctx} {e C : Tm} (h : Typing Γ e C) :
    ∀ {f a : Tm}, e = Tm.app f a →
      ∃ A B, Typing Γ f (Tm.pi A B) ∧ Typing Γ a A ∧ Conv (B[a]) C := by
  induction h with
  | ax Γ => intro f a he; cases he
  | var _ => intro f a he; cases he
  | pi _ _ _ _ _ => intro f a he; cases he
  | lam _ _ _ _ => intro f a he; cases he
  | app hf ha _ _ =>
      intro f a he
      cases he
      exact ⟨_, _, hf, ha, Conv.refl _⟩
  | conv _ _ hc ih _ =>
      intro f a he
      obtain ⟨A, B, hf, ha, hconv⟩ := ih he
      exact ⟨A, B, hf, ha, hconv.trans hc⟩

theorem Typing.app_inv {Γ : Ctx} {f a C : Tm} (h : Typing Γ (Tm.app f a) C) :
    ∃ A B, Typing Γ f (Tm.pi A B) ∧ Typing Γ a A ∧ Conv (B[a]) C :=
  h.app_inv' rfl

/-! ### Type correctness -/

/-- **Validity**: the type of a typable term is either the top sort `□` or itself typable. -/
theorem Typing.validity {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) :
    Wf Γ → A = Tm.sort Srt.box ∨ ∃ s : Srt, Typing Γ A (Tm.sort s) := by
  induction h with
  | ax Γ => intro _; exact Or.inl rfl
  | var hA => intro hΓ; exact Or.inr (hΓ.lookup_typed hA)
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro _
      cases t with
      | star => exact Or.inr ⟨Srt.box, Typing.ax _⟩
      | box => exact Or.inl rfl
  | @lam Γ A B b s hP hb ihP ihb => intro _; exact Or.inr ⟨s, hP⟩
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ
      rcases ihf hΓ with h₁ | ⟨s, hs⟩
      · exact absurd h₁ (by simp)
      · obtain ⟨s', t', hr, hA, hB, hconv⟩ := hs.pi_inv
        exact Or.inr ⟨t', hB.inst ha⟩
  | conv _ hB _ _ _ => intro _; exact Or.inr ⟨_, hB⟩

/-- The type of a term whose type is not the top sort is typable by a sort. -/
theorem Typing.typeTypable {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ)
    (hA : A ≠ Tm.sort Srt.box) : ∃ s : Srt, Typing Γ A (Tm.sort s) := by
  rcases h.validity hΓ with h₁ | h₂
  · exact absurd h₁ hA
  · exact h₂

/-! ### Context conversion -/

/-- `Δ` is a well-typed conversion of the context `Γ`: the entries are convertible, and the
entries of `Γ` remain typable over `Δ`. -/
def CtxConvOk (Γ Δ : Ctx) : Prop :=
  ∀ n A, Lookup Γ n A → ∃ A' s, Lookup Δ n A' ∧ Conv A A' ∧ Typing Δ A (Tm.sort s)

theorem CtxConvOk.refl {Γ : Ctx} (hΓ : Wf Γ) : CtxConvOk Γ Γ := by
  intro n A hA
  obtain ⟨s, hs⟩ := hΓ.lookup_typed hA
  exact ⟨A, s, hA, Conv.refl _, hs⟩

theorem CtxConvOk.cons {Γ Δ : Ctx} (h : CtxConvOk Γ Δ) {A : Tm} {s : Srt}
    (hA : Typing Δ A (Tm.sort s)) : CtxConvOk (A :: Γ) (A :: Δ) := by
  intro n B hB
  cases hB with
  | zero => exact ⟨shift A, s, Lookup.zero _ _, Conv.refl _, hA.weaken A⟩
  | @succ Γ' n' A' B' hB' =>
      obtain ⟨B'', s'', hB'', hconv, hty⟩ := h _ _ hB'
      exact ⟨shift B'', s'', Lookup.succ _ hB'', hconv.rename Nat.succ, hty.weaken A⟩

/-- Converting the first entry of a context, given that the new entry is typable. -/
theorem CtxConvOk.consConv {Γ : Ctx} (hΓ : Wf Γ) {A A' : Tm} {s : Srt} (hA : Typing Γ A (Tm.sort s))
    (hconv : Conv A A') : CtxConvOk (A :: Γ) (A' :: Γ) := by
  intro n B hB
  cases hB with
  | zero =>
      exact ⟨shift A', s, Lookup.zero _ _, hconv.rename Nat.succ, hA.weaken A'⟩
  | @succ Γ' n' A'' B' hB' =>
      obtain ⟨s', hs'⟩ := hΓ.lookup_typed hB'
      exact ⟨shift A'', s', Lookup.succ _ hB', Conv.refl _, hs'.weaken A'⟩

/-- Typing is stable under conversion of the context. -/
theorem Typing.ctxConv {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) {Δ : Ctx} (hΔ : CtxConvOk Γ Δ) :
    Typing Δ t A := by
  induction h generalizing Δ with
  | ax Γ => exact Typing.ax _
  | var hA =>
      obtain ⟨A', s, hA', hconv, hty⟩ := hΔ _ _ hA
      exact (Typing.var hA').conv hty hconv.symm
  | @pi Γ A B s t hr hA hB ihA ihB =>
      have hA' := ihA hΔ
      exact Typing.pi hr hA' (ihB (hΔ.cons hA'))
  | @lam Γ A B b s hP hb ihP ihb =>
      have hP' := ihP hΔ
      obtain ⟨s', t', hr, hA', hB', hconv⟩ := hP'.pi_inv
      exact Typing.lam hP' (ihb (hΔ.cons hA'))
  | app _ _ ihf iha => exact Typing.app (ihf hΔ) (iha hΔ)
  | conv _ _ hc iht ihB => exact (iht hΔ).conv (ihB hΔ) hc

/-! ### Subject reduction -/

/-- **Subject reduction**: β-reduction preserves typing. -/
theorem Typing.step {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) :
    Wf Γ → ∀ {t' : Tm}, Step t t' → Typing Γ t' A := by
  induction h with
  | ax Γ => intro _ t' hst; cases hst
  | var _ => intro _ t' hst; cases hst
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro hΓ t' hst
      cases hst with
      | piL _ hA' =>
          have hA₂ := ihA hΓ hA'
          exact Typing.pi hr hA₂ (hB.ctxConv (CtxConvOk.consConv hΓ hA (Conv.single hA')))
      | piR _ hB' => exact Typing.pi hr hA (ihB (Wf.cons hΓ hA) hB')
  | @lam Γ A B b s hP hb ihP ihb =>
      intro hΓ t' hst
      obtain ⟨s₁, t₁, hr, hA, hB, hconv⟩ := hP.pi_inv
      cases hst with
      | lamL _ hA' =>
          have hP₂ := ihP hΓ (Step.piL B hA')
          have hbody := hb.ctxConv (CtxConvOk.consConv hΓ hA (Conv.single hA'))
          exact (Typing.lam hP₂ hbody).conv hP (Conv.piL B (Conv.single hA')).symm
      | lamR _ hb' => exact Typing.lam hP (ihb (Wf.cons hΓ hA) hb')
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ t' hst
      have hBa : ∃ s : Srt, Typing Γ (B[a]) (Tm.sort s) := by
        rcases hf.validity hΓ with h₁ | ⟨s, hs⟩
        · exact absurd h₁ (by simp)
        · obtain ⟨s', t', hr, hA, hB, hconv⟩ := hs.pi_inv
          exact ⟨t', hB.inst ha⟩
      cases hst with
      | beta A₀ b a =>
          obtain ⟨B₀, s₀, hP₀, hb₀, hconv₀⟩ := hf.lam_inv
          obtain ⟨s₁, t₁, hr₁, hA₀, hB₀, _⟩ := hP₀.pi_inv
          have hAA : Conv A₀ A := pi_inj_left hconv₀
          have hBB : Conv B₀ B := pi_inj_right hconv₀
          have ha₀ : Typing Γ a A₀ := ha.conv hA₀ hAA.symm
          have hsub : Typing Γ (b[a]) (B₀[a]) := hb₀.inst ha₀
          obtain ⟨s₂, hs₂⟩ := hBa
          exact hsub.conv hs₂ (hBB.subst (scons a ids))
      | appL _ hf' => exact Typing.app (ihf hΓ hf') ha
      | appR _ ha' =>
          obtain ⟨s₂, hs₂⟩ := hBa
          exact (Typing.app hf (iha hΓ ha')).conv hs₂ (Conv.instArg B (Conv.single ha')).symm
  | @conv Γ t A B s ht hB hc iht ihB =>
      intro hΓ t' hst
      exact (iht hΓ hst).conv hB hc

/-- Subject reduction for many-step reduction. -/
theorem Typing.red {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) {t' : Tm}
    (hred : Red t t') : Typing Γ t' A := by
  induction hred with
  | refl => exact h
  | tail _ hs ih => exact ih.step hΓ hs

end LambdaPi
