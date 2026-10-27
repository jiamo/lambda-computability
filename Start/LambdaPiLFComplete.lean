/-
**Completeness of the type-directed algorithm for the corrected declarative equality of `λΠ`**
— task `M23-LF-EQUIV-COMPLETE`.

`TEq` (`Start/LambdaPiLFEquiv.lean`) cannot be the judgement of the completeness theorem:
its β-rule accepts a kind as the domain of the abstraction, and completeness fails for it
(`teq_not_complete`, `Start/LambdaPiLFTEqIncomplete.lean`); its premises use the β-typing, which
the η-rule leaves (`teq_typeLevel_counterexample`).  This module defines the corrected judgement,
over the βη-typing `TypingE` of `Start/LambdaPiTypingE.lean`, and proves the completeness of the
algorithm `EqvE` of `Start/LambdaPiLFAlgE.lean` for it.

* `LambdaPi.TEqE` — the declarative typed equality `Γ ⊢ M ≡ N : A`: `TEq` with `TypingE`
  premises, βη-conversion of the type, and a typable abstraction (`Γ ⊢ Πx:A. B : s`) in the β-rule
  and the congruence for abstractions;
* `TEqE.betaEtaConv` — declaratively equal terms are βη-convertible;
* **`TEqE.validity`** — both sides of an equation are typable at its type (the lemma that is
  false for `TEq`);
* `TEqE.er_eq` — equal types (or kinds) have the same erasure;
* `LambdaPi.RelSubE` — related substitutions, and the **fundamental lemmas**
  `TypingE.fundamental` and `TEqE.fundamental` of the Kripke logical relation `LRE`;
* **`TEqE.complete`** — completeness: `Γ ⊢ M ≡ N : A` gives `erCtx Γ ⊢ M ⇔ N : er A`;
  `TypingE.algEq_refl` — the algorithm is reflexive on typable terms.
-/

import Start.LambdaPiLFAlgE

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### The corrected declarative equality -/

/-- **Declarative typed equality** `Γ ⊢ M ≡ N : A` of `λΠ`, over the βη-typing. -/
inductive TEqE : Ctx → Tm → Tm → Tm → Prop
  | refl {Γ : Ctx} {M A : Tm} : TypingE Γ M A → TEqE Γ M M A
  | symm {Γ : Ctx} {M N A : Tm} : TEqE Γ M N A → TEqE Γ N M A
  | trans {Γ : Ctx} {M N P A : Tm} : TEqE Γ M N A → TEqE Γ N P A → TEqE Γ M P A
  | beta {Γ : Ctx} {A b a B : Tm} {s : Srt} : TypingE Γ (pi A B) (sort s) →
      TypingE (A :: Γ) b B → TypingE Γ a A → TEqE Γ (app (lam A b) a) (b[a]) (B[a])
  | eta {Γ : Ctx} {f A B : Tm} : TypingE Γ f (pi A B) →
      TEqE Γ (lam A (app (shift f) (var 0))) f (pi A B)
  | app {Γ : Ctx} {f f' a a' A B : Tm} : TEqE Γ f f' (pi A B) → TEqE Γ a a' A →
      TEqE Γ (app f a) (app f' a') (B[a])
  | lam {Γ : Ctx} {A A' b b' B : Tm} {s : Srt} : TypingE Γ (pi A B) (sort s) →
      TEqE Γ A A' (sort Srt.star) → TEqE (A :: Γ) b b' B → TEqE Γ (lam A b) (lam A' b') (pi A B)
  | pi {Γ : Ctx} {A A' B B' : Tm} {s t : Srt} : Rule s t → TEqE Γ A A' (sort s) →
      TEqE (A :: Γ) B B' (sort t) → TEqE Γ (pi A B) (pi A' B') (sort t)
  | conv {Γ : Ctx} {M N A B : Tm} {s : Srt} : TEqE Γ M N A → TypingE Γ B (sort s) →
      BetaEtaConv A B → TEqE Γ M N B

/-- Declaratively equal terms are βη-convertible. -/
theorem TEqE.betaEtaConv {Γ : Ctx} {M N A : Tm} (h : TEqE Γ M N A) : BetaEtaConv M N := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta => exact (BetaEtaConv.refl _).step (Or.inl (Step.beta _ _ _))
  | eta => exact betaEtaConv_eta _ _
  | app _ _ ihf iha => exact BetaEtaConv.appC ihf iha
  | lam _ _ _ _ ihb => exact BetaEtaConv.lamC ihb
  | pi _ _ _ ihA ihB => exact BetaEtaConv.piC ihA ihB
  | conv _ _ _ ih => exact ih

/-- The η-expansion of a typable function is typable at the same product. -/
theorem TypingE.etaExpand {Γ : Ctx} {f A B : Tm} (hf : TypingE Γ f (Tm.pi A B)) (hΓ : WfE Γ) :
    TypingE Γ (Tm.lam A (Tm.app (shift f) (Tm.var 0))) (Tm.pi A B) := by
  rcases hf.validity hΓ with h₁ | ⟨s, hP⟩
  · exact absurd h₁ (by simp)
  · have hf' : TypingE (A :: Γ) (shift f) (Tm.pi (shift A) (LambdaPi.rename (upr Nat.succ) B)) := by
      have := hf.weaken A
      simpa [shift] using this
    have hbody := TypingE.app hf' (TypingE.var (Lookup.zero Γ A))
    rw [inst_zero_rename_upr_succ] at hbody
    exact TypingE.lam hP hbody

/-- **Validity**: both sides of an equation are typable at its type. -/
theorem TEqE.validity {Γ : Ctx} {M N A : Tm} (h : TEqE Γ M N A) :
    WfE Γ → TypingE Γ M A ∧ TypingE Γ N A := by
  induction h with
  | refl h => intro _; exact ⟨h, h⟩
  | symm _ ih => intro hΓ; exact (ih hΓ).symm
  | trans _ _ ih₁ ih₂ => intro hΓ; exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | beta hP hb ha => intro _; exact ⟨TypingE.app (TypingE.lam hP hb) ha, hb.inst ha⟩
  | eta hf => intro hΓ; exact ⟨hf.etaExpand hΓ, hf⟩
  | @app Γ f f' a a' A B _ hea ihf iha =>
      intro hΓ
      obtain ⟨hf, hf'⟩ := ihf hΓ
      obtain ⟨ha, ha'⟩ := iha hΓ
      obtain ⟨s, t, _, _, hB⟩ := hf.pi_cod hΓ
      refine ⟨TypingE.app hf ha, ?_⟩
      exact (TypingE.app hf' ha').conv (hB.inst ha) (BetaEtaConv.instArg B hea.betaEtaConv.symm)
  | @lam Γ A A' b b' B s hP heA _ ihA ihb =>
      intro hΓ
      obtain ⟨s₁, t₁, hr, hA, hB, _⟩ := hP.pi_inv
      cases hr
      have hΓA : WfE (A :: Γ) := WfE.cons hΓ hA
      obtain ⟨-, hA'⟩ := ihA hΓ
      obtain ⟨hb, hb'⟩ := ihb hΓA
      have hc : BetaEtaConv A A' := heA.betaEtaConv
      have hP' : TypingE Γ (Tm.pi A' B) (sort t₁) := TypingE.pi rfl hA' (hB.ctxConv₁ hΓ hA hc)
      refine ⟨TypingE.lam hP hb, ?_⟩
      exact (TypingE.lam hP' (hb'.ctxConv₁ hΓ hA hc)).conv hP (BetaEtaConv.piL B hc.symm)
  | @pi Γ A A' B B' s t hr heA _ ihA ihB =>
      intro hΓ
      obtain ⟨hA, hA'⟩ := ihA hΓ
      obtain ⟨hB, hB'⟩ := ihB (WfE.cons hΓ hA)
      exact ⟨TypingE.pi hr hA hB,
        TypingE.pi hr hA' (hB'.ctxConv₁ hΓ hA heA.betaEtaConv)⟩
  | conv _ hB hc ih =>
      intro hΓ
      obtain ⟨h₁, h₂⟩ := ih hΓ
      exact ⟨h₁.conv hB hc, h₂.conv hB hc⟩

/-- The type of a typable term is the top sort or has the erasure of every βη-convertible typable
type. -/
theorem TypingE.er_conv_type {Γ : Ctx} {t A B : Tm} {s : Srt} (ht : TypingE Γ t A)
    (hB : TypingE Γ B (sort s)) (hc : BetaEtaConv A B) (hΓ : WfE Γ) : er A = er B := by
  rcases ht.validity hΓ with rfl | ⟨s', hA⟩
  · obtain ⟨k, hl, -⟩ := hB.lvl' hΓ
    exact (hl.not_conv_box hc).elim
  · exact (hA.er_conv hB hc hΓ).1

/-- **Equal types (or kinds) have the same erasure.** -/
theorem TEqE.er_eq {Γ : Ctx} {A A' : Tm} {s : Srt} (h : TEqE Γ A A' (sort s)) (hΓ : WfE Γ) :
    er A = er A' := by
  obtain ⟨hA, hA'⟩ := h.validity hΓ
  exact (hA.er_conv hA' h.betaEtaConv hΓ).1

/-! ### Substitution lemmas -/

theorem subst_up_inst (σ : ℕ → Tm) (a b : Tm) : (subst (up σ) b)[a] = subst (scons a σ) b := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ b
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [subst_rename]

theorem subst_inst_scons (τ : ℕ → Tm) (a b : Tm) :
    subst τ (b[a]) = subst (scons (subst τ a) τ) b := by
  simp only [inst, subst_subst]
  refine subst_congr ?_ b
  intro n
  cases n <;> rfl

theorem rename_subst_up_inst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (a b : Tm) :
    (rename (upr ρ) (subst (up σ) b))[a] = subst (scons a (fun n => rename ρ (σ n))) b := by
  have h1 : rename (upr ρ) (subst (up σ) b) = subst (up (fun k => rename ρ (σ k))) b := by
    rw [rename_subst]
    exact subst_congr (rename_up_subst ρ σ) b
  rw [h1, subst_up_inst]

theorem rename_eta_inst (ρ : ℕ → ℕ) (X a : Tm) :
    (rename (upr ρ) (app (shift X) (var 0)))[a] = app (rename ρ X) a := by
  rw [rename_app, rename_upr_shift]
  show subst (scons a ids) (app (shift (rename ρ X)) (rename (upr ρ) (var 0))) = _
  rw [subst_app]
  have h := inst_shift a (rename ρ X)
  simp only [inst] at h
  rw [h]
  rfl

theorem subst_eta (σ : ℕ → Tm) (A f : Tm) :
    subst σ (lam A (app (shift f) (var 0))) = lam (subst σ A) (app (shift (subst σ f)) (var 0)) := by
  simp [subst_up_shift]

/-! ### Related substitutions -/

/-- The erasure of a context. -/
def erCtx (Γ : Ctx) : List STy := Γ.map er

@[simp] theorem erCtx_cons (A : Tm) (Γ : Ctx) : erCtx (A :: Γ) = er A :: erCtx Γ := rfl

theorem Lookup.er_eq {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    (erCtx Γ).getD n STy.base = er A := by
  induction h with
  | zero Γ A => simp
  | @succ Γ n A B _ ih => simpa using ih

/-- **Related substitutions**: related at the erasure of every declaration, and of erasure
`base` (objects or variables). -/
def RelSubE (Γ : Ctx) (Δ : List STy) (σ τ : ℕ → Tm) : Prop :=
  (∀ n A, Lookup Γ n A → LRE (er A) Δ (σ n) (τ n)) ∧ (∀ n, er (σ n) = STy.base) ∧
    (∀ n, er (τ n) = STy.base)

theorem RelSubE.symm {Γ : Ctx} {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSubE Γ Δ σ τ) :
    RelSubE Γ Δ τ σ :=
  ⟨fun n A hA => LRE.symm (h.1 n A hA), h.2.2, h.2.1⟩

theorem RelSubE.right {Γ : Ctx} {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSubE Γ Δ σ τ) :
    RelSubE Γ Δ τ τ :=
  ⟨fun n A hA => LRE.right (h.1 n A hA), h.2.2, h.2.2⟩

theorem RelSubE.rename {Γ : Ctx} {Δ Δ' : List STy} {σ τ : ℕ → Tm} {ρ : ℕ → ℕ}
    (h : RelSubE Γ Δ σ τ) (hρ : RenS ρ Δ Δ') :
    RelSubE Γ Δ' (fun n => LambdaPi.rename ρ (σ n)) (fun n => LambdaPi.rename ρ (τ n)) :=
  ⟨fun n A hA => LRE.rename hρ (h.1 n A hA), fun n => by simp [h.2.1 n],
    fun n => by simp [h.2.2 n]⟩

theorem RelSubE.up {Γ : Ctx} {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSubE Γ Δ σ τ) (A : Tm) :
    RelSubE (A :: Γ) (er A :: Δ) (LambdaPi.up σ) (LambdaPi.up τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n B hB
    cases hB with
    | zero =>
        rw [er_shift]
        exact LRE.var (er A :: Δ) 0
    | @succ Γ' n' A' B' hB' =>
        rw [er_shift]
        exact LRE.rename (RenS.succ Δ (er A)) (h.1 _ _ hB')
  · intro n; cases n with
    | zero => rfl
    | succ n => simpa using h.2.1 n
  · intro n; cases n with
    | zero => rfl
    | succ n => simpa using h.2.2 n

theorem RelSubE.cons {Γ : Ctx} {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSubE Γ Δ σ τ) {A a b : Tm}
    (hab : LRE (er A) Δ a b) (ha : er a = STy.base) (hb : er b = STy.base) :
    RelSubE (A :: Γ) Δ (scons a σ) (scons b τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n B hB
    cases hB with
    | zero => rw [er_shift]; exact hab
    | @succ Γ' n' A' B' hB' => rw [er_shift]; exact h.1 _ _ hB'
  · intro n; cases n with
    | zero => exact ha
    | succ n => exact h.2.1 n
  · intro n; cases n with
    | zero => exact hb
    | succ n => exact h.2.2 n

/-- The identity substitutions are related. -/
theorem RelSubE.ids (Γ : Ctx) : RelSubE Γ (erCtx Γ) LambdaPi.ids LambdaPi.ids := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl⟩
  intro n A hA
  rw [← hA.er_eq]
  exact LRE.var (erCtx Γ) n

theorem RenS.refl (Δ : List STy) : RenS id Δ Δ := fun _ => rfl

/-! ### The fundamental lemmas -/

/-- An object stays of erasure `base` under a related substitution. -/
theorem er_subst_object {Γ : Ctx} {a A : Tm} (ha : TypingE Γ a A) (hA : TypingE Γ A (sort Srt.star))
    (hΓ : WfE Γ) {σ : ℕ → Tm} (hσ : ∀ n, er (σ n) = STy.base) : er (subst σ a) = STy.base := by
  rw [er_subst hσ]
  exact ha.er_object hA hΓ

/-- **The fundamental lemma for typing**: a typable term is related to itself under related
substitutions, at the erasure of its type. -/
theorem TypingE.fundamental {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) :
    WfE Γ → ∀ {Δ : List STy} {σ τ : ℕ → Tm}, RelSubE Γ Δ σ τ →
      LRE (er A) Δ (subst σ t) (subst τ t) := by
  induction h with
  | ax Γ => intro _ Δ σ τ _; exact EqvE.baseSort .refl .refl
  | var hA => intro _ Δ σ τ hs; exact hs.1 _ _ hA
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro hΓ Δ σ τ hs
      have hA' := LRE.escape (ihA hΓ hs)
      have hB' := LRE.escape (ihB (WfE.cons hΓ hA) (hs.up A))
      have heσ : er (subst σ A) = er A := er_subst hs.2.1 A
      have heτ : er (subst τ A) = er A := er_subst hs.2.2 A
      refine EqvE.basePi .refl .refl hA' (heσ.trans heτ.symm) ?_
      rw [heσ]
      exact hB'
  | @lam Γ A B b s hP hb ihP ihb =>
      intro hΓ Δ σ τ hs
      obtain ⟨s₁, t₁, hr, hA, _, _⟩ := hP.pi_inv
      have hΓA : WfE (A :: Γ) := WfE.cons hΓ hA
      intro Δ' ρ hρ a a' ha ha' haa
      have hs' := (hs.rename hρ).cons haa ha ha'
      have hrel := ihb hΓA hs'
      refine LRE.whExpand_left (WhStep.beta _ _ _) (LRE.whExpand_right (WhStep.beta _ _ _) ?_)
      rw [rename_subst_up_inst, rename_subst_up_inst]
      exact hrel
  | @app Γ f a A B hf ha ihf iha =>
      intro hΓ Δ σ τ hs
      obtain ⟨s₁, t₁, hr, hA, _⟩ := hf.pi_cod hΓ
      cases hr
      have haσ := er_subst_object ha hA hΓ hs.2.1
      have haτ := er_subst_object ha hA hΓ hs.2.2
      have hrel := ihf hΓ hs Δ id (RenS.refl Δ) _ _ haσ haτ (iha hΓ hs)
      rw [er_inst (ha.er_object hA hΓ)]
      simpa using hrel
  | @conv Γ t A B s ht hB hc iht _ =>
      intro hΓ Δ σ τ hs
      rw [← ht.er_conv_type hB hc hΓ]
      exact iht hΓ hs

/-- **The fundamental lemma for the declarative equality.** -/
theorem TEqE.fundamental {Γ : Ctx} {M N A : Tm} (h : TEqE Γ M N A) :
    WfE Γ → ∀ {Δ : List STy} {σ τ : ℕ → Tm}, RelSubE Γ Δ σ τ →
      LRE (er A) Δ (subst σ M) (subst τ N) := by
  induction h with
  | refl ht => intro hΓ Δ σ τ hs; exact ht.fundamental hΓ hs
  | symm _ ih => intro hΓ Δ σ τ hs; exact LRE.symm (ih hΓ hs.symm)
  | trans _ _ ih₁ ih₂ => intro hΓ Δ σ τ hs; exact LRE.trans (ih₁ hΓ hs) (ih₂ hΓ hs.right)
  | @beta Γ A b a B s hP hb ha =>
      intro hΓ Δ σ τ hs
      obtain ⟨s₁, t₁, hr, hA, _, _⟩ := hP.pi_inv
      cases hr
      have hΓA : WfE (A :: Γ) := WfE.cons hΓ hA
      have haσ := er_subst_object ha hA hΓ hs.2.1
      have haτ := er_subst_object ha hA hΓ hs.2.2
      have hs' := hs.cons (ha.fundamental hΓ hs) haσ haτ
      have hrel := hb.fundamental hΓA hs'
      rw [er_inst (ha.er_object hA hΓ)]
      refine LRE.whExpand_left (WhStep.beta _ _ _) ?_
      rw [subst_up_inst, subst_inst_scons]
      exact hrel
  | @eta Γ f A B hf =>
      intro hΓ Δ σ τ hs
      have hrel := hf.fundamental hΓ hs
      rw [subst_eta]
      intro Δ' ρ hρ a a' ha ha' haa
      refine LRE.whExpand_left (WhStep.beta _ _ _) ?_
      rw [rename_eta_inst]
      exact hrel Δ' ρ hρ a a' ha ha' haa
  | @app Γ f f' a a' A B hef hea ihf iha =>
      intro hΓ Δ σ τ hs
      obtain ⟨hf, -⟩ := hef.validity hΓ
      obtain ⟨ha, ha'⟩ := hea.validity hΓ
      obtain ⟨s₁, t₁, hr, hA, _⟩ := hf.pi_cod hΓ
      cases hr
      have haσ := er_subst_object ha hA hΓ hs.2.1
      have haτ := er_subst_object ha' hA hΓ hs.2.2
      have hrel := ihf hΓ hs Δ id (RenS.refl Δ) _ _ haσ haτ (iha hΓ hs)
      rw [er_inst (ha.er_object hA hΓ)]
      simpa using hrel
  | @lam Γ A A' b b' B s hP _ _ _ ihb =>
      intro hΓ Δ σ τ hs
      obtain ⟨s₁, t₁, hr, hA, _, _⟩ := hP.pi_inv
      have hΓA : WfE (A :: Γ) := WfE.cons hΓ hA
      intro Δ' ρ hρ a a' ha ha' haa
      have hs' := (hs.rename hρ).cons haa ha ha'
      have hrel := ihb hΓA hs'
      refine LRE.whExpand_left (WhStep.beta _ _ _) (LRE.whExpand_right (WhStep.beta _ _ _) ?_)
      rw [rename_subst_up_inst, rename_subst_up_inst]
      exact hrel
  | @pi Γ A A' B B' s t hr heA _ ihA ihB =>
      intro hΓ Δ σ τ hs
      obtain ⟨hA, _⟩ := heA.validity hΓ
      have hA' := LRE.escape (ihA hΓ hs)
      have hB' := LRE.escape (ihB (WfE.cons hΓ hA) (hs.up A))
      have heσ : er (subst σ A) = er A := er_subst hs.2.1 A
      have heτ : er (subst τ A') = er A' := er_subst hs.2.2 A'
      have he : er A = er A' := heA.er_eq hΓ
      refine EqvE.basePi .refl .refl hA' (heσ.trans (he.trans heτ.symm)) ?_
      rw [heσ]
      exact hB'
  | @conv Γ M N A B s heq hB hc ih =>
      intro hΓ Δ σ τ hs
      obtain ⟨hM, -⟩ := heq.validity hΓ
      rw [← hM.er_conv_type hB hc hΓ]
      exact ih hΓ hs

/-- **Completeness of the algorithm**: declaratively equal terms are algorithmically equivalent at
the erasure of their type. -/
theorem TEqE.complete {Γ : Ctx} {M N A : Tm} (h : TEqE Γ M N A) (hΓ : WfE Γ) :
    AlgEqE (erCtx Γ) M N (er A) := by
  have := LRE.escape (h.fundamental hΓ (RelSubE.ids Γ))
  simpa using this

/-- The algorithm is reflexive on typable terms. -/
theorem TypingE.algEq_refl {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) (hΓ : WfE Γ) :
    AlgEqE (erCtx Γ) t t (er A) :=
  (TEqE.refl h).complete hΓ

end LambdaPi
