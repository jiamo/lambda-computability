/-
**The fundamental lemma of the LF logical relation for well-typed terms** — task
`M23-LF-EQUIV-COMPLETE` (round 9, part C), continuing `Start/LambdaPiLFEquivPER.lean`.

* `LambdaPi.skel_subst_typeLevel` — **the skeleton of a substituted type-level term**: if the
  substitution gives every *kind* position of `Γ` a term of the right skeleton, the skeleton of
  `A[σ]` is that of `A` (object positions are irrelevant, `skel_irrel`);
* `LambdaPi.RelSub Γ Δ σ τ` — **related substitutions**: at every declaration `n : A` of `Γ`,
  `σ n` and `τ n` are related by the logical relation at the skeleton of `A`, and at the kind
  positions both have the declared skeleton;
* `LambdaPi.LR.fundamental` — **the fundamental lemma for the typing judgement**: a well-typed
  `Γ ⊢ t : A` in a well-formed context sends related substitutions to related terms,
  `LR (skel A) Δ t[σ] t[τ]`;
* `LambdaPi.AlgEq.refl_of_typing` — the algorithm is reflexive on well-typed terms (the identity
  substitution).

Open: the fundamental lemma for the declarative equality `TEq`; see
`docs/goal/evidence/M23-LF-EQUIV.md`, round 9.
-/

import Start.LambdaPiLFEquivPER

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### The skeleton of a substituted type-level term -/

/-- **The skeleton of a substituted type-level term**: only the kind positions matter. -/
theorem skel_subst_typeLevel {A : Tm} : ∀ {Γ : Ctx} {Γs Δ : List STy} {σ : ℕ → Tm}, Wf Γ →
    (∀ n, KindPos Γ n → skel Δ (σ n) = Γs.getD n STy.base) → TypeLevel Γ A →
    skel Δ (subst σ A) = skel Γs A := by
  induction A with
  | sort s => intro _ _ _ _ _ _ _; rfl
  | var n =>
      intro Γ Γs Δ σ hΓ hσ hB
      obtain ⟨T, hT⟩ := hB.typing
      obtain ⟨A, hl, _⟩ := hT.var_inv
      have hkind : IsKind Γ A := hB.var_isKind hΓ hl
      have : KindPos Γ n := hl.isKindSyn_iff.mp (isKindSyn_of_isKind hΓ hkind)
      simpa using hσ n this
  | app f a ihf _ =>
      intro Γ Γs Δ σ hΓ hσ hB
      simpa using ihf hΓ hσ (hB.app_fun hΓ)
  | lam A b ihA ihb =>
      intro Γ Γs Δ σ hΓ hσ hB
      have hA : Typing Γ A (Tm.sort Srt.star) := hB.lam_dom
      have hAeq := ihA hΓ hσ (typeLevel_of_typing_sort hA)
      have hσ' : ∀ n, KindPos (A :: Γ) n →
          skel (skel Δ (subst σ A) :: Δ) (up σ n) = (skel Γs A :: Γs).getD n STy.base := by
        intro n hn
        cases n with
        | zero => exact absurd hn (fun hk => not_isKindSyn_of_typing_star hΓ hk hA)
        | succ n => rw [up_succ, skel_rename_succ]; simpa using hσ n hn
      have hb := ihb (Wf.cons hΓ hA) hσ' (hB.lam_body hΓ)
      simp only [subst_lam, skel_lam]
      rw [hAeq] at hb ⊢
      exact hb
  | pi A B ihA ihB =>
      intro Γ Γs Δ σ hΓ hσ hB
      have hA : Typing Γ A (Tm.sort Srt.star) := hB.pi_dom
      have hAeq := ihA hΓ hσ (typeLevel_of_typing_sort hA)
      have hσ' : ∀ n, KindPos (A :: Γ) n →
          skel (skel Δ (subst σ A) :: Δ) (up σ n) = (skel Γs A :: Γs).getD n STy.base := by
        intro n hn
        cases n with
        | zero => exact absurd hn (fun hk => not_isKindSyn_of_typing_star hΓ hk hA)
        | succ n => rw [up_succ, skel_rename_succ]; simpa using hσ n hn
      have hb := ihB (Wf.cons hΓ hA) hσ' hB.pi_cod
      simp only [subst_pi, skel_pi]
      rw [hAeq] at hb ⊢
      rw [hb]

/-! ### Related substitutions -/

/-- **Related substitutions** from `Γ` into the skeleton context `Δ`. -/
def RelSub (Γ : Ctx) (Δ : List STy) (σ τ : ℕ → Tm) : Prop :=
  (∀ n A, Lookup Γ n A → LR (skel (skelCtx Γ) A) Δ (σ n) (τ n)) ∧
    (∀ n, KindPos Γ n → skel Δ (σ n) = (skelCtx Γ).getD n STy.base ∧
      skel Δ (τ n) = (skelCtx Γ).getD n STy.base)

theorem RenS.id' (Δ : List STy) : RenS id Δ Δ := fun _ => rfl

/-- Related substitutions are stable under renamings respecting the skeletons. -/
theorem RelSub.rename {Γ : Ctx} {Δ Δ' : List STy} {σ τ : ℕ → Tm} (h : RelSub Γ Δ σ τ)
    {ρ : ℕ → ℕ} (hρ : RenS ρ Δ Δ') :
    RelSub Γ Δ' (fun n => LambdaPi.rename ρ (σ n)) (fun n => LambdaPi.rename ρ (τ n)) := by
  refine ⟨fun n A hl => LR.rename hρ (h.1 n A hl), fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 n hn
  exact ⟨(skel_rename hρ _).trans h1, (skel_rename hρ _).trans h2⟩

/-- Extending related substitutions by related terms at an object position. -/
theorem RelSub.cons {Γ : Ctx} (hΓ : Wf Γ) {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSub Γ Δ σ τ)
    {A : Tm} (hA : Typing Γ A (Tm.sort Srt.star)) {a c : Tm}
    (hac : LR (skel (skelCtx Γ) A) Δ a c) :
    RelSub (A :: Γ) Δ (scons a σ) (scons c τ) := by
  refine ⟨fun n B hl => ?_, fun n hn => ?_⟩
  · cases hl with
    | zero => rw [skelCtx_cons, skel_shift]; exact hac
    | succ _ hl => rw [skelCtx_cons, skel_shift]; exact h.1 _ _ hl
  · cases n with
    | zero => exact absurd hn (fun hk => not_isKindSyn_of_typing_star hΓ hk hA)
    | succ n => simpa using h.2 n hn

/-- Lifting related substitutions under a binder of an object type. -/
theorem RelSub.up {Γ : Ctx} (hΓ : Wf Γ) {Δ : List STy} {σ τ : ℕ → Tm} (h : RelSub Γ Δ σ τ)
    {A : Tm} (hA : Typing Γ A (Tm.sort Srt.star)) :
    RelSub (A :: Γ) (skel (skelCtx Γ) A :: Δ) (up σ) (up τ) := by
  have h' := h.rename (RenS.succ Δ (skel (skelCtx Γ) A))
  have h0 : LR (skel (skelCtx Γ) A) (skel (skelCtx Γ) A :: Δ) (var 0) (var 0) :=
    LR.var (skel (skelCtx Γ) A :: Δ) 0
  have := RelSub.cons hΓ h' hA h0
  refine ⟨fun n B hl => ?_, fun n hn => ?_⟩
  · have e1 : ∀ n, LambdaPi.up σ n = scons (var 0) (fun n => LambdaPi.rename Nat.succ (σ n)) n := by
      intro n; cases n <;> rfl
    have e2 : ∀ n, LambdaPi.up τ n = scons (var 0) (fun n => LambdaPi.rename Nat.succ (τ n)) n := by
      intro n; cases n <;> rfl
    rw [e1, e2]; exact this.1 n B hl
  · cases n with
    | zero => exact absurd hn (fun hk => not_isKindSyn_of_typing_star hΓ hk hA)
    | succ n =>
        obtain ⟨h1, h2⟩ := h.2 n hn
        simp only [up_succ, skel_rename_succ, skelCtx_cons, List.getD_cons_succ]
        exact ⟨h1, h2⟩

/-- The substitution identity used at the β-redex of the abstraction case. -/
theorem lam_body_inst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (a b : Tm) :
    (LambdaPi.rename (upr ρ) (subst (up σ) b))[a] =
      subst (scons a (fun n => LambdaPi.rename ρ (σ n))) b := by
  rw [rename_subst, inst, subst_subst]
  refine subst_congr (fun n => ?_) b
  cases n with
  | zero => rfl
  | succ n =>
      simp only [up_succ, rename_rename, subst_rename, scons_succ]
      rw [rename_eq_subst]
      exact subst_congr (fun k => rfl) _

/-! ### The fundamental lemma -/

/-- **The fundamental lemma of the logical relation, for the typing judgement**: a well-typed
term sends related substitutions to related terms, at the skeleton of its type. -/
theorem LR.fundamental {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    ∀ {Δ : List STy} {σ τ : ℕ → Tm}, RelSub Γ Δ σ τ →
      LR (skel (skelCtx Γ) A) Δ (subst σ t) (subst τ t) := by
  induction h with
  | ax Γ => intro Δ σ τ _; exact Eqv.baseSort .refl .refl
  | @var Γ n A hl => intro Δ σ τ hσ; exact hσ.1 n A hl
  | @pi Γ A B s t hr hA hB ihA ihB =>
      intro Δ σ τ hσ
      cases hr
      have hAl := typeLevel_of_typing_sort hA
      have hs1 : skel Δ (subst σ A) = skel (skelCtx Γ) A :=
        skel_subst_typeLevel hΓ (fun n hn => (hσ.2 n hn).1) hAl
      have hs2 : skel Δ (subst τ A) = skel (skelCtx Γ) A :=
        skel_subst_typeLevel hΓ (fun n hn => (hσ.2 n hn).2) hAl
      have iA := ihA hΓ hσ
      have iB := ihB (Wf.cons hΓ hA) (hσ.up hΓ hA)
      simp only [skel_sort] at iA iB ⊢
      refine Eqv.basePi .refl .refl iA (hs1.trans hs2.symm) ?_
      rw [hs1]
      exact iB
  | @lam Γ A B b s hP hb ihP ihb =>
      intro Δ σ τ hσ
      obtain ⟨s', t', hr, hA, _, _⟩ := hP.pi_inv
      cases hr
      intro Δ' ρ hρ a c hac
      have hσ' := (hσ.rename hρ).cons hΓ hA hac
      have ib := ihb (Wf.cons hΓ hA) hσ'
      refine LR.whExpand_left (WhStep.beta _ _ _) (LR.whExpand_right (WhStep.beta _ _ _) ?_)
      rw [lam_body_inst, lam_body_inst]
      simpa using ib
  | @app Γ f a A B hf ha ihf iha =>
      intro Δ σ τ hσ
      have hstar : Typing Γ A (Tm.sort Srt.star) := by
        rcases hf.validity hΓ with hbox | ⟨s, hs⟩
        · exact absurd hbox (by simp)
        · obtain ⟨s', t', hr, hA, _, _⟩ := hs.pi_inv
          cases hr
          exact hA
      have hBlevel : TypeLevel (A :: Γ) B := by
        rcases hf.validity hΓ with hbox | ⟨s, hs⟩
        · exact absurd hbox (by simp)
        · obtain ⟨s', t', _, _, hB, _⟩ := hs.pi_inv
          exact typeLevel_of_typing_sort hB
      have hskel : skel (skel (skelCtx Γ) a :: skelCtx Γ) B =
          skel (skel (skelCtx Γ) A :: skelCtx Γ) B :=
        skel_irrel (Wf.cons hΓ hstar)
          ((SkAgree.refl Γ (skelCtx Γ)).cons_type hΓ hstar _ _) hBlevel
      have i := ihf hΓ hσ Δ id (RenS.id' Δ) _ _ (iha hΓ hσ)
      rw [skel_inst, hskel]
      simpa using i
  | @conv Γ t A B s ht hB hc iht _ =>
      intro Δ σ τ hσ
      have hAlevel : TypeLevel Γ A := by
        rcases ht.validity hΓ with rfl | ⟨s', hs'⟩
        · exact absurd (not_conv_box_of_typing hΓ hB hc.symm) (by simp)
        · exact typeLevel_of_typing_sort hs'
      rw [← skel_conv hΓ (skelCtx Γ) hAlevel (typeLevel_of_typing_sort hB) hc]
      exact iht hΓ hσ

/-- The identity substitution is related to itself. -/
theorem RelSub.ids (Γ : Ctx) : RelSub Γ (skelCtx Γ) ids ids := by
  refine ⟨fun n A hl => ?_, fun n _ => ⟨rfl, rfl⟩⟩
  rw [hl.skel_eq]
  exact LR.var _ n

/-- **The algorithm is reflexive on well-typed terms**: `Γ ⊢ t : A` gives
`Γ° ⊢ t ⇔ t : A°`. -/
theorem AlgEq.refl_of_typing {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    AlgEq (skelCtx Γ) t t (skel (skelCtx Γ) A) := by
  have := LR.fundamental h hΓ (RelSub.ids Γ)
  simpa using LR.escape this

end LambdaPi
