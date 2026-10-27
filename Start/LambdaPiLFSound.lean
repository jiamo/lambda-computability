/-
**Soundness of the type-directed algorithm for the declarative equality of `λΠ`** — task
`M23-LF-EQUIV-COMPLETE`.

Harper and Pfenning's soundness theorem: if two terms are typable at `A` and algorithmically
equivalent at the erasure of `A`, they are declaratively equal at `A`.

* `TEqE.whStep`, `TEqE.whRed` — a typable term is declaratively equal to its weak head reducts;
* `TypingE.whnf_arrow` — a type whose erasure is an arrow weak head reduces to a product (the
  weak head normal form is read off the algorithm's reflexivity derivation, `TypingE.algEq_refl`,
  so no normalization theorem is needed);
* `EqvE.sound_typed` — soundness, together with the path lemma: two typable paths related
  structurally are declaratively equal, their types are βη-convertible, and the synthesised
  simple type is the erasure of the type;
* **`AlgEqE.sound`** — the soundness theorem, and **`TEqE.iff_algEq`**: for terms typable at
  `A` in a well-formed context, `Γ ⊢ M ≡ N : A` holds exactly when `erCtx Γ ⊢ M ⇔ N : er A`.
-/

import Start.LambdaPiLFComplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Typing facts -/

/-- A term that is not the top sort and is βη-convertible to a typable term is not `□`. -/
theorem TypingE.ne_box_of_conv {Γ : Ctx} {A T : Tm} {s : Srt} (hT : TypingE Γ T (Tm.sort s))
    (hc : BetaEtaConv T A) (hΓ : WfE Γ) : A ≠ Tm.sort Srt.box := by
  rintro rfl
  obtain ⟨k, hl, -⟩ := hT.lvl' hΓ
  exact hl.not_conv_box hc.symm

/-- The type of a typable term that is βη-convertible to a typable type is typable. -/
theorem TypingE.type_typed {Γ : Ctx} {t A T : Tm} {s : Srt} (ht : TypingE Γ t A)
    (hT : TypingE Γ T (Tm.sort s)) (hc : BetaEtaConv T A) (hΓ : WfE Γ) :
    ∃ s', TypingE Γ A (Tm.sort s') := by
  rcases ht.validity hΓ with h | h
  · exact absurd h (hT.ne_box_of_conv hc hΓ)
  · exact h

/-- The body of the η-expansion of a function. -/
theorem TypingE.etaBody {Γ : Ctx} {f A B : Tm} (hf : TypingE Γ f (Tm.pi A B)) :
    TypingE (A :: Γ) (Tm.app (shift f) (Tm.var 0)) B := by
  have hf' : TypingE (A :: Γ) (shift f) (Tm.pi (shift A) (LambdaPi.rename (upr Nat.succ) B)) := by
    have := hf.weaken A
    simpa [shift] using this
  have hbody := TypingE.app hf' (TypingE.var (Lookup.zero Γ A))
  rwa [inst_zero_rename_upr_succ] at hbody

/-! ### Weak head reduction is a declarative equality -/

theorem TEqE.whStep {Γ : Ctx} {M M' A : Tm} (hst : WhStep M M') :
    TypingE Γ M A → WfE Γ → TEqE Γ M M' A := by
  induction hst generalizing A with
  | beta C b a =>
      intro h hΓ
      obtain ⟨X, Y, hf, ha, hc⟩ := h.app_inv
      obtain ⟨B, s, hP, hb, hc'⟩ := hf.lam_inv
      obtain ⟨hCX, hBY⟩ := betaEtaConv_pi_inv hc'
      obtain ⟨s₁, t₁, hr, hC, hB, _⟩ := hP.pi_inv
      have ha' : TypingE Γ a C := ha.conv hC hCX.symm
      have hBa : TypingE Γ (B[a]) (Tm.sort t₁) := hB.inst ha'
      have hc₂ : BetaEtaConv (B[a]) A := (hBY.subst (scons a ids)).trans hc
      obtain ⟨s', hA⟩ := h.type_typed hBa hc₂ hΓ
      exact (TEqE.beta hP hb ha').conv hA hc₂
  | @appL f f' a hs ih =>
      intro h hΓ
      obtain ⟨X, Y, hf, ha, hc⟩ := h.app_inv
      obtain ⟨s₁, t₁, _, _, hY⟩ := hf.pi_cod hΓ
      have hYa : TypingE Γ (Y[a]) (Tm.sort t₁) := hY.inst ha
      obtain ⟨s', hA⟩ := h.type_typed hYa hc hΓ
      exact (TEqE.app (ih hf hΓ) (TEqE.refl ha)).conv hA hc

theorem TEqE.whRed {Γ : Ctx} {M M' A : Tm} (hr : WhRed M M') (h : TypingE Γ M A) (hΓ : WfE Γ) :
    TEqE Γ M M' A := by
  induction hr with
  | refl => exact TEqE.refl h
  | tail hr' hs ih => exact ih.trans (TEqE.whStep hs (h.whRed hΓ hr') hΓ)

/-! ### Weak head normal forms of types -/

/-- A path has erasure `base`. -/
theorem IsPath.er {p : Tm} (h : IsPath p) : er p = STy.base := by
  induction h with
  | var n => rfl
  | app a _ ih => simpa using ih

/-- Weak head reduction preserves the level. -/
theorem Lvl.whRed {L : List Bool} {t u : Tm} {k : ℕ} (h : Lvl L t k) (hr : WhRed t u) :
    Lvl L u k := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact Lvl.step hs.step ih

/-- Weak head reduction of a term with a level preserves the erasure. -/
theorem er_whRed {L : List Bool} {t u : Tm} {k : ℕ} (h : Lvl L t k) (hr : WhRed t u) :
    er t = er u := by
  induction hr with
  | refl => rfl
  | tail hr' hs ih => exact ih.trans (er_step hs.step (h.whRed hr'))

/-- **A type whose erasure is an arrow weak head reduces to a product.** -/
theorem TypingE.whnf_arrow {Γ : Ctx} {A : Tm} {s : Srt} (h : TypingE Γ A (Tm.sort s)) (hΓ : WfE Γ)
    {σ τ : STy} (he : er A = STy.arrow σ τ) :
    ∃ C D, WhRed A (Tm.pi C D) ∧ er C = σ ∧ er D = τ := by
  obtain ⟨k, hl, -⟩ := h.lvl' hΓ
  have hrefl := h.algEq_refl hΓ
  rw [er_sort] at hrefl
  cases hrefl with
  | basePath hM _ hp =>
      have := (er_whRed hl hM).trans (PathEqE.isPath hp).1.er
      rw [he] at this
      cases this
  | baseSort hM _ =>
      have := er_whRed hl hM
      rw [he] at this
      cases this
  | @basePi _ _ _ C D _ _ hM _ _ _ _ =>
      have := er_whRed hl hM
      rw [he, er_pi] at this
      cases this
      exact ⟨C, D, hM, rfl, rfl⟩

/-! ### Soundness -/

/-- **Soundness of the algorithm**, with the path lemma, by induction on the algorithm. -/
theorem EqvE.sound_typed {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    ∀ {Γ : Ctx}, erCtx Γ = Δ → WfE Γ →
      (k = .alg → ∀ {A : Tm}, TypingE Γ M A → TypingE Γ N A → er A = τ → TEqE Γ M N A) ∧
      (k = .path → ∀ {A B : Tm}, TypingE Γ M A → TypingE Γ N B →
        TEqE Γ M N A ∧ BetaEtaConv A B ∧ er A = τ) := by
  induction h with
  | @arrow Δ M N σ τ _ ih =>
      intro Γ hΔ hΓ
      refine ⟨fun _ A hM hN he => ?_, fun h => by cases h⟩
      rcases hM.validity hΓ with rfl | ⟨s, hA⟩
      · simp at he
      obtain ⟨C, D, hred, hC, hD⟩ := hA.whnf_arrow hΓ he
      have hP : TypingE Γ (Tm.pi C D) (Tm.sort s) := hA.whRed hΓ hred
      have hcA : BetaEtaConv A (Tm.pi C D) := hred.betaEtaConv
      have hM' : TypingE Γ M (Tm.pi C D) := hM.conv hP hcA
      have hN' : TypingE Γ N (Tm.pi C D) := hN.conv hP hcA
      obtain ⟨s₁, t₁, hr, hCt, -, -⟩ := hP.pi_inv
      have hΓC : WfE (C :: Γ) := WfE.cons hΓ hCt
      have hΔ' : erCtx (C :: Γ) = σ :: Δ := by rw [erCtx_cons, hC, hΔ]
      have hbody := (ih hΔ' hΓC).1 rfl hM'.etaBody hN'.etaBody hD
      have hlam : TEqE Γ (Tm.lam C (Tm.app (shift M) (Tm.var 0)))
          (Tm.lam C (Tm.app (shift N) (Tm.var 0))) (Tm.pi C D) := by
        cases hr
        exact TEqE.lam hP (TEqE.refl hCt) hbody
      have heq : TEqE Γ M N (Tm.pi C D) :=
        ((TEqE.eta hM').symm.trans hlam).trans (TEqE.eta hN')
      exact heq.conv hA hcA.symm
  | @basePath Δ M N M' N' hM hN _ ih =>
      intro Γ hΔ hΓ
      refine ⟨fun _ A hMt hNt _ => ?_, fun h => by cases h⟩
      have h₁ := TEqE.whRed hM hMt hΓ
      have h₂ := TEqE.whRed hN hNt hΓ
      have hM't := hMt.whRed hΓ hM
      have hN't := hNt.whRed hΓ hN
      have hp := ((ih hΔ hΓ).2 rfl hM't hN't).1
      exact (h₁.trans hp).trans h₂.symm
  | @baseSort Δ M N s hM hN =>
      intro Γ hΔ hΓ
      refine ⟨fun _ A hMt hNt _ => ?_, fun h => by cases h⟩
      exact (TEqE.whRed hM hMt hΓ).trans (TEqE.whRed hN hNt hΓ).symm
  | @basePi Δ M N C D C' D' hM hN _ hsk _ ihC ihD =>
      intro Γ hΔ hΓ
      refine ⟨fun _ A hMt hNt _ => ?_, fun h => by cases h⟩
      have h₁ := TEqE.whRed hM hMt hΓ
      have h₂ := TEqE.whRed hN hNt hΓ
      have hP := hMt.whRed hΓ hM
      have hP' := hNt.whRed hΓ hN
      obtain ⟨s₁, t₁, hr, hC, hD, hc₁⟩ := hP.pi_inv
      obtain ⟨s₂, t₂, hr', hC', hD', hc₂⟩ := hP'.pi_inv
      cases hr
      cases hr'
      have ht : t₁ = t₂ := betaEtaConv_sort_inj (hc₁.trans hc₂.symm)
      subst ht
      have hCC : TEqE Γ C C' (Tm.sort Srt.star) := (ihC hΔ hΓ).1 rfl hC hC' rfl
      have hΓC : WfE (C :: Γ) := WfE.cons hΓ hC
      have hΔ' : erCtx (C :: Γ) = er C :: Δ := by rw [erCtx_cons, hΔ]
      have hD'C : TypingE (C :: Γ) D' (Tm.sort t₁) := hD'.ctxConv₁ hΓ hC' hCC.betaEtaConv.symm
      have hDD : TEqE (C :: Γ) D D' (Tm.sort t₁) := (ihD hΔ' hΓC).1 rfl hD hD'C rfl
      have hpi : TEqE Γ (Tm.pi C D) (Tm.pi C' D') (Tm.sort t₁) := TEqE.pi rfl hCC hDD
      have hpiA : TEqE Γ (Tm.pi C D) (Tm.pi C' D') A := by
        by_cases hA : A = Tm.sort Srt.box
        · subst hA
          have := betaEtaConv_sort_inj hc₁
          subst this
          exact hpi
        · rcases hMt.validity hΓ with h | ⟨s, hAs⟩
          · exact absurd h hA
          · exact hpi.conv hAs hc₁
      exact (h₁.trans hpiA).trans h₂.symm
  | @var Δ n =>
      intro Γ hΔ hΓ
      refine ⟨(fun h => by cases h), fun _ A B hA hB => ?_⟩
      obtain ⟨D, hl, hcA⟩ := hA.var_inv
      obtain ⟨D', hl', hcB⟩ := hB.var_inv
      have e := Lookup.det hl hl'
      subst e
      obtain ⟨s, hDs⟩ := hΓ.lookup_typed hl
      refine ⟨TEqE.refl hA, hcA.symm.trans hcB, ?_⟩
      obtain ⟨s', hAs⟩ := hA.type_typed hDs hcA hΓ
      rw [← (hDs.er_conv hAs hcA hΓ).1, ← hΔ, hl.er_eq]
  | @app Δ p q a b σ τ _ _ ihp iha =>
      intro Γ hΔ hΓ
      refine ⟨(fun h => by cases h), fun _ A B hA hB => ?_⟩
      obtain ⟨X₁, Y₁, hp, ha, hc₁⟩ := hA.app_inv
      obtain ⟨X₂, Y₂, hq, hb, hc₂⟩ := hB.app_inv
      obtain ⟨hpq, hcP, heP⟩ := (ihp hΔ hΓ).2 rfl hp hq
      obtain ⟨hX, hY⟩ := betaEtaConv_pi_inv hcP
      rw [er_pi] at heP
      cases heP
      obtain ⟨s₁, t₁, hr, hX₁, hY₁⟩ := hp.pi_cod hΓ
      cases hr
      have hb' : TypingE Γ b X₁ := hb.conv hX₁ hX.symm
      have hab : TEqE Γ a b X₁ := (iha hΔ hΓ).1 rfl ha hb' rfl
      have hY₁a : TypingE Γ (Y₁[a]) (Tm.sort t₁) := hY₁.inst ha
      obtain ⟨s', hAs⟩ := hA.type_typed hY₁a hc₁ hΓ
      refine ⟨(TEqE.app hpq hab).conv hAs hc₁, ?_, ?_⟩
      · have hYa : BetaEtaConv (Y₁[a]) (Y₂[b]) :=
          (hY.subst (scons a ids)).trans (BetaEtaConv.instArg Y₂ hab.betaEtaConv)
        exact (hc₁.symm.trans hYa).trans hc₂
      · rw [← (hY₁a.er_conv hAs hc₁ hΓ).1, er_inst (ha.er_object hX₁ hΓ)]

/-- **Soundness of the algorithm for the declarative equality.** -/
theorem AlgEqE.sound {Γ : Ctx} {M N A : Tm} (h : AlgEqE (erCtx Γ) M N (er A)) (hΓ : WfE Γ)
    (hM : TypingE Γ M A) (hN : TypingE Γ N A) : TEqE Γ M N A :=
  (h.sound_typed rfl hΓ).1 rfl hM hN rfl

/-- **The algorithm decides the declarative equality** of terms typable at the same type: the
declarative equality and algorithmic equivalence at the erasure coincide. -/
theorem TEqE.iff_algEq {Γ : Ctx} {M N A : Tm} (hΓ : WfE Γ) (hM : TypingE Γ M A)
    (hN : TypingE Γ N A) : TEqE Γ M N A ↔ AlgEqE (erCtx Γ) M N (er A) :=
  ⟨fun h => h.complete hΓ, fun h => h.sound hΓ hM hN⟩

end LambdaPi
