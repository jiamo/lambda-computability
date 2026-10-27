/-
**Martin-Löf type theory: transitivity of algorithmic conversion** — milestone M30
(`M30-MLTT-ALG`).

* inversion of the algorithmic judgements: `NeUp.inv_var`, `NeUp.inv_app`, `NeUp.inv_natrec`,
  `NeUp.inv_emptyrec`, `NeDown.inv`, `TyUp.inv`, `TmUp.inv`, and of the comparisons of weak
  head normal forms by the head of the type (`TyDown.inv_*`, `TmDown.inv_*`);
* `MLTT.Alg.trans` — **transitivity**, for all six judgements at once; for neutral terms the two
  inferred types are equal.  `NeUp.trans`, `NeDown.trans`, `TyUp.trans`, `TmUp.trans`.
-/

import Start.MLTTAlgSymm

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Inversion -/

theorem NeUp.inv_var {Γ : Ctx} {n : ℕ} {v B : Tm} (h : NeUp Γ (var n) v B) :
    v = var n ∧ HasTy Γ (var n) B := by
  cases h with
  | varRefl hv => exact ⟨rfl, hv⟩

theorem NeUp.inv_app {Γ : Ctx} {l b v B : Tm} (h : NeUp Γ (app l b) v B) :
    ∃ m c F G, v = app m c ∧ NeDown Γ l m (pi F G) ∧ TmUp Γ b c F ∧ B = G[b] := by
  cases h with
  | appCong hk ha => exact ⟨_, _, _, _, rfl, hk, ha, rfl⟩

theorem NeUp.inv_natrec {Γ : Ctx} {P z s n v B : Tm} (h : NeUp Γ (natrec P z s n) v B) :
    ∃ P' z' s' n', v = natrec P' z' s' n' ∧ TyUp (Tm.nat :: Γ) P P' ∧
      TmUp Γ z z' (P[Tm.zero]) ∧ TmUp (P :: Tm.nat :: Γ) s s' (stepTy P) ∧
      NeDown Γ n n' Tm.nat ∧ B = P[n] := by
  cases h with
  | natrecCong hP hz hs hn => exact ⟨_, _, _, _, rfl, hP, hz, hs, hn, rfl⟩

theorem NeUp.inv_emptyrec {Γ : Ctx} {P e v B : Tm} (h : NeUp Γ (emptyrec P e) v B) :
    ∃ P' e', v = emptyrec P' e' ∧ TyUp Γ P P' ∧ NeDown Γ e e' Tm.empty ∧ B = P := by
  cases h with
  | emptyrecCong hP he => exact ⟨_, _, rfl, hP, he, rfl⟩

theorem NeDown.inv {Γ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) :
    ∃ B, NeUp Γ k l B ∧ TyReds Γ B A ∧ Whnf A := by
  cases h with
  | down hk hBA hA => exact ⟨_, hk, hBA, hA⟩

theorem TyUp.inv {Γ : Ctx} {A B : Tm} (h : TyUp Γ A B) :
    ∃ A' B', TyReds Γ A A' ∧ TyReds Γ B B' ∧ Whnf A' ∧ Whnf B' ∧ TyDown Γ A' B' := by
  cases h with
  | tyRed hA hB hA' hB' hd => exact ⟨_, _, hA, hB, hA', hB', hd⟩

theorem TmUp.inv {Γ : Ctx} {t u A : Tm} (h : TmUp Γ t u A) :
    ∃ B t' u', TyReds Γ A B ∧ TReds Γ t t' B ∧ TReds Γ u u' B ∧ Whnf B ∧ Whnf t' ∧ Whnf u' ∧
      TmDown Γ t' u' B := by
  cases h with
  | tmRed hAB ht hu hB ht' hu' hd => exact ⟨_, _, _, hAB, ht, hu, hB, ht', hu', hd⟩

theorem TyDown.inv_univ {Γ : Ctx} {l : ℕ} {C : Tm} (h : TyDown Γ (Tm.univ l) C) :
    C = Tm.univ l := by
  cases h with
  | univRefl _ => rfl
  | neTy hd => cases (NeDown.neutral hd).1

theorem TyDown.inv_nat {Γ : Ctx} {C : Tm} (h : TyDown Γ Tm.nat C) : C = Tm.nat := by
  cases h with
  | natRefl _ => rfl
  | neTy hd => cases (NeDown.neutral hd).1

theorem TyDown.inv_empty {Γ : Ctx} {C : Tm} (h : TyDown Γ Tm.empty C) : C = Tm.empty := by
  cases h with
  | emptyRefl _ => rfl
  | neTy hd => cases (NeDown.neutral hd).1

theorem TyDown.inv_pi {Γ : Ctx} {H E C : Tm} (h : TyDown Γ (pi H E) C) :
    ∃ K M, C = pi K M ∧ TyUp Γ H K ∧ TyUp (H :: Γ) E M := by
  cases h with
  | piCong hF hG => exact ⟨_, _, rfl, hF, hG⟩
  | neTy hd => cases (NeDown.neutral hd).1

theorem TyDown.inv_ne {Γ : Ctx} {K C : Tm} (h : TyDown Γ K C) (hK : Neutral K) :
    ∃ l, NeDown Γ K C (Tm.univ l) := by
  cases h with
  | neTy hd => exact ⟨_, hd⟩
  | univRefl _ => cases hK
  | natRefl _ => cases hK
  | emptyRefl _ => cases hK
  | piCong _ _ => cases hK

theorem TmDown.inv_nat_ne {Γ : Ctx} {l v : Tm} (h : TmDown Γ l v Tm.nat) (hl : Neutral l) :
    NeDown Γ l v Tm.nat := by
  cases h with
  | neNat hd => exact hd
  | neNe _ _ hA _ => cases hA
  | zeroRefl _ => cases hl
  | succCong _ => cases hl

theorem TmDown.inv_empty {Γ : Ctx} {l v : Tm} (h : TmDown Γ l v Tm.empty) :
    NeDown Γ l v Tm.empty := by
  cases h with
  | neEmpty hd => exact hd
  | neNe _ _ hA _ => cases hA

theorem TmDown.inv_neTy {Γ : Ctx} {l v A : Tm} (h : TmDown Γ l v A) (hA : Neutral A) :
    ∃ B, HasTy Γ v A ∧ NeDown Γ l v B := by
  cases h with
  | neNe _ hv _ hd => exact ⟨_, hv, hd⟩
  | neNat _ => cases hA
  | neEmpty _ => cases hA
  | univTm _ _ _ => cases hA
  | zeroRefl _ => cases hA
  | succCong _ => cases hA
  | eta _ _ _ _ _ => cases hA

theorem TmDown.inv_univ {Γ : Ctx} {B v : Tm} {l : ℕ} (h : TmDown Γ B v (Tm.univ l)) :
    HasTy Γ v (Tm.univ l) ∧ TyDown Γ B v := by
  cases h with
  | univTm _ hv hd => exact ⟨hv, hd⟩
  | neNe _ _ hA _ => cases hA

theorem TmDown.inv_zero {Γ : Ctx} {v : Tm} (h : TmDown Γ Tm.zero v Tm.nat) : v = Tm.zero := by
  cases h with
  | zeroRefl _ => rfl
  | neNat hd => cases (NeDown.neutral hd).1
  | neNe _ _ hA _ => cases hA

theorem TmDown.inv_succ {Γ : Ctx} {n v : Tm} (h : TmDown Γ (succ n) v Tm.nat) :
    ∃ v', v = succ v' ∧ TmUp Γ n v' Tm.nat := by
  cases h with
  | succCong hd => exact ⟨_, rfl, hd⟩
  | neNat hd => cases (NeDown.neutral hd).1
  | neNe _ _ hA _ => cases hA

theorem TmDown.inv_pi {Γ : Ctx} {g v F G : Tm} (h : TmDown Γ g v (pi F G)) :
    HasTy Γ v (pi F G) ∧ Whnf v ∧
      TmUp (F :: Γ) (app (shift g) (var 0)) (app (shift v) (var 0)) G := by
  cases h with
  | eta _ hv _ hnv hd => exact ⟨hv, hnv, hd⟩
  | neNe _ _ hA _ => cases hA

/-! ### Transitivity -/

/-- The transitivity statement of each algorithmic judgement. -/
def AJd.Trans : AJd → Prop
  | .neUp Γ k l A => ∀ {m B : Tm}, NeUp Γ l m B → NeUp Γ k m A ∧ TyEq Γ A B
  | .neDown Γ k l A => ∀ {m B : Tm}, NeDown Γ l m B → NeDown Γ k m A ∧ TyEq Γ A B
  | .tyUp Γ A B => ∀ {C : Tm}, TyUp Γ B C → TyUp Γ A C
  | .tyDown Γ A B => ∀ {C : Tm}, TyDown Γ B C → TyDown Γ A C
  | .tmUp Γ t u A => ∀ {v : Tm}, TmUp Γ u v A → TmUp Γ t v A
  | .tmDown Γ t u A => ∀ {v : Tm}, TmDown Γ u v A → TmDown Γ t v A

/-- **Transitivity of algorithmic conversion.** -/
theorem Alg.trans {J : AJd} (h : Alg J) : J.Trans := by
  induction h with
  | varRefl hv =>
      intro m B h2
      obtain ⟨rfl, hv'⟩ := h2.inv_var
      exact ⟨Alg.varRefl hv, (Neutral.var _).tyUnique hv hv'⟩
  | appCong hk ha ihk iha =>
      intro m B h2
      obtain ⟨m', c, F', G', rfl, hd, hbc, rfl⟩ := h2.inv_app
      obtain ⟨hkm, hPP⟩ := ihk hd
      obtain ⟨hFF, hGG⟩ := TyEq.pi_inj hPP
      have hab := TmUp.sound ha
      refine ⟨Alg.appCong hkm (iha (hbc.conv (Der.symmT hFF))), ?_⟩
      have hG := (NeDown.sound hk).tyL.wfTy.pi_inv.2
      exact Der.transT (hG.instEq hab) (hGG.inst hab.tyR)
  | @natrecCong Γ P P' z z' s s' n n' hP hz _ hn ihP ihz ihs ihn =>
      intro m B h2
      obtain ⟨P'', z'', s'', n'', rfl, hP2, hz2, hs2, hn2, rfl⟩ := h2.inv_natrec
      have hPP := TyUp.sound hP
      have hΓ := (TmUp.sound hz).wf
      have hz' := ihz (hz2.conv (Der.symmT (hPP.inst (Der.zero hΓ))))
      have hctx : CtxEq (P' :: Tm.nat :: Γ) (P :: Tm.nat :: Γ) :=
        (CtxEq.refl (Der.cons hΓ (Der.natT hΓ))).cons' (Der.symmT hPP)
      have hs' := ihs ((hs2.stab hctx).conv (Der.symmT hPP.stepTy))
      refine ⟨Alg.natrecCong (ihP hP2) hz' hs' (ihn hn2).1, ?_⟩
      have hnn := NeDown.sound hn
      exact Der.transT (hPP.wfL.instEq hnn) (hPP.inst hnn.tyR)
  | emptyrecCong hP _ ihP ihe =>
      intro m B h2
      obtain ⟨P'', e'', rfl, hP2, he2, rfl⟩ := h2.inv_emptyrec
      exact ⟨Alg.emptyrecCong (ihP hP2) (ihe he2).1, TyUp.sound hP⟩
  | down _ hAB hB ih =>
      intro m C h2
      obtain ⟨B₂, hl₂, hBC, -⟩ := h2.inv
      obtain ⟨hkm, hAB₂⟩ := ih hl₂
      exact ⟨Alg.down hkm hAB hB, Der.transT (Der.symmT hAB.tyEq) (Der.transT hAB₂ hBC.tyEq)⟩
  | tyRed hA hB hA' hB' _ ih =>
      intro C h2
      obtain ⟨B₂, C', hB₂, hC, hB₂', hC', hd⟩ := h2.inv
      rw [TyReds.whnf_unique hB₂ hB hB₂' hB'] at hd
      exact Alg.tyRed hA hC hA' hC' (ih hd)
  | univRefl hΓ =>
      intro C h2
      rw [h2.inv_univ]
      exact Alg.univRefl hΓ
  | natRefl hΓ =>
      intro C h2
      rw [h2.inv_nat]
      exact Alg.natRefl hΓ
  | emptyRefl hΓ =>
      intro C h2
      rw [h2.inv_empty]
      exact Alg.emptyRefl hΓ
  | neTy hd ih =>
      intro C h2
      obtain ⟨l', hd₂⟩ := h2.inv_ne (NeDown.neutral hd).2
      exact Alg.neTy (ih hd₂).1
  | @piCong Γ F H G E hF _ ihF ihG =>
      intro C h2
      obtain ⟨K, M, rfl, hHK, hEM⟩ := h2.inv_pi
      have hFH := TyUp.sound hF
      have hctx : CtxEq (H :: Γ) (F :: Γ) := (CtxEq.refl hFH.wf).cons' (Der.symmT hFH)
      exact Alg.piCong (ihF hHK) (ihG (hEM.stab hctx))
  | tmRed hAB ht hu hB ht' hu' _ ih =>
      intro v h2
      obtain ⟨B₂, u₂, v₂, hAB₂, hu₂, hv₂, hB₂, hu₂', hv₂', hd⟩ := h2.inv
      have eB := TyReds.whnf_unique hAB₂ hAB hB₂ hB
      subst eB
      have eu := TReds.whnf_unique hu₂ hu hu₂' hu'
      subst eu
      exact Alg.tmRed hAB ht hv₂ hB ht' hv₂' (ih hd)
  | neNat hd ih =>
      intro v h2
      exact Alg.neNat (ih (h2.inv_nat_ne (NeDown.neutral hd).2)).1
  | neEmpty _ ih =>
      intro v h2
      exact Alg.neEmpty (ih h2.inv_empty).1
  | neNe hk _ hA _ ih =>
      intro v h2
      obtain ⟨B₂, hv, hd₂⟩ := h2.inv_neTy hA
      exact Alg.neNe hk hv hA (ih hd₂).1
  | univTm hA _ _ ih =>
      intro v h2
      obtain ⟨hv, hd₂⟩ := h2.inv_univ
      exact Alg.univTm hA hv (ih hd₂)
  | zeroRefl hΓ =>
      intro v h2
      rw [h2.inv_zero]
      exact Alg.zeroRefl hΓ
  | succCong _ ih =>
      intro v h2
      obtain ⟨v', rfl, hd₂⟩ := h2.inv_succ
      exact Alg.succCong (ih hd₂)
  | eta hf _ hnf _ _ ih =>
      intro v h2
      obtain ⟨hv, hnv, hd₂⟩ := h2.inv_pi
      exact Alg.eta hf hv hnf hnv (ih hd₂)

theorem NeUp.trans {Γ : Ctx} {k l m A B : Tm} (h₁ : NeUp Γ k l A) (h₂ : NeUp Γ l m B) :
    NeUp Γ k m A ∧ TyEq Γ A B :=
  Alg.trans h₁ h₂

theorem NeDown.trans {Γ : Ctx} {k l m A B : Tm} (h₁ : NeDown Γ k l A) (h₂ : NeDown Γ l m B) :
    NeDown Γ k m A ∧ TyEq Γ A B :=
  Alg.trans h₁ h₂

theorem TyUp.trans {Γ : Ctx} {A B C : Tm} (h₁ : TyUp Γ A B) (h₂ : TyUp Γ B C) : TyUp Γ A C :=
  Alg.trans h₁ h₂

theorem TmUp.trans {Γ : Ctx} {t u v A : Tm} (h₁ : TmUp Γ t u A) (h₂ : TmUp Γ u v A) :
    TmUp Γ t v A :=
  Alg.trans h₁ h₂

end MLTT
