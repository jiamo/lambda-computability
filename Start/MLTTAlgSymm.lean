/-
**Martin-Löf type theory: symmetry of algorithmic conversion** — milestone M30
(`M30-MLTT-ALG`).

* `MLTT.Alg.symm` — **symmetry**, for all six judgements at once, into any equal context (the
  context changes because the right-hand side of a product or of a `natrec` motive becomes the
  binder of the swapped comparison); for neutral terms the inferred type changes up to type
  equality.  `NeUp.symm`, `NeDown.symm`, `TyUp.symm`, `TmUp.symm` in the same context.
-/

import Start.MLTTAlgStab

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-- The symmetry statement of each algorithmic judgement. -/
def AJd.Symm : AJd → Prop
  | .neUp Γ k l A => ∀ {Δ : Ctx}, CtxEq Γ Δ → ∃ B, TyEq Γ A B ∧ NeUp Δ l k B
  | .neDown Γ k l A => ∀ {Δ : Ctx}, CtxEq Γ Δ → ∃ B, TyEq Γ A B ∧ NeDown Δ l k B
  | .tyUp Γ A B => ∀ {Δ : Ctx}, CtxEq Γ Δ → TyUp Δ B A
  | .tyDown Γ A B => ∀ {Δ : Ctx}, CtxEq Γ Δ → TyDown Δ B A
  | .tmUp Γ t u A => ∀ {Δ : Ctx}, CtxEq Γ Δ → TmUp Δ u t A
  | .tmDown Γ t u A => ∀ {Δ : Ctx}, CtxEq Γ Δ → TmDown Δ u t A

/-- **Symmetry of algorithmic conversion.** -/
theorem Alg.symm {J : AJd} (h : Alg J) : J.Symm := by
  induction h with
  | varRefl hv => intro Δ h; exact ⟨_, Der.reflT hv.wfTy, Alg.varRefl (hv.stab h)⟩
  | appCong hk ha ihk iha =>
      intro Δ h
      obtain ⟨B, hPB, hd⟩ := ihk h
      obtain ⟨F', G', rfl, hFF, hGG⟩ := hPB.pi_whnf (NeDown.whnf hd)
      have hab := TmUp.sound ha
      have hba := (iha h).conv (hFF.stab h)
      refine ⟨_, ?_, Alg.appCong hd hba⟩
      have hG := (NeDown.sound hk).tyL.wfTy.pi_inv.2
      exact Der.transT (hG.instEq hab) (hGG.inst hab.tyR)
  | natrecCong hP _ _ hn ihP ihz ihs ihn =>
      intro Δ h
      have hPP := TyUp.sound hP
      obtain ⟨B, hNB, hd⟩ := ihn h
      rw [hNB.nat_whnf (NeDown.whnf hd)] at hd
      have hnn := NeDown.sound hn
      have hz' := (ihz h).conv ((hPP.inst (Der.zero h.wfL)).stab h)
      have hctx := h.upNat.cons' hPP
      have hs' := (ihs hctx).conv (hPP.stepTy.stab hctx)
      refine ⟨_, ?_, Alg.natrecCong (ihP h.upNat) hz' hs' hd⟩
      exact Der.transT (hPP.wfL.instEq hnn) (hPP.inst hnn.tyR)
  | emptyrecCong hP _ ihP ihe =>
      intro Δ h
      obtain ⟨B, hEB, hd⟩ := ihe h
      rw [hEB.empty_whnf (NeDown.whnf hd)] at hd
      exact ⟨_, TyUp.sound hP, Alg.emptyrecCong (ihP h) hd⟩
  | down _ hAB _ ih =>
      intro Δ h
      obtain ⟨B', hAB', hd⟩ := ih h
      obtain ⟨B'', hr, hn⟩ := (NeUp.sound hd).tyL.wfTy.whnf
      refine ⟨B'', ?_, Alg.down hd hr hn⟩
      exact Der.transT (Der.symmT hAB.tyEq) (Der.transT hAB' (hr.tyEq.stab h.symm))
  | tyRed hA hB hA' hB' _ ih => intro Δ h; exact Alg.tyRed (hB.stab h) (hA.stab h) hB' hA' (ih h)
  | univRefl _ => intro Δ h; exact Alg.univRefl h.wfR
  | natRefl _ => intro Δ h; exact Alg.natRefl h.wfR
  | emptyRefl _ => intro Δ h; exact Alg.emptyRefl h.wfR
  | neTy _ ih =>
      intro Δ h
      obtain ⟨B, hUB, hd⟩ := ih h
      rw [hUB.univ_whnf (NeDown.whnf hd)] at hd
      exact Alg.neTy hd
  | piCong hF _ ihF ihG => intro Δ h; exact Alg.piCong (ihF h) (ihG (h.cons' (TyUp.sound hF)))
  | tmRed hAB ht hu hB ht' hu' _ ih =>
      intro Δ h
      exact Alg.tmRed (hAB.stab h) (hu.stab h) (ht.stab h) hB hu' ht' (ih h)
  | neNat _ ih =>
      intro Δ h
      obtain ⟨B, hNB, hd⟩ := ih h
      rw [hNB.nat_whnf (NeDown.whnf hd)] at hd
      exact Alg.neNat hd
  | neEmpty _ ih =>
      intro Δ h
      obtain ⟨B, hEB, hd⟩ := ih h
      rw [hEB.empty_whnf (NeDown.whnf hd)] at hd
      exact Alg.neEmpty hd
  | neNe hk hl hA _ ih =>
      intro Δ h
      obtain ⟨_, -, hd⟩ := ih h
      exact Alg.neNe (hl.stab h) (hk.stab h) hA hd
  | univTm hA hB _ ih => intro Δ h; exact Alg.univTm (hB.stab h) (hA.stab h) (ih h)
  | zeroRefl _ => intro Δ h; exact Alg.zeroRefl h.wfR
  | succCong _ ih => intro Δ h; exact Alg.succCong (ih h)
  | eta hf hg hnf hng _ ih =>
      intro Δ h
      exact Alg.eta (hg.stab h) (hf.stab h) hng hnf (ih (h.up hf.wfTy.pi_inv.1))

theorem NeUp.symm {Γ : Ctx} {k l A : Tm} (h : NeUp Γ k l A) : ∃ B, TyEq Γ A B ∧ NeUp Γ l k B :=
  Alg.symm h (CtxEq.refl (NeUp.sound h).wf)

theorem NeDown.symm {Γ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) :
    ∃ B, TyEq Γ A B ∧ NeDown Γ l k B :=
  Alg.symm h (CtxEq.refl (NeDown.sound h).wf)

theorem TyUp.symm {Γ : Ctx} {A B : Tm} (h : TyUp Γ A B) : TyUp Γ B A :=
  Alg.symm h (CtxEq.refl (TyUp.sound h).wf)

theorem TmUp.symm {Γ : Ctx} {t u A : Tm} (h : TmUp Γ t u A) : TmUp Γ u t A :=
  Alg.symm h (CtxEq.refl (TmUp.sound h).wf)

end MLTT
