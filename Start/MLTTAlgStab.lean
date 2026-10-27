/-
**Martin-Löf type theory: stability and type conversion of algorithmic conversion** —
milestone M30 (`M30-MLTT-ALG`).

* `MLTT.CtxEq` — judgementally equal contexts, and `CtxEq.substR`: the identity substitution
  relates them, so every declarative judgement transfers (`WfTy.stab`, `HasTy.stab`,
  `TyEq.stab`, `DEq.stab`, and the typed reductions `TRed.stab`, `TReds.stab`, `TyReds.stab`);
* `MLTT.Alg.stab` — **stability**: algorithmic conversion transfers to an equal context;
* `MLTT.Alg.conv` — **conversion**: the type at which two terms are algorithmically equal can be
  replaced by an equal type (`TmUp.conv`);
* `MLTT.TyEq.stepTy` — equal motives give equal types of the step of `natrec`.
-/

import Start.MLTTAlg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Equal contexts -/

/-- **Judgementally equal contexts.** -/
inductive CtxEq : Ctx → Ctx → Prop
  | nil : CtxEq List.nil List.nil
  | cons {Γ Δ : Ctx} {A B : Tm} : CtxEq Γ Δ → WfCtx (A :: Γ) → WfCtx (B :: Δ) → TyEq Γ A B →
      CtxEq (A :: Γ) (B :: Δ)

theorem CtxEq.wfL {Γ Δ : Ctx} (h : CtxEq Γ Δ) : WfCtx Γ := by
  cases h with
  | nil => exact Der.nil
  | cons _ hA _ _ => exact hA

theorem CtxEq.wfR {Γ Δ : Ctx} (h : CtxEq Γ Δ) : WfCtx Δ := by
  cases h with
  | nil => exact Der.nil
  | cons _ _ hB _ => exact hB

/-- **The identity substitution relates equal contexts.** -/
theorem CtxEq.substR {Γ Δ : Ctx} (h : CtxEq Γ Δ) : SubstR declEq Γ Δ MLTT.ids MLTT.ids := by
  induction h with
  | nil => exact Der.nil
  | @cons Γ Δ A B _ _ hB hAB ih =>
      have hρ : Wk Δ (B :: Δ) Nat.succ := ⟨RenOk.shift Δ B, hB⟩
      have ht := ih.wk hρ
      have hv := hAB.valid declEq
      obtain ⟨l, I, hI, -⟩ := hv.1.red ih
      have hIB := hv.2.2 Δ _ _ ih l I hI
      simp only [subst_ids] at hI hIB
      have hABΔ : TyEq Δ A B := hI.escapeTyEq hIB
      obtain ⟨J, hJ, -, -⟩ := TyR.wk l hI hρ
      have hvar : HasTy (B :: Δ) (var 0) (shift A) :=
        Der.conv (Der.var hB (Lookup.zero Δ B)) (Der.symmT (hABΔ.weaken hB))
      refine ⟨ht, l, J, ?_, hJ.var hvar⟩
      have e : subst (stail MLTT.ids) A = shift A := by
        rw [shift, rename_eq_subst]; rfl
      rw [e]
      exact hJ

theorem WfTy.stab {Γ Δ : Ctx} {A : Tm} (h : WfTy Γ A) (hΓΔ : CtxEq Γ Δ) : WfTy Δ A := by
  obtain ⟨l, I, hI, -⟩ := (h.valid declEq).red hΓΔ.substR
  rw [subst_ids] at hI
  exact hI.wfTy

theorem HasTy.stab {Γ Δ : Ctx} {t A : Tm} (h : HasTy Γ t A) (hΓΔ : CtxEq Γ Δ) : HasTy Δ t A := by
  obtain ⟨l, I, hI, ht⟩ := (h.valid declEq).red hΓΔ.substR
  simp only [subst_ids] at hI ht
  exact (hI.escapeTm ht).1

theorem TyEq.stab {Γ Δ : Ctx} {A B : Tm} (h : TyEq Γ A B) (hΓΔ : CtxEq Γ Δ) : TyEq Δ A B := by
  have hv := h.valid declEq
  have hs := hΓΔ.substR
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have := hI.escapeTyEq (hv.2.2 _ _ _ hs l I hI)
  simp only [subst_ids] at this
  exact this

theorem DEq.stab {Γ Δ : Ctx} {t u A : Tm} (h : DEq Γ t u A) (hΓΔ : CtxEq Γ Δ) : DEq Δ t u A := by
  have hv := h.valid declEq
  have hs := hΓΔ.substR
  obtain ⟨l, I, hI, -⟩ := hv.1.1.red hs
  have := (hI.escapeTm (hv.2.2 _ _ _ hs l I hI)).2.2
  simp only [subst_ids] at this
  exact this

theorem CtxEq.refl : ∀ {Γ : Ctx}, WfCtx Γ → CtxEq Γ Γ
  | [], _ => CtxEq.nil
  | A :: Γ, h => by
      cases h with
      | cons hΓ hA => exact CtxEq.cons (CtxEq.refl hΓ) (Der.cons hΓ hA) (Der.cons hΓ hA) (Der.reflT hA)

theorem CtxEq.symm {Γ Δ : Ctx} (h : CtxEq Γ Δ) : CtxEq Δ Γ := by
  induction h with
  | nil => exact CtxEq.nil
  | cons hΓΔ hA hB hAB ih => exact CtxEq.cons ih hB hA (Der.symmT (hAB.stab hΓΔ))

/-- Extending equal contexts by equal types. -/
theorem CtxEq.cons' {Γ Δ : Ctx} {A B : Tm} (h : CtxEq Γ Δ) (hAB : TyEq Γ A B) :
    CtxEq (A :: Γ) (B :: Δ) :=
  CtxEq.cons h (Der.cons h.wfL hAB.wfL) (Der.cons h.wfR (hAB.wfR.stab h)) hAB

/-- Extending equal contexts by one type. -/
theorem CtxEq.up {Γ Δ : Ctx} {A : Tm} (h : CtxEq Γ Δ) (hA : WfTy Γ A) : CtxEq (A :: Γ) (A :: Δ) :=
  h.cons' (Der.reflT hA)

theorem CtxEq.upNat {Γ Δ : Ctx} (h : CtxEq Γ Δ) : CtxEq (Tm.nat :: Γ) (Tm.nat :: Δ) :=
  h.up (Der.natT h.wfL)

/-! ### Stability of typed reduction -/

theorem TRed.stab {Γ Δ : Ctx} {t u A : Tm} (h : TRed Γ t u A) (hΓΔ : CtxEq Γ Δ) : TRed Δ t u A := by
  induction h generalizing Δ with
  | conv _ he ih => exact TRed.conv (ih hΓΔ) (he.stab hΓΔ)
  | appL _ ha ih => exact TRed.appL (ih hΓΔ) (ha.stab hΓΔ)
  | beta hA hb ha => exact TRed.beta (hA.stab hΓΔ) (hb.stab (hΓΔ.up hA)) (ha.stab hΓΔ)
  | natrecS hP hz hs _ ih =>
      exact TRed.natrecS (hP.stab hΓΔ.upNat) (hz.stab hΓΔ) (hs.stab (hΓΔ.upNat.up hP)) (ih hΓΔ)
  | natrecZero hP hz hs =>
      exact TRed.natrecZero (hP.stab hΓΔ.upNat) (hz.stab hΓΔ) (hs.stab (hΓΔ.upNat.up hP))
  | natrecSucc hP hz hs hn =>
      exact TRed.natrecSucc (hP.stab hΓΔ.upNat) (hz.stab hΓΔ) (hs.stab (hΓΔ.upNat.up hP))
        (hn.stab hΓΔ)
  | emptyrecS hP _ ih => exact TRed.emptyrecS (hP.stab hΓΔ) (ih hΓΔ)

theorem TReds.stab {Γ Δ : Ctx} {t u A : Tm} (h : TReds Γ t u A) (hΓΔ : CtxEq Γ Δ) :
    TReds Δ t u A := by
  induction h with
  | refl ht => exact TReds.refl (ht.stab hΓΔ)
  | step hs _ ih => exact TReds.step (hs.stab hΓΔ) ih

theorem TyReds.stab {Γ Δ : Ctx} {A B : Tm} (h : TyReds Γ A B) (hΓΔ : CtxEq Γ Δ) :
    TyReds Δ A B := by
  induction h with
  | refl hA => exact TyReds.refl (hA.stab hΓΔ)
  | step hs _ ih => exact TyReds.step (hs.stab hΓΔ) ih

/-! ### Stability of algorithmic conversion -/

/-- The stability statement of each algorithmic judgement. -/
def AJd.Stab : AJd → Prop
  | .neUp Γ k l A => ∀ {Δ : Ctx}, CtxEq Γ Δ → NeUp Δ k l A
  | .neDown Γ k l A => ∀ {Δ : Ctx}, CtxEq Γ Δ → NeDown Δ k l A
  | .tyUp Γ A B => ∀ {Δ : Ctx}, CtxEq Γ Δ → TyUp Δ A B
  | .tyDown Γ A B => ∀ {Δ : Ctx}, CtxEq Γ Δ → TyDown Δ A B
  | .tmUp Γ t u A => ∀ {Δ : Ctx}, CtxEq Γ Δ → TmUp Δ t u A
  | .tmDown Γ t u A => ∀ {Δ : Ctx}, CtxEq Γ Δ → TmDown Δ t u A

/-- **Stability**: algorithmic conversion transfers to an equal context. -/
theorem Alg.stab {J : AJd} (h : Alg J) : J.Stab := by
  induction h with
  | varRefl hv => intro Δ h; exact Alg.varRefl (hv.stab h)
  | appCong _ _ ihk iha => intro Δ h; exact Alg.appCong (ihk h) (iha h)
  | natrecCong hP _ _ _ ihP ihz ihs ihn =>
      intro Δ h
      exact Alg.natrecCong (ihP h.upNat) (ihz h) (ihs (h.upNat.up (TyUp.sound hP).wfL)) (ihn h)
  | emptyrecCong _ _ ihP ihe => intro Δ h; exact Alg.emptyrecCong (ihP h) (ihe h)
  | down _ hAB hB ih => intro Δ h; exact Alg.down (ih h) (hAB.stab h) hB
  | tyRed hA hB hA' hB' _ ih => intro Δ h; exact Alg.tyRed (hA.stab h) (hB.stab h) hA' hB' (ih h)
  | univRefl _ => intro Δ h; exact Alg.univRefl h.wfR
  | natRefl _ => intro Δ h; exact Alg.natRefl h.wfR
  | emptyRefl _ => intro Δ h; exact Alg.emptyRefl h.wfR
  | neTy _ ih => intro Δ h; exact Alg.neTy (ih h)
  | piCong hF _ ihF ihG => intro Δ h; exact Alg.piCong (ihF h) (ihG (h.up (TyUp.sound hF).wfL))
  | tmRed hAB ht hu hB ht' hu' _ ih =>
      intro Δ h
      exact Alg.tmRed (hAB.stab h) (ht.stab h) (hu.stab h) hB ht' hu' (ih h)
  | neNat _ ih => intro Δ h; exact Alg.neNat (ih h)
  | neEmpty _ ih => intro Δ h; exact Alg.neEmpty (ih h)
  | neNe hk hl hA _ ih => intro Δ h; exact Alg.neNe (hk.stab h) (hl.stab h) hA (ih h)
  | univTm hA hB _ ih => intro Δ h; exact Alg.univTm (hA.stab h) (hB.stab h) (ih h)
  | zeroRefl _ => intro Δ h; exact Alg.zeroRefl h.wfR
  | succCong _ ih => intro Δ h; exact Alg.succCong (ih h)
  | eta hf hg hnf hng _ ih =>
      intro Δ h
      exact Alg.eta (hf.stab h) (hg.stab h) hnf hng (ih (h.up hf.wfTy.pi_inv.1))

theorem NeUp.stab {Γ Δ : Ctx} {k l A : Tm} (h : NeUp Γ k l A) (hΓΔ : CtxEq Γ Δ) : NeUp Δ k l A :=
  Alg.stab h hΓΔ

theorem NeDown.stab {Γ Δ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) (hΓΔ : CtxEq Γ Δ) :
    NeDown Δ k l A :=
  Alg.stab h hΓΔ

theorem TyUp.stab {Γ Δ : Ctx} {A B : Tm} (h : TyUp Γ A B) (hΓΔ : CtxEq Γ Δ) : TyUp Δ A B :=
  Alg.stab h hΓΔ

theorem TyDown.stab {Γ Δ : Ctx} {A B : Tm} (h : TyDown Γ A B) (hΓΔ : CtxEq Γ Δ) : TyDown Δ A B :=
  Alg.stab h hΓΔ

theorem TmUp.stab {Γ Δ : Ctx} {t u A : Tm} (h : TmUp Γ t u A) (hΓΔ : CtxEq Γ Δ) :
    TmUp Δ t u A :=
  Alg.stab h hΓΔ

theorem TmDown.stab {Γ Δ : Ctx} {t u A : Tm} (h : TmDown Γ t u A) (hΓΔ : CtxEq Γ Δ) :
    TmDown Δ t u A :=
  Alg.stab h hΓΔ

/-! ### Conversion of the type -/

/-- The conversion statement of the term judgements. -/
def AJd.Conv : AJd → Prop
  | .tmUp Γ t u A => ∀ {B : Tm}, TyEq Γ A B → TmUp Γ t u B
  | .tmDown Γ t u A => ∀ {B : Tm}, TyEq Γ A B → Whnf B → TmDown Γ t u B
  | _ => True

/-- **Conversion**: algorithmically equal terms are algorithmically equal at every equal
type. -/
theorem Alg.conv {J : AJd} (h : Alg J) : J.Conv := by
  induction h with
  | tmRed hAB ht hu _ ht' hu' _ ih =>
      intro C hAC
      obtain ⟨C', hCC', hC'⟩ := hAC.wfR.whnf
      have hBC' := Der.transT (Der.symmT hAB.tyEq) (Der.transT hAC hCC'.tyEq)
      exact Alg.tmRed hCC' (ht.conv hBC') (hu.conv hBC') hC' ht' hu' (ih hBC' hC')
  | neNat hd =>
      intro C hC hCw
      rw [hC.nat_whnf hCw]
      exact Alg.neNat hd
  | neEmpty hd =>
      intro C hC hCw
      rw [hC.empty_whnf hCw]
      exact Alg.neEmpty hd
  | neNe hk hl hA hd =>
      intro C hC hCw
      exact Alg.neNe (Der.conv hk hC) (Der.conv hl hC) (hC.ne_whnf hA hCw) hd
  | univTm hA hB hd =>
      intro C hC hCw
      rw [hC.univ_whnf hCw]
      exact Alg.univTm hA hB hd
  | zeroRefl hΓ =>
      intro C hC hCw
      rw [hC.nat_whnf hCw]
      exact Alg.zeroRefl hΓ
  | succCong hd =>
      intro C hC hCw
      rw [hC.nat_whnf hCw]
      exact Alg.succCong hd
  | eta hf hg hnf hng _ ih =>
      intro C hC hCw
      obtain ⟨H, E', rfl, hFH, hGE⟩ := hC.pi_whnf hCw
      have hd := (ih hGE).stab ((CtxEq.refl hf.wf).cons' hFH)
      exact Alg.eta (Der.conv hf hC) (Der.conv hg hC) hnf hng hd
  | _ => trivial

theorem TmUp.conv {Γ : Ctx} {t u A B : Tm} (h : TmUp Γ t u A) (hAB : TyEq Γ A B) : TmUp Γ t u B :=
  Alg.conv h hAB

theorem TmDown.conv {Γ : Ctx} {t u A B : Tm} (h : TmDown Γ t u A) (hAB : TyEq Γ A B) (hB : Whnf B) :
    TmDown Γ t u B :=
  Alg.conv h hAB hB

/-! ### The type of the step of `natrec` -/

/-- Equal motives give equal types of the step. -/
theorem TyEq.stepTy {Γ : Ctx} {P P' : Tm} (h : TyEq (Tm.nat :: Γ) P P') :
    TyEq (P :: Tm.nat :: Γ) (stepTy P) (stepTy P') := by
  have hv := valid_stepTyEq (h.valid declEq) P
  have hwf : WfCtx (P :: Tm.nat :: Γ) := Der.cons h.wf h.wfL
  have hs := SubstR.idsOf hwf
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have := hI.escapeTyEq (hv.2.2 _ _ _ hs l I hI)
  simp only [subst_ids] at this
  exact this

end MLTT
