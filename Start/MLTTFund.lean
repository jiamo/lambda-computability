/-
**Martin-Löf type theory: the fundamental theorem** — milestone M30 (`M30-MLTT-FUND`).

Every derivable judgement of `MLTT.Der` is valid, for every generic equality: well-formed
contexts are valid, well-formed types are reducible under related substitutions, typable terms
are reducibly equal to themselves, and derivable equations are reducibly true.  One induction on
the derivation, each rule discharged by its validity lemma (`Start/MLTTFundBasic.lean`,
`Start/MLTTFundPi.lean`, `Start/MLTTFundPiIntro.lean`, `Start/MLTTFundNat.lean`).

* `MLTT.Jd.Valid` — the semantic counterpart of each judgement form;
* **`MLTT.Der.valid`** — the fundamental theorem.
-/

import Start.MLTTFundNat

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-- The validity of each judgement form. -/
def Jd.Valid (E : GenEq) : Jd → Prop
  | .wf Γ => ValidCtx E Γ
  | .tyWf Γ A => ValidCtx E Γ ∧ ValidTy E Γ A
  | .ty Γ t A => ValidCtx E Γ ∧ ValidTm E Γ t A
  | .tyEq Γ A B => ValidCtx E Γ ∧ ValidTyEq E Γ A B
  | .eq Γ t u A => ValidCtx E Γ ∧ ValidEq E Γ t u A

/-- **The fundamental theorem**: every derivable judgement is valid. -/
theorem Der.valid (E : GenEq) {J : Jd} (h : Der J) : J.Valid E := by
  induction h with
  | nil => trivial
  | cons _ _ ihΓ ihA => exact ⟨ihΓ, ihA.2⟩
  | univT l _ ih => exact ⟨ih, valid_univT l⟩
  | natT _ ih => exact ⟨ih, valid_natT⟩
  | emptyT _ ih => exact ⟨ih, valid_emptyT⟩
  | piT _ _ ihF ihG => exact ⟨ihF.1, valid_piT ihF.1 ihF.2 ihG.2⟩
  | el _ ih => exact ⟨ih.1, valid_el ih.2⟩
  | var _ hl ih => exact ⟨ih, valid_var ih hl⟩
  | univU l _ ih => exact ⟨ih, valid_univU l⟩
  | natU _ ih => exact ⟨ih, valid_natU⟩
  | emptyU _ ih => exact ⟨ih, valid_emptyU⟩
  | piU _ _ ihF ihG => exact ⟨ihF.1, valid_piU ihF.1 ihF.2 ihG.2⟩
  | lam _ _ ihF ihb => exact ⟨ihF.1, valid_lam ihF.1 ihF.2 ihb.2⟩
  | app _ _ ihf iha => exact ⟨ihf.1, valid_app ihf.1 ihf.2 iha.2⟩
  | zero _ ih => exact ⟨ih, valid_zero⟩
  | succ _ ih => exact ⟨ih.1, valid_succ ih.2⟩
  | natrec _ _ _ _ ihP ihz ihs ihn => exact ⟨ihz.1, valid_natrec ihz.1 ihP.2 ihz.2 ihs.2 ihn.2⟩
  | emptyrec _ _ ihP ihe => exact ⟨ihP.1, valid_emptyrec ihP.1 ihP.2 ihe.2⟩
  | conv _ _ iht ihe => exact ⟨iht.1, valid_conv iht.1 iht.2 ihe.2⟩
  | reflT _ ih => exact ⟨ih.1, valid_reflT ih.2⟩
  | symmT _ ih => exact ⟨ih.1, valid_symmT ih.1 ih.2⟩
  | transT _ _ ih₁ ih₂ => exact ⟨ih₁.1, valid_transT ih₁.1 ih₁.2 ih₂.2⟩
  | piCongT _ _ _ ihF ihFH ihGE => exact ⟨ihF.1, valid_piCongT ihF.1 ihF.2 ihFH.2 ihGE.2⟩
  | elEq _ ih => exact ⟨ih.1, valid_elEq ih.2⟩
  | refl _ ih => exact ⟨ih.1, valid_refl ih.2⟩
  | symm _ ih => exact ⟨ih.1, valid_symm ih.1 ih.2⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, valid_trans ih₁.1 ih₁.2 ih₂.2⟩
  | eqConv _ _ ih₁ ih₂ => exact ⟨ih₁.1, valid_eqConv ih₁.1 ih₁.2 ih₂.2⟩
  | piCongU _ _ _ ihF ihFH ihGE => exact ⟨ihF.1, valid_piCongU ihF.1 ihF.2 ihFH.2 ihGE.2⟩
  | appCong _ _ ihf iha => exact ⟨ihf.1, valid_appCong ihf.1 ihf.2 iha.2⟩
  | succCong _ ih => exact ⟨ih.1, valid_succCong ih.2⟩
  | natrecCong _ _ _ _ _ ihP ihPP ihz ihs ihn =>
      exact ⟨ihz.1, valid_natrecCong ihz.1 ihP.2 ihPP.2 ihz.2 ihs.2 ihn.2⟩
  | emptyrecCong _ _ ihP ihe => exact ⟨ihe.1, valid_emptyrecCong ihe.1 ihP.2 ihe.2⟩
  | beta _ _ _ ihF ihb iha => exact ⟨ihF.1, valid_beta ihF.1 ihF.2 ihb.2 iha.2⟩
  | eta _ _ _ _ ihF ihf ihg ihe => exact ⟨ihF.1, valid_eta ihF.1 ihf.2 ihg.2 ihe.2⟩
  | natrecZero _ _ _ ihP ihz ihs => exact ⟨ihz.1, valid_natrecZero ihz.1 ihP.2 ihz.2 ihs.2⟩
  | natrecSucc _ _ _ _ ihP ihz ihs ihn =>
      exact ⟨ihz.1, valid_natrecSucc ihz.1 ihP.2 ihz.2 ihs.2 ihn.2⟩

theorem WfCtx.valid (E : GenEq) {Γ : Ctx} (h : WfCtx Γ) : ValidCtx E Γ := Der.valid E h

theorem WfTy.valid (E : GenEq) {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : ValidTy E Γ A :=
  (Der.valid E h).2

theorem HasTy.valid (E : GenEq) {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : ValidTm E Γ t A :=
  (Der.valid E h).2

theorem TyEq.valid (E : GenEq) {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : ValidTyEq E Γ A B :=
  (Der.valid E h).2

theorem DEq.valid (E : GenEq) {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) : ValidEq E Γ t u A :=
  (Der.valid E h).2

end MLTT
