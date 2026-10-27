/-
**Martin-Löf type theory: the fundamental theorem, functions** — milestone M30
(`M30-MLTT-FUND`).

The validity of the rules of dependent functions: `valid_lam`, `valid_app`, `valid_appCong`,
`valid_beta`, `valid_eta`, `valid_piCongT`, `valid_piU`, `valid_piCongU`, with
`SubstR.ctxConv` / `ValidTy.ctxConv` (validity is stable under conversion of the last type of the
context).
-/

import Start.MLTTFundPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

variable {E : GenEq}

theorem rename_upr_id (t : Tm) : rename (upr id) t = t := by
  rw [rename_congr upr_id, rename_id]

theorem Wk.id {Δ : Ctx} (hΔ : WfCtx Δ) : Wk Δ Δ id := ⟨RenOk.id Δ, hΔ⟩

/-! ### Context conversion -/

theorem SubstR.ctxConv {Γ Δ : Ctx} {F H : Tm} (hΓ : ValidCtx E Γ) (hFH : ValidTyEq E Γ F H)
    {σ σ' : ℕ → Tm} (h : SubstR E (H :: Γ) Δ σ σ') : SubstR E (F :: Γ) Δ σ σ' := by
  obtain ⟨ht, l, J, hJ, hab⟩ := h
  obtain ⟨l', I, hI, -⟩ := hFH.1.red (ht.left hΓ)
  have hIH := hFH.2.2 Δ _ _ (ht.left hΓ) l' I hI
  exact ⟨ht, l', I, hI, (((TyR.good l' hI).conv hJ hIH) _ _).mpr hab⟩

theorem ValidTy.ctxConv {Γ : Ctx} {F H A : Tm} (hΓ : ValidCtx E Γ) (hFH : ValidTyEq E Γ F H)
    (h : ValidTy E (F :: Γ) A) : ValidTy E (H :: Γ) A := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, fun Δ σ σ' hs => hl Δ σ σ' (hs.ctxConv hΓ hFH)⟩

theorem ValidTyEq.ctxConv {Γ : Ctx} {F H A B : Tm} (hΓ : ValidCtx E Γ) (hFH : ValidTyEq E Γ F H)
    (h : ValidTyEq E (F :: Γ) A B) : ValidTyEq E (H :: Γ) A B :=
  ⟨h.1.ctxConv hΓ hFH, h.2.1.ctxConv hΓ hFH, fun Δ σ σ' hs => h.2.2 Δ σ σ' (hs.ctxConv hΓ hFH)⟩

/-! ### Shared facts at a substitution -/

/-- Extending a weakened pair of related substitutions by related arguments, through the domain
of a reducible product. -/
theorem SubstR.consWk {Γ Δ Δ' : Ctx} {F : Tm} {σ σ' : ℕ → Tm} {ρ : ℕ → ℕ} {l : ℕ} {IF : Interp}
    (hs : SubstR E Γ Δ σ σ') (hρ : Wk Δ Δ' ρ) (hF : TyR E l Δ' (rename ρ (subst σ F)) IF)
    {a a' : Tm} (haa : IF.tmEq a a') :
    SubstR E (F :: Γ) Δ' (scons a (fun n => rename ρ (σ n))) (scons a' (fun n => rename ρ (σ' n))) := by
  refine ⟨hs.wk hρ, l, IF, ?_, haa⟩
  rw [rename_subst] at hF
  exact hF

/-- The typing of a substituted body, from the validity of a term in an extended context. -/
theorem ValidTm.tyUp {Γ Δ : Ctx} {F b G : Tm} (hΓ : ValidCtx E Γ) (hF : ValidTy E Γ F)
    (hb : ValidTm E (F :: Γ) b G) {σ : ℕ → Tm} (hσ : SubstR E Γ Δ σ σ)
    (hwf : WfCtx (subst σ F :: Δ)) : HasTy (subst σ F :: Δ) (subst (up σ) b) (subst (up σ) G) := by
  have hup := SubstR.up hΓ hF hσ hwf
  obtain ⟨l, I, hI, h⟩ := hb.red hup
  exact (hI.escapeTm h).1

/-! ### Abstraction -/

/-- **Validity of abstraction.** -/
theorem valid_lam {Γ : Ctx} {F G b : Tm} (hΓ : ValidCtx E Γ) (hF : ValidTy E Γ F)
    (hb : ValidTm E (F :: Γ) b G) : ValidTm E Γ (lam b) (pi F G) := by
  have hPi := valid_piT hΓ hF hb.1
  refine ValidTm.intro hPi (fun Δ σ σ' hs => ?_)
  have hσ := hs.left hΓ
  have hσ' := hs.right hΓ
  obtain ⟨l, I, hI, hIeq⟩ := hPi.red hs
  refine ⟨l, I, hI, ?_⟩
  have hI' : TyR E l Δ (pi (subst σ F) (subst (up σ) G)) I := hI
  -- typings of the two abstractions
  obtain ⟨lF, IF₀, hIF₀, -⟩ := hF.red hσ
  obtain ⟨lF', IF₁, hIF₁, -⟩ := hF.red hσ'
  have hwf := Der.cons hs.wfCtx hIF₀.wfTy
  have hwf' := Der.cons hs.wfCtx hIF₁.wfTy
  have hbσ := hb.tyUp hΓ hF hσ hwf
  have hbσ' := hb.tyUp hΓ hF hσ' hwf'
  have hlam : HasTy Δ (lam (subst (up σ) b)) (pi (subst σ F) (subst (up σ) G)) :=
    Der.lam hIF₀.wfTy hbσ
  have hPiEq : TyEq Δ (pi (subst σ' F) (subst (up σ') G)) (pi (subst σ F) (subst (up σ) G)) :=
    Der.symmT (E.ty_eq (hI'.escapeTyEq hIeq))
  have hlam' : HasTy Δ (lam (subst (up σ') b)) (pi (subst σ F) (subst (up σ) G)) :=
    Der.conv (Der.lam hIF₁.wfTy hbσ') hPiEq
  refine PiTm.intro hI' (TRedsT.refl hlam) (TRedsT.refl hlam') (Whnf.lam _) (Whnf.lam _) ?_
  intro IF IG rF rG Δ' ρ a a' hρ haa
  have ha := (TyR.good l (rF Δ' ρ hρ)).left haa
  have hs₂ := hs.consWk hρ (rF Δ' ρ hρ) haa
  have eGa := rename_subst_up_inst ρ σ a G
  have eba := rename_subst_up_inst ρ σ a b
  have eba' := rename_subst_up_inst ρ σ' a' b
  have eGa' := rename_subst_up_inst ρ σ' a' G
  have hIG : TyR E l Δ' (subst (scons a fun n => rename ρ (σ n)) G) (IG Δ' ρ a) := by
    rw [← eGa]; exact rG Δ' ρ a hρ ha
  have hrel := hb.2 Δ' _ _ hs₂ l (IG Δ' ρ a) hIG
  obtain ⟨hl, hr, -⟩ := hIG.escapeTm hrel
  obtain ⟨hta, hta', -⟩ := (rF Δ' ρ hρ).escapeTm haa
  have hFρ := (rF Δ' ρ hρ).wfTy
  have hρF : RenOk (upr ρ) (subst σ F :: Δ) (rename ρ (subst σ F) :: Δ') := hρ.1.up _
  have hwfρ : WfCtx (rename ρ (subst σ F) :: Δ') := Der.cons hρ.2 hFρ
  -- the left β-step
  have hβ : TRed Δ' (app (rename ρ (lam (subst (up σ) b))) a)
      ((rename (upr ρ) (subst (up σ) b))[a]) ((rename (upr ρ) (subst (up σ) G))[a]) :=
    TRed.beta hFρ (hbσ.rename hρF hwfρ) hta
  rw [eba, eGa] at hβ
  -- the right β-step, at the converted type
  have hσ'F : TyEq Δ (subst σ' F) (subst σ F) := by
    obtain ⟨lFF, IFF, hIFF, hIFFeq⟩ := hF.red hs
    exact Der.symmT (E.ty_eq (hIFF.escapeTyEq hIFFeq))
  have hFρ' : WfTy Δ' (rename ρ (subst σ' F)) := hIF₁.wfTy.rename hρ.1 hρ.2
  have hta'' : HasTy Δ' a' (rename ρ (subst σ' F)) :=
    Der.conv hta' (Der.symmT (hσ'F.rename hρ.1 hρ.2))
  have hρF' : RenOk (upr ρ) (subst σ' F :: Δ) (rename ρ (subst σ' F) :: Δ') := hρ.1.up _
  have hβ' : TRed Δ' (app (rename ρ (lam (subst (up σ') b))) a')
      ((rename (upr ρ) (subst (up σ') b))[a']) ((rename (upr ρ) (subst (up σ') G))[a']) :=
    TRed.beta hFρ' (hbσ'.rename hρF' (Der.cons hρ.2 hFρ')) hta''
  rw [eba', eGa'] at hβ'
  have hGeq : TyEq Δ' (subst (scons a' fun n => rename ρ (σ' n)) G)
      (subst (scons a fun n => rename ρ (σ n)) G) := by
    obtain ⟨lG, IGG, hIGG, hIGGeq⟩ := hb.1.red hs₂
    exact Der.symmT (E.ty_eq (hIGG.escapeTyEq hIGGeq))
  have hred : TRedsT Δ' (app (rename ρ (lam (subst (up σ) b))) a)
      (subst (scons a fun n => rename ρ (σ n)) b) (subst (scons a fun n => rename ρ (σ n)) G) :=
    ⟨hβ.tyLeft, hl, TReds.step hβ (TReds.refl hl)⟩
  have hred' : TRedsT Δ' (app (rename ρ (lam (subst (up σ') b))) a')
      (subst (scons a' fun n => rename ρ (σ' n)) b) (subst (scons a fun n => rename ρ (σ n)) G) :=
    ⟨Der.conv hβ'.tyLeft hGeq, hr, TReds.step (TRed.conv hβ' hGeq) (TReds.refl hr)⟩
  have h₁ := hIG.expandTm hred hrel
  exact hIG.expandTm' hred' h₁

theorem ValidTm.ctxConv {Γ : Ctx} {F H t A : Tm} (hΓ : ValidCtx E Γ) (hFH : ValidTyEq E Γ F H)
    (h : ValidTm E (F :: Γ) t A) : ValidTm E (H :: Γ) t A :=
  ⟨h.1.ctxConv hΓ hFH, fun Δ σ σ' hs => h.2 Δ σ σ' (hs.ctxConv hΓ hFH)⟩

theorem ValidEq.ctxConv {Γ : Ctx} {F H t u A : Tm} (hΓ : ValidCtx E Γ) (hFH : ValidTyEq E Γ F H)
    (h : ValidEq E (F :: Γ) t u A) : ValidEq E (H :: Γ) t u A :=
  ⟨h.1.ctxConv hΓ hFH, h.2.1.ctxConv hΓ hFH, fun Δ σ σ' hs => h.2.2 Δ σ σ' (hs.ctxConv hΓ hFH)⟩

/-! ### Application -/

/-- The core of application: related functions applied to related arguments. -/
theorem app_rel {Δ : Ctx} {F G f g a b : Tm} {l : ℕ} {I : Interp}
    (hI : TyR E l Δ (pi F G) I) (hfg : I.tmEq f g) {lF : ℕ} {IF₀ : Interp}
    (hF₀ : TyR E lF Δ F IF₀) (hab : IF₀.tmEq a b) :
    ∃ J, TyR E l Δ (G[a]) J ∧ J.tyEq (G[b]) ∧ J.tmEq (app f a) (app g b) := by
  obtain ⟨IF, IG, hF, hG, hPi, rF, rG, extG, -, htm⟩ := hI.pi_inv
  have hΔ := hF.wf
  have hFid : TyR E l Δ F (IF Δ id) := by
    have := rF Δ id (Wk.id hΔ); rwa [rename_id] at this
  have hab' : (IF Δ id).tmEq a b := ((TyR.irrel hF₀ hFid).2 _ _).mp hab
  have ha := (TyR.good l hFid).left hab'
  have hb := (TyR.good l hFid).right hab'
  have hGa : TyR E l Δ (G[a]) (IG Δ id a) := by
    have := rG Δ id a (Wk.id hΔ) (by simpa using ha); rwa [rename_upr_id] at this
  have hGb : (IG Δ id a).tyEq (G[b]) := by
    have := extG Δ id a b (Wk.id hΔ) (by simpa using ha) (by simpa using hb) (by simpa using hab')
    rwa [rename_upr_id] at this
  refine ⟨IG Δ id a, hGa, hGb, ?_⟩
  obtain ⟨f', g', hf', hg', hnf, hng, -, happ⟩ := (htm f g).mp hfg
  have h₁ := happ Δ id a b (Wk.id hΔ) (by simpa using hab')
  simp only [rename_id] at h₁
  obtain ⟨hta, htb, -⟩ := hFid.escapeTm hab'
  have hGab : TyEq Δ (G[b]) (G[a]) := Der.symmT (E.ty_eq (hGa.escapeTyEq hGb))
  have hred : TRedsT Δ (app f a) (app f' a) (G[a]) := hf'.appL hta
  have hred' : TRedsT Δ (app g b) (app g' b) (G[a]) := (hg'.appL htb).conv hGab
  exact hGa.expandTm' hred' (hGa.expandTm hred h₁)

/-- The codomain of a reducible product at related arguments, against a reducibly equal product. -/
theorem codom_rel {Δ : Ctx} {F G F' G' a b : Tm} {l : ℕ} {I : Interp}
    (hI : TyR E l Δ (pi F G) I) (hIeq : I.tyEq (pi F' G')) {lF : ℕ} {IF₀ : Interp}
    (hF₀ : TyR E lF Δ F IF₀) (hab : IF₀.tmEq a b) :
    ∃ J, TyR E l Δ (G[a]) J ∧ J.tyEq (G'[b]) := by
  obtain ⟨IF, IG, hF, hG, hPi, rF, rG, extG, hty, -⟩ := hI.pi_inv
  have hΔ := hF.wf
  have hFid : TyR E l Δ F (IF Δ id) := by
    have := rF Δ id (Wk.id hΔ); rwa [rename_id] at this
  have hab' : (IF Δ id).tmEq a b := ((TyR.irrel hF₀ hFid).2 _ _).mp hab
  have ha := (TyR.good l hFid).left hab'
  have hb := (TyR.good l hFid).right hab'
  have hGa : TyR E l Δ (G[a]) (IG Δ id a) := by
    have := rG Δ id a (Wk.id hΔ) (by simpa using ha); rwa [rename_upr_id] at this
  have hGb : TyR E l Δ (G[b]) (IG Δ id b) := by
    have := rG Δ id b (Wk.id hΔ) (by simpa using hb); rwa [rename_upr_id] at this
  have hGab : (IG Δ id a).tyEq (G[b]) := by
    have := extG Δ id a b (Wk.id hΔ) (by simpa using ha) (by simpa using hb) (by simpa using hab')
    rwa [rename_upr_id] at this
  obtain ⟨F'', G'', DB, -, -, hcod⟩ := (hty _).mp hIeq
  have e := DB.red.of_whnf (Whnf.pi _ _)
  simp only [pi.injEq] at e
  rw [e.2] at hcod
  have hcod' : (IG Δ id b).tyEq (G'[b]) := by
    have := hcod Δ id b (Wk.id hΔ) (by simpa using hb); rwa [rename_upr_id] at this
  exact ⟨IG Δ id a, hGa, (TyR.good l hGa).tyTrans hGb hGab hcod'⟩

/-- **The instances of a codomain at valid equal arguments are valid equal types.** -/
theorem valid_instTyEq {Γ : Ctx} {F G a b : Tm} (hPi : ValidTy E Γ (pi F G))
    (hab : ValidEq E Γ a b F) : ValidTyEq E Γ (G[a]) (G[b]) := by
  obtain ⟨l, hl⟩ := hPi
  have key : ∀ {c d : Tm}, (∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∀ lF IF₀, TyR E lF Δ (subst σ F) IF₀ →
      IF₀.tmEq (subst σ c) (subst σ' d)) → ∀ Δ σ σ', SubstR E Γ Δ σ σ' →
      ∃ J, TyR E l Δ (subst σ (G[c])) J ∧ J.tyEq (subst σ' (G[d])) := by
    intro c d hcd Δ σ σ' hs
    obtain ⟨I, hI, hIeq⟩ := hl Δ σ σ' hs
    obtain ⟨lF, IF₀, hF₀, -⟩ := hab.1.1.red hs
    rw [subst_inst, subst_inst]
    exact codom_rel hI hIeq hF₀ (hcd Δ σ σ' hs lF IF₀ hF₀)
  refine ValidTyEq.intro ⟨l, key hab.1.2⟩ ⟨l, key hab.2.1.2⟩ (fun Δ σ σ' hs => ?_)
  obtain ⟨J, hJ, hJeq⟩ := key hab.2.2 Δ σ σ' hs
  exact ⟨l, J, hJ, hJeq⟩

theorem valid_instTy {Γ : Ctx} {F G a : Tm} (hPi : ValidTy E Γ (pi F G)) (ha : ValidTm E Γ a F) :
    ValidTy E Γ (G[a]) :=
  (valid_instTyEq hPi (valid_refl ha)).1

/-- **Validity of application, with congruence.** -/
theorem valid_appCong {Γ : Ctx} {f g a b F G : Tm} (hΓ : ValidCtx E Γ)
    (hfg : ValidEq E Γ f g (pi F G)) (hab : ValidEq E Γ a b F) :
    ValidEq E Γ (app f a) (app g b) (G[a]) := by
  have hPi := hfg.1.1
  have core : ∀ {f g a b : Tm}, ValidEq E Γ f g (pi F G) → ValidEq E Γ a b F →
      ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l J, TyR E l Δ (subst σ (G[a])) J ∧
        J.tmEq (subst σ (app f a)) (subst σ' (app g b)) := by
    intro f g a b hfg hab Δ σ σ' hs
    obtain ⟨l, I, hI, -⟩ := hPi.red hs
    have hI' : TyR E l Δ (pi (subst σ F) (subst (up σ) G)) I := hI
    obtain ⟨lF, IF₀, hF₀, -⟩ := hab.1.1.red hs
    obtain ⟨J, hJ, -, hJtm⟩ := app_rel hI' (hfg.2.2 Δ σ σ' hs l I hI) hF₀
      (hab.2.2 Δ σ σ' hs lF IF₀ hF₀)
    refine ⟨l, J, ?_, hJtm⟩
    rw [subst_inst]; exact hJ
  have hTa : ValidTy E Γ (G[a]) := valid_instTy hPi hab.1
  have hfa : ValidTm E Γ (app f a) (G[a]) :=
    ValidTm.intro hTa (core (valid_refl hfg.1) (valid_refl hab.1))
  have hgb : ValidTm E Γ (app g b) (G[a]) := by
    have hgb' : ValidTm E Γ (app g b) (G[b]) :=
      ValidTm.intro (valid_instTy hPi hab.2.1) (fun Δ σ σ' hs => by
        have := core (valid_refl hfg.2.1) (valid_refl hab.2.1) Δ σ σ' hs
        exact this)
    exact valid_conv hΓ hgb' (valid_symmT hΓ (valid_instTyEq hPi hab))
  exact ValidEq.intro hfa hgb (core hfg hab)

theorem valid_app {Γ : Ctx} {f a F G : Tm} (hΓ : ValidCtx E Γ) (hf : ValidTm E Γ f (pi F G))
    (ha : ValidTm E Γ a F) : ValidTm E Γ (app f a) (G[a]) :=
  (valid_appCong hΓ (valid_refl hf) (valid_refl ha)).1

/-! ### β and η -/

/-- **Validity of β.** -/
theorem valid_beta {Γ : Ctx} {F G b a : Tm} (hΓ : ValidCtx E Γ) (hF : ValidTy E Γ F)
    (hb : ValidTm E (F :: Γ) b G) (ha : ValidTm E Γ a F) :
    ValidEq E Γ (app (lam b) a) (b[a]) (G[a]) := by
  have hPi := valid_piT hΓ hF hb.1
  have hlam := valid_lam hΓ hF hb
  have hTa := valid_instTy hPi ha
  have core : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l J, TyR E l Δ (subst σ (G[a])) J ∧
      J.tmEq (subst (scons (subst σ a) σ) b) (subst (scons (subst σ' a) σ') b) := by
    intro Δ σ σ' hs
    obtain ⟨lF, IF₀, hF₀, -⟩ := hF.red hs
    have hs₂ : SubstR E (F :: Γ) Δ (scons (subst σ a) σ) (scons (subst σ' a) σ') :=
      ⟨hs, lF, IF₀, hF₀, ha.2 Δ σ σ' hs lF IF₀ hF₀⟩
    obtain ⟨l, J, hJ, hJb⟩ := hb.red hs₂
    refine ⟨l, J, ?_, hJb⟩
    rw [subst_inst_scons]; exact hJ
  refine ValidEq.intro (valid_app hΓ hlam ha) (ValidTm.intro hTa (fun Δ σ σ' hs => ?_))
    (fun Δ σ σ' hs => ?_)
  · obtain ⟨l, J, hJ, hJb⟩ := core Δ σ σ' hs
    refine ⟨l, J, hJ, ?_⟩
    rw [subst_inst_scons, subst_inst_scons]; exact hJb
  · obtain ⟨l, J, hJ, hJb⟩ := core Δ σ σ' hs
    refine ⟨l, J, hJ, ?_⟩
    have hσ := hs.left hΓ
    obtain ⟨lF, IF₀, hF₀, -⟩ := hF.red hσ
    have hwf := Der.cons hs.wfCtx hF₀.wfTy
    have hbσ := hb.tyUp hΓ hF hσ hwf
    obtain ⟨hta, -, -⟩ := hF₀.escapeTm (ha.2 Δ σ σ hσ lF IF₀ hF₀)
    have hβ : TRed Δ (app (lam (subst (up σ) b)) (subst σ a)) ((subst (up σ) b)[subst σ a])
        ((subst (up σ) G)[subst σ a]) := TRed.beta hF₀.wfTy hbσ hta
    rw [subst_up_inst, subst_up_inst] at hβ
    have hJ' : TyR E l Δ (subst (scons (subst σ a) σ) G) J := by
      rw [← subst_inst_scons]; exact hJ
    obtain ⟨hl, -, -⟩ := hJ'.escapeTm hJb
    have hred : TRedsT Δ (app (lam (subst (up σ) b)) (subst σ a))
        (subst (scons (subst σ a) σ) b) (subst (scons (subst σ a) σ) G) :=
      ⟨hβ.tyLeft, hl, TReds.step hβ (TReds.refl hl)⟩
    have h₁ := hJ'.expandTm hred hJb
    rw [subst_inst_scons]
    exact h₁

/-- **Validity of the extensionality rule (η).** -/
theorem valid_eta {Γ : Ctx} {f g F G : Tm} (hΓ : ValidCtx E Γ) (hf : ValidTm E Γ f (pi F G))
    (hg : ValidTm E Γ g (pi F G))
    (he : ValidEq E (F :: Γ) (app (shift f) (var 0)) (app (shift g) (var 0)) G) :
    ValidEq E Γ f g (pi F G) := by
  refine ValidEq.intro hf hg (fun Δ σ σ' hs => ?_)
  obtain ⟨l, I, hI, -⟩ := hf.1.red hs
  have hI' : TyR E l Δ (pi (subst σ F) (subst (up σ) G)) I := hI
  refine ⟨l, I, hI, ?_⟩
  obtain ⟨IF, IG, -, -, -, rF, rG, -, -, htm⟩ := hI'.pi_inv
  obtain ⟨f₁, f₂, hf₁, -, hnf₁, -, -, -⟩ := (htm _ _).mp (hf.2 Δ σ σ' hs l I hI)
  obtain ⟨g₁, g₂, -, hg₂, -, hng₂, -, -⟩ := (htm _ _).mp (hg.2 Δ σ σ' hs l I hI)
  refine PiTm.intro hI' hf₁ hg₂ hnf₁ hng₂ ?_
  intro IF' IG' rF' rG' Δ' ρ a a' hρ haa
  have hgood := TyR.good l (rF' Δ' ρ hρ)
  have ha := hgood.left haa
  have hs₂ := hs.consWk hρ (rF' Δ' ρ hρ) haa
  have hs₃ := (hs.left hΓ).consWk hρ (rF' Δ' ρ hρ) haa
  have eGa := rename_subst_up_inst ρ σ a G
  have eGa' := rename_subst_up_inst ρ σ a' G
  have hIG : TyR E l Δ' (subst (scons a fun n => rename ρ (σ n)) G) (IG' Δ' ρ a) := by
    rw [← eGa]; exact rG' Δ' ρ a hρ ha
  have hrel := he.2.2 Δ' _ _ hs₂ l (IG' Δ' ρ a) hIG
  rw [subst_shift_app_var0, subst_shift_app_var0, ← rename_subst, ← rename_subst] at hrel
  obtain ⟨hta, hta', -⟩ := (rF' Δ' ρ hρ).escapeTm haa
  have hpiρ : ∀ {t t' : Tm}, TRedsT Δ t t' (pi (subst σ F) (subst (up σ) G)) →
      TRedsT Δ' (rename ρ t) (rename ρ t')
        (pi (rename ρ (subst σ F)) (rename (upr ρ) (subst (up σ) G))) :=
    fun h => h.rename hρ.1 hρ.2
  have hredL : TRedsT Δ' (app (rename ρ (subst σ f)) a) (app (rename ρ f₁) a)
      (subst (scons a fun n => rename ρ (σ n)) G) := by
    rw [← eGa]; exact (hpiρ hf₁).appL hta
  have hGeq : TyEq Δ' (subst (scons a' fun n => rename ρ (σ n)) G)
      (subst (scons a fun n => rename ρ (σ n)) G) := by
    obtain ⟨lG, K, hK, hKeq⟩ := he.1.1.red hs₃
    exact Der.symmT (E.ty_eq (hK.escapeTyEq hKeq))
  have hredR : TRedsT Δ' (app (rename ρ (subst σ' g)) a') (app (rename ρ g₂) a')
      (subst (scons a fun n => rename ρ (σ n)) G) := by
    have := (hpiρ hg₂).appL hta'
    rw [eGa'] at this
    exact this.conv hGeq
  have g₂good := TyR.good l hIG
  have h₁ := hIG.reduceTm hredL hrel
  have h₂ := hIG.reduceTm hredR (g₂good.symm h₁)
  exact g₂good.symm h₂

/-! ### Products as types and as terms of universes -/

/-- **Validity of the congruence for products (types).** -/
theorem valid_piCongT {Γ : Ctx} {F H G E' : Tm} (hΓ : ValidCtx E Γ) (hF : ValidTy E Γ F)
    (hFH : ValidTyEq E Γ F H) (hGE : ValidTyEq E (F :: Γ) G E') :
    ValidTyEq E Γ (pi F G) (pi H E') := by
  have hPi := valid_piT hΓ hF hGE.1
  have hPi' := valid_piT hΓ hFH.2.1 (hGE.2.1.ctxConv hΓ hFH)
  refine ValidTyEq.intro hPi hPi' (fun Δ σ σ' hs => ?_)
  obtain ⟨l, I, hI, -⟩ := hPi.red hs
  have hI' : TyR E l Δ (pi (subst σ F) (subst (up σ) G)) I := hI
  refine ⟨l, I, hI, ?_⟩
  obtain ⟨IF, IG, hFw, -, -, rF, rG, -, hty, -⟩ := hI'.pi_inv
  obtain ⟨l₂, I₂, hI₂, -⟩ := hPi'.red (hs.right hΓ)
  refine (hty _).mpr ⟨subst σ' H, subst (up σ') E', TyRedsT.refl hI₂.wfTy, ?_, ?_, ?_⟩
  · obtain ⟨lF, IF₀, hF₀, -⟩ := hF.red hs
    have hFH' := hFH.2.2 Δ σ σ' hs lF IF₀ hF₀
    have hup := SubstR.up hΓ hF hs (Der.cons hs.wfCtx hFw)
    obtain ⟨lG, IG₀, hG₀, -⟩ := hGE.1.red hup
    have hGE' := hGE.2.2 _ _ _ hup lG IG₀ hG₀
    exact E.pi_cong hFw (hF₀.escapeTyEq hFH') (hG₀.escapeTyEq hGE')
  · intro Δ' ρ hρ
    have hrF := rF Δ' ρ hρ
    rw [rename_subst] at hrF
    have := hFH.2.2 Δ' _ _ (hs.wk hρ) l (IF Δ' ρ) hrF
    rw [rename_subst]; exact this
  · intro Δ' ρ a hρ ha
    have hs₂ := hs.consWk hρ (rF Δ' ρ hρ) ha
    have hrG := rG Δ' ρ a hρ ha
    rw [rename_subst_up_inst] at hrG
    have := hGE.2.2 Δ' _ _ hs₂ l (IG Δ' ρ a) hrG
    rw [rename_subst_up_inst]; exact this

/-- **Validity of the congruence for products in a universe.** -/
theorem valid_piCongU {Γ : Ctx} {F H G E' : Tm} {i j : ℕ} (hΓ : ValidCtx E Γ)
    (hF : ValidTm E Γ F (univ i)) (hFH : ValidEq E Γ F H (univ i))
    (hGE : ValidEq E (F :: Γ) G E' (univ j)) :
    ValidEq E Γ (pi F G) (pi H E') (univ (max i j)) := by
  have hFt := valid_el hF
  have hHt := valid_el hFH.2.1
  have hFHt := valid_elEq hFH
  have hE'H : ValidTm E (H :: Γ) E' (univ j) := hGE.2.1.ctxConv hΓ hFHt
  have hPiCong := valid_piCongT hΓ hFt hFHt (valid_elEq hGE)
  -- a related pair of products in the universe
  have core : ∀ {F₁ H₁ G₁ E₁ : Tm}, ValidTm E Γ F₁ (univ i) → ValidEq E Γ F₁ H₁ (univ i) →
      ValidEq E (F₁ :: Γ) G₁ E₁ (univ j) → ValidTm E (H₁ :: Γ) E₁ (univ j) →
      ValidTyEq E Γ (pi F₁ G₁) (pi H₁ E₁) →
      ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l I, TyR E l Δ (subst σ (univ (max i j))) I ∧
        I.tmEq (subst σ (pi F₁ G₁)) (subst σ' (pi H₁ E₁)) := by
    intro F₁ H₁ G₁ E₁ hF₁ hFH₁ hGE₁ hE₁ hPC Δ σ σ' hs
    have hΔ := hs.wfCtx
    have hσ := hs.left hΓ
    have hσ' := hs.right hΓ
    have hF₁t := valid_el hF₁
    have hH₁t := valid_el hFH₁.2.1
    have hUi := TyR.univ_canon (E := E) hΔ (Nat.lt_succ_self i)
    have hUj : ∀ {Δ' : Ctx}, WfCtx Δ' → TyR E (j + 1) Δ' (univ j) (univI E Δ' j) :=
      fun h => TyR.univ_canon h (Nat.lt_succ_self j)
    -- the domains
    obtain ⟨hσF, -, -⟩ := hUi.escapeTm (hF₁.2 Δ σ σ hσ (i + 1) _ hUi)
    obtain ⟨hσ'H, -, -⟩ := hUi.escapeTm (hFH₁.2.1.2 Δ σ' σ' hσ' (i + 1) _ hUi)
    obtain ⟨-, -, hFH'⟩ := hUi.escapeTm (hFH₁.2.2 Δ σ σ' hs (i + 1) _ hUi)
    -- the codomains
    have hwf := Der.cons hΔ (Der.el hσF)
    have hwf' := Der.cons hΔ (Der.el hσ'H)
    have hupσ := SubstR.up hΓ hF₁t hσ hwf
    have hup := SubstR.up hΓ hF₁t hs hwf
    have hupσ' := SubstR.up hΓ hH₁t hσ' hwf'
    obtain ⟨hσG, -, -⟩ := (hUj hwf).escapeTm (hGE₁.1.2 _ _ _ hupσ (j + 1) _ (hUj hwf))
    obtain ⟨hσ'E, -, -⟩ := (hUj hwf').escapeTm (hE₁.2 _ _ _ hupσ' (j + 1) _ (hUj hwf'))
    obtain ⟨-, -, hGE'⟩ := (hUj hwf).escapeTm (hGE₁.2.2 _ _ _ hup (j + 1) _ (hUj hwf))
    have hP := Der.piU hσF hσG
    have hP' := Der.piU hσ'H hσ'E
    -- the reducibility of the two products
    obtain ⟨I, hI, -⟩ := valid_piT_at hΓ (valid_el_at hF₁) (valid_el_at hGE₁.1) hσ
    obtain ⟨J, hJ, -⟩ := valid_piT_at hΓ (valid_el_at hFH₁.2.1) (valid_el_at hE₁) hσ'
    refine ⟨max i j + 1, univI E Δ (max i j), TyR.univ_canon hΔ (Nat.lt_succ_self _), ?_⟩
    exact ⟨_, _, TRedsT.refl hP, TRedsT.refl hP', Whnf.pi _ _, Whnf.pi _ _,
      E.piU_cong hσF hFH' hGE', ⟨I, hI, hPC.2.2 Δ σ σ' hs _ I hI⟩, ⟨J, hJ⟩⟩
  have hFF := valid_refl hF
  have hHH := valid_refl hFH.2.1
  have hGG := valid_refl hGE.1
  have hEE := valid_refl hE'H
  have hPiFF : ValidTyEq E Γ (pi F G) (pi F G) := valid_reflT (valid_piT hΓ hFt (valid_el hGE.1))
  have hPiHH : ValidTyEq E Γ (pi H E') (pi H E') := valid_reflT (valid_piT hΓ hHt (valid_el hE'H))
  exact ValidEq.intro
    (ValidTm.intro (valid_univT (max i j)) (core hF hFF hGG hGE.1 hPiFF))
    (ValidTm.intro (valid_univT (max i j)) (core hFH.2.1 hHH hEE hE'H hPiHH))
    (core hF hFH hGE hE'H hPiCong)

theorem valid_piU {Γ : Ctx} {F G : Tm} {i j : ℕ} (hΓ : ValidCtx E Γ)
    (hF : ValidTm E Γ F (univ i)) (hG : ValidTm E (F :: Γ) G (univ j)) :
    ValidTm E Γ (pi F G) (univ (max i j)) :=
  (valid_piCongU hΓ hF (valid_refl hF) (valid_refl hG)).1

end MLTT
