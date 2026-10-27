/-
**Martin-Löf type theory: completeness of algorithmic conversion** — milestone M30
(`M30-MLTT-ALG`).

* `MLTT.TyR.liftNe` — **lifting**: algorithmically equal neutral terms are algorithmically equal
  terms at every reducible type equal to their inferred type, by η-expansion along the
  reducibility proof of the type (at a product, the variable is lifted at the domain and the
  applications at the codomain);
* `MLTT.algEq` — **the algorithmic generic equality**: `TyUp`, `TmUp`, and neutral comparison up
  to type equality (`NeAt`), with every property the logical relation needs (soundness,
  symmetry, transitivity, conversion, weakening, closure under weak head reduction, the
  congruences, η);
* `MLTT.TyEq.alg`, `MLTT.DEq.alg` — **completeness**: by the fundamental theorem
  (`MLTT.Der.valid`) instantiated at `algEq`, judgementally equal types and terms are
  algorithmically equal;
* `MLTT.TyEq.iff_alg`, `MLTT.DEq.iff_alg` — the declarative and the algorithmic equalities
  coincide.
-/

import Start.MLTTAlgTrans

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Neutral comparison at a type -/

/-- Reducing the inferred type of a neutral comparison to a weak head normal form. -/
theorem NeUp.toDown {Γ : Ctx} {k m B C : Tm} (h : NeUp Γ k m B) (hBC : TyEq Γ B C) :
    ∃ C', NeDown Γ k m C' ∧ TyEq Γ C' C := by
  obtain ⟨C', hr, hn⟩ := hBC.wfL.whnf
  exact ⟨C', Alg.down h hr hn, Der.transT (Der.symmT hr.tyEq) hBC⟩

/-- Algorithmic equality of neutral terms at the type `A`: their inferred type equals `A`. -/
def NeAt (Γ : Ctx) (k l A : Tm) : Prop := ∃ B, TyEq Γ A B ∧ NeUp Γ k l B

theorem NeAt.sound {Γ : Ctx} {k l A : Tm} (h : NeAt Γ k l A) : DEq Γ k l A := by
  obtain ⟨B, hAB, h⟩ := h
  exact Der.eqConv h.sound (Der.symmT hAB)

/-! ### Lifting neutral comparison -/

/-- **Lifting**: neutral terms algorithmically equal at a type equal to a reducible type `A` are
algorithmically equal terms of `A`. -/
theorem TyR.liftNe {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR declEq l Γ A I) :
    ∀ {k m B : Tm}, NeUp Γ k m B → TyEq Γ A B → TmUp Γ k m A := by
  rw [TyR.unfold] at h
  induction h with
  | univ _ D =>
      intro k m B hkm hAB
      obtain ⟨C', hd, hC'⟩ := hkm.toDown (Der.transT (Der.symmT hAB) D.tyEq)
      have e := TyEq.univ_whnf (Der.symmT hC') (NeDown.whnf hd)
      subst e
      have hkmD := NeDown.sound hd
      obtain ⟨hnk, hnm⟩ := NeDown.neutral hd
      exact Alg.tmRed D.red (TReds.refl hkmD.tyL) (TReds.refl hkmD.tyR) (Whnf.univ _)
        (Whnf.ne hnk) (Whnf.ne hnm) (Alg.univTm hkmD.tyL hkmD.tyR (Alg.neTy hd))
  | nat D =>
      intro k m B hkm hAB
      obtain ⟨C', hd, hC'⟩ := hkm.toDown (Der.transT (Der.symmT hAB) D.tyEq)
      have e := TyEq.nat_whnf (Der.symmT hC') (NeDown.whnf hd)
      subst e
      have hkmD := NeDown.sound hd
      obtain ⟨hnk, hnm⟩ := NeDown.neutral hd
      exact Alg.tmRed D.red (TReds.refl hkmD.tyL) (TReds.refl hkmD.tyR) Whnf.nat
        (Whnf.ne hnk) (Whnf.ne hnm) (Alg.neNat hd)
  | empty D =>
      intro k m B hkm hAB
      obtain ⟨C', hd, hC'⟩ := hkm.toDown (Der.transT (Der.symmT hAB) D.tyEq)
      have e := TyEq.empty_whnf (Der.symmT hC') (NeDown.whnf hd)
      subst e
      have hkmD := NeDown.sound hd
      obtain ⟨hnk, hnm⟩ := NeDown.neutral hd
      exact Alg.tmRed D.red (TReds.refl hkmD.tyL) (TReds.refl hkmD.tyR) Whnf.empty
        (Whnf.ne hnk) (Whnf.ne hnm) (Alg.neEmpty hd)
  | ne D hN _ =>
      intro k m B hkm hAB
      have hBN := Der.transT (Der.symmT hAB) D.tyEq
      obtain ⟨C', hd, -⟩ := hkm.toDown hBN
      have hkmB := NeUp.sound hkm
      obtain ⟨hnk, hnm⟩ := NeDown.neutral hd
      have hk := Der.conv hkmB.tyL hBN
      have hm := Der.conv hkmB.tyR hBN
      exact Alg.tmRed D.red (TReds.refl hk) (TReds.refl hm) (Whnf.ne hN) (Whnf.ne hnk)
        (Whnf.ne hnm) (Alg.neNe hk hm hN hd)
  | @pi Γ A F G IF IG D hF _ _ rF _ _ ihF ihG =>
      intro k m B hkm hAB
      have hBP := Der.transT (Der.symmT hAB) D.tyEq
      have hkmB := NeUp.sound hkm
      have hk := Der.conv hkmB.tyL hBP
      have hm := Der.conv hkmB.tyR hBP
      obtain ⟨hnk, hnm⟩ := NeUp.neutral hkm
      have hwf : WfCtx (F :: Γ) := Der.cons hF.wf hF
      have hρ : Wk Γ (F :: Γ) Nat.succ := ⟨RenOk.shift Γ F, hwf⟩
      -- the weakened comparison, with its type reduced to a product
      have hkm' := hkm.rename (RenOk.shift Γ F) hwf
      have hBP' : TyEq (F :: Γ) (shift B) (pi (shift F) (rename (upr Nat.succ) G)) :=
        TyEq.weaken hBP hwf
      obtain ⟨C', hd, hC'⟩ := hkm'.toDown hBP'
      obtain ⟨H, E', rfl, hFH, hGE⟩ := TyEq.pi_whnf (Der.symmT hC') (NeDown.whnf hd)
      -- the variable at the domain
      have hv0 : HasTy (F :: Γ) (Tm.var 0) (shift F) := Der.var hwf (Lookup.zero Γ F)
      have hvar : TmUp (F :: Γ) (Tm.var 0) (Tm.var 0) (rename Nat.succ F) :=
        ihF (F :: Γ) Nat.succ hρ (Alg.varRefl hv0) (Der.reflT hv0.wfTy)
      have happ := Alg.appCong hd (hvar.conv hFH)
      -- the applications at the codomain
      have ha : (IF (F :: Γ) Nat.succ).tmEq (Tm.var 0) (Tm.var 0) := (rF _ _ hρ).toTyR.var hv0
      have hbody := ihG (F :: Γ) Nat.succ (Tm.var 0) hρ ha happ (hGE.inst hv0)
      rw [shift_inst_rename] at hbody
      exact Alg.tmRed D.red (TReds.refl hk) (TReds.refl hm) (Whnf.pi _ _) (Whnf.ne hnk)
        (Whnf.ne hnm) (Alg.eta hk hm (Whnf.ne hnk) (Whnf.ne hnm) hbody)

theorem NeAt.toTm {Γ : Ctx} {k l A : Tm} (h : NeAt Γ k l A) : TmUp Γ k l A := by
  obtain ⟨B, hAB, h⟩ := h
  obtain ⟨l', I, hI⟩ := hAB.wfL.tyR
  exact hI.liftNe h hAB

/-! ### The fields of the algorithmic generic equality -/

theorem TmUp.toTyUp {Γ : Ctx} {A B : Tm} {l : ℕ} (h : TmUp Γ A B (Tm.univ l)) : TyUp Γ A B := by
  obtain ⟨C, A', B', hC, hA, hB, -, hA', hB', hd⟩ := h.inv
  have e := hC.of_whnf (Whnf.univ l)
  subst e
  obtain ⟨-, hd'⟩ := hd.inv_univ
  exact Alg.tyRed (hA.toTyReds l rfl) (hB.toTyReds l rfl) hA' hB' hd'

theorem TyUp.of_red {Γ : Ctx} {A A' B B' : Tm} (hA : TyRedsT Γ A A') (hB : TyRedsT Γ B B')
    (hA' : Whnf A') (hB' : Whnf B') (h : TyUp Γ A' B') : TyUp Γ A B := by
  obtain ⟨A'', B'', hA₂, hB₂, -, -, hd⟩ := h.inv
  rw [hA₂.of_whnf hA', hB₂.of_whnf hB'] at hd
  exact Alg.tyRed hA.red hB.red hA' hB' hd

theorem TmUp.of_red {Γ : Ctx} {A B a a' b b' : Tm} (hAB : TyRedsT Γ A B) (ha : TRedsT Γ a a' B)
    (hb : TRedsT Γ b b' B) (hB : Whnf B) (ha' : Whnf a') (hb' : Whnf b') (h : TmUp Γ a' b' B) :
    TmUp Γ a b A := by
  obtain ⟨C, a'', b'', hC, ha₂, hb₂, -, -, -, hd⟩ := h.inv
  rw [hC.of_whnf hB] at ha₂ hb₂ hd
  rw [ha₂.of_whnf ha', hb₂.of_whnf hb'] at hd
  exact Alg.tmRed hAB.red ha.red hb.red hB ha' hb' hd

theorem TyUp.univ_refl {Γ : Ctx} (l : ℕ) (hΓ : WfCtx Γ) : TyUp Γ (Tm.univ l) (Tm.univ l) :=
  Alg.tyRed (TyReds.refl (Der.univT l hΓ)) (TyReds.refl (Der.univT l hΓ)) (Whnf.univ _)
    (Whnf.univ _) (Alg.univRefl hΓ)

theorem TyUp.nat_refl {Γ : Ctx} (hΓ : WfCtx Γ) : TyUp Γ Tm.nat Tm.nat :=
  Alg.tyRed (TyReds.refl (Der.natT hΓ)) (TyReds.refl (Der.natT hΓ)) Whnf.nat Whnf.nat
    (Alg.natRefl hΓ)

theorem TyUp.empty_refl {Γ : Ctx} (hΓ : WfCtx Γ) : TyUp Γ Tm.empty Tm.empty :=
  Alg.tyRed (TyReds.refl (Der.emptyT hΓ)) (TyReds.refl (Der.emptyT hΓ)) Whnf.empty Whnf.empty
    (Alg.emptyRefl hΓ)

/-- A comparison of types that are terms of a universe, as terms of the universe. -/
theorem TmUp.of_univ {Γ : Ctx} {A B : Tm} {l : ℕ} (hA : HasTy Γ A (Tm.univ l))
    (hB : HasTy Γ B (Tm.univ l)) (hnA : Whnf A) (hnB : Whnf B) (h : TyDown Γ A B) :
    TmUp Γ A B (Tm.univ l) :=
  Alg.tmRed (TyReds.refl (Der.univT l hA.wf)) (TReds.refl hA) (TReds.refl hB) (Whnf.univ _) hnA
    hnB (Alg.univTm hA hB h)

theorem TmUp.univU_refl {Γ : Ctx} (l : ℕ) (hΓ : WfCtx Γ) :
    TmUp Γ (Tm.univ l) (Tm.univ l) (Tm.univ (l + 1)) :=
  TmUp.of_univ (Der.univU l hΓ) (Der.univU l hΓ) (Whnf.univ _) (Whnf.univ _) (Alg.univRefl hΓ)

theorem TmUp.natU_refl {Γ : Ctx} (hΓ : WfCtx Γ) : TmUp Γ Tm.nat Tm.nat (Tm.univ 0) :=
  TmUp.of_univ (Der.natU hΓ) (Der.natU hΓ) Whnf.nat Whnf.nat (Alg.natRefl hΓ)

theorem TmUp.emptyU_refl {Γ : Ctx} (hΓ : WfCtx Γ) : TmUp Γ Tm.empty Tm.empty (Tm.univ 0) :=
  TmUp.of_univ (Der.emptyU hΓ) (Der.emptyU hΓ) Whnf.empty Whnf.empty (Alg.emptyRefl hΓ)

theorem TyUp.pi_cong {Γ : Ctx} {F H G E : Tm} (hF : WfTy Γ F) (hFH : TyUp Γ F H)
    (hGE : TyUp (F :: Γ) G E) : TyUp Γ (pi F G) (pi H E) := by
  have hFH' := TyUp.sound hFH
  have hGE' := TyUp.sound hGE
  exact Alg.tyRed (TyReds.refl (Der.piT hF hGE'.wfL))
    (TyReds.refl (Der.piT hFH'.wfR (hGE'.wfR.ctxConv hFH'))) (Whnf.pi _ _) (Whnf.pi _ _)
    (Alg.piCong hFH hGE)

theorem TmUp.piU_cong {Γ : Ctx} {F H G E : Tm} {i j : ℕ} (hF : HasTy Γ F (Tm.univ i))
    (hFH : TmUp Γ F H (Tm.univ i)) (hGE : TmUp (F :: Γ) G E (Tm.univ j)) :
    TmUp Γ (pi F G) (pi H E) (Tm.univ (max i j)) := by
  have hFH' := TmUp.sound hFH
  have hGE' := TmUp.sound hGE
  exact TmUp.of_univ (Der.piU hF hGE'.tyL) (Der.piU hFH'.tyR (hGE'.tyR.ctxConv (Der.elEq hFH')))
    (Whnf.pi _ _) (Whnf.pi _ _) (Alg.piCong hFH.toTyUp hGE.toTyUp)

theorem TmUp.zero_refl {Γ : Ctx} (hΓ : WfCtx Γ) : TmUp Γ Tm.zero Tm.zero Tm.nat :=
  Alg.tmRed (TyReds.refl (Der.natT hΓ)) (TReds.refl (Der.zero hΓ)) (TReds.refl (Der.zero hΓ))
    Whnf.nat Whnf.zero Whnf.zero (Alg.zeroRefl hΓ)

theorem TmUp.succ_cong {Γ : Ctx} {m n : Tm} (h : TmUp Γ m n Tm.nat) :
    TmUp Γ (succ m) (succ n) Tm.nat := by
  have h' := TmUp.sound h
  exact Alg.tmRed (TyReds.refl (Der.natT h'.wf)) (TReds.refl (Der.succ h'.tyL))
    (TReds.refl (Der.succ h'.tyR)) Whnf.nat (Whnf.succ _) (Whnf.succ _) (Alg.succCong h)

theorem TmUp.eta {Γ : Ctx} {f g F G : Tm} (hf : HasTy Γ f (pi F G)) (hg : HasTy Γ g (pi F G))
    (hnf : Whnf f) (hng : Whnf g)
    (h : TmUp (F :: Γ) (app (shift f) (var 0)) (app (shift g) (var 0)) G) : TmUp Γ f g (pi F G) :=
  Alg.tmRed (TyReds.refl hf.wfTy) (TReds.refl hf) (TReds.refl hg) (Whnf.pi _ _) hnf hng
    (Alg.eta hf hg hnf hng h)

theorem NeAt.symm {Γ : Ctx} {k l A : Tm} (h : NeAt Γ k l A) : NeAt Γ l k A := by
  obtain ⟨B, hAB, h⟩ := h
  obtain ⟨B', hBB', h'⟩ := h.symm
  exact ⟨B', Der.transT hAB hBB', h'⟩

theorem NeAt.trans {Γ : Ctx} {k l m A : Tm} (h₁ : NeAt Γ k l A) (h₂ : NeAt Γ l m A) :
    NeAt Γ k m A := by
  obtain ⟨B₁, hAB₁, h₁⟩ := h₁
  obtain ⟨B₂, -, h₂⟩ := h₂
  exact ⟨B₁, hAB₁, (h₁.trans h₂).1⟩

theorem NeAt.app {Γ : Ctx} {f g a b F G : Tm} (h : NeAt Γ f g (pi F G)) (hab : TmUp Γ a b F) :
    NeAt Γ (app f a) (app g b) (G[a]) := by
  obtain ⟨B, hPB, hfg⟩ := h
  obtain ⟨C', hd, hC'⟩ := hfg.toDown (Der.symmT hPB)
  obtain ⟨F', G', rfl, hFF, hGG⟩ := TyEq.pi_whnf (Der.symmT hC') (NeDown.whnf hd)
  exact ⟨_, hGG.inst (TmUp.sound hab).tyL, Alg.appCong hd (hab.conv hFF)⟩

theorem NeAt.natrec {Γ : Ctx} {P P' z z' s s' n n' : Tm} (hP : WfTy (Tm.nat :: Γ) P)
    (hPP : TyUp (Tm.nat :: Γ) P P') (hz : TmUp Γ z z' (P[Tm.zero]))
    (hs : TmUp (P :: Tm.nat :: Γ) s s' (stepTy P)) (hn : NeAt Γ n n' Tm.nat) :
    NeAt Γ (natrec P z s n) (natrec P' z' s' n') (P[n]) := by
  obtain ⟨B, hNB, hnn⟩ := hn
  obtain ⟨C', hd, hC'⟩ := hnn.toDown (Der.symmT hNB)
  have e := TyEq.nat_whnf (Der.symmT hC') (NeDown.whnf hd)
  subst e
  exact ⟨_, Der.reflT (hP.inst (NeDown.sound hd).tyL), Alg.natrecCong hPP hz hs hd⟩

theorem NeAt.emptyrec {Γ : Ctx} {P P' e e' : Tm} (hPP : TyUp Γ P P') (he : NeAt Γ e e' Tm.empty) :
    NeAt Γ (emptyrec P e) (emptyrec P' e') P := by
  obtain ⟨B, hEB, hee⟩ := he
  obtain ⟨C', hd, hC'⟩ := hee.toDown (Der.symmT hEB)
  have e := TyEq.empty_whnf (Der.symmT hC') (NeDown.whnf hd)
  subst e
  exact ⟨_, Der.reflT (TyUp.sound hPP).wfL, Alg.emptyrecCong hPP hd⟩

/-! ### The algorithmic generic equality -/

/-- **Algorithmic conversion is a generic equality.** -/
def algEq : GenEq where
  ty := TyUp
  tm := TmUp
  ne := NeAt
  ne_tm := NeAt.toTm
  ty_eq := TyUp.sound
  tm_eq := TmUp.sound
  ne_eq := NeAt.sound
  univ := TmUp.toTyUp
  ty_symm := TyUp.symm
  ty_trans := TyUp.trans
  tm_symm := TmUp.symm
  tm_trans := TmUp.trans
  ne_symm := NeAt.symm
  ne_trans := NeAt.trans
  tm_conv := TmUp.conv
  ne_conv := fun ⟨B, hAB, h⟩ hAC => ⟨B, Der.transT (Der.symmT hAC) hAB, h⟩
  ty_wk := fun hρ hΔ h => h.rename hρ hΔ
  tm_wk := fun hρ hΔ h => h.rename hρ hΔ
  ne_wk := fun hρ hΔ ⟨_, hAB, h⟩ => ⟨_, hAB.rename hρ hΔ, h.rename hρ hΔ⟩
  ty_red := TyUp.of_red
  tm_red := TmUp.of_red
  univ_refl := TyUp.univ_refl
  univU_refl := TmUp.univU_refl
  nat_refl := TyUp.nat_refl
  natU_refl := TmUp.natU_refl
  empty_refl := TyUp.empty_refl
  emptyU_refl := TmUp.emptyU_refl
  pi_cong := TyUp.pi_cong
  piU_cong := TmUp.piU_cong
  zero_refl := TmUp.zero_refl
  succ_cong := TmUp.succ_cong
  eta := fun _ hf hg hnf hng h => TmUp.eta hf hg hnf hng h
  var_refl := fun hv => ⟨_, Der.reflT hv.wfTy, Alg.varRefl hv⟩
  app_cong := NeAt.app
  natrec_cong := NeAt.natrec
  emptyrec_cong := NeAt.emptyrec

/-! ### Completeness -/

/-- **Completeness for types**: judgementally equal types are algorithmically equal. -/
theorem TyEq.alg {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : TyUp Γ A B := by
  have hv := h.valid algEq
  have hs := SubstR.ids (h.wf.valid algEq) h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have := hI.escapeTyEq (hv.2.2 Γ _ _ hs l I hI)
  simp only [subst_ids] at this
  exact this

/-- **Completeness for terms**: judgementally equal terms are algorithmically equal. -/
theorem DEq.alg {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) : TmUp Γ t u A := by
  have hv := h.valid algEq
  have hs := SubstR.ids (h.wf.valid algEq) h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.1.red hs
  have := (hI.escapeTm (hv.2.2 Γ _ _ hs l I hI)).2.2
  simp only [subst_ids] at this
  exact this

/-- **The declarative and the algorithmic equality of types coincide.** -/
theorem TyEq.iff_alg {Γ : Ctx} {A B : Tm} : TyEq Γ A B ↔ TyUp Γ A B := ⟨TyEq.alg, TyUp.sound⟩

/-- **The declarative and the algorithmic equality of terms coincide.** -/
theorem DEq.iff_alg {Γ : Ctx} {t u A : Tm} : DEq Γ t u A ↔ TmUp Γ t u A :=
  ⟨DEq.alg, TmUp.sound⟩

end MLTT
