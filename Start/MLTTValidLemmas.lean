/-
**Martin-Löf type theory: tools for the fundamental theorem** — milestone M30
(`M30-MLTT-FUND`).

* `MLTT.TyInterp` — a chosen interpretation of a reducible type (irrelevance makes the choice
  harmless), used to build the families of a reducible product;
* `ValidTm.intro`, `ValidEq.intro`, `ValidTyEq.intro` — it suffices to check a semantic
  judgement against one reducibility proof of the substituted type;
* `TyR.reduce`, `TyR.reduceTm` — closure of reducibility under weak head *reduction* (the
  converse of `TyR.expand`, `TyR.expandTm`), from the determinism of reduction;
* typed reduction under eliminators (`TRedsT.appL`, `TRedsT.natrecS`, `TRedsT.emptyrecS`);
* the substitution algebra of binders under renamings (`rename_subst_up_inst`,
  `subst_up_up_inst2`, `subst_shift_app_var0`).
-/

import Start.MLTTValid

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Substitution algebra -/

theorem rename_subst_up_inst (ρ : ℕ → ℕ) (σ : ℕ → Tm) (a b : Tm) :
    (rename (upr ρ) (subst (up σ) b))[a] = subst (scons a (fun n => rename ρ (σ n))) b := by
  rw [rename_subst, subst_congr (rename_up ρ σ), subst_up_inst]

theorem subst_up_up_inst2 (σ : ℕ → Tm) (a r s : Tm) :
    inst2 a r (subst (up (up σ)) s) = subst (scons r (scons a σ)) s := by
  simp only [inst2, subst_subst]
  refine subst_congr ?_ s
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp [subst_rename]

theorem subst_shift_app_var0 (σ : ℕ → Tm) (a f : Tm) :
    subst (scons a σ) (app (shift f) (var 0)) = app (subst σ f) a := by
  simp only [subst_app, subst_var, scons_zero, shift, subst_rename]
  rfl

theorem rename_shift_app_var0_inst (ρ : ℕ → ℕ) (f a : Tm) :
    (rename (upr ρ) (app (shift f) (var 0)))[a] = app (rename ρ f) a := by
  rw [rename_shift_var0]
  simp only [inst, subst_app, subst_var, scons_zero, shift, subst_rename]
  rw [rename_eq_subst]
  rfl

/-! ### Chosen interpretations -/

open Classical in
/-- A chosen interpretation of a type at a level (meaningful when the type is reducible). -/
noncomputable def TyInterp (E : GenEq) (l : ℕ) (Δ : Ctx) (A : Tm) : Interp :=
  if h : ∃ I, TyR E l Δ A I then Classical.choose h else ⟨fun _ => False, fun _ _ => False⟩

theorem TyInterp.spec {E : GenEq} {l : ℕ} {Δ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Δ A I) :
    TyR E l Δ A (TyInterp E l Δ A) := by
  have hex : ∃ I, TyR E l Δ A I := ⟨I, h⟩
  unfold TyInterp
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-! ### Introducing semantic judgements -/

theorem ValidTm.intro {E : GenEq} {Γ : Ctx} {t A : Tm} (hA : ValidTy E Γ A)
    (h : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l I, TyR E l Δ (subst σ A) I ∧
      I.tmEq (subst σ t) (subst σ' t)) : ValidTm E Γ t A := by
  refine ⟨hA, fun Δ σ σ' hs l I hI => ?_⟩
  obtain ⟨l', I', hI', h'⟩ := h Δ σ σ' hs
  exact ((TyR.irrel hI' hI).2 _ _).mp h'

theorem ValidEq.intro {E : GenEq} {Γ : Ctx} {t u A : Tm} (ht : ValidTm E Γ t A)
    (hu : ValidTm E Γ u A)
    (h : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l I, TyR E l Δ (subst σ A) I ∧
      I.tmEq (subst σ t) (subst σ' u)) : ValidEq E Γ t u A := by
  refine ⟨ht, hu, fun Δ σ σ' hs l I hI => ?_⟩
  obtain ⟨l', I', hI', h'⟩ := h Δ σ σ' hs
  exact ((TyR.irrel hI' hI).2 _ _).mp h'

theorem ValidTyEq.intro {E : GenEq} {Γ : Ctx} {A B : Tm} (hA : ValidTy E Γ A)
    (hB : ValidTy E Γ B)
    (h : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l I, TyR E l Δ (subst σ A) I ∧ I.tyEq (subst σ' B)) :
    ValidTyEq E Γ A B := by
  refine ⟨hA, hB, fun Δ σ σ' hs l I hI => ?_⟩
  obtain ⟨l', I', hI', h'⟩ := h Δ σ σ' hs
  exact ((TyR.irrel hI' hI).1 _).mp h'

/-- A valid term is related at the substitution instances, for any reducibility proof. -/
theorem ValidTm.red {E : GenEq} {Γ : Ctx} {t A : Tm} (h : ValidTm E Γ t A) {Δ : Ctx}
    {σ σ' : ℕ → Tm} (hs : SubstR E Γ Δ σ σ') :
    ∃ l I, TyR E l Δ (subst σ A) I ∧ I.tmEq (subst σ t) (subst σ' t) := by
  obtain ⟨l, I, hI, -⟩ := h.1.red hs
  exact ⟨l, I, hI, h.2 Δ σ σ' hs l I hI⟩

/-! ### Typed reduction under eliminators -/

theorem TReds.appL {Γ : Ctx} {t t' a F G : Tm} (h : TReds Γ t t' (pi F G)) (ha : HasTy Γ a F) :
    TReds Γ (app t a) (app t' a) (G[a]) := by
  generalize hT : pi F G = T at h
  induction h with
  | refl ht => subst hT; exact TReds.refl (Der.app ht ha)
  | step hs _ ih => subst hT; exact TReds.step (TRed.appL hs ha) (ih rfl)

theorem TRedsT.appL {Γ : Ctx} {t t' a F G : Tm} (h : TRedsT Γ t t' (pi F G)) (ha : HasTy Γ a F) :
    TRedsT Γ (app t a) (app t' a) (G[a]) :=
  ⟨Der.app h.tyL ha, Der.app h.tyR ha, h.red.appL ha⟩

/-- `natrec` under many-step reduction of the scrutinee, given that the motive is constant up to
type equality along the reduction (Abel, Öhman and Vezzosi take the same premise). -/
theorem TReds.natrecS {Γ : Ctx} {P z s n n' : Tm} (hP : WfTy (Tm.nat :: Γ) P)
    (hz : HasTy Γ z (P[Tm.zero])) (hs : HasTy (P :: Tm.nat :: Γ) s (stepTy P))
    (h : TReds Γ n n' Tm.nat) (hPeq : ∀ m, TReds Γ n m Tm.nat → TyEq Γ (P[n]) (P[m])) :
    TReds Γ (natrec P z s n) (natrec P z s n') (P[n]) := by
  suffices H : ∀ {T}, TReds Γ n n' T → T = Tm.nat →
      (∀ m, TReds Γ n m Tm.nat → TyEq Γ (P[n]) (P[m])) →
      TReds Γ (natrec P z s n) (natrec P z s n') (P[n]) from H h rfl hPeq
  clear h hPeq
  intro T h'
  induction h' with
  | refl hn => intro hT _; subst hT; exact TReds.refl (Der.natrec hP hz hs hn)
  | @step n m n' T hst hr ih =>
      intro hT hPeq
      subst hT
      have hst' := TRed.natrecS hP hz hs hst
      refine TReds.step hst' ?_
      have hnm : TyEq Γ (P[n]) (P[m]) := hPeq m (TReds.step hst (TReds.refl hr.tyLeft))
      have ih' := ih rfl (fun k hk => Der.transT (Der.symmT hnm) (hPeq k (TReds.step hst hk)))
      exact ih'.conv (Der.symmT hnm)

theorem TReds.emptyrecS {Γ : Ctx} {P e e' : Tm} (hP : WfTy Γ P) (h : TReds Γ e e' Tm.empty) :
    TReds Γ (emptyrec P e) (emptyrec P e') P := by
  suffices H : ∀ {T}, TReds Γ e e' T → T = Tm.empty →
      TReds Γ (emptyrec P e) (emptyrec P e') P from H h rfl
  clear h
  intro T h'
  induction h' with
  | refl he => intro hT; subst hT; exact TReds.refl (Der.emptyrec hP he)
  | step hst _ ih => intro hT; subst hT; exact TReds.step (TRed.emptyrecS hP hst) (ih rfl)

/-! ### Reduction closure of reducibility -/

/-- The rest of a reduction to a weak head normal form, after a prefix. -/
theorem TReds.tail {Γ Γ' : Ctx} {t f t' A B : Tm} (hf : TReds Γ t f A) (ht : TReds Γ' t t' B)
    (hn : Whnf f) : TReds Γ t' f A := by
  induction ht generalizing f with
  | refl => exact hf
  | step hs _ ih =>
      cases hf with
      | refl => exact (hn.no_tred hs).elim
      | step hs' hf' =>
          rw [TRed.det hs hs'] at ih
          exact ih hf' hn

theorem TyReds.tail {Γ : Ctx} {A X A' : Tm} (hX : TyReds Γ A X) (hA : TyReds Γ A A')
    (hn : Whnf X) : TyReds Γ A' X := by
  induction hA generalizing X with
  | refl => exact hX
  | step hs _ ih =>
      cases hX with
      | refl => exact (hn.no_tred hs).elim
      | step hs' hX' =>
          rw [TRed.det hs hs'] at ih
          exact ih hX' hn

theorem TRedsT.tail {Γ : Ctx} {t f t' A B : Tm} (hf : TRedsT Γ t f A) (ht : TRedsT Γ t t' B)
    (hn : Whnf f) (hB : TyEq Γ B A) : TRedsT Γ t' f A :=
  ⟨Der.conv ht.tyR hB, hf.tyR, hf.red.tail ht.red hn⟩

theorem TyRedsT.tail {Γ : Ctx} {A X A' : Tm} (hX : TyRedsT Γ A X) (hA : TyRedsT Γ A A')
    (hn : Whnf X) : TyRedsT Γ A' X :=
  ⟨hA.wfR, hX.wfR, hX.red.tail hA.red hn⟩

/-- **A type reducible and reducing to `A'` gives `A'` reducible**, with the same
interpretation. -/
theorem TyR.reduce {E : GenEq} {l : ℕ} {Γ : Ctx} {A A' : Tm} {I : Interp}
    (hA : TyRedsT Γ A A') (h : TyR E l Γ A I) : TyR E l Γ A' I := by
  rw [TyR.unfold] at h ⊢
  cases h with
  | univ hl D => exact TyRAt.univ hl (D.tail hA (Whnf.univ _))
  | nat D => exact TyRAt.nat (D.tail hA Whnf.nat)
  | empty D => exact TyRAt.empty (D.tail hA Whnf.empty)
  | ne D hN hNN => exact TyRAt.ne (D.tail hA (Whnf.ne hN)) hN hNN
  | pi IF IG D hF hG hPi rF rG extG =>
      exact TyRAt.pi IF IG (D.tail hA (Whnf.pi _ _)) hF hG hPi rF rG extG

theorem NatR.reduce {E : GenEq} {Γ : Ctx} {t t' u : Tm} (ht : TRedsT Γ t t' Tm.nat)
    (h : NatR E Γ t u) : NatR E Γ t' u := by
  have hc : TyEq Γ Tm.nat Tm.nat := Der.reflT (Der.natT ht.tyL.wf)
  cases h with
  | zero ht' hu => exact NatR.zero (ht'.tail ht Whnf.zero hc) hu
  | succ ht' hu hsm hr => exact NatR.succ (ht'.tail ht (Whnf.succ _) hc) hu hsm hr
  | ne ht' hu hn hm hnm => exact NatR.ne (ht'.tail ht (Whnf.ne hn) hc) hu hn hm hnm

/-- **A term related to `u` and reducing to `t'` gives `t'` related to `u`.** -/
theorem TyR.reduceTm {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t t' u : Tm} (ht : TRedsT Γ t t' A) (htu : I.tmEq t u) : I.tmEq t' u := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D =>
      obtain ⟨t₀, u₀, ht₀, hu, hnt, hnu, htu', ⟨It, hIt, hItu⟩, hJu⟩ := htu
      have htU := ht.conv D.tyEq
      have ht₀' := ht₀.tail htU hnt (Der.reflT (Der.univT _ D.wfL.wf))
      exact ⟨t₀, u₀, ht₀', hu, hnt, hnu, htu', ⟨It, hIt.reduce htU.toTy, hItu⟩, hJu⟩
  | nat D => exact NatR.reduce (ht.conv D.tyEq) htu
  | empty D =>
      obtain ⟨n, m, ht₀, hu, hn, hm, hnm⟩ := htu
      exact ⟨n, m, ht₀.tail ht (Whnf.ne hn) D.tyEq, hu, hn, hm, hnm⟩
  | ne D hN _ =>
      obtain ⟨n, m, ht₀, hu, hn, hm, hnm⟩ := htu
      exact ⟨n, m, ht₀.tail ht (Whnf.ne hn) D.tyEq, hu, hn, hm, hnm⟩
  | pi IF IG D _ _ _ _ _ _ =>
      obtain ⟨f, g, ht₀, hu, hnf, hng, hfg, happ⟩ := htu
      exact ⟨f, g, ht₀.tail ht hnf D.tyEq, hu, hnf, hng, hfg, happ⟩

end MLTT
