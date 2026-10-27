/-
**Martin-Löf type theory: the fundamental theorem, natural numbers and the empty type** —
milestone M30 (`M30-MLTT-FUND`).

* substitution facts for the motive and the step of `natrec` (`subst_inst_eq`,
  `subst_stepTy_scons`, `subst_inst2_scons`, `subst_stepTy_eq`);
* `SubstR.natCons`, `SubstR.natHead`, `SubstR.stepSubst` — related substitutions and natural
  numbers;
* `ValidTy.natInst`, `valid_natInstTyEq` — instances of valid (equal) motives at valid (equal)
  numbers; `valid_stepTyEq` — the step types of valid equal motives;
* `natrec_core` — **the heart of the rule for `natrec`**: by induction on the reducible
  equality of the scrutinees (zero, successor, neutral), two `natrec`s with related motives,
  bases and steps are reducibly equal;
* `valid_natrecCong`, `valid_natrec`, `valid_natrecZero`, `valid_natrecSucc`,
  `valid_emptyrecCong`, `valid_emptyrec`.
-/

import Start.MLTTFundPiIntro

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

variable {E : GenEq}

/-! ### Substitution facts -/

theorem subst_inst_eq (σ : ℕ → Tm) (n P : Tm) : subst σ (P[n]) = subst (scons (subst σ n) σ) P := by
  rw [subst_inst, subst_up_inst]

theorem subst_stepTy_scons (σ : ℕ → Tm) (r k P : Tm) :
    subst (scons r (scons k σ)) (stepTy P) = (subst (up σ) P)[succ k] := by
  rw [subst_up_inst]
  simp only [stepTy, subst_subst]
  refine subst_congr ?_ P
  intro i
  cases i <;> rfl

theorem subst_inst2_scons (σ : ℕ → Tm) (n r s : Tm) :
    subst σ (inst2 n r s) = subst (scons (subst σ r) (scons (subst σ n) σ)) s := by
  simp only [inst2, subst_subst]
  refine subst_congr ?_ s
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem subst_stepTy_eq (σ : ℕ → Tm) (P : Tm) :
    subst σ (stepTy P) = subst (scons (succ (σ 1)) (fun k => σ (k + 2))) P := by
  simp only [stepTy, subst_subst]
  refine subst_congr ?_ P
  intro i
  cases i <;> rfl

theorem TReds.tyRight {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) : HasTy Γ u A := by
  induction h with
  | refl ht => exact ht
  | step _ _ ih => exact ih

/-! ### Related substitutions and natural numbers -/

theorem SubstR.natCons {Γ Δ : Ctx} {σ σ' : ℕ → Tm} (h : SubstR E Γ Δ σ σ') {k k' : Tm}
    (hk : NatR E Δ k k') : SubstR E (nat :: Γ) Δ (scons k σ) (scons k' σ') :=
  ⟨h, 0, natI E Δ, TyR.nat_canon h.wfCtx 0, hk⟩

theorem SubstR.natHead {Γ Δ : Ctx} {σ σ' : ℕ → Tm} (h : SubstR E (nat :: Γ) Δ σ σ') :
    NatR E Δ (σ 0) (σ' 0) := by
  obtain ⟨ht, l, I, hI, hab⟩ := h
  exact ((TyR.irrel hI (TyR.nat_canon ht.wfCtx 0)).2 _ _).mp hab

/-- A valid equation of `ℕ` gives reducibly equal numbers under related substitutions. -/
theorem ValidEq.natR {Γ Δ : Ctx} {n n' : Tm} (h : ValidEq E Γ n n' nat) {σ σ' : ℕ → Tm}
    (hs : SubstR E Γ Δ σ σ') : NatR E Δ (subst σ n) (subst σ' n') :=
  h.2.2 Δ σ σ' hs 0 (natI E Δ) (TyR.nat_canon hs.wfCtx 0)

theorem NatR.refl_left {Γ : Ctx} {t u : Tm} (h : NatR E Γ t u) : NatR E Γ t t :=
  NatR.trans h (NatR.symm h)

theorem NatR.refl_right {Γ : Ctx} {t u : Tm} (h : NatR E Γ t u) : NatR E Γ u u :=
  NatR.trans (NatR.symm h) h

/-- The substitution of the step type of `natrec`. -/
theorem SubstR.stepSubst {Γ Δ : Ctx} {Q : Tm} {σ σ' : ℕ → Tm}
    (h : SubstR E (Q :: nat :: Γ) Δ σ σ') :
    SubstR E (nat :: Γ) Δ (scons (succ (σ 1)) (fun k => σ (k + 2)))
      (scons (succ (σ' 1)) (fun k => σ' (k + 2))) := by
  obtain ⟨h₁, -⟩ := h
  have hk : NatR E Δ (σ 1) (σ' 1) := h₁.natHead
  obtain ⟨ht, hu, he⟩ := hk.escape
  refine ⟨h₁.1, 0, natI E Δ, TyR.nat_canon h₁.wfCtx 0, ?_⟩
  exact NatR.succ (TRedsT.refl (Der.succ ht)) (TRedsT.refl (Der.succ hu)) (E.succ_cong he) hk

/-! ### Instances of motives -/

theorem ValidTy.natInst {Γ : Ctx} {P n : Tm} (hP : ValidTy E (nat :: Γ) P)
    (hn : ValidTm E Γ n nat) : ValidTy E Γ (P[n]) := by
  obtain ⟨l, hl⟩ := hP
  refine ⟨l, fun Δ σ σ' hs => ?_⟩
  rw [subst_inst_eq, subst_inst_eq]
  exact hl Δ _ _ (hs.natCons ((valid_refl hn).natR hs))

/-- **Instances of valid equal motives at valid equal numbers are valid equal types.** -/
theorem valid_natInstTyEq {Γ : Ctx} {P P' n n' : Tm} (hPP : ValidTyEq E (nat :: Γ) P P')
    (hn : ValidEq E Γ n n' nat) : ValidTyEq E Γ (P[n]) (P'[n']) := by
  refine ValidTyEq.intro (hPP.1.natInst hn.1) (hPP.2.1.natInst hn.2.1) (fun Δ σ σ' hs => ?_)
  have hs₂ := hs.natCons (hn.natR hs)
  obtain ⟨l, I, hI, -⟩ := hPP.1.red hs₂
  refine ⟨l, I, ?_, ?_⟩
  · rw [subst_inst_eq]; exact hI
  · rw [subst_inst_eq]; exact hPP.2.2 Δ _ _ hs₂ l I hI

/-- **The step types of valid equal motives are valid equal types.** -/
theorem valid_stepTyEq {Γ : Ctx} {P P' : Tm} (hPP : ValidTyEq E (nat :: Γ) P P') (Q : Tm) :
    ValidTyEq E (Q :: nat :: Γ) (stepTy P) (stepTy P') := by
  have hty : ∀ {R : Tm}, ValidTy E (nat :: Γ) R → ValidTy E (Q :: nat :: Γ) (stepTy R) := by
    intro R hR
    obtain ⟨l, hl⟩ := hR
    refine ⟨l, fun Δ σ σ' hs => ?_⟩
    rw [subst_stepTy_eq, subst_stepTy_eq]
    exact hl Δ _ _ hs.stepSubst
  refine ValidTyEq.intro (hty hPP.1) (hty hPP.2.1) (fun Δ σ σ' hs => ?_)
  have hs₂ := hs.stepSubst
  obtain ⟨l, I, hI, -⟩ := hPP.1.red hs₂
  refine ⟨l, I, ?_, ?_⟩
  · rw [subst_stepTy_eq]; exact hI
  · rw [subst_stepTy_eq]; exact hPP.2.2 Δ _ _ hs₂ l I hI

/-! ### Typings at a substitution -/

/-- The typings of a `natrec` whose components are valid, at a substitution related to itself. -/
theorem natrec_typing {Γ Δ : Ctx} {P z s : Tm} (hΓ : ValidCtx E Γ) (hP : ValidTy E (nat :: Γ) P)
    (hz : ValidTm E Γ z (P[zero])) (hs : ValidTm E (P :: nat :: Γ) s (stepTy P))
    {σ : ℕ → Tm} (hσ : SubstR E Γ Δ σ σ) :
    WfTy (nat :: Δ) (subst (up σ) P) ∧ HasTy Δ (subst σ z) ((subst (up σ) P)[zero]) ∧
      HasTy (subst (up σ) P :: nat :: Δ) (subst (up (up σ)) s) (stepTy (subst (up σ) P)) := by
  have hΔ := hσ.wfCtx
  have hNΔ : WfCtx (nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
  have hupN : SubstR E (nat :: Γ) (nat :: Δ) (up σ) (up σ) := SubstR.up hΓ valid_natT hσ hNΔ
  obtain ⟨lP, IP, hIP, -⟩ := hP.red hupN
  have hPw : WfTy (nat :: Δ) (subst (up σ) P) := hIP.wfTy
  refine ⟨hPw, ?_, ?_⟩
  · obtain ⟨l, I, hI, h⟩ := hz.red hσ
    have := (hI.escapeTm h).1
    rw [subst_inst] at this
    exact this
  · have hΓN : ValidCtx E (nat :: Γ) := ⟨hΓ, valid_natT⟩
    have hupP := SubstR.up hΓN hP hupN (Der.cons hNΔ hPw)
    obtain ⟨l, I, hI, h⟩ := hs.red hupP
    have := (hI.escapeTm h).1
    rw [subst_stepTy] at this
    exact this

/-- Typed reduction of `natrec` along a reduction of the scrutinee. -/
theorem natrec_red {Δ : Ctx} {P z s m k : Tm} (hP : WfTy (nat :: Δ) P)
    (hz : HasTy Δ z (P[zero])) (hs : HasTy (P :: nat :: Δ) s (stepTy P))
    (hm : TRedsT Δ m k nat) (hPeq : ∀ k', TReds Δ m k' nat → TyEq Δ (P[m]) (P[k'])) :
    TRedsT Δ (natrec P z s m) (natrec P z s k) (P[m]) :=
  ⟨Der.natrec hP hz hs hm.tyL, Der.conv (Der.natrec hP hz hs hm.tyR) (Der.symmT (hPeq k hm.red)),
    TReds.natrecS hP hz hs hm.red hPeq⟩

/-! ### The core of `natrec` -/

/-- **Two `natrec`s with related motives, bases, steps and scrutinees are reducibly equal.** -/
theorem natrec_core {Γ Δ : Ctx} {P P' z z' s s' : Tm} (hΓ : ValidCtx E Γ)
    (hP : ValidTy E (nat :: Γ) P) (hP' : ValidTy E (nat :: Γ) P')
    (hPP : ValidTyEq E (nat :: Γ) P P')
    (hz : ValidTm E Γ z (P[zero])) (hz' : ValidTm E Γ z' (P'[zero]))
    (hzz : ValidEq E Γ z z' (P[zero]))
    (hs : ValidTm E (P :: nat :: Γ) s (stepTy P)) (hs' : ValidTm E (P' :: nat :: Γ) s' (stepTy P'))
    (hss : ValidEq E (P :: nat :: Γ) s s' (stepTy P))
    {σ σ' : ℕ → Tm} (hσσ : SubstR E Γ Δ σ σ') :
    ∀ {m m' : Tm}, NatR E Δ m m' → ∀ l I, TyR E l Δ ((subst (up σ) P)[m]) I →
      I.tmEq (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) m)
        (natrec (subst (up σ') P') (subst σ' z') (subst (up (up σ')) s') m') := by
  have hσ := hσσ.left hΓ
  have hσ' := hσσ.right hΓ
  have hΔ := hσσ.wfCtx
  have hNΔ : WfCtx (nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
  have hΓN : ValidCtx E (nat :: Γ) := ⟨hΓ, valid_natT⟩
  obtain ⟨tP, tz, ts⟩ := natrec_typing hΓ hP hz hs hσ
  obtain ⟨tP', tz', ts'⟩ := natrec_typing hΓ hP' hz' hs' hσ'
  -- generic equalities of the components, for the neutral case
  have hupσσ' : SubstR E (nat :: Γ) (nat :: Δ) (up σ) (up σ') := SubstR.up hΓ valid_natT hσσ hNΔ
  have eP : E.ty (nat :: Δ) (subst (up σ) P) (subst (up σ') P') := by
    obtain ⟨l, I, hI, -⟩ := hPP.1.red hupσσ'
    exact hI.escapeTyEq (hPP.2.2 _ _ _ hupσσ' l I hI)
  have ez : E.tm Δ (subst σ z) (subst σ' z') ((subst (up σ) P)[zero]) := by
    obtain ⟨l, I, hI, -⟩ := hz.1.red hσσ
    have := (hI.escapeTm (hzz.2.2 Δ σ σ' hσσ l I hI)).2.2
    rw [subst_inst] at this
    exact this
  have es : E.tm (subst (up σ) P :: nat :: Δ) (subst (up (up σ)) s) (subst (up (up σ')) s')
      (stepTy (subst (up σ) P)) := by
    have hup₂ := SubstR.up hΓN hP hupσσ' (Der.cons hNΔ tP)
    obtain ⟨l, I, hI, -⟩ := hss.1.1.red hup₂
    have := (hI.escapeTm (hss.2.2 _ _ _ hup₂ l I hI)).2.2
    rw [subst_stepTy] at this
    exact this
  -- the motive at related numbers
  have Pinst : ∀ {k k'}, NatR E Δ k k' →
      TyEq Δ ((subst (up σ) P)[k]) ((subst (up σ) P)[k']) := by
    intro k k' hk
    obtain ⟨l, I, hI, hIeq⟩ := hP.red (hσ.natCons hk)
    have := E.ty_eq (hI.escapeTyEq hIeq)
    rwa [← subst_up_inst, ← subst_up_inst] at this
  have P'inst : ∀ {k k'}, NatR E Δ k k' →
      TyEq Δ ((subst (up σ') P')[k]) ((subst (up σ') P')[k']) := by
    intro k k' hk
    obtain ⟨l, I, hI, hIeq⟩ := hP'.red (hσ'.natCons hk)
    have := E.ty_eq (hI.escapeTyEq hIeq)
    rwa [← subst_up_inst, ← subst_up_inst] at this
  have PP'inst : ∀ {k k'}, NatR E Δ k k' →
      TyEq Δ ((subst (up σ') P')[k']) ((subst (up σ) P)[k]) := by
    intro k k' hk
    have hs₂ := hσσ.natCons hk
    obtain ⟨l, I, hI, -⟩ := hPP.1.red hs₂
    have := E.ty_eq (hI.escapeTyEq (hPP.2.2 _ _ _ hs₂ l I hI))
    rw [← subst_up_inst, ← subst_up_inst] at this
    exact Der.symmT this
  -- converting interpretations of the motive along related numbers
  have convP : ∀ {k k' : Tm} {l₁ l₂ : ℕ} {J K : Interp}, NatR E Δ k k' →
      TyR E l₁ Δ ((subst (up σ) P)[k]) J → TyR E l₂ Δ ((subst (up σ) P)[k']) K →
      ∀ t u, (J.tmEq t u ↔ K.tmEq t u) := by
    intro k k' l₁ l₂ J K hk hJ hK
    obtain ⟨l, M, hM, hMeq⟩ := hP.red (hσ.natCons hk)
    rw [← subst_up_inst] at hM
    rw [← subst_up_inst] at hMeq
    have hJeq : J.tyEq ((subst (up σ) P)[k']) := ((TyR.irrel hM hJ).1 _).mp hMeq
    exact (TyR.good l₁ hJ).conv hK hJeq
  -- reductions of the two `natrec`s
  have redL : ∀ {m k}, NatR E Δ m m → TRedsT Δ m k nat →
      TRedsT Δ (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) m)
        (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) k) ((subst (up σ) P)[m]) := by
    intro m k hmm hmk
    refine natrec_red tP tz ts hmk (fun k' hk' => Pinst ?_)
    exact NatR.symm (NatR.reduce ⟨hmk.tyL, hk'.tyRight, hk'⟩ hmm)
  have redR : ∀ {m k}, NatR E Δ m m → TRedsT Δ m k nat →
      TRedsT Δ (natrec (subst (up σ') P') (subst σ' z') (subst (up (up σ')) s') m)
        (natrec (subst (up σ') P') (subst σ' z') (subst (up (up σ')) s') k)
        ((subst (up σ') P')[m]) := by
    intro m k hmm hmk
    refine natrec_red tP' tz' ts' hmk (fun k' hk' => P'inst ?_)
    exact NatR.symm (NatR.reduce ⟨hmk.tyL, hk'.tyRight, hk'⟩ hmm)
  -- the induction on the scrutinees
  intro m m' hmm'
  induction hmm' with
  | @zero m m' hm hm' =>
      intro l I hI
      have hr : NatR E Δ m m' := NatR.zero hm hm'
      have hZ : TRedsT Δ zero zero nat := TRedsT.refl (Der.zero hΔ)
      have hz0m : NatR E Δ zero m := NatR.symm (NatR.zero hm hZ)
      -- the left side reduces to the base
      have hT : TyEq Δ ((subst (up σ) P)[zero]) ((subst (up σ) P)[m]) := Pinst hz0m
      have hLred := (redL hr.refl_left hm).trans
        ⟨Der.conv (Der.natrec tP tz ts (Der.zero hΔ)) hT, Der.conv tz hT,
          TReds.step (TRed.conv (TRed.natrecZero tP tz ts) hT) (TReds.refl (Der.conv tz hT))⟩
      -- the right side reduces to its base, at the converted type
      have hT' : TyEq Δ ((subst (up σ') P')[zero]) ((subst (up σ') P')[m']) :=
        P'inst (NatR.symm (NatR.zero hm' hZ))
      have hRred := (redR hr.refl_right hm').trans
        ⟨Der.conv (Der.natrec tP' tz' ts' (Der.zero hΔ)) hT', Der.conv tz' hT',
          TReds.step (TRed.conv (TRed.natrecZero tP' tz' ts') hT') (TReds.refl (Der.conv tz' hT'))⟩
      have hRred' := hRred.conv (PP'inst hr)
      -- the bases are related
      obtain ⟨lJ, J, hJ, -⟩ := hz.1.red hσσ
      have hJ' : TyR E lJ Δ ((subst (up σ) P)[zero]) J := by rw [subst_inst] at hJ; exact hJ
      have hmid := (convP hz0m hJ' hI _ _).mp (hzz.2.2 Δ σ σ' hσσ lJ J hJ)
      exact hI.expandTm' hRred' (hI.expandTm hLred hmid)
  | @succ m m' k k' hm hm' hsk hkk ih =>
      intro l I hI
      have hr : NatR E Δ m m' := NatR.succ hm hm' hsk hkk
      obtain ⟨tk, tk', ekk⟩ := hkk.escape
      have hkk₀ := hkk.refl_left
      have hSk : NatR E Δ m (succ k) :=
        NatR.succ hm (TRedsT.refl (Der.succ tk)) (E.succ_cong hkk₀.escape.2.2) hkk₀
      have hT : TyEq Δ ((subst (up σ) P)[succ k]) ((subst (up σ) P)[m]) := Pinst (NatR.symm hSk)
      -- the related substitutions for the step
      obtain ⟨l₀, I₀, hI₀, -⟩ := hP.red (hσ.natCons hkk₀)
      have hI₀' : TyR E l₀ Δ ((subst (up σ) P)[k]) I₀ := by rw [subst_up_inst]; exact hI₀
      have hττ : SubstR E (P :: nat :: Γ) Δ
          (scons (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) k) (scons k σ))
          (scons (natrec (subst (up σ') P') (subst σ' z') (subst (up (up σ')) s') k')
            (scons k' σ')) :=
        ⟨hσσ.natCons hkk, l₀, I₀, hI₀, ih l₀ I₀ hI₀'⟩
      have hΓNP : ValidCtx E (P :: nat :: Γ) := ⟨hΓN, hP⟩
      obtain ⟨l₁, J, hJ, -⟩ := hss.1.1.red (hττ.left hΓNP)
      have hrel := hss.2.2 Δ _ _ hττ l₁ J hJ
      rw [subst_stepTy_scons] at hJ
      have hmid := (convP (NatR.symm hSk) hJ hI _ _).mp hrel
      -- the left side
      have hLstep := TRed.conv (TRed.natrecSucc tP tz ts tk) hT
      rw [subst_up_up_inst2] at hLstep
      have tL := (hJ.escapeTm hrel).1
      have hLred := (redL hr.refl_left hm).trans
        ⟨hLstep.tyLeft, Der.conv tL hT, TReds.step hLstep (TReds.refl (Der.conv tL hT))⟩
      -- the right side
      have hm'm' := hr.refl_right
      have hSk' : NatR E Δ m' (succ k') :=
        NatR.succ hm' (TRedsT.refl (Der.succ tk')) (E.succ_cong hkk.refl_right.escape.2.2)
          hkk.refl_right
      have hT' : TyEq Δ ((subst (up σ') P')[succ k']) ((subst (up σ') P')[m']) :=
        P'inst (NatR.symm hSk')
      have hRstep := TRed.conv (TRed.natrecSucc tP' tz' ts' tk') hT'
      rw [subst_up_up_inst2] at hRstep
      have tR : HasTy Δ (subst (scons (natrec (subst (up σ') P') (subst σ' z')
          (subst (up (up σ')) s') k') (scons k' σ')) s') ((subst (up σ') P')[m']) :=
        Der.conv (hI.escapeTm hmid).2.1 (Der.symmT (PP'inst hr))
      have hRred := (redR hm'm' hm').trans ⟨hRstep.tyLeft, tR, TReds.step hRstep (TReds.refl tR)⟩
      have hRred' := hRred.conv (PP'inst hr)
      exact hI.expandTm' hRred' (hI.expandTm hLred hmid)
  | @ne m m' n n' hm hm' hn hn' hnn =>
      intro l I hI
      have hr : NatR E Δ m m' := NatR.ne hm hm' hn hn' hnn
      have tn := hm.tyR
      have tn' := hm'.tyR
      have hnn₀ : E.ne Δ n n Tm.nat := E.ne_trans hnn (E.ne_symm hnn)
      have hmn : NatR E Δ m n := NatR.ne hm (TRedsT.refl tn) hn hn hnn₀
      have hmn' : NatR E Δ m n' := NatR.ne hm (TRedsT.refl tn') hn hn' hnn
      have hT : TyEq Δ ((subst (up σ) P)[n]) ((subst (up σ) P)[m]) := Pinst (NatR.symm hmn)
      have hT' : TyEq Δ ((subst (up σ') P')[n']) ((subst (up σ) P)[m]) := PP'inst hmn'
      have hLred := redL hr.refl_left hm
      have hRred := (redR hr.refl_right hm').conv (PP'inst hr)
      have hneu : I.tmEq (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) n)
          (natrec (subst (up σ') P') (subst σ' z') (subst (up (up σ')) s') n') :=
        hI.neutral (Neutral.natrec _ _ _ hn) (Neutral.natrec _ _ _ hn')
          (Der.conv (Der.natrec tP tz ts tn) hT) (Der.conv (Der.natrec tP' tz' ts' tn') hT')
          (E.ne_conv (E.natrec_cong tP eP ez es hnn) hT)
      exact hI.expandTm' hRred (hI.expandTm hLred hneu)

/-! ### The rules of `natrec` -/

/-- **Validity of the congruence for `natrec`.** -/
theorem valid_natrecCong {Γ : Ctx} {P P' z z' s s' n n' : Tm} (hΓ : ValidCtx E Γ)
    (hP : ValidTy E (nat :: Γ) P) (hPP : ValidTyEq E (nat :: Γ) P P')
    (hzz : ValidEq E Γ z z' (P[zero])) (hss : ValidEq E (P :: nat :: Γ) s s' (stepTy P))
    (hnn : ValidEq E Γ n n' nat) :
    ValidEq E Γ (natrec P z s n) (natrec P' z' s' n') (P[n]) := by
  have hP' := hPP.2.1
  have hΓN : ValidCtx E (nat :: Γ) := ⟨hΓ, valid_natT⟩
  have hz := hzz.1
  have hz' : ValidTm E Γ z' (P'[zero]) :=
    valid_conv hΓ hzz.2.1 (valid_natInstTyEq hPP (valid_refl valid_zero))
  have hs := hss.1
  have hΓNP' : ValidCtx E (P' :: nat :: Γ) := ⟨hΓN, hP'⟩
  have hs' : ValidTm E (P' :: nat :: Γ) s' (stepTy P') :=
    valid_conv hΓNP' (hss.2.1.ctxConv hΓN hPP) (valid_stepTyEq hPP P')
  -- the relation of two `natrec`s, under related substitutions
  have rel : ∀ {Q Q' w w' r r' c c' : Tm}, ValidTy E (nat :: Γ) Q → ValidTy E (nat :: Γ) Q' →
      ValidTyEq E (nat :: Γ) Q Q' → ValidTm E Γ w (Q[zero]) → ValidTm E Γ w' (Q'[zero]) →
      ValidEq E Γ w w' (Q[zero]) → ValidTm E (Q :: nat :: Γ) r (stepTy Q) →
      ValidTm E (Q' :: nat :: Γ) r' (stepTy Q') → ValidEq E (Q :: nat :: Γ) r r' (stepTy Q) →
      ValidEq E Γ c c' nat → ∀ Δ σ σ', SubstR E Γ Δ σ σ' →
        ∃ l I, TyR E l Δ (subst σ (Q[c])) I ∧
          I.tmEq (subst σ (natrec Q w r c)) (subst σ' (natrec Q' w' r' c')) := by
    intro Q Q' w w' r r' c c' hQ hQ' hQQ hw hw' hww hr hr' hrr hcc Δ σ σ' hs₀
    obtain ⟨l, I, hI, -⟩ := (hQ.natInst hcc.1).red hs₀
    refine ⟨l, I, hI, ?_⟩
    have hI' : TyR E l Δ ((subst (up σ) Q)[subst σ c]) I := by rw [← subst_inst]; exact hI
    exact natrec_core hΓ hQ hQ' hQQ hw hw' hww hr hr' hrr hs₀ (hcc.natR hs₀) l I hI'
  have hA : ValidTm E Γ (natrec P z s n) (P[n]) :=
    ValidTm.intro (hP.natInst hnn.1) (rel hP hP (valid_reflT hP) hz hz (valid_refl hz) hs hs
      (valid_refl hs) (valid_refl hnn.1))
  have hB' : ValidTm E Γ (natrec P' z' s' n') (P'[n']) :=
    ValidTm.intro (hP'.natInst hnn.2.1) (rel hP' hP' (valid_reflT hP') hz' hz' (valid_refl hz')
      hs' hs' (valid_refl hs') (valid_refl hnn.2.1))
  have hB : ValidTm E Γ (natrec P' z' s' n') (P[n]) :=
    valid_conv hΓ hB' (valid_symmT hΓ (valid_natInstTyEq hPP hnn))
  exact ValidEq.intro hA hB (rel hP hP' hPP hz hz' hzz hs hs' hss hnn)

theorem valid_natrec {Γ : Ctx} {P z s n : Tm} (hΓ : ValidCtx E Γ) (hP : ValidTy E (nat :: Γ) P)
    (hz : ValidTm E Γ z (P[zero])) (hs : ValidTm E (P :: nat :: Γ) s (stepTy P))
    (hn : ValidTm E Γ n nat) : ValidTm E Γ (natrec P z s n) (P[n]) :=
  (valid_natrecCong hΓ hP (valid_reflT hP) (valid_refl hz) (valid_refl hs) (valid_refl hn)).1

/-- **Validity of the computation rule of `natrec` at zero.** -/
theorem valid_natrecZero {Γ : Ctx} {P z s : Tm} (hΓ : ValidCtx E Γ) (hP : ValidTy E (nat :: Γ) P)
    (hz : ValidTm E Γ z (P[zero])) (hs : ValidTm E (P :: nat :: Γ) s (stepTy P)) :
    ValidEq E Γ (natrec P z s zero) z (P[zero]) := by
  refine ValidEq.intro (valid_natrec hΓ hP hz hs valid_zero) hz (fun Δ σ σ' hs₀ => ?_)
  obtain ⟨l, J, hJ, -⟩ := hz.1.red hs₀
  refine ⟨l, J, hJ, ?_⟩
  obtain ⟨tP, tz, ts⟩ := natrec_typing hΓ hP hz hs (hs₀.left hΓ)
  have hrel := hz.2 Δ σ σ' hs₀ l J hJ
  have hJ' : TyR E l Δ ((subst (up σ) P)[zero]) J := by rw [subst_inst] at hJ; exact hJ
  have hred : TRedsT Δ (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) zero)
      (subst σ z) ((subst (up σ) P)[zero]) :=
    ⟨Der.natrec tP tz ts (Der.zero hs₀.wfCtx), tz,
      TReds.step (TRed.natrecZero tP tz ts) (TReds.refl tz)⟩
  exact hJ'.expandTm hred hrel

/-- **Validity of the computation rule of `natrec` at a successor.** -/
theorem valid_natrecSucc {Γ : Ctx} {P z s n : Tm} (hΓ : ValidCtx E Γ)
    (hP : ValidTy E (nat :: Γ) P) (hz : ValidTm E Γ z (P[zero]))
    (hs : ValidTm E (P :: nat :: Γ) s (stepTy P)) (hn : ValidTm E Γ n nat) :
    ValidEq E Γ (natrec P z s (succ n)) (inst2 n (natrec P z s n) s) (P[succ n]) := by
  have hΓN : ValidCtx E (nat :: Γ) := ⟨hΓ, valid_natT⟩
  have hr := valid_natrec hΓ hP hz hs hn
  -- the step at the related substitutions
  have core : ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l J, TyR E l Δ (subst σ (P[succ n])) J ∧
      J.tmEq (subst (scons (subst σ (natrec P z s n)) (scons (subst σ n) σ)) s)
        (subst (scons (subst σ' (natrec P z s n)) (scons (subst σ' n) σ')) s) := by
    intro Δ σ σ' hs₀
    have hnn := (valid_refl hn).natR hs₀
    obtain ⟨l₀, I₀, hI₀, -⟩ := hP.red ((hs₀.left hΓ).natCons hnn.refl_left)
    have hI₀' : TyR E l₀ Δ (subst σ (P[n])) I₀ := by rw [subst_inst_eq]; exact hI₀
    have hττ : SubstR E (P :: nat :: Γ) Δ
        (scons (subst σ (natrec P z s n)) (scons (subst σ n) σ))
        (scons (subst σ' (natrec P z s n)) (scons (subst σ' n) σ')) :=
      ⟨hs₀.natCons hnn, l₀, I₀, hI₀, hr.2 Δ σ σ' hs₀ l₀ I₀ hI₀'⟩
    obtain ⟨l, J, hJ, hJs⟩ := hs.red hττ
    refine ⟨l, J, ?_, hJs⟩
    rw [subst_stepTy_scons] at hJ
    rw [subst_inst, subst_succ]
    exact hJ
  refine ValidEq.intro (valid_natrec hΓ hP hz hs (valid_succ hn))
    (ValidTm.intro (hP.natInst (valid_succ hn)) (fun Δ σ σ' hs₀ => ?_)) (fun Δ σ σ' hs₀ => ?_)
  · obtain ⟨l, J, hJ, hJs⟩ := core Δ σ σ' hs₀
    refine ⟨l, J, hJ, ?_⟩
    rw [subst_inst2_scons, subst_inst2_scons]
    exact hJs
  · obtain ⟨l, J, hJ, hJs⟩ := core Δ σ σ' hs₀
    refine ⟨l, J, hJ, ?_⟩
    obtain ⟨tP, tz, ts⟩ := natrec_typing hΓ hP hz hs (hs₀.left hΓ)
    have tn : HasTy Δ (subst σ n) nat := ((valid_refl hn).natR (hs₀.left hΓ)).escape.1
    have hstep := TRed.natrecSucc tP tz ts tn
    rw [subst_up_up_inst2] at hstep
    have hJ' : TyR E l Δ ((subst (up σ) P)[succ (subst σ n)]) J := by
      rw [subst_inst, subst_succ] at hJ; exact hJ
    have tL := (hJ'.escapeTm hJs).1
    have hred : TRedsT Δ (natrec (subst (up σ) P) (subst σ z) (subst (up (up σ)) s) (succ (subst σ n)))
        (subst (scons (subst σ (natrec P z s n)) (scons (subst σ n) σ)) s)
        ((subst (up σ) P)[succ (subst σ n)]) :=
      ⟨hstep.tyLeft, tL, TReds.step hstep (TReds.refl tL)⟩
    rw [subst_inst2_scons]
    exact hJ'.expandTm hred hJs

/-! ### The empty type -/

/-- **Validity of the congruence for the eliminator of the empty type.** -/
theorem valid_emptyrecCong {Γ : Ctx} {P P' e e' : Tm} (hΓ : ValidCtx E Γ)
    (hPP : ValidTyEq E Γ P P') (hee : ValidEq E Γ e e' empty) :
    ValidEq E Γ (emptyrec P e) (emptyrec P' e') P := by
  have rel : ∀ {Q Q' c c' : Tm}, ValidTyEq E Γ Q Q' → ValidEq E Γ c c' empty →
      ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ l I, TyR E l Δ (subst σ Q) I ∧
        I.tmEq (subst σ (emptyrec Q c)) (subst σ' (emptyrec Q' c')) := by
    intro Q Q' c c' hQQ hcc Δ σ σ' hs₀
    obtain ⟨l, I, hI, -⟩ := hQQ.1.red hs₀
    refine ⟨l, I, hI, ?_⟩
    obtain ⟨n, n', hn, hn', hne, hne', hnn⟩ :=
      hcc.2.2 Δ σ σ' hs₀ 0 (emptyI E Δ) (TyR.empty_canon hs₀.wfCtx 0)
    have hQQ' := hQQ.2.2 Δ σ σ' hs₀ l I hI
    have eQ := hI.escapeTyEq hQQ'
    have hTE : TyEq Δ (subst σ Q) (subst σ' Q') := E.ty_eq eQ
    obtain ⟨l', I', hI', -⟩ := hQQ.2.1.red (hs₀.right hΓ)
    have tQ := hI.wfTy
    have tQ' := hI'.wfTy
    have hred : TRedsT Δ (emptyrec (subst σ Q) (subst σ c)) (emptyrec (subst σ Q) n) (subst σ Q) :=
      ⟨Der.emptyrec tQ hn.tyL, Der.emptyrec tQ hn.tyR, TReds.emptyrecS tQ hn.red⟩
    have hred' : TRedsT Δ (emptyrec (subst σ' Q') (subst σ' c')) (emptyrec (subst σ' Q') n')
        (subst σ Q) :=
      ⟨Der.conv (Der.emptyrec tQ' hn'.tyL) (Der.symmT hTE),
        Der.conv (Der.emptyrec tQ' hn'.tyR) (Der.symmT hTE),
        (TReds.emptyrecS tQ' hn'.red).conv (Der.symmT hTE)⟩
    have hneu : I.tmEq (emptyrec (subst σ Q) n) (emptyrec (subst σ' Q') n') :=
      hI.neutral (Neutral.emptyrec _ hne) (Neutral.emptyrec _ hne') (Der.emptyrec tQ hn.tyR)
        (Der.conv (Der.emptyrec tQ' hn'.tyR) (Der.symmT hTE)) (E.emptyrec_cong eQ hnn)
    exact hI.expandTm' hred' (hI.expandTm hred hneu)
  have hA : ValidTm E Γ (emptyrec P e) P :=
    ValidTm.intro hPP.1 (rel (valid_reflT hPP.1) (valid_refl hee.1))
  have hB' : ValidTm E Γ (emptyrec P' e') P' :=
    ValidTm.intro hPP.2.1 (rel (valid_reflT hPP.2.1) (valid_refl hee.2.1))
  exact ValidEq.intro hA (valid_conv hΓ hB' (valid_symmT hΓ hPP)) (rel hPP hee)

theorem valid_emptyrec {Γ : Ctx} {P e : Tm} (hΓ : ValidCtx E Γ) (hP : ValidTy E Γ P)
    (he : ValidTm E Γ e empty) : ValidTm E Γ (emptyrec P e) P :=
  (valid_emptyrecCong hΓ (valid_reflT hP) (valid_refl he)).1

end MLTT
