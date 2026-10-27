/-
**Martin-Löf type theory: algorithmic conversion and its soundness** — milestone M30
(`M30-MLTT-ALG`).

The type-directed conversion algorithm of Abel, Öhman and Vezzosi (*Decidability of conversion
for type theory in type theory*, POPL 2018), for the hierarchy `U 0 : U 1 : …`.  Six mutually
defined judgements, one inductive family `MLTT.Alg` over the forms `MLTT.AJd`:

* `Γ ⊢ k ~ l ↑ A` (`NeUp`) — neutral terms with the same head variable, with a type `A` of the
  variable propagated through the eliminators;
* `Γ ⊢ k ~ l ↓ A` (`NeDown`) — the same, with the inferred type reduced to weak head normal form;
* `Γ ⊢ A [conv↑] B` (`TyUp`) — types, reduced to weak head normal forms and then compared
  (`TyDown`) by their heads;
* `Γ ⊢ t [conv↑] u : A` (`TmUp`) — terms, with the type and both terms reduced to weak head
  normal forms and then compared (`TmDown`) by the head of the type: η-expansion at products,
  heads at `ℕ`, neutral comparison at `⊥` and at neutral types, and **type comparison at
  universes** — so that the algorithm never needs the level of a type.

* `MLTT.Alg.sound` — **soundness**: algorithmically equal neutrals, types and terms are
  judgementally equal (`NeUp.sound`, `TyUp.sound`, `TmUp.sound`).  The universe case needs the
  fact that two algorithmically equal types in universes `U i` and `U j` have `i = j` and are
  equal as terms of `U i`; it is proved within the same induction (`AJd.Sound`), from inversion
  of typing and the uniqueness of the types of neutral terms (`Start/MLTTInversion.lean`).
* `MLTT.Alg.ren` — **weakening** of all six judgements.
-/

import Start.MLTTInversion

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Reductions of types and of terms of a universe -/

/-- A reduction of a type and a typed reduction of the same term to weak head normal forms end at
the same term. -/
theorem TyReds.whnf_eq_treds {Γ Γ' : Ctx} {A A' A'' T : Tm} (h : TyReds Γ A A') (h' : TReds Γ' A A'' T)
    (hn : Whnf A') (hn' : Whnf A'') : A' = A'' := by
  induction h generalizing A'' with
  | refl => exact (h'.of_whnf hn).symm
  | step hs _ ih =>
      cases h' with
      | refl => exact (hn'.no_tred hs).elim
      | step hs' h'' =>
          rw [TRed.det hs hs'] at ih
          exact ih h'' hn hn'

/-- A term of a universe reduces, as a term of that universe, along its type reduction. -/
theorem HasTy.univ_tyReds {Γ : Ctx} {A A' : Tm} {i : ℕ} (h : HasTy Γ A (univ i)) (hr : TyReds Γ A A')
    (hn : Whnf A') : TReds Γ A A' (univ i) := by
  obtain ⟨A'', hr', hn'⟩ := h.whnf
  rw [hr.whnf_eq_treds hr' hn hn']
  exact hr'

/-! ### The algorithmic judgements -/

/-- The forms of the algorithmic judgements. -/
inductive AJd where
  /-- `Γ ⊢ k ~ l ↑ A`: neutral terms, with inferred type `A`. -/
  | neUp (Γ : Ctx) (k l A : Tm)
  /-- `Γ ⊢ k ~ l ↓ A`: neutral terms, with inferred type reduced to the weak head normal `A`. -/
  | neDown (Γ : Ctx) (k l A : Tm)
  /-- `Γ ⊢ A [conv↑] B`: types. -/
  | tyUp (Γ : Ctx) (A B : Tm)
  /-- `Γ ⊢ A [conv↓] B`: types in weak head normal form. -/
  | tyDown (Γ : Ctx) (A B : Tm)
  /-- `Γ ⊢ t [conv↑] u : A`: terms. -/
  | tmUp (Γ : Ctx) (t u A : Tm)
  /-- `Γ ⊢ t [conv↓] u : A`: terms and type in weak head normal form. -/
  | tmDown (Γ : Ctx) (t u A : Tm)

/-- **Algorithmic conversion.** -/
inductive Alg : AJd → Prop
  /- Neutral terms -/
  | varRefl {Γ : Ctx} {n : ℕ} {A : Tm} : HasTy Γ (var n) A → Alg (.neUp Γ (var n) (var n) A)
  | appCong {Γ : Ctx} {k l a b F G : Tm} : Alg (.neDown Γ k l (pi F G)) → Alg (.tmUp Γ a b F) →
      Alg (.neUp Γ (app k a) (app l b) (G[a]))
  | natrecCong {Γ : Ctx} {P P' z z' s s' n n' : Tm} : Alg (.tyUp (Tm.nat :: Γ) P P') →
      Alg (.tmUp Γ z z' (P[Tm.zero])) → Alg (.tmUp (P :: Tm.nat :: Γ) s s' (stepTy P)) →
      Alg (.neDown Γ n n' Tm.nat) →
      Alg (.neUp Γ (natrec P z s n) (natrec P' z' s' n') (P[n]))
  | emptyrecCong {Γ : Ctx} {P P' e e' : Tm} : Alg (.tyUp Γ P P') → Alg (.neDown Γ e e' Tm.empty) →
      Alg (.neUp Γ (emptyrec P e) (emptyrec P' e') P)
  | down {Γ : Ctx} {k l A B : Tm} : Alg (.neUp Γ k l A) → TyReds Γ A B → Whnf B →
      Alg (.neDown Γ k l B)
  /- Types -/
  | tyRed {Γ : Ctx} {A A' B B' : Tm} : TyReds Γ A A' → TyReds Γ B B' → Whnf A' → Whnf B' →
      Alg (.tyDown Γ A' B') → Alg (.tyUp Γ A B)
  | univRefl {Γ : Ctx} {l : ℕ} : WfCtx Γ → Alg (.tyDown Γ (Tm.univ l) (Tm.univ l))
  | natRefl {Γ : Ctx} : WfCtx Γ → Alg (.tyDown Γ Tm.nat Tm.nat)
  | emptyRefl {Γ : Ctx} : WfCtx Γ → Alg (.tyDown Γ Tm.empty Tm.empty)
  | neTy {Γ : Ctx} {K M : Tm} {l : ℕ} : Alg (.neDown Γ K M (Tm.univ l)) → Alg (.tyDown Γ K M)
  | piCong {Γ : Ctx} {F H G E : Tm} : Alg (.tyUp Γ F H) → Alg (.tyUp (F :: Γ) G E) →
      Alg (.tyDown Γ (pi F G) (pi H E))
  /- Terms -/
  | tmRed {Γ : Ctx} {t t' u u' A B : Tm} : TyReds Γ A B → TReds Γ t t' B → TReds Γ u u' B →
      Whnf B → Whnf t' → Whnf u' → Alg (.tmDown Γ t' u' B) → Alg (.tmUp Γ t u A)
  | neNat {Γ : Ctx} {k l : Tm} : Alg (.neDown Γ k l Tm.nat) → Alg (.tmDown Γ k l Tm.nat)
  | neEmpty {Γ : Ctx} {k l : Tm} : Alg (.neDown Γ k l Tm.empty) → Alg (.tmDown Γ k l Tm.empty)
  | neNe {Γ : Ctx} {k l A B : Tm} : HasTy Γ k A → HasTy Γ l A → Neutral A →
      Alg (.neDown Γ k l B) → Alg (.tmDown Γ k l A)
  | univTm {Γ : Ctx} {A B : Tm} {l : ℕ} : HasTy Γ A (Tm.univ l) → HasTy Γ B (Tm.univ l) →
      Alg (.tyDown Γ A B) → Alg (.tmDown Γ A B (Tm.univ l))
  | zeroRefl {Γ : Ctx} : WfCtx Γ → Alg (.tmDown Γ Tm.zero Tm.zero Tm.nat)
  | succCong {Γ : Ctx} {m n : Tm} : Alg (.tmUp Γ m n Tm.nat) →
      Alg (.tmDown Γ (succ m) (succ n) Tm.nat)
  | eta {Γ : Ctx} {f g F G : Tm} : HasTy Γ f (pi F G) → HasTy Γ g (pi F G) → Whnf f → Whnf g →
      Alg (.tmUp (F :: Γ) (app (shift f) (var 0)) (app (shift g) (var 0)) G) →
      Alg (.tmDown Γ f g (pi F G))

/-- `Γ ⊢ k ~ l ↑ A`. -/
abbrev NeUp (Γ : Ctx) (k l A : Tm) : Prop := Alg (.neUp Γ k l A)
/-- `Γ ⊢ k ~ l ↓ A`. -/
abbrev NeDown (Γ : Ctx) (k l A : Tm) : Prop := Alg (.neDown Γ k l A)
/-- `Γ ⊢ A [conv↑] B`. -/
abbrev TyUp (Γ : Ctx) (A B : Tm) : Prop := Alg (.tyUp Γ A B)
/-- `Γ ⊢ A [conv↓] B`. -/
abbrev TyDown (Γ : Ctx) (A B : Tm) : Prop := Alg (.tyDown Γ A B)
/-- `Γ ⊢ t [conv↑] u : A`. -/
abbrev TmUp (Γ : Ctx) (t u A : Tm) : Prop := Alg (.tmUp Γ t u A)
/-- `Γ ⊢ t [conv↓] u : A`. -/
abbrev TmDown (Γ : Ctx) (t u A : Tm) : Prop := Alg (.tmDown Γ t u A)

/-! ### Soundness -/

/-- Two types in universes, equal as terms of the first. -/
def UnivSound (Γ : Ctx) (A B : Tm) : Prop :=
  ∀ i j, HasTy Γ A (Tm.univ i) → HasTy Γ B (Tm.univ j) → i = j ∧ DEq Γ A B (Tm.univ i)

/-- The soundness statement of each algorithmic judgement. -/
def AJd.Sound : AJd → Prop
  | .neUp Γ k l A => DEq Γ k l A ∧ Neutral k ∧ Neutral l
  | .neDown Γ k l A => DEq Γ k l A ∧ Neutral k ∧ Neutral l ∧ Whnf A
  | .tyUp Γ A B => TyEq Γ A B ∧ UnivSound Γ A B
  | .tyDown Γ A B => TyEq Γ A B ∧ UnivSound Γ A B ∧ Whnf A ∧ Whnf B
  | .tmUp Γ t u A => DEq Γ t u A
  | .tmDown Γ t u A => DEq Γ t u A ∧ Whnf t ∧ Whnf u ∧ Whnf A

/-- **Soundness of algorithmic conversion.** -/
theorem Alg.sound {J : AJd} (h : Alg J) : J.Sound := by
  induction h with
  | varRefl hv => exact ⟨Der.refl hv, Neutral.var _, Neutral.var _⟩
  | appCong _ _ ihk iha =>
      obtain ⟨hkl, hk, hl, -⟩ := ihk
      exact ⟨Der.appCong hkl iha, Neutral.app _ hk, Neutral.app _ hl⟩
  | natrecCong _ _ _ _ ihP ihz ihs ihn =>
      obtain ⟨hnn, hk, hl, -⟩ := ihn
      exact ⟨Der.natrecCong ihP.1.wfL ihP.1 ihz ihs hnn, Neutral.natrec _ _ _ hk,
        Neutral.natrec _ _ _ hl⟩
  | emptyrecCong _ _ ihP ihe =>
      obtain ⟨hee, hk, hl, -⟩ := ihe
      exact ⟨Der.emptyrecCong ihP.1 hee, Neutral.emptyrec _ hk, Neutral.emptyrec _ hl⟩
  | down _ hAB hB ih =>
      obtain ⟨hkl, hk, hl⟩ := ih
      exact ⟨Der.eqConv hkl hAB.tyEq, hk, hl, hB⟩
  | tyRed hA hB hA' hB' _ ih =>
      obtain ⟨hAB, hU, -, -⟩ := ih
      refine ⟨Der.transT hA.tyEq (Der.transT hAB (Der.symmT hB.tyEq)), ?_⟩
      intro i j hAi hBj
      have rA := hAi.univ_tyReds hA hA'
      have rB := hBj.univ_tyReds hB hB'
      obtain ⟨rfl, hAB'⟩ := hU i j rA.tyRight rB.tyRight
      exact ⟨rfl, Der.trans rA.deq (Der.trans hAB' (Der.symm rB.deq))⟩
  | univRefl hΓ =>
      refine ⟨Der.reflT (Der.univT _ hΓ), ?_, Whnf.univ _, Whnf.univ _⟩
      intro i j hi hj
      exact ⟨(TyEq.univ_inj hi.inv_univ).trans (TyEq.univ_inj hj.inv_univ).symm, Der.refl hi⟩
  | natRefl hΓ =>
      refine ⟨Der.reflT (Der.natT hΓ), ?_, Whnf.nat, Whnf.nat⟩
      intro i j hi hj
      exact ⟨(TyEq.univ_inj hi.inv_nat).trans (TyEq.univ_inj hj.inv_nat).symm, Der.refl hi⟩
  | emptyRefl hΓ =>
      refine ⟨Der.reflT (Der.emptyT hΓ), ?_, Whnf.empty, Whnf.empty⟩
      intro i j hi hj
      exact ⟨(TyEq.univ_inj hi.inv_empty).trans (TyEq.univ_inj hj.inv_empty).symm, Der.refl hi⟩
  | neTy _ ih =>
      obtain ⟨hKM, hK, hM, -⟩ := ih
      refine ⟨Der.elEq hKM, ?_, Whnf.ne hK, Whnf.ne hM⟩
      intro i j hi hj
      have ei := TyEq.univ_inj (hK.tyUnique hi hKM.tyL)
      have ej := TyEq.univ_inj (hM.tyUnique hj hKM.tyR)
      refine ⟨ei.trans ej.symm, ?_⟩
      rw [ei]
      exact hKM
  | piCong _ _ ihF ihG =>
      obtain ⟨hFH, hUF⟩ := ihF
      obtain ⟨hGE, hUG⟩ := ihG
      refine ⟨Der.piCongT hFH.wfL hFH hGE, ?_, Whnf.pi _ _, Whnf.pi _ _⟩
      intro i j hi hj
      obtain ⟨i₁, j₁, hF, hG, hi'⟩ := hi.inv_pi
      obtain ⟨i₂, j₂, hH, hE, hj'⟩ := hj.inv_pi
      obtain ⟨rfl, hFH'⟩ := hUF i₁ i₂ hF hH
      obtain ⟨rfl, hGE'⟩ := hUG j₁ j₂ hG (hE.ctxConv (Der.symmT hFH))
      have ei := TyEq.univ_inj hi'
      have ej := TyEq.univ_inj hj'
      refine ⟨ei.trans ej.symm, ?_⟩
      rw [ei]
      exact Der.piCongU hF hFH' hGE'
  | tmRed hAB ht hu _ _ _ _ ih =>
      obtain ⟨htu, -, -, -⟩ := ih
      exact Der.eqConv (Der.trans ht.deq (Der.trans htu (Der.symm hu.deq))) (Der.symmT hAB.tyEq)
  | neNat _ ih =>
      obtain ⟨hkl, hk, hl, -⟩ := ih
      exact ⟨hkl, Whnf.ne hk, Whnf.ne hl, Whnf.nat⟩
  | neEmpty _ ih =>
      obtain ⟨hkl, hk, hl, -⟩ := ih
      exact ⟨hkl, Whnf.ne hk, Whnf.ne hl, Whnf.empty⟩
  | neNe hk _ hA _ ih =>
      obtain ⟨hkl, hnk, hnl, -⟩ := ih
      exact ⟨Der.eqConv hkl (hnk.tyUnique hkl.tyL hk), Whnf.ne hnk, Whnf.ne hnl, Whnf.ne hA⟩
  | univTm hA hB _ ih =>
      obtain ⟨-, hU, hA', hB'⟩ := ih
      exact ⟨(hU _ _ hA hB).2, hA', hB', Whnf.univ _⟩
  | zeroRefl hΓ => exact ⟨Der.refl (Der.zero hΓ), Whnf.zero, Whnf.zero, Whnf.nat⟩
  | succCong _ ih => exact ⟨Der.succCong ih, Whnf.succ _, Whnf.succ _, Whnf.nat⟩
  | eta hf hg hnf hng _ ih => exact ⟨Der.eta hf.wfTy.pi_inv.1 hf hg ih, hnf, hng, Whnf.pi _ _⟩

theorem NeUp.sound {Γ : Ctx} {k l A : Tm} (h : NeUp Γ k l A) : DEq Γ k l A := (Alg.sound h).1

theorem NeUp.neutral {Γ : Ctx} {k l A : Tm} (h : NeUp Γ k l A) : Neutral k ∧ Neutral l :=
  (Alg.sound h).2

theorem NeDown.sound {Γ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) : DEq Γ k l A :=
  (Alg.sound h).1

theorem NeDown.neutral {Γ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) : Neutral k ∧ Neutral l :=
  ⟨(Alg.sound h).2.1, (Alg.sound h).2.2.1⟩

theorem NeDown.whnf {Γ : Ctx} {k l A : Tm} (h : NeDown Γ k l A) : Whnf A := (Alg.sound h).2.2.2

theorem TyUp.sound {Γ : Ctx} {A B : Tm} (h : TyUp Γ A B) : TyEq Γ A B := (Alg.sound h).1

theorem TyDown.sound {Γ : Ctx} {A B : Tm} (h : TyDown Γ A B) : TyEq Γ A B := (Alg.sound h).1

theorem TyDown.whnf {Γ : Ctx} {A B : Tm} (h : TyDown Γ A B) : Whnf A ∧ Whnf B :=
  (Alg.sound h).2.2

theorem TmUp.sound {Γ : Ctx} {t u A : Tm} (h : TmUp Γ t u A) : DEq Γ t u A := Alg.sound h

theorem TmDown.sound {Γ : Ctx} {t u A : Tm} (h : TmDown Γ t u A) : DEq Γ t u A := (Alg.sound h).1

theorem TmDown.whnf {Γ : Ctx} {t u A : Tm} (h : TmDown Γ t u A) : Whnf t ∧ Whnf u ∧ Whnf A :=
  (Alg.sound h).2

/-! ### Weakening -/

/-- The weakening statement of each algorithmic judgement. -/
def AJd.Ren : AJd → Prop
  | .neUp Γ k l A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      NeUp Δ (rename ρ k) (rename ρ l) (rename ρ A)
  | .neDown Γ k l A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      NeDown Δ (rename ρ k) (rename ρ l) (rename ρ A)
  | .tyUp Γ A B => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      TyUp Δ (rename ρ A) (rename ρ B)
  | .tyDown Γ A B => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      TyDown Δ (rename ρ A) (rename ρ B)
  | .tmUp Γ t u A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      TmUp Δ (rename ρ t) (rename ρ u) (rename ρ A)
  | .tmDown Γ t u A => ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, RenOk ρ Γ Δ → WfCtx Δ →
      TmDown Δ (rename ρ t) (rename ρ u) (rename ρ A)

/-- **Weakening of algorithmic conversion.** -/
theorem Alg.ren {J : AJd} (h : Alg J) : J.Ren := by
  induction h with
  | varRefl hv =>
      intro Δ ρ hρ hΔ
      exact Alg.varRefl (hv.rename hρ hΔ)
  | appCong _ _ ihk iha =>
      intro Δ ρ hρ hΔ
      have := Alg.appCong (ihk hρ hΔ) (iha hρ hΔ)
      rwa [← rename_inst] at this
  | @natrecCong Γ P P' z z' s s' n n' hP _ _ _ ihP ihz ihs ihn =>
      intro Δ ρ hρ hΔ
      have hN : WfCtx (Tm.nat :: Δ) := Der.cons hΔ (Der.natT hΔ)
      have hP' : WfTy (Tm.nat :: Δ) (rename (upr ρ) P) :=
        (TyUp.sound hP).wfL.rename (hρ.up Tm.nat) hN
      have hz := ihz hρ hΔ
      rw [rename_inst] at hz
      have hs := ihs ((hρ.up Tm.nat).up P) (Der.cons hN hP')
      rw [rename_stepTy] at hs
      have := Alg.natrecCong (ihP (hρ.up Tm.nat) hN) hz hs (ihn hρ hΔ)
      rwa [← rename_inst] at this
  | emptyrecCong _ _ ihP ihe =>
      intro Δ ρ hρ hΔ
      exact Alg.emptyrecCong (ihP hρ hΔ) (ihe hρ hΔ)
  | down _ hAB hB ih =>
      intro Δ ρ hρ hΔ
      exact Alg.down (ih hρ hΔ) (hAB.rename hρ hΔ) (hB.rename ρ)
  | tyRed hA hB hA' hB' _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.tyRed (hA.rename hρ hΔ) (hB.rename hρ hΔ) (hA'.rename ρ) (hB'.rename ρ) (ih hρ hΔ)
  | univRefl _ =>
      intro Δ ρ _ hΔ
      exact Alg.univRefl hΔ
  | natRefl _ =>
      intro Δ ρ _ hΔ
      exact Alg.natRefl hΔ
  | emptyRefl _ =>
      intro Δ ρ _ hΔ
      exact Alg.emptyRefl hΔ
  | neTy _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.neTy (ih hρ hΔ)
  | @piCong Γ F H G E hF _ ihF ihG =>
      intro Δ ρ hρ hΔ
      have hF' : WfTy Δ (rename ρ F) := (TyUp.sound hF).wfL.rename hρ hΔ
      exact Alg.piCong (ihF hρ hΔ) (ihG (hρ.up F) (Der.cons hΔ hF'))
  | tmRed hAB ht hu hB ht' hu' _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.tmRed (hAB.rename hρ hΔ) (ht.rename hρ hΔ) (hu.rename hρ hΔ) (hB.rename ρ)
        (ht'.rename ρ) (hu'.rename ρ) (ih hρ hΔ)
  | neNat _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.neNat (ih hρ hΔ)
  | neEmpty _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.neEmpty (ih hρ hΔ)
  | neNe hk hl hA _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.neNe (hk.rename hρ hΔ) (hl.rename hρ hΔ) (hA.rename ρ) (ih hρ hΔ)
  | univTm hA hB _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.univTm (hA.rename hρ hΔ) (hB.rename hρ hΔ) (ih hρ hΔ)
  | zeroRefl _ =>
      intro Δ ρ _ hΔ
      exact Alg.zeroRefl hΔ
  | succCong _ ih =>
      intro Δ ρ hρ hΔ
      exact Alg.succCong (ih hρ hΔ)
  | @eta Γ f g F G hf hg hnf hng _ ih =>
      intro Δ ρ hρ hΔ
      have hF' : WfTy Δ (rename ρ F) := hf.wfTy.pi_inv.1.rename hρ hΔ
      have he := ih (hρ.up F) (Der.cons hΔ hF')
      rw [rename_shift_var0, rename_shift_var0] at he
      exact Alg.eta (hf.rename hρ hΔ) (hg.rename hρ hΔ) (hnf.rename ρ) (hng.rename ρ) he

theorem NeUp.rename {Γ Δ : Ctx} {k l A : Tm} {ρ : ℕ → ℕ} (h : NeUp Γ k l A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : NeUp Δ (MLTT.rename ρ k) (MLTT.rename ρ l) (MLTT.rename ρ A) :=
  Alg.ren h hρ hΔ

theorem NeDown.rename {Γ Δ : Ctx} {k l A : Tm} {ρ : ℕ → ℕ} (h : NeDown Γ k l A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : NeDown Δ (MLTT.rename ρ k) (MLTT.rename ρ l) (MLTT.rename ρ A) :=
  Alg.ren h hρ hΔ

theorem TyUp.rename {Γ Δ : Ctx} {A B : Tm} {ρ : ℕ → ℕ} (h : TyUp Γ A B) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TyUp Δ (MLTT.rename ρ A) (MLTT.rename ρ B) :=
  Alg.ren h hρ hΔ

theorem TmUp.rename {Γ Δ : Ctx} {t u A : Tm} {ρ : ℕ → ℕ} (h : TmUp Γ t u A) (hρ : RenOk ρ Γ Δ)
    (hΔ : WfCtx Δ) : TmUp Δ (MLTT.rename ρ t) (MLTT.rename ρ u) (MLTT.rename ρ A) :=
  Alg.ren h hρ hΔ

end MLTT
