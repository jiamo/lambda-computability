/-
**Martin-Löf type theory: syntactic consequences of the fundamental theorem** — milestone M30
(`M30-MLTT-INV`).

The metatheory of the declarative system that the conversion algorithm needs, derived from
`MLTT.Der.valid` at the declarative generic equality (as in Abel, Öhman and Vezzosi's
`Typed.Consequences`):

* `MLTT.HasTy.wfTy`, `MLTT.DEq.tyL`, `MLTT.DEq.tyR`, `MLTT.TyEq.wfL`, `MLTT.TyEq.wfR` —
  **syntactic validity**: the type of a typable term is well formed, and the sides of an
  equation are typable;
* `MLTT.WfTy.inst`, `MLTT.HasTy.inst`, `MLTT.TyEq.inst`, `MLTT.DEq.inst`, `MLTT.WfTy.instEq` —
  **substitution** of one term (or of two equal terms) for the variable `0`;
* `MLTT.HasTy.ctxConv` and its companions — **context conversion** of the last entry;
* `MLTT.HasTy.inv_univ`, `inv_nat`, `inv_empty`, `inv_pi`, `inv_var`, `inv_lam`, `inv_app`,
  `inv_zero`, `inv_succ`, `inv_natrec`, `inv_emptyrec` — **inversion of typing**;
* `MLTT.Neutral.tyUnique` — **a neutral term has a unique type** up to type equality;
* `MLTT.TyEq.univ_whnf`, `nat_whnf`, `empty_whnf`, `pi_whnf`, `ne_whnf` — a weak head normal
  type equal to a universe, `ℕ`, `⊥`, a product or a neutral type has the same head.
-/

import Start.MLTTConsequences

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Reducibility at the identity -/

theorem TyEq.tyR {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : ∃ l I, TyR declEq l Γ A I ∧ I.tyEq B := by
  have hv := h.valid declEq
  have hs := SubstR.idsOf h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have hIeq := hv.2.2 Γ ids ids hs l I hI
  simp only [subst_ids] at hI hIeq
  exact ⟨l, I, hI, hIeq⟩

theorem DEq.tmR {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) :
    ∃ l I, TyR declEq l Γ A I ∧ I.tmEq t u := by
  have hv := h.valid declEq
  have hs := SubstR.idsOf h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.1.red hs
  have hIeq := hv.2.2 Γ ids ids hs l I hI
  simp only [subst_ids] at hI hIeq
  exact ⟨l, I, hI, hIeq⟩

/-! ### Syntactic validity -/

/-- The type of a typable term is well formed. -/
theorem HasTy.wfTy {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : WfTy Γ A := by
  obtain ⟨l, I, hI, -⟩ := h.tmR
  exact hI.wfTy

theorem DEq.tyL {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) : HasTy Γ t A := by
  obtain ⟨l, I, hI, htu⟩ := h.tmR
  exact (hI.escapeTm htu).1

theorem DEq.tyR {Γ : Ctx} {t u A : Tm} (h : DEq Γ t u A) : HasTy Γ u A := by
  obtain ⟨l, I, hI, htu⟩ := h.tmR
  exact (hI.escapeTm htu).2.1

theorem TyEq.wfL {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : WfTy Γ A := by
  obtain ⟨l, I, hI, -⟩ := h.tyR
  exact hI.wfTy

theorem TyEq.wfR {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) : WfTy Γ B := TyEq.wfL (Der.symmT h)

/-- A well-formed product has a well-formed domain and codomain. -/
theorem WfTy.pi_inv {Γ : Ctx} {F G : Tm} (h : WfTy Γ (pi F G)) : WfTy Γ F ∧ WfTy (F :: Γ) G := by
  obtain ⟨l, I, hI⟩ := h.tyR
  obtain ⟨-, -, hF, hG, -⟩ := hI.pi_inv
  exact ⟨hF, hG⟩

/-! ### Substitution -/

/-- A term related to itself extends the identity substitution. -/
theorem SubstR.single {Γ : Ctx} {F a b : Tm} (hab : DEq Γ a b F) :
    SubstR declEq (F :: Γ) Γ (scons a MLTT.ids) (scons b MLTT.ids) := by
  obtain ⟨l, I, hI, hab'⟩ := hab.tmR
  refine ⟨SubstR.idsOf hab.wf, l, I, ?_, hab'⟩
  rw [stail_scons, subst_ids]
  exact hI

theorem WfTy.inst {Γ : Ctx} {F G a : Tm} (hG : WfTy (F :: Γ) G) (ha : HasTy Γ a F) :
    WfTy Γ (G[a]) := by
  obtain ⟨l, I, hI, -⟩ := (hG.valid declEq).red (SubstR.single (Der.refl ha))
  exact hI.wfTy

/-- Substituting equal terms gives equal types. -/
theorem WfTy.instEq {Γ : Ctx} {F G a b : Tm} (hG : WfTy (F :: Γ) G) (hab : DEq Γ a b F) :
    TyEq Γ (G[a]) (G[b]) := by
  obtain ⟨l, I, hI, hIeq⟩ := (hG.valid declEq).red (SubstR.single hab)
  exact hI.escapeTyEq hIeq

theorem HasTy.inst {Γ : Ctx} {F G t a : Tm} (ht : HasTy (F :: Γ) t G) (ha : HasTy Γ a F) :
    HasTy Γ (t[a]) (G[a]) := by
  obtain ⟨l, I, hI, h⟩ := (ht.valid declEq).red (SubstR.single (Der.refl ha))
  exact (hI.escapeTm h).1

theorem TyEq.inst {Γ : Ctx} {F G G' a : Tm} (h : TyEq (F :: Γ) G G') (ha : HasTy Γ a F) :
    TyEq Γ (G[a]) (G'[a]) := by
  have hv := h.valid declEq
  have hs := SubstR.single (Der.refl ha)
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  exact hI.escapeTyEq (hv.2.2 Γ _ _ hs l I hI)

theorem DEq.inst {Γ : Ctx} {F G t u a : Tm} (h : DEq (F :: Γ) t u G) (ha : HasTy Γ a F) :
    DEq Γ (t[a]) (u[a]) (G[a]) := by
  have hv := h.valid declEq
  have hs := SubstR.single (Der.refl ha)
  obtain ⟨l, I, hI, -⟩ := hv.1.1.red hs
  exact (hI.escapeTm (hv.2.2 Γ _ _ hs l I hI)).2.2

/-! ### Context conversion -/

/-- The identity substitution from `F :: Γ` to `H :: Γ`, for `F ≡ H`. -/
theorem SubstR.ctxConvId {Γ : Ctx} {F H : Tm} (hFH : TyEq Γ F H) :
    SubstR declEq (F :: Γ) (H :: Γ) MLTT.ids MLTT.ids := by
  have hΓ := hFH.wf
  have hwf : WfCtx (H :: Γ) := Der.cons hΓ hFH.wfR
  have hρ : Wk Γ (H :: Γ) Nat.succ := ⟨RenOk.shift Γ H, hwf⟩
  have ht := (SubstR.idsOf hΓ).wk hρ
  obtain ⟨l, I, hI⟩ := hFH.wfL.tyR
  obtain ⟨J, hJ, -, -⟩ := TyR.wk l hI hρ
  have hv : HasTy (H :: Γ) (var 0) (shift F) :=
    Der.conv (Der.var hwf (Lookup.zero Γ H)) (Der.symmT (hFH.weaken hwf))
  refine ⟨ht, l, J, ?_, hJ.var hv⟩
  have e : subst (stail MLTT.ids) F = shift F := by
    rw [shift, rename_eq_subst]; rfl
  rw [e]
  exact hJ

theorem WfTy.ctxConv {Γ : Ctx} {F H A : Tm} (h : WfTy (F :: Γ) A) (hFH : TyEq Γ F H) :
    WfTy (H :: Γ) A := by
  obtain ⟨l, I, hI, -⟩ := (h.valid declEq).red (SubstR.ctxConvId hFH)
  rw [subst_ids] at hI
  exact hI.wfTy

theorem HasTy.ctxConv {Γ : Ctx} {F H t A : Tm} (h : HasTy (F :: Γ) t A) (hFH : TyEq Γ F H) :
    HasTy (H :: Γ) t A := by
  obtain ⟨l, I, hI, ht⟩ := (h.valid declEq).red (SubstR.ctxConvId hFH)
  simp only [subst_ids] at hI ht
  exact (hI.escapeTm ht).1

theorem TyEq.ctxConv {Γ : Ctx} {F H A B : Tm} (h : TyEq (F :: Γ) A B) (hFH : TyEq Γ F H) :
    TyEq (H :: Γ) A B := by
  have hv := h.valid declEq
  have hs := SubstR.ctxConvId hFH
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have := hI.escapeTyEq (hv.2.2 _ _ _ hs l I hI)
  simp only [subst_ids] at this
  exact this

theorem DEq.ctxConv {Γ : Ctx} {F H t u A : Tm} (h : DEq (F :: Γ) t u A) (hFH : TyEq Γ F H) :
    DEq (H :: Γ) t u A := by
  have hv := h.valid declEq
  have hs := SubstR.ctxConvId hFH
  obtain ⟨l, I, hI, -⟩ := hv.1.1.red hs
  have := (hI.escapeTm (hv.2.2 _ _ _ hs l I hI)).2.2
  simp only [subst_ids] at this
  exact this

/-! ### Inversion of typing -/

theorem HasTy.inv_univ {Γ : Ctx} {k : ℕ} {C : Tm} (h : HasTy Γ (univ k) C) :
    TyEq Γ C (univ (k + 1)) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (univ k) C →
      TyEq Γ C (univ (k + 1)) from H h rfl
  intro J hd
  induction hd
  case univU l hΓ _ => intro _ _ hJ; cases hJ; exact Der.reflT (Der.univT _ hΓ)
  case conv _ hAB ih _ => intro _ _ hJ; cases hJ; exact Der.transT (Der.symmT hAB) (ih rfl)
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_nat {Γ : Ctx} {C : Tm} (h : HasTy Γ nat C) : TyEq Γ C (univ 0) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ nat C →
      TyEq Γ C (univ 0) from H h rfl
  intro J hd
  induction hd
  case natU hΓ _ => intro _ _ hJ; cases hJ; exact Der.reflT (Der.univT _ hΓ)
  case conv _ hAB ih _ => intro _ _ hJ; cases hJ; exact Der.transT (Der.symmT hAB) (ih rfl)
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_empty {Γ : Ctx} {C : Tm} (h : HasTy Γ empty C) : TyEq Γ C (univ 0) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ empty C →
      TyEq Γ C (univ 0) from H h rfl
  intro J hd
  induction hd
  case emptyU hΓ _ => intro _ _ hJ; cases hJ; exact Der.reflT (Der.univT _ hΓ)
  case conv _ hAB ih _ => intro _ _ hJ; cases hJ; exact Der.transT (Der.symmT hAB) (ih rfl)
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_pi {Γ : Ctx} {F G C : Tm} (h : HasTy Γ (pi F G) C) :
    ∃ i j, HasTy Γ F (univ i) ∧ HasTy (F :: Γ) G (univ j) ∧ TyEq Γ C (univ (max i j)) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (pi F G) C →
      ∃ i j, HasTy Γ F (univ i) ∧ HasTy (F :: Γ) G (univ j) ∧ TyEq Γ C (univ (max i j))
    from H h rfl
  intro J hd
  induction hd
  case piU hF hG _ _ =>
    intro _ _ hJ; cases hJ
    exact ⟨_, _, hF, hG, Der.reflT (Der.univT _ (Der.wf_ctx hF))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨i, j, hF, hG, hC⟩ := ih rfl
    exact ⟨i, j, hF, hG, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_var {Γ : Ctx} {n : ℕ} {C : Tm} (h : HasTy Γ (var n) C) :
    ∃ A, Lookup Γ n A ∧ TyEq Γ C A := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (var n) C →
      ∃ A, Lookup Γ n A ∧ TyEq Γ C A from H h rfl
  intro J hd
  induction hd
  case var hΓ hl _ =>
    intro _ _ hJ; cases hJ
    exact ⟨_, hl, Der.reflT (HasTy.wfTy (Der.var hΓ hl))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨A, hl, hC⟩ := ih rfl
    exact ⟨A, hl, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_lam {Γ : Ctx} {b C : Tm} (h : HasTy Γ (lam b) C) :
    ∃ F G, WfTy Γ F ∧ HasTy (F :: Γ) b G ∧ TyEq Γ C (pi F G) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (lam b) C →
      ∃ F G, WfTy Γ F ∧ HasTy (F :: Γ) b G ∧ TyEq Γ C (pi F G) from H h rfl
  intro J hd
  induction hd
  case lam hF hb _ _ =>
    intro _ _ hJ; cases hJ
    exact ⟨_, _, hF, hb, Der.reflT (HasTy.wfTy (Der.lam hF hb))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨F, G, hF, hb, hC⟩ := ih rfl
    exact ⟨F, G, hF, hb, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_app {Γ : Ctx} {f a C : Tm} (h : HasTy Γ (app f a) C) :
    ∃ F G, HasTy Γ f (pi F G) ∧ HasTy Γ a F ∧ TyEq Γ C (G[a]) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (app f a) C →
      ∃ F G, HasTy Γ f (pi F G) ∧ HasTy Γ a F ∧ TyEq Γ C (G[a]) from H h rfl
  intro J hd
  induction hd
  case app hf ha _ _ =>
    intro _ _ hJ; cases hJ
    exact ⟨_, _, hf, ha, Der.reflT (HasTy.wfTy (Der.app hf ha))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨F, G, hf, ha, hC⟩ := ih rfl
    exact ⟨F, G, hf, ha, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_zero {Γ : Ctx} {C : Tm} (h : HasTy Γ zero C) : TyEq Γ C nat := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ zero C →
      TyEq Γ C nat from H h rfl
  intro J hd
  induction hd
  case zero hΓ _ => intro _ _ hJ; cases hJ; exact Der.reflT (Der.natT hΓ)
  case conv _ hAB ih _ => intro _ _ hJ; cases hJ; exact Der.transT (Der.symmT hAB) (ih rfl)
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_succ {Γ : Ctx} {n C : Tm} (h : HasTy Γ (succ n) C) :
    HasTy Γ n nat ∧ TyEq Γ C nat := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (succ n) C →
      HasTy Γ n nat ∧ TyEq Γ C nat from H h rfl
  intro J hd
  induction hd
  case succ hn _ => intro _ _ hJ; cases hJ; exact ⟨hn, Der.reflT (Der.natT (Der.wf_ctx hn))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨hn, hC⟩ := ih rfl
    exact ⟨hn, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_natrec {Γ : Ctx} {P z s n C : Tm} (h : HasTy Γ (natrec P z s n) C) :
    WfTy (nat :: Γ) P ∧ HasTy Γ z (P[zero]) ∧ HasTy (P :: nat :: Γ) s (stepTy P) ∧
      HasTy Γ n nat ∧ TyEq Γ C (P[n]) := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (natrec P z s n) C →
      WfTy (nat :: Γ) P ∧ HasTy Γ z (P[zero]) ∧ HasTy (P :: nat :: Γ) s (stepTy P) ∧
        HasTy Γ n nat ∧ TyEq Γ C (P[n]) from H h rfl
  intro J hd
  induction hd
  case natrec hP hz hs hn _ _ _ _ =>
    intro _ _ hJ; cases hJ
    exact ⟨hP, hz, hs, hn, Der.reflT (HasTy.wfTy (Der.natrec hP hz hs hn))⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨hP, hz, hs, hn, hC⟩ := ih rfl
    exact ⟨hP, hz, hs, hn, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

theorem HasTy.inv_emptyrec {Γ : Ctx} {P e C : Tm} (h : HasTy Γ (emptyrec P e) C) :
    WfTy Γ P ∧ HasTy Γ e empty ∧ TyEq Γ C P := by
  suffices H : ∀ {J : Jd}, Der J → ∀ {Γ : Ctx} {C : Tm}, J = .ty Γ (emptyrec P e) C →
      WfTy Γ P ∧ HasTy Γ e empty ∧ TyEq Γ C P from H h rfl
  intro J hd
  induction hd
  case emptyrec hP he _ _ => intro _ _ hJ; cases hJ; exact ⟨hP, he, Der.reflT hP⟩
  case conv _ hAB ih _ =>
    intro _ _ hJ; cases hJ
    obtain ⟨hP, he, hC⟩ := ih rfl
    exact ⟨hP, he, Der.transT (Der.symmT hAB) hC⟩
  all_goals intro _ _ hJ; cases hJ

/-! ### Uniqueness of the type of a neutral term -/

/-- **A neutral term has a unique type**, up to type equality. -/
theorem Neutral.tyUnique {n : Tm} (hn : Neutral n) :
    ∀ {Γ : Ctx} {A B : Tm}, HasTy Γ n A → HasTy Γ n B → TyEq Γ A B := by
  induction hn with
  | var k =>
      intro Γ A B hA hB
      obtain ⟨X, hX, hAX⟩ := hA.inv_var
      obtain ⟨Y, hY, hBY⟩ := hB.inv_var
      rw [Lookup.det hX hY] at hAX
      exact Der.transT hAX (Der.symmT hBY)
  | app a _ ih =>
      intro Γ A B hA hB
      obtain ⟨F, G, hf, ha, hAG⟩ := hA.inv_app
      obtain ⟨F', G', hf', -, hBG⟩ := hB.inv_app
      obtain ⟨-, hGG⟩ := TyEq.pi_inj (ih hf hf')
      exact Der.transT hAG (Der.transT (hGG.inst ha) (Der.symmT hBG))
  | natrec P z s _ _ =>
      intro Γ A B hA hB
      exact Der.transT hA.inv_natrec.2.2.2.2 (Der.symmT hB.inv_natrec.2.2.2.2)
  | emptyrec P _ _ =>
      intro Γ A B hA hB
      exact Der.transT hA.inv_emptyrec.2.2 (Der.symmT hB.inv_emptyrec.2.2)

/-! ### Heads of equal weak head normal types -/

theorem TyEq.univ_whnf {Γ : Ctx} {l : ℕ} {B : Tm} (h : TyEq Γ (univ l) B) (hB : Whnf B) :
    B = univ l := by
  obtain ⟨k, I, hI, hIB⟩ := h.tyR
  have hD := hI.univ_inv B hIB
  exact hD.red.of_whnf hB |>.symm

theorem TyEq.nat_whnf {Γ : Ctx} {B : Tm} (h : TyEq Γ nat B) (hB : Whnf B) : B = nat := by
  obtain ⟨k, I, hI, hIB⟩ := h.tyR
  rw [TyR.unfold] at hI
  cases hI with
  | univ hl D => exact absurd (D.red.of_whnf Whnf.nat) (by simp)
  | nat D => exact (hIB.red.of_whnf hB).symm
  | empty D => exact absurd (D.red.of_whnf Whnf.nat) (by simp)
  | ne D hN _ =>
      have e := D.red.of_whnf Whnf.nat
      rw [e] at hN; cases hN
  | pi IF IG D _ _ _ _ _ _ => exact absurd (D.red.of_whnf Whnf.nat) (by simp)

theorem TyEq.empty_whnf {Γ : Ctx} {B : Tm} (h : TyEq Γ empty B) (hB : Whnf B) : B = empty := by
  obtain ⟨k, I, hI, hIB⟩ := h.tyR
  rw [TyR.unfold] at hI
  cases hI with
  | univ hl D => exact absurd (D.red.of_whnf Whnf.empty) (by simp)
  | nat D => exact absurd (D.red.of_whnf Whnf.empty) (by simp)
  | empty D => exact (hIB.red.of_whnf hB).symm
  | ne D hN _ =>
      have e := D.red.of_whnf Whnf.empty
      rw [e] at hN; cases hN
  | pi IF IG D _ _ _ _ _ _ => exact absurd (D.red.of_whnf Whnf.empty) (by simp)

theorem TyEq.ne_whnf {Γ : Ctx} {N B : Tm} (h : TyEq Γ N B) (hN : Neutral N) (hB : Whnf B) :
    Neutral B := by
  obtain ⟨k, I, hI, hIB⟩ := h.tyR
  rw [TyR.unfold] at hI
  cases hI with
  | univ hl D =>
      have e := D.red.of_whnf (Whnf.ne hN)
      rw [← e] at hN; cases hN
  | nat D =>
      have e := D.red.of_whnf (Whnf.ne hN)
      rw [← e] at hN; cases hN
  | empty D =>
      have e := D.red.of_whnf (Whnf.ne hN)
      rw [← e] at hN; cases hN
  | ne D _ _ =>
      obtain ⟨M, hBM, hM, -⟩ := hIB
      rw [hBM.red.of_whnf hB] at hM
      exact hM
  | pi IF IG D _ _ _ _ _ _ =>
      have e := D.red.of_whnf (Whnf.ne hN)
      rw [← e] at hN; cases hN

theorem TyEq.pi_whnf {Γ : Ctx} {F G B : Tm} (h : TyEq Γ (pi F G) B) (hB : Whnf B) :
    ∃ H E', B = pi H E' ∧ TyEq Γ F H ∧ TyEq (F :: Γ) G E' := by
  obtain ⟨k, I, hI, hIB⟩ := h.tyR
  obtain ⟨IF, IG, -, -, -, -, -, -, hty, -⟩ := hI.pi_inv
  obtain ⟨H, E', DB, -⟩ := (hty B).mp hIB
  have e := DB.red.of_whnf hB
  subst e
  exact ⟨H, E', rfl, (TyEq.pi_inj h).1, (TyEq.pi_inj h).2⟩

/-- A type equal to a weak head normal neutral type is not a universe, `ℕ`, `⊥` or a product. -/
theorem TyEq.whnf_ne_cases {Γ : Ctx} {A B : Tm} (h : TyEq Γ A B) (hA : Whnf A) (hB : Whnf B) :
    (A = B ∧ (A = nat ∨ A = empty ∨ ∃ l, A = univ l)) ∨
      (∃ F G H E', A = pi F G ∧ B = pi H E' ∧ TyEq Γ F H ∧ TyEq (F :: Γ) G E') ∨
      (Neutral A ∧ Neutral B) := by
  obtain ⟨k, I, hI⟩ := h.wfL.tyR
  rw [TyR.unfold] at hI
  cases hI with
  | univ hl D =>
      have e := D.red.of_whnf hA
      subst e
      exact Or.inl ⟨(h.univ_whnf hB).symm, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  | nat D =>
      have e := D.red.of_whnf hA
      subst e
      exact Or.inl ⟨(h.nat_whnf hB).symm, Or.inl rfl⟩
  | empty D =>
      have e := D.red.of_whnf hA
      subst e
      exact Or.inl ⟨(h.empty_whnf hB).symm, Or.inr (Or.inl rfl)⟩
  | ne D hN _ =>
      have e := D.red.of_whnf hA
      subst e
      exact Or.inr (Or.inr ⟨hN, h.ne_whnf hN hB⟩)
  | pi IF IG D _ _ _ _ _ _ =>
      have e := D.red.of_whnf hA
      subst e
      obtain ⟨H, E', rfl, hFH, hGE⟩ := h.pi_whnf hB
      exact Or.inr (Or.inl ⟨_, _, H, E', rfl, rfl, hFH, hGE⟩)

end MLTT
