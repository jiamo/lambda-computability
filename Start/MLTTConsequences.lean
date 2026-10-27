/-
**Martin-Löf type theory: consequences of the fundamental theorem** — milestone M30
(`M30-MLTT-NORM`).

Instantiated with the declarative equality (`MLTT.declEq`) at the identity substitution, the
fundamental theorem gives:

* `MLTT.HasTy.whnf`, `MLTT.WfTy.whnf` — **weak head normalization**: every typable term and every
  well-formed type reduces to a weak head normal form;
* `MLTT.TyEq.pi_inj` — **injectivity of products**: `Π F G ≡ Π H E` gives `F ≡ H` and `G ≡ E`;
* `MLTT.TyEq.univ_inj` — the universe hierarchy is injective: `U i ≡ U j` gives `i = j`;
* `MLTT.Der.neHead`, `MLTT.Neutral.not_closed` — a typable neutral term has a declared head
  variable, so there is no closed one;
* `MLTT.canonicity` — **canonicity**: a closed natural number is definitionally a numeral;
* `MLTT.consistency` — **consistency**: there is no closed term of the empty type.
-/

import Start.MLTTFund

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Reducibility at the identity -/

theorem SubstR.idsOf {Γ : Ctx} (h : WfCtx Γ) : SubstR declEq Γ Γ MLTT.ids MLTT.ids :=
  SubstR.ids (h.valid declEq) h

/-- A well-formed type is reducible. -/
theorem WfTy.tyR {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : ∃ l I, TyR declEq l Γ A I := by
  obtain ⟨l, I, hI, -⟩ := (h.valid declEq).red (SubstR.idsOf h.wf)
  rw [subst_ids] at hI
  exact ⟨l, I, hI⟩

/-- A typable term is reducible, at any reducibility proof of its type. -/
theorem HasTy.tmR {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) :
    ∃ l I, TyR declEq l Γ A I ∧ I.tmEq t t := by
  obtain ⟨l, I, hI, ht⟩ := (h.valid declEq).red (SubstR.idsOf h.wf)
  rw [subst_ids] at hI ht
  exact ⟨l, I, hI, ht⟩

/-! ### Weak head normalization -/

theorem NatR.whnf {E : GenEq} {Γ : Ctx} {t u : Tm} (h : NatR E Γ t u) :
    ∃ t', TReds Γ t t' Tm.nat ∧ Whnf t' := by
  cases h with
  | zero ht _ => exact ⟨_, ht.red, Whnf.zero⟩
  | succ ht _ _ _ => exact ⟨_, ht.red, Whnf.succ _⟩
  | ne ht _ hn _ _ => exact ⟨_, ht.red, Whnf.ne hn⟩

/-- A reducibly related term has a weak head normal form. -/
theorem TyR.tm_whnf {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t u : Tm} (htu : I.tmEq t u) : ∃ t', TReds Γ t t' A ∧ Whnf t' := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D =>
      obtain ⟨t', -, ht, -, hnt, -⟩ := htu
      exact ⟨t', ht.red.conv (Der.symmT D.tyEq), hnt⟩
  | nat D =>
      obtain ⟨t', ht, hnt⟩ := NatR.whnf htu
      exact ⟨t', ht.conv (Der.symmT D.tyEq), hnt⟩
  | empty D =>
      obtain ⟨n, -, ht, -, hn, -⟩ := htu
      exact ⟨n, ht.red.conv (Der.symmT D.tyEq), Whnf.ne hn⟩
  | ne D _ _ =>
      obtain ⟨n, -, ht, -, hn, -⟩ := htu
      exact ⟨n, ht.red.conv (Der.symmT D.tyEq), Whnf.ne hn⟩
  | pi IF IG D _ _ _ _ _ _ =>
      obtain ⟨f, -, ht, -, hnf, -⟩ := htu
      exact ⟨f, ht.red.conv (Der.symmT D.tyEq), hnf⟩

/-- A reducible type has a weak head normal form. -/
theorem TyR.ty_whnf {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I) :
    ∃ A', TyReds Γ A A' ∧ Whnf A' := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D => exact ⟨_, D.red, Whnf.univ _⟩
  | nat D => exact ⟨_, D.red, Whnf.nat⟩
  | empty D => exact ⟨_, D.red, Whnf.empty⟩
  | ne D hN _ => exact ⟨_, D.red, Whnf.ne hN⟩
  | pi IF IG D _ _ _ _ _ _ => exact ⟨_, D.red, Whnf.pi _ _⟩

/-- **Weak head normalization of terms.** -/
theorem HasTy.whnf {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : ∃ t', TReds Γ t t' A ∧ Whnf t' := by
  obtain ⟨l, I, hI, ht⟩ := h.tmR
  exact hI.tm_whnf ht

/-- **Weak head normalization of types.** -/
theorem WfTy.whnf {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : ∃ A', TyReds Γ A A' ∧ Whnf A' := by
  obtain ⟨l, I, hI⟩ := h.tyR
  exact hI.ty_whnf

/-! ### Injectivity -/

/-- **Injectivity of products.** -/
theorem TyEq.pi_inj {Γ : Ctx} {F G H E' : Tm} (h : TyEq Γ (pi F G) (pi H E')) :
    TyEq Γ F H ∧ TyEq (F :: Γ) G E' := by
  have hv := h.valid declEq
  have hs := SubstR.idsOf h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have hIeq := hv.2.2 Γ ids ids hs l I hI
  simp only [subst_ids] at hI hIeq
  obtain ⟨IF, IG, hF, -, -, rF, rG, -, hty, -⟩ := hI.pi_inv
  obtain ⟨F', G', DB, -, hdom, hcod⟩ := (hty _).mp hIeq
  have e := DB.red.of_whnf (Whnf.pi _ _)
  simp only [pi.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hΓ := h.wf
  refine ⟨?_, ?_⟩
  · have hid := rF Γ id (Wk.id hΓ)
    have := hid.escapeTyEq (hdom Γ id (Wk.id hΓ))
    simp only [rename_id] at this
    exact this
  · have hwf : WfCtx (F :: Γ) := Der.cons hΓ hF
    have hρ : Wk Γ (F :: Γ) Nat.succ := ⟨RenOk.shift Γ F, hwf⟩
    have hv0 : (IF (F :: Γ) Nat.succ).tmEq (var 0) (var 0) :=
      (rF _ _ hρ).var (Der.var hwf (Lookup.zero Γ F))
    have hG := rG _ _ (var 0) hρ hv0
    have hGE := hcod _ _ (var 0) hρ hv0
    have := hG.escapeTyEq hGE
    rw [shift_inst_rename, shift_inst_rename] at this
    exact this

/-- The interpretation of a universe. -/
theorem TyR.univ_inv {E : GenEq} {l : ℕ} {Γ : Ctx} {i : ℕ} {I : Interp}
    (h : TyR E l Γ (univ i) I) : ∀ B, I.tyEq B → TyRedsT Γ B (univ i) := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D =>
      have e := D.red.of_whnf (Whnf.univ _)
      simp only [univ.injEq] at e
      subst e
      exact fun _ hB => hB
  | nat D => exact absurd (D.red.of_whnf (Whnf.univ _)) (by simp)
  | empty D => exact absurd (D.red.of_whnf (Whnf.univ _)) (by simp)
  | ne D hN _ =>
      have e := D.red.of_whnf (Whnf.univ _)
      rw [e] at hN; cases hN
  | pi IF IG D _ _ _ _ _ _ => exact absurd (D.red.of_whnf (Whnf.univ _)) (by simp)

/-- **The universe hierarchy is injective.** -/
theorem TyEq.univ_inj {Γ : Ctx} {i j : ℕ} (h : TyEq Γ (univ i) (univ j)) : i = j := by
  have hv := h.valid declEq
  have hs := SubstR.idsOf h.wf
  obtain ⟨l, I, hI, -⟩ := hv.1.red hs
  have hIeq := hv.2.2 Γ ids ids hs l I hI
  simp only [subst_univ] at hI hIeq
  have hD := hI.univ_inv _ hIeq
  have e := hD.red.of_whnf (Whnf.univ _)
  simp only [univ.injEq] at e
  exact e

/-! ### Neutral terms in the empty context -/

/-- For typing judgements: a neutral term has a declared head variable. -/
def Jd.NeHead : Jd → Prop
  | .ty Γ t _ => Neutral t → ∃ n B, Lookup Γ n B
  | _ => True

theorem Der.neHead {J : Jd} (h : Der J) : J.NeHead := by
  induction h
  case var _ hl _ => exact fun _ => ⟨_, _, hl⟩
  case app _ _ ihf _ =>
    intro hn
    cases hn with
    | app _ hf => exact ihf hf
  case natrec _ _ _ _ _ _ _ ihn =>
    intro hn
    cases hn with
    | natrec _ _ _ h => exact ihn h
  case emptyrec _ _ _ ihe =>
    intro hn
    cases hn with
    | emptyrec _ h => exact ihe h
  case conv _ _ iht _ => exact iht
  all_goals first
    | trivial
    | (intro hn; cases hn)

/-- **There is no closed neutral term.** -/
theorem Neutral.not_closed {n A : Tm} (hn : Neutral n) (h : HasTy [] n A) : False := by
  obtain ⟨k, B, hl⟩ := (Der.neHead h) hn
  cases hl

/-! ### Canonicity and consistency -/

/-- The numeral of a natural number. -/
def numeral : ℕ → Tm
  | 0 => zero
  | k + 1 => succ (numeral k)

theorem NatR.canonical {t u : Tm} (h : NatR declEq ([] : Ctx) t u) : ∃ k, DEq [] t (numeral k) nat := by
  induction h with
  | zero ht _ => exact ⟨0, ht.red.deq⟩
  | succ ht _ _ _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, Der.trans ht.red.deq (Der.succCong hk)⟩
  | ne ht _ hn _ _ => exact (hn.not_closed ht.tyR).elim

/-- **Canonicity**: a closed natural number is definitionally equal to a numeral. -/
theorem canonicity {t : Tm} (h : HasTy [] t nat) : ∃ k, DEq [] t (numeral k) nat := by
  obtain ⟨l, I, hI, ht⟩ := h.tmR
  have hN := TyR.nat_canon (E := declEq) h.wf l
  exact NatR.canonical (((TyR.irrel hI hN).2 _ _).mp ht)

/-- **Consistency**: the empty type has no closed term. -/
theorem consistency {t : Tm} (h : HasTy [] t empty) : False := by
  obtain ⟨l, I, hI, ht⟩ := h.tmR
  have hE := TyR.empty_canon (E := declEq) h.wf l
  obtain ⟨n, -, hn, -, hne, -⟩ := ((TyR.irrel hI hE).2 _ _).mp ht
  exact hne.not_closed hn.tyR

end MLTT
