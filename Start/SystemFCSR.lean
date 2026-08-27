/-
**Subject reduction for Church-style System F.**

`Start/SystemFC.lean` derives strong normalization of the annotated calculus from the Curry-style
theorem by erasure; that argument never inspects the types of the reducts.  This file proves that
the reducts are typable at all, and at the same type: the two substitution lemmas of the annotated
calculus and the preservation theorem.

Typing is syntax directed here — the two quantifier rules have their own term formers — so the
generation lemma that made the Curry-style proof delicate is a plain inversion.

* `SystemFC.TypingC.lift_gen`, `SystemFC.TypingC.lift_one` — weakening in the term variables;
* `SystemFC.TypingC.substTy`, `SystemFC.TypingC.shiftTy` — substitution of the type variables;
* `SystemFC.TypingC.subst_gen`, `SystemFC.TypingC.subst_zero` — substitution of a term variable;
* `SystemFC.TypingC.preservation` — **subject reduction**: both β and type-β preserve typing.
-/

import Start.SystemFC

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemFC

open Lambda SystemF

/-! ### Weakening in the term variables -/

/-- Weakening, in the general form needed to go under an abstraction. -/
theorem TypingC.lift_gen {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    ∀ (k : ℕ) (Δ : List FTy),
      (∀ i A', Γ[i]? = some A' → Δ[if i < k then i else i + 1]? = some A') →
      TypingC Δ (lift 1 k t) A := by
  induction h with
  | @var Γ i A hi =>
      intro k Δ hk
      have hb := hk i A hi
      by_cases hik : i < k
      · rw [if_pos hik] at hb
        have hl : lift 1 k (FTm.var i) = FTm.var i := by simp [lift, hik]
        rw [hl]
        exact TypingC.var hb
      · rw [if_neg hik] at hb
        have hl : lift 1 k (FTm.var i) = FTm.var (i + 1) := by simp [lift, hik]
        rw [hl]
        exact TypingC.var hb
  | app _ _ iha ihb =>
      intro k Δ hk
      exact TypingC.app (iha k Δ hk) (ihb k Δ hk)
  | @lam Γ t A B _ ih =>
      intro k Δ hk
      refine TypingC.lam ?_
      refine ih (k + 1) (A :: Δ) ?_
      intro i A' hi
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          simp
      | succ j =>
          have hj : Γ[j]? = some A' := by simpa using hi
          have hb := hk j A' hj
          by_cases hjk : j < k
          · rw [if_pos hjk] at hb
            rw [if_pos (by omega : j + 1 < k + 1)]
            simpa using hb
          · rw [if_neg hjk] at hb
            rw [if_neg (by omega : ¬ (j + 1 < k + 1))]
            simpa using hb
  | @tlam Γ t A _ ih =>
      intro k Δ hk
      refine TypingC.tlam ?_
      refine ih k (Δ.map tyShift) ?_
      intro i A' hi
      rw [List.getElem?_map] at hi ⊢
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : tyShift A₀ = A' := by simpa using hi
          subst hA'
          rw [hk i A₀ hΓ]
          rfl
  | tapp B _ ih =>
      intro k Δ hk
      exact TypingC.tapp B (ih k Δ hk)

/-- Weakening by one variable in front of the context. -/
theorem TypingC.lift_one {Δ : List FTy} {u : FTm} {A : FTy} (h : TypingC Δ u A) (B : FTy) :
    TypingC (B :: Δ) (lift 1 0 u) A := by
  refine h.lift_gen 0 (B :: Δ) ?_
  intro i A' hi
  simpa using hi

/-! ### Substitution of the type variables -/

/-- **A derivation of the annotated calculus may be substituted in its type variables.** -/
theorem TypingC.substTy {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    ∀ s : ℕ → FTy, TypingC (Γ.map (tySubst s)) (substTyTm s t) (tySubst s A) := by
  induction h with
  | @var Γ i A hi =>
      intro s
      refine TypingC.var ?_
      rw [List.getElem?_map, hi]
      rfl
  | app _ _ iha ihb => intro s; exact TypingC.app (iha s) (ihb s)
  | lam _ ih => intro s; exact TypingC.lam (ih s)
  | @tlam Γ t A _ ih =>
      intro s
      refine TypingC.tlam ?_
      have hmap : (Γ.map tyShift).map (tySubst (ups s))
          = (Γ.map (tySubst s)).map tyShift := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun X _ => tySubst_tyShift s X
      have := ih (ups s)
      rwa [hmap] at this
  | @tapp Γ t A B _ ih =>
      intro s
      rw [tySubst_tyInst]
      exact TypingC.tapp _ (ih s)

/-- Weakening a derivation of the annotated calculus by a fresh type variable. -/
theorem TypingC.shiftTy {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    TypingC (Γ.map tyShift) (shiftTyTm t) (tyShift A) := by
  have hsub := h.substTy (fun i => FTy.var (i + 1))
  have hA : tySubst (fun i => FTy.var (i + 1)) A = tyShift A := (tyShift_eq_tySubst A).symm
  have hΓ : Γ.map (tySubst (fun i => FTy.var (i + 1))) = Γ.map tyShift :=
    List.map_congr_left fun X _ => (tyShift_eq_tySubst X).symm
  rw [hA, hΓ] at hsub
  exact hsub

/-! ### Substitution of a term variable -/

/-- **Substituting a term variable**, in the general form needed to go under an abstraction. -/
theorem TypingC.subst_gen {Γ : List FTy} {t : FTm} {B : FTy} (h : TypingC Γ t B) :
    ∀ (k : ℕ) (Δ : List FTy) (u : FTm) (A : FTy),
      Γ[k]? = some A → TypingC Δ u A →
      (∀ i A', i < k → Γ[i]? = some A' → Δ[i]? = some A') →
      (∀ i A', k ≤ i → Γ[i + 1]? = some A' → Δ[i]? = some A') →
      TypingC Δ (subst u k t) B := by
  induction h with
  | @var Γ i B hi =>
      intro k Δ u A hk hu hlt hge
      by_cases hik : i = k
      · subst hik
        have hAB : A = B := by rw [hk] at hi; simpa using hi
        subst hAB
        have hl : subst u i (FTm.var i) = u := by simp [subst]
        rw [hl]
        exact hu
      · by_cases hgt : i > k
        · have hl : subst u k (FTm.var i) = FTm.var (i - 1) := by
            simp [subst, hik, hgt]
          rw [hl]
          refine TypingC.var (hge (i - 1) B (by omega) ?_)
          have : i - 1 + 1 = i := by omega
          rw [this]
          exact hi
        · have hl : subst u k (FTm.var i) = FTm.var i := by
            simp [subst, hik, hgt]
          rw [hl]
          exact TypingC.var (hlt i B (by omega) hi)
  | app _ _ iha ihb =>
      intro k Δ u A hk hu hlt hge
      exact TypingC.app (iha k Δ u A hk hu hlt hge) (ihb k Δ u A hk hu hlt hge)
  | @lam Γ t A₀ B₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      refine TypingC.lam ?_
      refine ih (k + 1) (A₀ :: Δ) (lift 1 0 u) A (by simpa using hk) (hu.lift_one A₀) ?_ ?_
      · intro i A' hi hget
        cases i with
        | zero => simpa using hget
        | succ j =>
            have hj : Γ[j]? = some A' := by simpa using hget
            have := hlt j A' (by omega) hj
            simpa using this
      · intro i A' hi hget
        cases i with
        | zero => omega
        | succ j =>
            have hj : Γ[j + 1]? = some A' := by simpa using hget
            have := hge j A' (by omega) hj
            simpa using this
  | @tlam Γ t A₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      refine TypingC.tlam ?_
      refine ih k (Δ.map tyShift) (shiftTyTm u) (tyShift A) ?_ hu.shiftTy ?_ ?_
      · rw [List.getElem?_map, hk]; rfl
      · intro i A' hi hget
        rw [List.getElem?_map] at hget ⊢
        match hΓ : Γ[i]? with
        | none => rw [hΓ] at hget; exact absurd hget (by simp)
        | some A₁ =>
            rw [hΓ] at hget
            have hA' : tyShift A₁ = A' := by simpa using hget
            subst hA'
            rw [hlt i A₁ hi hΓ]
            rfl
      · intro i A' hi hget
        rw [List.getElem?_map] at hget ⊢
        match hΓ : Γ[i + 1]? with
        | none => rw [hΓ] at hget; exact absurd hget (by simp)
        | some A₁ =>
            rw [hΓ] at hget
            have hA' : tyShift A₁ = A' := by simpa using hget
            subst hA'
            rw [hge i A₁ hi hΓ]
            rfl
  | tapp B₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      exact TypingC.tapp B₀ (ih k Δ u A hk hu hlt hge)

/-- **Substituting the variable `0`**, the form used by the β-rule. -/
theorem TypingC.subst_zero {Γ : List FTy} {t u : FTm} {A B : FTy}
    (ht : TypingC (A :: Γ) t B) (hu : TypingC Γ u A) : TypingC Γ (subst u 0 t) B := by
  refine ht.subst_gen 0 Γ u A (by simp) hu ?_ ?_
  · intro i A' hi _
    omega
  · intro i A' _ hget
    simpa using hget

/-! ### Subject reduction -/

/-- **Subject reduction for Church-style System F**: β and type-β preserve typing. -/
theorem TypingC.preservation {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    ∀ t' : FTm, step t t' → TypingC Γ t' A := by
  induction h with
  | var _ => intro t' hs; cases hs
  | @app Γ a b A₀ B ha hb iha ihb =>
      intro t' hs
      cases hs with
      | beta A₁ s u =>
          cases ha with
          | lam hbody => exact hbody.subst_zero hb
      | appL _ hstep => exact TypingC.app (iha _ hstep) hb
      | appR _ hstep => exact TypingC.app ha (ihb _ hstep)
  | @lam Γ t A₀ B _ ih =>
      intro t' hs
      cases hs with
      | lam _ hstep => exact TypingC.lam (ih _ hstep)
  | @tlam Γ t A₀ _ ih =>
      intro t' hs
      cases hs with
      | tlam hstep => exact TypingC.tlam (ih _ hstep)
  | @tapp Γ t A₀ B hall ih =>
      intro t' hs
      cases hs with
      | tbeta s _ =>
          cases hall with
          | tlam hbody =>
              have hsub := hbody.substTy (tyScons B)
              have hmap : (Γ.map tyShift).map (tySubst (tyScons B)) = Γ := by
                simp only [List.map_map, Function.comp_def]
                refine (List.map_congr_left fun X _ => ?_).trans (List.map_id Γ)
                exact tyInst_tyShift B X
              rw [hmap] at hsub
              exact hsub
      | tapp _ hstep => exact TypingC.tapp B (ih _ hstep)

end SystemFC
