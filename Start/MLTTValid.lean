/-
**Martin-Löf type theory: validity** — milestone M30 (`M30-MLTT-FUND`).

The semantic judgements of Abel, Öhman and Vezzosi's fundamental theorem, closed under related
substitutions:

* `MLTT.SubstR E Γ Δ σ σ'` — `σ` and `σ'` substitute for the variables of `Γ` terms of `Δ`
  that are pointwise reducibly equal, at the substituted types;
* `MLTT.ValidCtx`, `MLTT.ValidTy`, `MLTT.ValidTm`, `MLTT.ValidTyEq`, `MLTT.ValidEq` —
  valid contexts, types, terms and equations: under related substitutions, the substituted type
  is reducible and the substituted terms (types) are reducibly equal.  The term judgements
  quantify over all reducibility proofs of the substituted type, which irrelevance permits.

Properties of related substitutions in valid contexts: `SubstR.symm`, `SubstR.trans`,
`SubstR.wk` (weakening of the target), `SubstR.cons` (extension by related terms),
`SubstR.lookup` (related at every variable), `SubstR.up` (lifting under a binder),
`SubstR.ids` (the identity substitution is related to itself).
-/

import Start.MLTTLogRelWk

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Related substitutions -/

/-- The tail of a substitution. -/
def stail (σ : ℕ → Tm) : ℕ → Tm := fun n => σ (n + 1)

@[simp] theorem stail_scons (a : Tm) (σ : ℕ → Tm) : stail (scons a σ) = σ := rfl

/-- **Related substitutions** from `Γ` to `Δ`. -/
def SubstR (E : GenEq) : Ctx → Ctx → (ℕ → Tm) → (ℕ → Tm) → Prop
  | [], Δ, _, _ => WfCtx Δ
  | A :: Γ, Δ, σ, σ' => SubstR E Γ Δ (stail σ) (stail σ') ∧
      ∃ l I, TyR E l Δ (subst (stail σ) A) I ∧ I.tmEq (σ 0) (σ' 0)

theorem SubstR.wfCtx {E : GenEq} : ∀ {Γ Δ : Ctx} {σ σ' : ℕ → Tm}, SubstR E Γ Δ σ σ' → WfCtx Δ
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => SubstR.wfCtx h.1

/-! ### Validity -/

/-- A valid type: reducible under related substitutions, at one level, with the two
substitution instances reducibly equal. -/
def ValidTy (E : GenEq) (Γ : Ctx) (A : Tm) : Prop :=
  ∃ l, ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ I, TyR E l Δ (subst σ A) I ∧ I.tyEq (subst σ' A)

/-- Valid contexts: each type valid in the context before it. -/
def ValidCtx (E : GenEq) : Ctx → Prop
  | [] => True
  | A :: Γ => ValidCtx E Γ ∧ ValidTy E Γ A

/-- A valid term of a valid type. -/
def ValidTm (E : GenEq) (Γ : Ctx) (t A : Tm) : Prop :=
  ValidTy E Γ A ∧ ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∀ l I, TyR E l Δ (subst σ A) I →
    I.tmEq (subst σ t) (subst σ' t)

/-- A valid type equation. -/
def ValidTyEq (E : GenEq) (Γ : Ctx) (A B : Tm) : Prop :=
  ValidTy E Γ A ∧ ValidTy E Γ B ∧ ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∀ l I, TyR E l Δ (subst σ A) I →
    I.tyEq (subst σ' B)

/-- A valid term equation. -/
def ValidEq (E : GenEq) (Γ : Ctx) (t u A : Tm) : Prop :=
  ValidTm E Γ t A ∧ ValidTm E Γ u A ∧ ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∀ l I,
    TyR E l Δ (subst σ A) I → I.tmEq (subst σ t) (subst σ' u)

/-! ### Properties of related substitutions -/

theorem subst_shift_stail (σ : ℕ → Tm) (A : Tm) : subst σ (shift A) = subst (stail σ) A := by
  simp only [shift, subst_rename]; rfl

/-- A substitution related to another is related to itself, and related substitutions are
symmetric and transitive, in a valid context. -/
theorem SubstR.per {E : GenEq} : ∀ {Γ : Ctx}, ValidCtx E Γ → ∀ {Δ : Ctx},
    (∀ {σ σ'}, SubstR E Γ Δ σ σ' → SubstR E Γ Δ σ' σ) ∧
    (∀ {σ σ' σ''}, SubstR E Γ Δ σ σ' → SubstR E Γ Δ σ' σ'' → SubstR E Γ Δ σ σ'')
  | [], _, _ => ⟨fun h => h, fun h _ => h⟩
  | A :: Γ, hΓ, Δ => by
      obtain ⟨hΓ', l₀, hA⟩ := hΓ
      have ih := SubstR.per (Δ := Δ) hΓ'
      refine ⟨?_, ?_⟩
      · rintro σ σ' ⟨ht, l, I, hI, hab⟩
        refine ⟨ih.1 ht, ?_⟩
        -- the type at `σ'` is reducible, and reducibly equal to the type at `σ`
        obtain ⟨J, hJ, hJeq⟩ := hA Δ (stail σ') (stail σ) (ih.1 ht)
        obtain ⟨K, hK, hKeq⟩ := hA Δ (stail σ) (stail σ') ht
        have g := TyR.good l hI
        refine ⟨l₀, J, hJ, ?_⟩
        have hconv := (TyR.good l₀ hJ).conv hI hJeq
        exact ((hconv _ _).mpr (g.symm hab))
      · rintro σ σ' σ'' ⟨ht, l, I, hI, hab⟩ ⟨ht', l', I', hI', hbc⟩
        refine ⟨ih.2 ht ht', l, I, hI, ?_⟩
        -- transport the second equation to the type at `σ`
        obtain ⟨K, hK, hKeq⟩ := hA Δ (stail σ) (stail σ') ht
        have hI'I : ∀ t u, I'.tmEq t u ↔ I.tmEq t u := by
          intro t u
          have h1 := ((TyR.good l₀ hK).conv hI' hKeq t u)
          have h2 := (TyR.irrel hK hI).2 t u
          exact h1.symm.trans h2
        exact (TyR.good l hI).trans hab ((hI'I _ _).mp hbc)

theorem SubstR.symm {E : GenEq} {Γ Δ : Ctx} (hΓ : ValidCtx E Γ) {σ σ' : ℕ → Tm}
    (h : SubstR E Γ Δ σ σ') : SubstR E Γ Δ σ' σ :=
  (SubstR.per hΓ).1 h

theorem SubstR.trans {E : GenEq} {Γ Δ : Ctx} (hΓ : ValidCtx E Γ) {σ σ' σ'' : ℕ → Tm}
    (h : SubstR E Γ Δ σ σ') (h' : SubstR E Γ Δ σ' σ'') : SubstR E Γ Δ σ σ'' :=
  (SubstR.per hΓ).2 h h'

theorem SubstR.left {E : GenEq} {Γ Δ : Ctx} (hΓ : ValidCtx E Γ) {σ σ' : ℕ → Tm}
    (h : SubstR E Γ Δ σ σ') : SubstR E Γ Δ σ σ :=
  h.trans hΓ (h.symm hΓ)

theorem SubstR.right {E : GenEq} {Γ Δ : Ctx} (hΓ : ValidCtx E Γ) {σ σ' : ℕ → Tm}
    (h : SubstR E Γ Δ σ σ') : SubstR E Γ Δ σ' σ' :=
  (h.symm hΓ).trans hΓ h

/-- **Weakening of related substitutions.** -/
theorem SubstR.wk {E : GenEq} : ∀ {Γ Δ Δ' : Ctx} {σ σ' : ℕ → Tm} {ρ : ℕ → ℕ},
    SubstR E Γ Δ σ σ' → Wk Δ Δ' ρ →
    SubstR E Γ Δ' (fun n => rename ρ (σ n)) (fun n => rename ρ (σ' n))
  | [], _, _, _, _, _, _, hρ => hρ.2
  | A :: Γ, Δ, Δ', σ, σ', ρ, ⟨ht, l, I, hI, hab⟩, hρ => by
      refine ⟨SubstR.wk ht hρ, ?_⟩
      obtain ⟨J, hJ, -, hJtm⟩ := TyR.wk l hI hρ
      refine ⟨l, J, ?_, hJtm _ _ hab⟩
      have e : rename ρ (subst (stail σ) A) = subst (stail fun n => rename ρ (σ n)) A := by
        rw [rename_subst]; rfl
      rw [← e]
      exact hJ

/-- Extending related substitutions by related terms. -/
theorem SubstR.cons {E : GenEq} {Γ Δ : Ctx} {σ σ' : ℕ → Tm} {A a b : Tm} {l : ℕ} {I : Interp}
    (h : SubstR E Γ Δ σ σ') (hI : TyR E l Δ (subst σ A) I) (hab : I.tmEq a b) :
    SubstR E (A :: Γ) Δ (scons a σ) (scons b σ') :=
  ⟨h, l, I, hI, hab⟩

/-- **Related substitutions are related at every variable.** -/
theorem SubstR.lookup {E : GenEq} : ∀ {Γ : Ctx} {n : ℕ} {A : Tm}, Lookup Γ n A → ValidCtx E Γ →
    ∀ {Δ : Ctx} {σ σ' : ℕ → Tm}, SubstR E Γ Δ σ σ' → ∀ l I, TyR E l Δ (subst σ A) I →
      I.tmEq (σ n) (σ' n)
  | _, _, _, Lookup.zero Γ A, ⟨_, _⟩, Δ, σ, σ', ⟨_, l', I', hI', hab⟩, l, I, hI => by
      rw [subst_shift_stail] at hI
      exact ((TyR.irrel hI' hI).2 _ _).mp hab
  | _, _, _, @Lookup.succ Γ n A B hl, ⟨hΓ, _⟩, Δ, σ, σ', ⟨ht, _⟩, l, I, hI => by
      rw [subst_shift_stail] at hI
      exact SubstR.lookup hl hΓ ht l I hI

/-! ### Validity at the identity -/

/-- A valid type is reducible at related substitutions (with some interpretation). -/
theorem ValidTy.red {E : GenEq} {Γ : Ctx} {A : Tm} (h : ValidTy E Γ A) {Δ : Ctx} {σ σ' : ℕ → Tm}
    (hs : SubstR E Γ Δ σ σ') : ∃ l I, TyR E l Δ (subst σ A) I ∧ I.tyEq (subst σ' A) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨I, hI, hIeq⟩ := hl Δ σ σ' hs
  exact ⟨l, I, hI, hIeq⟩

/-- Lifting related substitutions under a binder: `up σ` and `up σ'` are related from `A :: Γ`
to `subst σ A :: Δ`. -/
theorem SubstR.up {E : GenEq} {Γ Δ : Ctx} (hΓ : ValidCtx E Γ) {A : Tm} (hA : ValidTy E Γ A)
    {σ σ' : ℕ → Tm} (h : SubstR E Γ Δ σ σ') (hwf : WfCtx (subst σ A :: Δ)) :
    SubstR E (A :: Γ) (subst σ A :: Δ) (MLTT.up σ) (MLTT.up σ') := by
  have hρ : Wk Δ (subst σ A :: Δ) Nat.succ := ⟨RenOk.shift Δ _, hwf⟩
  have hw := h.wk hρ
  obtain ⟨l, I, hI, -⟩ := hA.red (h.left hΓ)
  obtain ⟨J, hJ, -, -⟩ := TyR.wk l hI hρ
  refine ⟨hw, l, J, ?_, ?_⟩
  · have e : rename Nat.succ (subst σ A) = subst (stail (MLTT.up σ)) A := by
      rw [rename_subst]; rfl
    rw [← e]; exact hJ
  · -- the variable `0` is reducible at the weakened type
    have hJ' : TyR E l (subst σ A :: Δ) (shift (subst σ A)) J := hJ
    have hv : HasTy (subst σ A :: Δ) (var 0) (shift (subst σ A)) :=
      Der.var hwf (Lookup.zero _ _)
    exact hJ'.var hv

/-- **The identity substitution is related to itself** in a well-formed valid context. -/
theorem SubstR.ids {E : GenEq} : ∀ {Γ : Ctx}, ValidCtx E Γ → WfCtx Γ →
    SubstR E Γ Γ MLTT.ids MLTT.ids
  | [], _, hwf => hwf
  | A :: Γ, ⟨hΓ, hA⟩, hwf => by
      have hwfΓ : WfCtx Γ := by cases hwf with | cons h _ => exact h
      have hid := SubstR.ids hΓ hwfΓ
      have hup := SubstR.up hΓ hA hid (by simpa using hwf)
      simp only [subst_ids] at hup
      have e : MLTT.up MLTT.ids = MLTT.ids := funext up_ids
      rw [e] at hup
      exact hup

end MLTT
