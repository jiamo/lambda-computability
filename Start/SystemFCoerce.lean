/-
**System F with type-equality coercions** — task `M25-SYSTEM-FC`, the core of GHC in the style of
Sulzmann, Chakravarty, Peyton Jones and Donnelly (2007), over the types of `Start/SystemF.lean`
(type variables, `→` and `∀`).

* `FCoerce.Co` — coercions: reflexivity, symmetry, transitivity, application of the arrow
  constructor (`γ₁ → γ₂`), `∀`-congruence, instantiation (`γ @ C`), axioms, and the two
  decompositions of an arrow coercion (`left γ`, `right γ`) used by the push rule;
* `FCoerce.CoTyping Ax γ A B` — `γ : A ~ B` with respect to an axiom set `Ax`;
* `FCoerce.Tm`, `FCoerce.Typing` — Church-style System F terms with the cast `t ▷ γ`;
* `FCoerce.Step` — β, type-β, the congruences, and the coercion rules: collapsing two casts
  (`(t ▷ γ₁) ▷ γ₂ ⟶ t ▷ (γ₁ ; γ₂)`), and pushing a cast through an application and a type
  application;
* `FCoerce.Typing.preservation` — **subject reduction**, for axiom sets of closed types
  (`AxClosed`);
* `FCoerce.Consistent` — **consistency of the axiom set**: no coercion relates an arrow type and a
  `∀`-type;
* `FCoerce.Typing.progress` — **progress for closed terms, under the consistency hypothesis**: a
  closed well-typed term is a value or takes a step.
-/

import Start.SystemFSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FCoerce

open SystemF

/-! ### Coercions -/

/-- Coercions, the evidence of type equalities. -/
inductive Co where
  /-- Reflexivity. -/
  | refl : FTy → Co
  /-- Symmetry. -/
  | sym : Co → Co
  /-- Transitivity. -/
  | trans : Co → Co → Co
  /-- Application of the arrow constructor: `γ₁ → γ₂`. -/
  | arr : Co → Co → Co
  /-- Congruence under `∀`. -/
  | all : Co → Co
  /-- Instantiation: `γ @ C`. -/
  | inst : Co → FTy → Co
  /-- The `i`-th axiom. -/
  | ax : ℕ → Co
  /-- Left decomposition of an arrow coercion. -/
  | left : Co → Co
  /-- Right decomposition of an arrow coercion. -/
  | right : Co → Co

/-- Substituting the type variables of a coercion. -/
def substTyCo (s : ℕ → FTy) : Co → Co
  | .refl A => .refl (tySubst s A)
  | .sym γ => .sym (substTyCo s γ)
  | .trans γ δ => .trans (substTyCo s γ) (substTyCo s δ)
  | .arr γ δ => .arr (substTyCo s γ) (substTyCo s δ)
  | .all γ => .all (substTyCo (ups s) γ)
  | .inst γ C => .inst (substTyCo s γ) (tySubst s C)
  | .ax i => .ax i
  | .left γ => .left (substTyCo s γ)
  | .right γ => .right (substTyCo s γ)

/-- **Coercion typing**: `CoTyping Ax γ A B` is `γ : A ~ B` for the axiom set `Ax`. -/
inductive CoTyping (Ax : List (FTy × FTy)) : Co → FTy → FTy → Prop
  /-- Reflexivity. -/
  | refl (A : FTy) : CoTyping Ax (.refl A) A A
  /-- Symmetry. -/
  | sym {γ : Co} {A B : FTy} : CoTyping Ax γ A B → CoTyping Ax (.sym γ) B A
  /-- Transitivity. -/
  | trans {γ δ : Co} {A B C : FTy} :
      CoTyping Ax γ A B → CoTyping Ax δ B C → CoTyping Ax (.trans γ δ) A C
  /-- Application of the arrow constructor. -/
  | arr {γ δ : Co} {A₁ A₂ B₁ B₂ : FTy} : CoTyping Ax γ A₁ A₂ → CoTyping Ax δ B₁ B₂ →
      CoTyping Ax (.arr γ δ) (.arrow A₁ B₁) (.arrow A₂ B₂)
  /-- Congruence under `∀`. -/
  | all {γ : Co} {A B : FTy} : CoTyping Ax γ A B → CoTyping Ax (.all γ) (.all A) (.all B)
  /-- Instantiation. -/
  | inst {γ : Co} {A B : FTy} (C : FTy) : CoTyping Ax γ (.all A) (.all B) →
      CoTyping Ax (.inst γ C) (tyInst C A) (tyInst C B)
  /-- An axiom. -/
  | ax {i : ℕ} {A B : FTy} : Ax[i]? = some (A, B) → CoTyping Ax (.ax i) A B
  /-- Left decomposition. -/
  | left {γ : Co} {A₁ A₂ B₁ B₂ : FTy} :
      CoTyping Ax γ (.arrow A₁ B₁) (.arrow A₂ B₂) → CoTyping Ax (.left γ) A₁ A₂
  /-- Right decomposition. -/
  | right {γ : Co} {A₁ A₂ B₁ B₂ : FTy} :
      CoTyping Ax γ (.arrow A₁ B₁) (.arrow A₂ B₂) → CoTyping Ax (.right γ) B₁ B₂

/-- The axioms relate closed types: they are fixed by every type substitution. -/
def AxClosed (Ax : List (FTy × FTy)) : Prop :=
  ∀ p ∈ Ax, ∀ s : ℕ → FTy, tySubst s p.1 = p.1 ∧ tySubst s p.2 = p.2

/-- Coercion typing is stable under type substitution, for closed axioms. -/
theorem CoTyping.substTy {Ax : List (FTy × FTy)} (hAx : AxClosed Ax) {γ : Co} {A B : FTy}
    (h : CoTyping Ax γ A B) :
    ∀ s : ℕ → FTy, CoTyping Ax (substTyCo s γ) (tySubst s A) (tySubst s B) := by
  induction h with
  | refl A => intro s; exact .refl _
  | sym _ ih => intro s; exact .sym (ih s)
  | trans _ _ ih₁ ih₂ => intro s; exact .trans (ih₁ s) (ih₂ s)
  | arr _ _ ih₁ ih₂ => intro s; exact .arr (ih₁ s) (ih₂ s)
  | all _ ih => intro s; exact .all (ih (ups s))
  | inst C _ ih =>
      intro s
      rw [tySubst_tyInst, tySubst_tyInst]
      exact .inst _ (ih s)
  | @ax i A B hi =>
      intro s
      obtain ⟨h1, h2⟩ := hAx (A, B) (List.mem_of_getElem? hi) s
      simp only at h1 h2
      rw [h1, h2]
      exact .ax hi
  | left _ ih => intro s; exact .left (ih s)
  | right _ ih => intro s; exact .right (ih s)

/-! ### Terms -/

/-- Terms of System F with coercions. -/
inductive Tm where
  /-- A term variable. -/
  | var : ℕ → Tm
  /-- Application. -/
  | app : Tm → Tm → Tm
  /-- Abstraction, annotated with the type of the bound variable. -/
  | lam : FTy → Tm → Tm
  /-- Abstraction over a type variable. -/
  | tlam : Tm → Tm
  /-- Instantiation. -/
  | tapp : Tm → FTy → Tm
  /-- The cast `t ▷ γ`. -/
  | cast : Tm → Co → Tm

/-- Substituting the type variables of a term. -/
def substTyTm (s : ℕ → FTy) : Tm → Tm
  | .var i => .var i
  | .app a b => .app (substTyTm s a) (substTyTm s b)
  | .lam A t => .lam (tySubst s A) (substTyTm s t)
  | .tlam t => .tlam (substTyTm (ups s) t)
  | .tapp t B => .tapp (substTyTm s t) (tySubst s B)
  | .cast t γ => .cast (substTyTm s t) (substTyCo s γ)

/-- Weakening the type variables of a term. -/
def shiftTyTm (t : Tm) : Tm := substTyTm (fun i => FTy.var (i + 1)) t

/-- Lifting the term variables. -/
def lift (n k : ℕ) : Tm → Tm
  | .var y => if y < k then .var y else .var (y + n)
  | .app a b => .app (lift n k a) (lift n k b)
  | .lam A t => .lam A (lift n (k + 1) t)
  | .tlam t => .tlam (lift n k t)
  | .tapp t B => .tapp (lift n k t) B
  | .cast t γ => .cast (lift n k t) γ

/-- Substituting a term variable. -/
def subst (u : Tm) (x : ℕ) : Tm → Tm
  | .var y => if y = x then u else if y > x then .var (y - 1) else .var y
  | .app a b => .app (subst u x a) (subst u x b)
  | .lam A t => .lam A (subst (lift 1 0 u) (x + 1) t)
  | .tlam t => .tlam (subst (shiftTyTm u) x t)
  | .tapp t B => .tapp (subst u x t) B
  | .cast t γ => .cast (subst u x t) γ

/-! ### Typing -/

/-- **Typing for System F with coercions**, relative to the axiom set `Ax`. -/
inductive Typing (Ax : List (FTy × FTy)) : List FTy → Tm → FTy → Prop
  /-- A variable. -/
  | var {Γ : List FTy} {i : ℕ} {A : FTy} : Γ[i]? = some A → Typing Ax Γ (.var i) A
  /-- Application. -/
  | app {Γ : List FTy} {a b : Tm} {A B : FTy} :
      Typing Ax Γ a (.arrow A B) → Typing Ax Γ b A → Typing Ax Γ (.app a b) B
  /-- Abstraction. -/
  | lam {Γ : List FTy} {t : Tm} {A B : FTy} :
      Typing Ax (A :: Γ) t B → Typing Ax Γ (.lam A t) (.arrow A B)
  /-- Abstraction over a type variable. -/
  | tlam {Γ : List FTy} {t : Tm} {A : FTy} :
      Typing Ax (Γ.map tyShift) t A → Typing Ax Γ (.tlam t) (.all A)
  /-- Instantiation. -/
  | tapp {Γ : List FTy} {t : Tm} {A : FTy} (B : FTy) :
      Typing Ax Γ t (.all A) → Typing Ax Γ (.tapp t B) (tyInst B A)
  /-- The cast. -/
  | cast {Γ : List FTy} {t : Tm} {γ : Co} {A B : FTy} :
      Typing Ax Γ t A → CoTyping Ax γ A B → Typing Ax Γ (.cast t γ) B

/-! ### Reduction -/

/-- One step of reduction. -/
inductive Step : Tm → Tm → Prop
  /-- β. -/
  | beta (A : FTy) (t u : Tm) : Step (.app (.lam A t) u) (subst u 0 t)
  /-- Type-β. -/
  | tbeta (t : Tm) (B : FTy) : Step (.tapp (.tlam t) B) (substTyTm (tyScons B) t)
  /-- Two casts collapse into one: `(t ▷ γ) ▷ δ ⟶ t ▷ (γ ; δ)`. -/
  | castTrans (t : Tm) (γ δ : Co) : Step (.cast (.cast t γ) δ) (.cast t (.trans γ δ))
  /-- Pushing a cast through an application:
  `((λx:A. t) ▷ γ) u ⟶ ((λx:A. t) (u ▷ sym (left γ))) ▷ right γ`. -/
  | pushApp (A : FTy) (t : Tm) (γ : Co) (u : Tm) :
      Step (.app (.cast (.lam A t) γ) u)
        (.cast (.app (.lam A t) (.cast u (.sym (.left γ)))) (.right γ))
  /-- Pushing a cast through a type application: `((Λ. t) ▷ γ) C ⟶ ((Λ. t) C) ▷ (γ @ C)`. -/
  | pushTApp (t : Tm) (γ : Co) (C : FTy) :
      Step (.tapp (.cast (.tlam t) γ) C) (.cast (.tapp (.tlam t) C) (.inst γ C))
  /-- Congruence, left of an application. -/
  | appL {a a' : Tm} (b : Tm) : Step a a' → Step (.app a b) (.app a' b)
  /-- Congruence, right of an application. -/
  | appR (a : Tm) {b b' : Tm} : Step b b' → Step (.app a b) (.app a b')
  /-- Congruence, under an abstraction. -/
  | lam (A : FTy) {t t' : Tm} : Step t t' → Step (.lam A t) (.lam A t')
  /-- Congruence, under a type abstraction. -/
  | tlam {t t' : Tm} : Step t t' → Step (.tlam t) (.tlam t')
  /-- Congruence, in an instantiation. -/
  | tapp {t t' : Tm} (B : FTy) : Step t t' → Step (.tapp t B) (.tapp t' B)
  /-- Congruence, in a cast. -/
  | cast {t t' : Tm} (γ : Co) : Step t t' → Step (.cast t γ) (.cast t' γ)

/-! ### Weakening and substitution -/

variable {Ax : List (FTy × FTy)}

/-- Weakening, in the general form needed to go under an abstraction. -/
theorem Typing.lift_gen {Γ : List FTy} {t : Tm} {A : FTy} (h : Typing Ax Γ t A) :
    ∀ (k : ℕ) (Δ : List FTy),
      (∀ i A', Γ[i]? = some A' → Δ[if i < k then i else i + 1]? = some A') →
      Typing Ax Δ (lift 1 k t) A := by
  induction h with
  | @var Γ i A hi =>
      intro k Δ hk
      have hb := hk i A hi
      by_cases hik : i < k
      · rw [ite_eq_left hik] at hb
        have hl : lift 1 k (Tm.var i) = Tm.var i := by simp [lift, hik]
        rw [hl]
        exact Typing.var hb
      · rw [ite_eq_right hik] at hb
        have hl : lift 1 k (Tm.var i) = Tm.var (i + 1) := by simp [lift, hik]
        rw [hl]
        exact Typing.var hb
  | app _ _ iha ihb =>
      intro k Δ hk
      exact Typing.app (iha k Δ hk) (ihb k Δ hk)
  | @lam Γ t A B _ ih =>
      intro k Δ hk
      refine Typing.lam ?_
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
          · rw [ite_eq_left hjk] at hb
            rw [ite_eq_left (by omega : j + 1 < k + 1)]
            simpa using hb
          · rw [ite_eq_right hjk] at hb
            rw [ite_eq_right (by omega : ¬ (j + 1 < k + 1))]
            simpa using hb
  | @tlam Γ t A _ ih =>
      intro k Δ hk
      refine Typing.tlam ?_
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
      exact Typing.tapp B (ih k Δ hk)
  | cast _ hγ ih =>
      intro k Δ hk
      exact Typing.cast (ih k Δ hk) hγ

/-- Weakening by one variable in front of the context. -/
theorem Typing.lift_one {Δ : List FTy} {u : Tm} {A : FTy} (h : Typing Ax Δ u A) (B : FTy) :
    Typing Ax (B :: Δ) (lift 1 0 u) A := by
  refine h.lift_gen 0 (B :: Δ) ?_
  intro i A' hi
  simpa using hi

/-- **A derivation may be substituted in its type variables**, for closed axioms. -/
theorem Typing.substTy (hAx : AxClosed Ax) {Γ : List FTy} {t : Tm} {A : FTy}
    (h : Typing Ax Γ t A) :
    ∀ s : ℕ → FTy, Typing Ax (Γ.map (tySubst s)) (substTyTm s t) (tySubst s A) := by
  induction h with
  | @var Γ i A hi =>
      intro s
      refine Typing.var ?_
      rw [List.getElem?_map, hi]
      rfl
  | app _ _ iha ihb => intro s; exact Typing.app (iha s) (ihb s)
  | lam _ ih => intro s; exact Typing.lam (ih s)
  | @tlam Γ t A _ ih =>
      intro s
      refine Typing.tlam ?_
      have hmap : (Γ.map tyShift).map (tySubst (ups s))
          = (Γ.map (tySubst s)).map tyShift := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun X _ => tySubst_tyShift s X
      have := ih (ups s)
      rwa [hmap] at this
  | @tapp Γ t A B _ ih =>
      intro s
      rw [tySubst_tyInst]
      exact Typing.tapp _ (ih s)
  | cast _ hγ ih => intro s; exact Typing.cast (ih s) (hγ.substTy hAx s)

/-- Weakening a derivation by a fresh type variable. -/
theorem Typing.shiftTy (hAx : AxClosed Ax) {Γ : List FTy} {t : Tm} {A : FTy}
    (h : Typing Ax Γ t A) : Typing Ax (Γ.map tyShift) (shiftTyTm t) (tyShift A) := by
  have hsub := h.substTy hAx (fun i => FTy.var (i + 1))
  have hA : tySubst (fun i => FTy.var (i + 1)) A = tyShift A := (tyShift_eq_tySubst A).symm
  have hΓ : Γ.map (tySubst (fun i => FTy.var (i + 1))) = Γ.map tyShift :=
    List.map_congr_left fun X _ => (tyShift_eq_tySubst X).symm
  rw [hA, hΓ] at hsub
  exact hsub

/-- **Substituting a term variable**, in the general form needed to go under an abstraction. -/
theorem Typing.subst_gen (hAx : AxClosed Ax) {Γ : List FTy} {t : Tm} {B : FTy}
    (h : Typing Ax Γ t B) :
    ∀ (k : ℕ) (Δ : List FTy) (u : Tm) (A : FTy),
      Γ[k]? = some A → Typing Ax Δ u A →
      (∀ i A', i < k → Γ[i]? = some A' → Δ[i]? = some A') →
      (∀ i A', k ≤ i → Γ[i + 1]? = some A' → Δ[i]? = some A') →
      Typing Ax Δ (subst u k t) B := by
  induction h with
  | @var Γ i B hi =>
      intro k Δ u A hk hu hlt hge
      by_cases hik : i = k
      · subst hik
        have hAB : A = B := by rw [hk] at hi; simpa using hi
        subst hAB
        have hl : subst u i (Tm.var i) = u := by simp [subst]
        rw [hl]
        exact hu
      · by_cases hgt : i > k
        · have hl : subst u k (Tm.var i) = Tm.var (i - 1) := by
            simp [subst, hik, hgt]
          rw [hl]
          refine Typing.var (hge (i - 1) B (by omega) ?_)
          have : i - 1 + 1 = i := by omega
          rw [this]
          exact hi
        · have hl : subst u k (Tm.var i) = Tm.var i := by
            simp [subst, hik, hgt]
          rw [hl]
          exact Typing.var (hlt i B (by omega) hi)
  | app _ _ iha ihb =>
      intro k Δ u A hk hu hlt hge
      exact Typing.app (iha k Δ u A hk hu hlt hge) (ihb k Δ u A hk hu hlt hge)
  | @lam Γ t A₀ B₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      refine Typing.lam ?_
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
      refine Typing.tlam ?_
      refine ih k (Δ.map tyShift) (shiftTyTm u) (tyShift A) ?_ (hu.shiftTy hAx) ?_ ?_
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
      exact Typing.tapp B₀ (ih k Δ u A hk hu hlt hge)
  | cast _ hγ ih =>
      intro k Δ u A hk hu hlt hge
      exact Typing.cast (ih k Δ u A hk hu hlt hge) hγ

/-- Substituting the variable `0`, the form used by the β-rule. -/
theorem Typing.subst_zero (hAx : AxClosed Ax) {Γ : List FTy} {t u : Tm} {A B : FTy}
    (ht : Typing Ax (A :: Γ) t B) (hu : Typing Ax Γ u A) : Typing Ax Γ (subst u 0 t) B := by
  refine ht.subst_gen hAx 0 Γ u A (by simp) hu ?_ ?_
  · intro i A' hi _
    omega
  · intro i A' _ hget
    simpa using hget

/-! ### Preservation -/

/-- **Subject reduction for System F with coercions**: for an axiom set of closed types, every
reduction step preserves the type. -/
theorem Typing.preservation (hAx : AxClosed Ax) {Γ : List FTy} {t : Tm} {A : FTy}
    (h : Typing Ax Γ t A) : ∀ t' : Tm, Step t t' → Typing Ax Γ t' A := by
  induction h with
  | var _ => intro t' hs; cases hs
  | @app Γ a b A₀ B ha hb iha ihb =>
      intro t' hs
      cases hs with
      | beta A₁ s u =>
          cases ha with
          | lam hbody => exact hbody.subst_zero hAx hb
      | pushApp A₁ s γ u =>
          cases ha with
          | cast hlam hγ =>
              cases hlam with
              | lam hbody =>
                  exact Typing.cast (Typing.app (Typing.lam hbody)
                    (Typing.cast hb (CoTyping.sym (CoTyping.left hγ)))) (CoTyping.right hγ)
      | appL _ hstep => exact Typing.app (iha _ hstep) hb
      | appR _ hstep => exact Typing.app ha (ihb _ hstep)
  | @lam Γ t A₀ B _ ih =>
      intro t' hs
      cases hs with
      | lam _ hstep => exact Typing.lam (ih _ hstep)
  | @tlam Γ t A₀ _ ih =>
      intro t' hs
      cases hs with
      | tlam hstep => exact Typing.tlam (ih _ hstep)
  | @tapp Γ t A₀ B hall ih =>
      intro t' hs
      cases hs with
      | tbeta s _ =>
          cases hall with
          | tlam hbody =>
              have hsub := hbody.substTy hAx (tyScons B)
              have hmap : (Γ.map tyShift).map (tySubst (tyScons B)) = Γ := by
                simp only [List.map_map, Function.comp_def]
                refine (List.map_congr_left fun X _ => ?_).trans (List.map_id Γ)
                exact tyInst_tyShift B X
              rw [hmap] at hsub
              exact hsub
      | pushTApp s γ _ =>
          cases hall with
          | cast htl hγ =>
              cases htl with
              | tlam hbody =>
                  exact Typing.cast (Typing.tapp B (Typing.tlam hbody)) (CoTyping.inst B hγ)
      | tapp _ hstep => exact Typing.tapp B (ih _ hstep)
  | @cast Γ t γ A₀ B ht hγ ih =>
      intro t' hs
      cases hs with
      | castTrans s γ₁ _ =>
          cases ht with
          | cast hs' hγ₁ => exact Typing.cast hs' (CoTyping.trans hγ₁ hγ)
      | cast _ hstep => exact Typing.cast (ih _ hstep) hγ

/-- Subject reduction along many steps. -/
theorem Typing.preservation_star (hAx : AxClosed Ax) {Γ : List FTy} {t t' : Tm} {A : FTy}
    (h : Typing Ax Γ t A) (hs : Relation.ReflTransGen Step t t') : Typing Ax Γ t' A := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.preservation hAx _ hstep

/-! ### Progress -/

/-- **Consistency of the axiom set** (for the type constructors `→` and `∀`): no coercion relates
an arrow type and a `∀`-type. -/
def Consistent (Ax : List (FTy × FTy)) : Prop :=
  ∀ (γ : Co) (A₁ B₁ C : FTy),
    ¬ CoTyping Ax γ (.arrow A₁ B₁) (.all C) ∧ ¬ CoTyping Ax γ (.all C) (.arrow A₁ B₁)

/-- Plain values: abstractions and type abstractions. -/
inductive PlainValue : Tm → Prop
  /-- An abstraction. -/
  | lam (A : FTy) (t : Tm) : PlainValue (.lam A t)
  /-- A type abstraction. -/
  | tlam (t : Tm) : PlainValue (.tlam t)

/-- Values: plain values, possibly under one cast. -/
inductive Value : Tm → Prop
  /-- A plain value. -/
  | plain {v : Tm} : PlainValue v → Value v
  /-- A plain value under one cast. -/
  | cast {v : Tm} (γ : Co) : PlainValue v → Value (.cast v γ)

/-- **Progress for System F with coercions**: under the hypothesis that the axiom set is
consistent, a closed well-typed term is a value or takes a step. -/
theorem Typing.progress (hcon : Consistent Ax) {t : Tm} {A : FTy} (h : Typing Ax [] t A) :
    Value t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : List FTy) = Γ at h
  induction h with
  | var hi => subst hΓ; simp at hi
  | @app Γ a b A₀ B ha hb iha _ =>
      right
      rcases iha hΓ with hv | ⟨a', ha'⟩
      · cases hv with
        | plain hp =>
            cases hp with
            | lam A₁ s => exact ⟨_, Step.beta A₁ s b⟩
            | tlam s => cases ha
        | cast γ hp =>
            cases hp with
            | lam A₁ s => exact ⟨_, Step.pushApp A₁ s γ b⟩
            | tlam s =>
                cases ha with
                | cast htl hγ =>
                    cases htl with
                    | tlam _ => exact absurd hγ (hcon γ _ _ _).2
      · exact ⟨_, Step.appL b ha'⟩
  | lam _ _ => left; exact Value.plain (PlainValue.lam _ _)
  | tlam _ _ => left; exact Value.plain (PlainValue.tlam _)
  | @tapp Γ t A₀ B ht iht =>
      right
      rcases iht hΓ with hv | ⟨t', ht'⟩
      · cases hv with
        | plain hp =>
            cases hp with
            | lam A₁ s => cases ht
            | tlam s => exact ⟨_, Step.tbeta s B⟩
        | cast γ hp =>
            cases hp with
            | lam A₁ s =>
                cases ht with
                | cast hl hγ =>
                    cases hl with
                    | lam _ => exact absurd hγ (hcon γ _ _ _).1
            | tlam s => exact ⟨_, Step.pushTApp s γ B⟩
      · exact ⟨_, Step.tapp B ht'⟩
  | @cast Γ t γ A₀ B _ _ iht =>
      rcases iht hΓ with hv | ⟨t', ht'⟩
      · cases hv with
        | plain hp => left; exact Value.cast γ hp
        | @cast v γ' hp => right; exact ⟨_, Step.castTrans v γ' γ⟩
      · right; exact ⟨_, Step.cast γ ht'⟩

/-- **Type safety**: under consistency and closed axioms, a closed well-typed term never reaches
a stuck term: every reduct is a value or takes a further step, at the same type. -/
theorem Typing.safety (hAx : AxClosed Ax) (hcon : Consistent Ax) {t t' : Tm} {A : FTy}
    (h : Typing Ax [] t A) (hs : Relation.ReflTransGen Step t t') :
    Typing Ax [] t' A ∧ (Value t' ∨ ∃ t'', Step t' t'') :=
  ⟨h.preservation_star hAx hs, (h.preservation_star hAx hs).progress hcon⟩

end FCoerce
