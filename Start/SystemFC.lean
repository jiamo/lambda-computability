/-
**Church-style System F**: terms carry type annotations, abstraction over a type variable and
instantiation are term formers, and reduction has both a β-rule and a type-β rule.  Its **strong
normalization** is derived here from the Curry-style theorem of `Start/SystemF.lean` by erasure.

Erasure forgets the annotations: `Λα. t` and `t [B]` both erase to the erasure of `t`.  A Church
β-step erases to a β-step of the untyped calculus, but a *type*-β step erases to nothing at all —
the two sides have the same erasure — so the erasure alone cannot prove termination.  What it does
prove, together with the observation that a type-β step destroys one `Λ` and that substituting a
type into a term does not create any, is termination for the lexicographic combination of the two:
this is `SystemFC.snc_of_sn_erase`.

* `SystemFC.FTm` — the annotated terms, with their term-variable substitution (mirroring
  `Lambda.lift` and `Lambda.subst`) and their type-variable substitution;
* `SystemFC.step` — β and type-β with all the congruences;
* `SystemFC.TypingC` — the typing rules of Church-style System F;
* `SystemFC.erase`, `SystemFC.typing_erase` — **erasure of a typable term is typable in the
  Curry-style system** with the same type;
* `SystemFC.step_erase` — the simulation: a step either erases to a step, or leaves the erasure
  alone and removes a `Λ`;
* `SystemFC.sn_of_typingC` — **strong normalization for Church-style System F**.
-/

import Start.SystemFChurch

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemFC

open Lambda SystemF

/-! ### Annotated terms -/

/-- Terms of Church-style System F. -/
inductive FTm where
  /-- A term variable. -/
  | var : ℕ → FTm
  /-- Application. -/
  | app : FTm → FTm → FTm
  /-- Abstraction, annotated with the type of the bound variable. -/
  | lam : FTy → FTm → FTm
  /-- Abstraction over a type variable. -/
  | tlam : FTm → FTm
  /-- Instantiation of a quantified type. -/
  | tapp : FTm → FTy → FTm

/-- Substituting the type variables of the annotations of a term. -/
def substTyTm (s : ℕ → FTy) : FTm → FTm
  | FTm.var i => FTm.var i
  | FTm.app a b => FTm.app (substTyTm s a) (substTyTm s b)
  | FTm.lam A t => FTm.lam (tySubst s A) (substTyTm s t)
  | FTm.tlam t => FTm.tlam (substTyTm (ups s) t)
  | FTm.tapp t B => FTm.tapp (substTyTm s t) (tySubst s B)

/-- Weakening the type variables of the annotations of a term. -/
def shiftTyTm (t : FTm) : FTm := substTyTm (fun i => FTy.var (i + 1)) t

/-- Instantiating the outermost type variable of the annotations of a term. -/
def instTyTm (B : FTy) (t : FTm) : FTm := substTyTm (tyScons B) t

/-- Lifting the term variables, exactly as `Lambda.lift`. -/
def lift (n k : ℕ) : FTm → FTm
  | FTm.var y => if y < k then FTm.var y else FTm.var (y + n)
  | FTm.app a b => FTm.app (lift n k a) (lift n k b)
  | FTm.lam A t => FTm.lam A (lift n (k + 1) t)
  | FTm.tlam t => FTm.tlam (lift n k t)
  | FTm.tapp t B => FTm.tapp (lift n k t) B

/-- Substituting a term variable, exactly as `Lambda.subst`; entering a type abstraction shifts
the type variables of the substituted term. -/
def subst (s : FTm) (x : ℕ) : FTm → FTm
  | FTm.var y => if y = x then s else if y > x then FTm.var (y - 1) else FTm.var y
  | FTm.app a b => FTm.app (subst s x a) (subst s x b)
  | FTm.lam A t => FTm.lam A (subst (lift 1 0 s) (x + 1) t)
  | FTm.tlam t => FTm.tlam (subst (shiftTyTm s) x t)
  | FTm.tapp t B => FTm.tapp (subst s x t) B

/-! ### Reduction -/

/-- One step of reduction: β, type-β, and the congruences. -/
inductive step : FTm → FTm → Prop
  /-- β. -/
  | beta (A : FTy) (t u : FTm) : step (FTm.app (FTm.lam A t) u) (subst u 0 t)
  /-- Type-β. -/
  | tbeta (t : FTm) (B : FTy) : step (FTm.tapp (FTm.tlam t) B) (instTyTm B t)
  /-- Congruence, left of an application. -/
  | appL {a a' : FTm} (b : FTm) : step a a' → step (FTm.app a b) (FTm.app a' b)
  /-- Congruence, right of an application. -/
  | appR (a : FTm) {b b' : FTm} : step b b' → step (FTm.app a b) (FTm.app a b')
  /-- Congruence, under an abstraction. -/
  | lam (A : FTy) {t t' : FTm} : step t t' → step (FTm.lam A t) (FTm.lam A t')
  /-- Congruence, under a type abstraction. -/
  | tlam {t t' : FTm} : step t t' → step (FTm.tlam t) (FTm.tlam t')
  /-- Congruence, in an instantiation. -/
  | tapp {t t' : FTm} (B : FTy) : step t t' → step (FTm.tapp t B) (FTm.tapp t' B)

/-- Strong normalization for the annotated calculus. -/
def SNC (t : FTm) : Prop := Acc (fun a b => step b a) t

/-! ### Typing -/

/-- Typing for Church-style System F. -/
inductive TypingC : List FTy → FTm → FTy → Prop
  /-- A variable has the type recorded in the context. -/
  | var {Γ : List FTy} {i : ℕ} {A : FTy} : Γ[i]? = some A → TypingC Γ (FTm.var i) A
  /-- Application. -/
  | app {Γ : List FTy} {a b : FTm} {A B : FTy} :
      TypingC Γ a (FTy.arrow A B) → TypingC Γ b A → TypingC Γ (FTm.app a b) B
  /-- Abstraction. -/
  | lam {Γ : List FTy} {t : FTm} {A B : FTy} :
      TypingC (A :: Γ) t B → TypingC Γ (FTm.lam A t) (FTy.arrow A B)
  /-- Abstraction over a type variable. -/
  | tlam {Γ : List FTy} {t : FTm} {A : FTy} :
      TypingC (Γ.map tyShift) t A → TypingC Γ (FTm.tlam t) (FTy.all A)
  /-- Instantiation. -/
  | tapp {Γ : List FTy} {t : FTm} {A : FTy} (B : FTy) :
      TypingC Γ t (FTy.all A) → TypingC Γ (FTm.tapp t B) (tyInst B A)

/-! ### Erasure -/

/-- Erasing the type annotations of a term. -/
def erase : FTm → Lambda
  | FTm.var i => Lambda.var i
  | FTm.app a b => Lambda.app (erase a) (erase b)
  | FTm.lam _ t => Lambda.lam (erase t)
  | FTm.tlam t => erase t
  | FTm.tapp t _ => erase t

@[simp] theorem erase_substTyTm (s : ℕ → FTy) (t : FTm) : erase (substTyTm s t) = erase t := by
  induction t generalizing s with
  | var i => rfl
  | app a b iha ihb => simp only [substTyTm, erase, iha, ihb]
  | lam A t ih => simp only [substTyTm, erase, ih]
  | tlam t ih => simp only [substTyTm, erase, ih]
  | tapp t B ih => simp only [substTyTm, erase, ih]

@[simp] theorem erase_shiftTyTm (t : FTm) : erase (shiftTyTm t) = erase t :=
  erase_substTyTm _ t

@[simp] theorem erase_instTyTm (B : FTy) (t : FTm) : erase (instTyTm B t) = erase t :=
  erase_substTyTm _ t

@[simp] theorem erase_lift (n k : ℕ) (t : FTm) :
    erase (lift n k t) = Lambda.lift n k (erase t) := by
  induction t generalizing k with
  | var i =>
      by_cases h : i < k
      · simp [lift, erase, Lambda.lift, h]
      · simp [lift, erase, Lambda.lift, h]
  | app a b iha ihb => simp only [lift, erase, Lambda.lift, iha, ihb]
  | lam A t ih => simp only [lift, erase, Lambda.lift, ih]
  | tlam t ih => simp only [lift, erase, ih]
  | tapp t B ih => simp only [lift, erase, ih]

@[simp] theorem erase_subst (s : FTm) (x : ℕ) (t : FTm) :
    erase (subst s x t) = Lambda.subst (erase s) x (erase t) := by
  induction t generalizing s x with
  | var i =>
      by_cases h : i = x
      · simp [subst, erase, Lambda.subst, h]
      · by_cases h' : i > x
        · simp [subst, erase, Lambda.subst, h, h']
        · simp [subst, erase, Lambda.subst, h, h']
  | app a b iha ihb => simp only [subst, erase, Lambda.subst, iha, ihb]
  | lam A t ih => simp only [subst, erase, Lambda.subst, ih, erase_lift]
  | tlam t ih => simp only [subst, erase, ih, erase_shiftTyTm]
  | tapp t B ih => simp only [subst, erase, ih]

/-- **The erasure of a typable term is typable in the Curry-style system**, at the same type. -/
theorem typing_erase {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    Typing Γ (erase t) A := by
  induction h with
  | var hi => exact Typing.var hi
  | app _ _ iha ihb => exact Typing.app iha ihb
  | lam _ ih => exact Typing.lam ih
  | tlam _ ih => exact Typing.tlam ih
  | tapp B _ ih => exact Typing.tapp B ih

/-! ### The simulation -/

/-- The number of type abstractions in a term. -/
def tlamCount : FTm → ℕ
  | FTm.var _ => 0
  | FTm.app a b => tlamCount a + tlamCount b
  | FTm.lam _ t => tlamCount t
  | FTm.tlam t => tlamCount t + 1
  | FTm.tapp t _ => tlamCount t

@[simp] theorem tlamCount_substTyTm (s : ℕ → FTy) (t : FTm) :
    tlamCount (substTyTm s t) = tlamCount t := by
  induction t generalizing s with
  | var i => rfl
  | app a b iha ihb => simp only [substTyTm, tlamCount, iha, ihb]
  | lam A t ih => simp only [substTyTm, tlamCount, ih]
  | tlam t ih => simp only [substTyTm, tlamCount, ih]
  | tapp t B ih => simp only [substTyTm, tlamCount, ih]

/-- **The simulation lemma**: a step of the annotated calculus either erases to a step of the
untyped calculus, or leaves the erasure unchanged and destroys a type abstraction. -/
theorem step_erase {t t' : FTm} (h : step t t') :
    (erase t = erase t' ∧ tlamCount t' < tlamCount t) ∨ Lambda.step (erase t) (erase t') := by
  induction h with
  | beta A t u =>
      refine Or.inr ?_
      simpa [erase] using Lambda.step.beta (erase t) (erase u)
  | tbeta t B =>
      refine Or.inl ⟨by simp [erase], ?_⟩
      simp [tlamCount, instTyTm]
  | @appL a a' b _ ih =>
      rcases ih with ⟨heq, hlt⟩ | hstep
      · exact Or.inl ⟨by simp only [erase, heq], by simp only [tlamCount]; omega⟩
      · exact Or.inr (Lambda.step.app_left _ _ _ hstep)
  | @appR a b b' _ ih =>
      rcases ih with ⟨heq, hlt⟩ | hstep
      · exact Or.inl ⟨by simp only [erase, heq], by simp only [tlamCount]; omega⟩
      · exact Or.inr (Lambda.step.app_right _ _ _ hstep)
  | @lam A t t' _ ih =>
      rcases ih with ⟨heq, hlt⟩ | hstep
      · exact Or.inl ⟨by simp only [erase, heq], by simpa only [tlamCount] using hlt⟩
      · exact Or.inr (Lambda.step.lam _ _ hstep)
  | @tlam t t' _ ih =>
      rcases ih with ⟨heq, hlt⟩ | hstep
      · exact Or.inl ⟨by simp only [erase, heq], by simp only [tlamCount]; omega⟩
      · exact Or.inr (by simpa only [erase] using hstep)
  | @tapp t t' B _ ih =>
      rcases ih with ⟨heq, hlt⟩ | hstep
      · exact Or.inl ⟨by simp only [erase, heq], by simpa only [tlamCount] using hlt⟩
      · exact Or.inr (by simpa only [erase] using hstep)

/-- A term whose erasure is strongly normalizing is strongly normalizing: the induction is
lexicographic, on the erasure first and on the number of type abstractions second. -/
theorem snc_aux : ∀ s : Lambda, SN s → ∀ (n : ℕ) (t : FTm),
    erase t = s → tlamCount t < n → SNC t := by
  intro s hs
  induction hs with
  | intro s _ ih =>
      intro n
      induction n with
      | zero => intro t _ hlt; exact absurd hlt (Nat.not_lt_zero _)
      | succ n ihn =>
          intro t het hlt
          refine Acc.intro t fun t' hstep => ?_
          rcases step_erase hstep with ⟨heq, hcount⟩ | hstep'
          · exact ihn t' (by rw [← heq]; exact het) (by omega)
          · refine ih (erase t') ?_ (tlamCount t' + 1) t' rfl (Nat.lt_succ_self _)
            rw [← het]
            exact hstep'

theorem snc_of_sn_erase {t : FTm} (h : SN (erase t)) : SNC t :=
  snc_aux (erase t) h (tlamCount t + 1) t rfl (Nat.lt_succ_self _)

/-- **Strong normalization for Church-style System F.** -/
theorem sn_of_typingC {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) : SNC t :=
  snc_of_sn_erase (sn_of_typing (typing_erase h))

/-- Non-vacuity: the polymorphic identity, with its annotations. -/
theorem typingC_id : TypingC [] (FTm.tlam (FTm.lam (FTy.var 0) (FTm.var 0))) idTy :=
  TypingC.tlam (TypingC.lam (TypingC.var (by simp)))

end SystemFC
