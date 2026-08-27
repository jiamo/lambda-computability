/-
**The substitution calculus of Church-style System F.**

`Start/SystemFC.lean` defines the annotated terms with two substitutions: `SystemFC.subst`,
substituting a term for a term variable (which shifts the *type* variables of the substituted term
when it enters a `Λ`), and `SystemFC.substTyTm`, substituting types for the type variables of the
annotations.  This file proves how the two commute with each other and with lifting.  These are the
equations the confluence proof of `Start/SystemFCConfluence.lean` needs, and they are the annotated
counterparts of the laws of `Start/Syntax.lean` for the untyped calculus and of
`Start/SystemFSubst.lean` for the types.

* `SystemFC.substTyTm_substTyTm`, `SystemFC.substTyTm_var_id`, `SystemFC.substTyTm_shiftTyTm`,
  `SystemFC.instTyTm_shiftTyTm` — the composition and cancellation laws of type substitution on
  terms;
* `SystemFC.substTyTm_lift`, `SystemFC.substTyTm_subst` — type substitution commutes with the term
  substitution and with lifting;
* `SystemFC.lift_lift`, `SystemFC.lift_subst`, `SystemFC.lift_subst_lo`,
  `SystemFC.lift_subst_zero`, `SystemFC.subst_lift`, `SystemFC.subst_subst`,
  `SystemFC.subst_subst_zero` — the term-variable calculus;
* `SystemFC.instTyTm_subst`, `SystemFC.subst_instTyTm`, `SystemFC.substTyTm_instTyTm` — the three
  equations that make the type-β rule commute with the other reductions.
-/

import Start.SystemFC

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemFC

open SystemF

/-! ### Type substitution on terms -/

/-- Composition of two liftings of a type substitution under a binder. -/
theorem ups_comp (s r : ℕ → FTy) :
    (fun i => tySubst (ups s) (ups r i)) = ups (fun i => tySubst s (r i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact tySubst_tyShift s (r i)

/-- Type substitutions on terms compose. -/
theorem substTyTm_substTyTm (s r : ℕ → FTy) (t : FTm) :
    substTyTm s (substTyTm r t) = substTyTm (fun i => tySubst s (r i)) t := by
  induction t generalizing s r with
  | var i => rfl
  | app a b iha ihb => simp only [substTyTm, iha, ihb]
  | lam A t ih => simp only [substTyTm, ih, tySubst_tySubst]
  | tlam t ih => simp only [substTyTm, ih, ups_comp]
  | tapp t B ih => simp only [substTyTm, ih, tySubst_tySubst]

/-- The identity type substitution acts as the identity on terms. -/
theorem substTyTm_var_id (t : FTm) : substTyTm FTy.var t = t := by
  have hups : ups FTy.var = FTy.var := by
    funext i; cases i <;> rfl
  induction t with
  | var i => rfl
  | app a b iha ihb => simp only [substTyTm, iha, ihb]
  | lam A t ih => simp only [substTyTm, ih, tySubst_var_id]
  | tlam t ih => rw [substTyTm, hups, ih]
  | tapp t B ih => simp only [substTyTm, ih, tySubst_var_id]

/-- Type substitution commutes with the weakening of the type variables. -/
theorem substTyTm_shiftTyTm (s : ℕ → FTy) (t : FTm) :
    substTyTm (ups s) (shiftTyTm t) = shiftTyTm (substTyTm s t) := by
  rw [shiftTyTm, shiftTyTm, substTyTm_substTyTm, substTyTm_substTyTm]
  congr 1
  funext i
  simp only [tySubst]
  exact tyShift_eq_tySubst (s i)

/-- Instantiating a type variable that was just introduced by weakening does nothing. -/
theorem instTyTm_shiftTyTm (B : FTy) (t : FTm) : instTyTm B (shiftTyTm t) = t := by
  rw [instTyTm, shiftTyTm, substTyTm_substTyTm]
  have h : (fun i => tySubst (tyScons B) (FTy.var (i + 1))) = FTy.var := by
    funext i; rfl
  rw [h, substTyTm_var_id]

/-- Type substitution commutes with lifting of the term variables. -/
theorem substTyTm_lift (s : ℕ → FTy) (n k : ℕ) (t : FTm) :
    substTyTm s (lift n k t) = lift n k (substTyTm s t) := by
  induction t generalizing s k with
  | var i => by_cases h : i < k <;> simp [lift, substTyTm, h]
  | app a b iha ihb => simp only [lift, substTyTm, iha, ihb]
  | lam A t ih => simp only [lift, substTyTm, ih]
  | tlam t ih => simp only [lift, substTyTm, ih]
  | tapp t B ih => simp only [lift, substTyTm, ih]

/-- Lifting the term variables commutes with weakening the type variables. -/
theorem lift_shiftTyTm (n k : ℕ) (t : FTm) :
    lift n k (shiftTyTm t) = shiftTyTm (lift n k t) := (substTyTm_lift _ n k t).symm

/-- Type substitution commutes with substitution of a term variable. -/
theorem substTyTm_subst (s : ℕ → FTy) (u : FTm) (x : ℕ) (t : FTm) :
    substTyTm s (subst u x t) = subst (substTyTm s u) x (substTyTm s t) := by
  induction t generalizing s u x with
  | var i =>
      by_cases h1 : i = x
      · simp [subst, substTyTm, h1]
      · by_cases h2 : i > x <;> simp [subst, substTyTm, h1, h2]
  | app a b iha ihb => simp only [subst, substTyTm, iha, ihb]
  | lam A t ih => simp only [subst, substTyTm, ih, substTyTm_lift]
  | tlam t ih => simp only [subst, substTyTm, ih, substTyTm_shiftTyTm]
  | tapp t B ih => simp only [subst, substTyTm, ih]

/-! ### The term-variable calculus -/

/-- Two liftings commute. -/
theorem lift_lift (t : FTm) (m n k j : ℕ) (h : j ≤ k) :
    lift m j (lift n k t) = lift n (k + m) (lift m j t) := by
  induction t generalizing j k with
  | var i =>
      by_cases h2 : i < j
      · have h1 : i < k := lt_of_lt_of_le h2 h
        simp [lift, h1, h2, show i < k + m by omega]
      · by_cases h1 : i < k
        · simp [lift, h1, h2, show i + m < k + m by omega]
        · simp [lift, h1, h2, show ¬ (i + m < k + m) by omega,
            show ¬ (i + n < j) by omega]
          omega
  | app a b iha ihb => simp only [lift, iha _ _ h, ihb _ _ h]
  | lam A t ih =>
      simp only [lift]
      rw [ih (k + 1) (j + 1) (by omega)]
      congr 2
      omega
  | tlam t ih => simp only [lift, ih _ _ h]
  | tapp t B ih => simp only [lift, ih _ _ h]

/-- Substitution and lifting commute, the lifting being below the substituted variable. -/
theorem lift_subst (t u : FTm) (n k x : ℕ) (h : k ≤ x) :
    lift n k (subst u x t) = subst (lift n k u) (x + n) (lift n k t) := by
  induction t generalizing u k x with
  | var i =>
      by_cases h1 : i = x
      · subst h1
        simp [lift, subst, show ¬ i < k from Nat.not_lt.mpr h]
      · by_cases h2 : i < k
        · have hix : i < x := lt_of_lt_of_le h2 h
          simp [lift, subst, h1, h2, show ¬ i > x by omega, show i ≠ x + n by omega,
            show ¬ i > x + n by omega]
        · have hcases : i > x ∨ i < x := by omega
          rcases hcases with h3 | h3
          · have hpos : 0 < i := by omega
            simp [lift, subst, h1, h2, h3, show i + n > x + n by omega,
              show ¬ (i - 1 < k) by omega]
            omega
          · simp [lift, subst, h1, h2, show ¬ i > x by omega,
              show ¬ (i + n > x + n) by omega]
  | app a b iha ihb => simp only [lift, subst, iha _ _ _ h, ihb _ _ _ h]
  | lam A t ih =>
      simp only [lift, subst]
      rw [ih (lift 1 0 u) (k + 1) (x + 1) (by omega)]
      have hl : lift n (k + 1) (lift 1 0 u) = lift 1 0 (lift n k u) := by
        simpa using (lift_lift u 1 n k 0 (Nat.zero_le k)).symm
      rw [hl]
      congr 2
      omega
  | tlam t ih =>
      simp only [lift, subst]
      rw [ih (shiftTyTm u) k x h, lift_shiftTyTm]
  | tapp t B ih => simp only [lift, subst, ih _ _ _ h]

/-- Substitution and lifting commute, the lifting being above the substituted variable. -/
theorem lift_subst_lo (t u : FTm) (n k x : ℕ) (h : x ≤ k) :
    lift n k (subst u x t) = subst (lift n k u) x (lift n (k + 1) t) := by
  induction t generalizing u k x with
  | var i =>
      by_cases h1 : i = x
      · subst h1
        simp [lift, subst, show i < k + 1 by omega]
      · by_cases h3 : i > x
        · by_cases h2 : i < k + 1
          · have hpos : 0 < i := by omega
            simp [lift, subst, h1, h2, h3, show i - 1 < k by omega]
          · have hpos : 0 < i := by omega
            simp [lift, subst, h1, h2, h3, show ¬ (i - 1 < k) by omega,
              show i + n > x by omega, show i + n ≠ x by omega]
            omega
        · have hlt : i < x := by omega
          simp [lift, subst, h1, h3, show i < k + 1 by omega, show i < k by omega]
  | app a b iha ihb => simp only [lift, subst, iha _ _ _ h, ihb _ _ _ h]
  | lam A t ih =>
      simp only [lift, subst]
      rw [ih (lift 1 0 u) (k + 1) (x + 1) (by omega)]
      have hl : lift n (k + 1) (lift 1 0 u) = lift 1 0 (lift n k u) := by
        simpa using (lift_lift u 1 n k 0 (Nat.zero_le k)).symm
      rw [hl]
  | tlam t ih =>
      simp only [lift, subst]
      rw [ih (shiftTyTm u) k x h, lift_shiftTyTm]
  | tapp t B ih => simp only [lift, subst, ih _ _ _ h]

/-- Lifting commutes with β-substitution. -/
theorem lift_subst_zero (t u : FTm) (n k : ℕ) :
    lift n k (subst u 0 t) = subst (lift n k u) 0 (lift n (k + 1) t) :=
  lift_subst_lo t u n k 0 (Nat.zero_le k)

/-- Substituting for a variable that was just introduced by lifting does nothing. -/
theorem subst_lift (t u : FTm) (x : ℕ) : subst u x (lift 1 x t) = t := by
  induction t generalizing u x with
  | var i =>
      by_cases h : i < x
      · simp [lift, subst, h, show i ≠ x by omega, show ¬ i > x by omega]
      · simp [lift, subst, h, show i + 1 ≠ x by omega, show i + 1 > x by omega]
  | app a b iha ihb => simp only [lift, subst, iha, ihb]
  | lam A t ih => simp only [lift, subst, ih]
  | tlam t ih => simp only [lift, subst, ih]
  | tapp t B ih => simp only [lift, subst, ih]

/-- The substitution lemma: two substitutions in succession. -/
theorem subst_subst (t u v : FTm) (x y : ℕ) (h : y ≤ x) :
    subst u x (subst v y t) = subst (subst u x v) y (subst (lift 1 y u) (x + 1) t) := by
  induction t generalizing u v x y with
  | var i =>
      by_cases h1 : i = y
      · subst h1
        simp [subst, show i ≠ x + 1 by omega, show ¬ i > x + 1 by omega]
      · by_cases h2 : i = x + 1
        · subst h2
          have hgt : x + 1 > y := by omega
          simp only [subst, if_neg h1, if_pos hgt]
          simpa using (subst_lift u (subst u x v) y).symm
        · by_cases h3 : i > x + 1
          · have hpos : 0 < i := by omega
            simp [subst, h1, h2, h3, show i > y by omega, show i - 1 > x by omega,
              show i - 1 ≠ x by omega, show i - 1 > y by omega, show i - 1 ≠ y by omega]
          · by_cases h4 : i > y
            · have hpos : 0 < i := by omega
              simp [subst, h1, h2, h3, h4, show i - 1 ≠ x by omega, show ¬ (i - 1 > x) by omega]
            · simp [subst, h1, h2, h3, h4, show i ≠ x by omega, show ¬ (i > x) by omega]
  | app a b iha ihb => simp only [subst, iha _ _ _ _ h, ihb _ _ _ _ h]
  | lam A t ih =>
      simp only [subst]
      rw [ih (lift 1 0 u) (lift 1 0 v) (x + 1) (y + 1) (by omega)]
      have h1 : subst (lift 1 0 u) (x + 1) (lift 1 0 v) = lift 1 0 (subst u x v) := by
        simpa using (lift_subst v u 1 0 x (Nat.zero_le x)).symm
      have h2 : lift 1 (y + 1) (lift 1 0 u) = lift 1 0 (lift 1 y u) := by
        simpa using (lift_lift u 1 1 y 0 (Nat.zero_le y)).symm
      rw [h1, h2]
  | tlam t ih =>
      simp only [subst]
      rw [ih (shiftTyTm u) (shiftTyTm v) x y h]
      have h1 : subst (shiftTyTm u) x (shiftTyTm v) = shiftTyTm (subst u x v) :=
        (substTyTm_subst _ u x v).symm
      have h2 : lift 1 y (shiftTyTm u) = shiftTyTm (lift 1 y u) := lift_shiftTyTm 1 y u
      rw [h1, h2]
  | tapp t B ih => simp only [subst, ih _ _ _ _ h]

/-- The substitution lemma in the form the β-rule needs. -/
theorem subst_subst_zero (t u v : FTm) (x : ℕ) :
    subst u x (subst v 0 t) = subst (subst u x v) 0 (subst (lift 1 0 u) (x + 1) t) :=
  subst_subst t u v x 0 (Nat.zero_le x)

/-! ### The type-β rule -/

/-- Instantiating a type commutes with β-substitution. -/
theorem instTyTm_subst (B : FTy) (u : FTm) (x : ℕ) (t : FTm) :
    instTyTm B (subst u x t) = subst (instTyTm B u) x (instTyTm B t) :=
  substTyTm_subst _ u x t

/-- Substituting a term into a type instantiation. -/
theorem subst_instTyTm (B : FTy) (u : FTm) (x : ℕ) (t : FTm) :
    subst u x (instTyTm B t) = instTyTm B (subst (shiftTyTm u) x t) := by
  rw [instTyTm_subst, instTyTm_shiftTyTm]

/-- Type substitution commutes with type instantiation. -/
theorem substTyTm_instTyTm (s : ℕ → FTy) (B : FTy) (t : FTm) :
    substTyTm s (instTyTm B t) = instTyTm (tySubst s B) (substTyTm (ups s) t) := by
  rw [instTyTm, instTyTm, substTyTm_substTyTm, substTyTm_substTyTm]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      change tySubst s (FTy.var i) = tySubst (tyScons (tySubst s B)) (tyShift (s i))
      rw [tyScons_eq, tySubst_tyCons_tyShift, tySubst_var_id]
      rfl

end SystemFC
