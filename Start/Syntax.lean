/-
Lambda calculus syntax: Term type, lifting, substitution, and core lemmas.
Extracted from Start/Basic.lean following LACI-style modularization.
-/

import Start.Tactics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
Definition of the untyped lambda calculus syntax using De Bruijn indices.
-/
inductive Lambda
  | var : ℕ → Lambda
  | app : Lambda → Lambda → Lambda
  | lam : Lambda → Lambda

/-
Definition of substitution and lifting for Lambda calculus.
-/
/-- Lifting: `lift n k t` increments all free variables in `t` that are >= `k` by `n`. -/
def Lambda.lift (n : ℕ) (k : ℕ) : Lambda → Lambda
  | Lambda.var y => if y < k then Lambda.var y else Lambda.var (y + n)
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.lift n k t₁) (Lambda.lift n k t₂)
  | Lambda.lam t => Lambda.lam (Lambda.lift n (k + 1) t)

/-- Proper substitution: `subst s x t` replaces variable `x` in `t` with `s`.
    When entering a lambda, the indices in `s` must be lifted. -/
def Lambda.subst (s : Lambda) (x : ℕ) : Lambda → Lambda
  | Lambda.var y =>
    if y = x then s
    else if y > x then Lambda.var (y - 1)
    else Lambda.var y
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.subst s x t₁) (Lambda.subst s x t₂)
  | Lambda.lam t => Lambda.lam (Lambda.subst (Lambda.lift 1 0 s) (x + 1) t)

------------------------------------------------------------------------
-- Lift lemmas
------------------------------------------------------------------------

/-- lift 0 is the identity. -/
theorem Lambda.lift_zero (k : ℕ) (t : Lambda) : Lambda.lift 0 k t = t := by
  induction t generalizing k with
  | var y => simp [Lambda.lift]
  | app t1 t2 ih1 ih2 => simp [Lambda.lift, ih1, ih2]
  | lam t ih => simp [Lambda.lift, ih]

/-- Multiple lifts can be combined. -/
theorem Lambda.lift_add (n m : ℕ) (k : ℕ) (t : Lambda) :
    Lambda.lift (n + m) k t = Lambda.lift n k (Lambda.lift m k t) := by
  induction t generalizing k with
  | var y =>
      by_cases hy : y < k
      · simp [Lambda.lift, hy]
      · have hym : ¬ y + m < k := by
          exact Nat.not_lt.mpr (le_trans (Nat.le_of_not_lt hy) (Nat.le_add_right y m))
        simp [Lambda.lift, hy, hym]
        simp [Nat.add_left_comm, Nat.add_comm]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.lift, ih1, ih2]
  | lam t ih =>
      simp [Lambda.lift, ih]

/-- Commutativity of lifting. -/
theorem Lambda.lift_lift (t : Lambda) (n m k j : ℕ) (h : k ≤ j) :
    Lambda.lift n k (Lambda.lift m j t) = Lambda.lift m (j + n) (Lambda.lift n k t) := by
  induction t generalizing k j with
  | var y =>
      by_cases hyk : y < k
      · have hyj : y < j := lt_of_lt_of_le hyk h
        have hyjn : y < j + n := lt_of_lt_of_le hyj (Nat.le_add_right j n)
        simp [Lambda.lift, hyk, hyj, hyjn]
      · by_cases hyj : y < j
        · have hyjn : y + n < j + n := Nat.add_lt_add_right hyj n
          simp [Lambda.lift, hyk, hyj, hyjn]
        · have hymk : ¬ y + m < k := by
            exact Nat.not_lt.mpr (le_trans (Nat.le_of_not_lt hyk) (Nat.le_add_right y m))
          have hynj : ¬ y + n < j + n := by
            exact Nat.not_lt.mpr (Nat.add_le_add_right (Nat.le_of_not_lt hyj) n)
          simp [Lambda.lift, hyk, hyj, hymk, hynj]
          simp [Nat.add_left_comm, Nat.add_comm]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.lift, ih1 _ _ h, ih2 _ _ h]
  | lam t ih =>
      simpa [Lambda.lift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg Lambda.lam (ih (k := k + 1) (j := j + 1) (Nat.succ_le_succ h))

------------------------------------------------------------------------
-- Lift-substitution interaction lemmas
------------------------------------------------------------------------

/-- Substitution and lifting commute (case 1). -/
theorem Lambda.lift_subst (t : Lambda) (s : Lambda) (n k x : ℕ) (h : k ≤ x) :
    Lambda.lift n k (Lambda.subst s x t) = Lambda.subst (Lambda.lift n k s) (x + n)
        (Lambda.lift n k t) := by
  induction t generalizing s k x with
  | var y =>
      by_cases hxy : x = y
      · subst hxy
        have hxk : ¬ x < k := Nat.not_lt.mpr h
        simp [Lambda.lift, Lambda.subst, hxk]
      · by_cases hyk : y < k
        · have hyxneq : y ≠ x := by
            intro hy_eq
            exact hxy hy_eq.symm
          have hyltx : y < x := lt_of_lt_of_le hyk h
          have hygt : ¬ y > x := Nat.not_lt.mpr (Nat.le_of_lt hyltx)
          have hyneq : y ≠ x + n := by
            exact ne_of_lt (lt_of_lt_of_le hyltx (Nat.le_add_right x n))
          have hyngt : ¬ y > x + n := by
            exact Nat.not_lt.mpr (Nat.le_of_lt (lt_of_lt_of_le hyltx (Nat.le_add_right x n)))
          simp [Lambda.lift, Lambda.subst, hyxneq, hyk, hygt, hyneq, hyngt]
        · by_cases hyx : y > x
          · have hyxneq : y ≠ x := by
              intro hy_eq
              exact hxy hy_eq.symm
            have hy1k : ¬ y - 1 < k := by
              exact Nat.not_lt.mpr (le_trans h (Nat.le_sub_one_of_lt hyx))
            have hyneq : y + n ≠ x + n := by
              intro h'
              exact hxy ((Nat.add_right_cancel h').symm)
            have hygt' : y + n > x + n := by
              simpa using Nat.add_lt_add_right hyx n
            have hypos : 1 ≤ y := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le x) hyx)
            have hsubeq : y + n - 1 = y - 1 + n := by
              rw [Nat.add_comm y n, Nat.add_sub_assoc hypos, Nat.add_comm]
            simp [Lambda.lift, Lambda.subst, hyxneq, hyk, hyx, hy1k, hygt', hsubeq]
          · have hyltx : y < x := by
              have hyxneq : y ≠ x := by
                intro hy_eq
                exact hxy hy_eq.symm
              exact lt_of_le_of_ne (Nat.le_of_not_gt hyx) hyxneq
            have hyxneq : y ≠ x := by
              intro hy_eq
              exact hxy hy_eq.symm
            have hyltxn : y + n < x + n := Nat.add_lt_add_right hyltx n
            simp [Lambda.lift, Lambda.subst, hyxneq, hyk, hyx]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.lift, Lambda.subst, ih1, ih2, h]
  | lam t ih =>
      have h' := ih (s := Lambda.lift 1 0 s) (k := k + 1) (x := x + 1) (Nat.succ_le_succ h)
      have h_lift :
          Lambda.lift n (k + 1) (Lambda.lift 1 0 s) = Lambda.lift 1 0 (Lambda.lift n k s) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Lambda.lift_lift s 1 n 0 k (Nat.zero_le k)).symm
      simpa [Lambda.lift, Lambda.subst, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h_lift]
          using
        congrArg Lambda.lam h'

/-- Lifting and substitution commute when x ≤ k. -/
theorem Lambda.lift_subst_lo (t s : Lambda) (n k x : ℕ) (h : x ≤ k) :
    Lambda.lift n k (Lambda.subst s x t) = Lambda.subst (Lambda.lift n k s) x
        (Lambda.lift n (k + 1) t) := by
  induction t generalizing s k x with
  | var y =>
      by_cases hxy : y = x
      · subst hxy
        have hyk1 : y < k + 1 := lt_of_le_of_lt h (Nat.lt_succ_self k)
        simp [Lambda.lift, Lambda.subst, hyk1]
      · by_cases hyx : y > x
        · by_cases hyk1 : y < k + 1
          · have hypos : y ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le x) hyx)
            have hy1k : y - 1 < k := by
              have hy1lt : y - 1 < y := Nat.pred_lt hypos
              exact lt_of_lt_of_le hy1lt (Nat.lt_succ_iff.mp hyk1)
            have hyxneq : y ≠ x := Nat.ne_of_gt hyx
            simp [Lambda.lift, Lambda.subst, hyxneq, hyx, hy1k, hyk1]
          · have hy1k : ¬ y - 1 < k := by
              intro hy1k
              have hyk1' : y < k + 1 := by
                have hypos : 0 < y := lt_of_le_of_lt (Nat.zero_le x) hyx
                rw [show y = Nat.succ (y - 1) by simpa using (Nat.succ_pred_eq_of_pos hypos).symm]
                simpa using Nat.succ_lt_succ hy1k
              exact hyk1 hyk1'
            have hyxneq : y ≠ x := Nat.ne_of_gt hyx
            have hygt' : y + n > x := lt_of_lt_of_le hyx (Nat.le_add_right y n)
            have hyneqn : y + n ≠ x := Nat.ne_of_gt hygt'
            have hy1eq : y - 1 + n = y + n - 1 := by
              have hypos : 1 ≤ y := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le x) hyx)
              rw [Nat.add_comm (y - 1) n, Nat.add_comm y n, Nat.add_sub_assoc hypos]
            simp [Lambda.lift, Lambda.subst, hyxneq, hyx, hy1k, hyk1, hygt', hyneqn, hy1eq]
        · have hyltx : y < x := by
            have hyxne : y ≠ x := hxy
            exact lt_of_le_of_ne (Nat.le_of_not_gt hyx) hyxne
          have hyk : y < k := lt_of_lt_of_le hyltx h
          have hyk1 : y < k + 1 := lt_trans hyltx (lt_of_le_of_lt h (Nat.lt_succ_self k))
          have hyxneq : y ≠ x := hxy
          have hyngt : ¬ y > x := hyx
          simp [Lambda.lift, Lambda.subst, hyxneq, hyngt, hyk, hyk1]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.lift, Lambda.subst, ih1, ih2, h]
  | lam t ih =>
      have h' := ih (s := Lambda.lift 1 0 s) (k := k + 1) (x := x + 1) (Nat.succ_le_succ h)
      have h_lift :
          Lambda.lift n (k + 1) (Lambda.lift 1 0 s) = Lambda.lift 1 0 (Lambda.lift n k s) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Lambda.lift_lift s 1 n 0 k (Nat.zero_le _)).symm
      simpa [Lambda.lift, Lambda.subst, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h_lift]
          using
        congrArg Lambda.lam h'

/-- Lifting commutes with beta-substitution at index `0`. -/
theorem Lambda.lift_subst_zero (t s : Lambda) (n k : ℕ) :
    Lambda.lift n k (Lambda.subst s 0 t) = Lambda.subst (Lambda.lift n k s) 0
        (Lambda.lift n (k + 1) t) := by
  simpa using Lambda.lift_subst_lo t s n k 0 (Nat.zero_le k)

------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

/-- Substitution and lifting commute (case 2). -/
theorem Lambda.subst_lift (t : Lambda) (s : Lambda) (x : ℕ) :
    Lambda.subst s x (Lambda.lift 1 x t) = t := by
  induction t generalizing s x with
  | var y =>
      by_cases hy : y < x
      · have hneq : y ≠ x := ne_of_lt hy
        have hngt : ¬ y > x := Nat.not_lt.mpr (Nat.le_of_lt hy)
        simp [Lambda.lift, Lambda.subst, hy, hneq, hngt]
      · have hgt : y + 1 > x := by
          exact lt_of_le_of_lt (Nat.le_of_not_lt hy) (Nat.lt_succ_self y)
        have hneq : y + 1 ≠ x := Nat.ne_of_gt hgt
        simp [Lambda.lift, Lambda.subst, hy, hneq, hgt]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.lift, Lambda.subst, ih1, ih2]
  | lam t ih =>
      simpa [Lambda.lift, Lambda.subst] using
        congrArg Lambda.lam (ih (Lambda.lift 1 0 s) (x + 1))

/-- The substitution lemma: applying two substitutions in succession. -/
theorem Lambda.subst_subst (t : Lambda) (s1 s2 : Lambda) (x y : ℕ) (h : y ≤ x) :
    Lambda.subst s1 x (Lambda.subst s2 y t) =
    Lambda.subst (Lambda.subst s1 x s2) y (Lambda.subst (Lambda.lift 1 y s1) (x + 1) t) := by
  induction t generalizing s1 s2 x y with
  | var z =>
      by_cases hzy : z = y
      · subst z
        have hneq : y ≠ x + 1 := by omega
        have hngt : ¬ y > x + 1 := by omega
        simp [Lambda.subst, hneq, hngt]
      · by_cases hzx1 : z = x + 1
        · subst hzx1
          have hgt : x + 1 > y := by omega
          have hneq : x + 1 ≠ y := by omega
          have h_inner :
              Lambda.subst (Lambda.lift 1 y s1) (x + 1) (Lambda.var (x + 1)) =
                Lambda.lift 1 y s1 := by
            simp [Lambda.subst]
          have h_lhs : Lambda.subst s1 x (Lambda.subst s2 y (Lambda.var (x + 1))) = s1 := by
            simp [Lambda.subst, hneq, hgt]
          rw [h_lhs, h_inner]
          simpa using (Lambda.subst_lift s1 (Lambda.subst s1 x s2) y).symm
        · by_cases hzgtx1 : z > x + 1
          · have hzgy : z > y := by omega
            have hgtx : z - 1 > x := by omega
            have hgty : z - 1 > y := by omega
            have hneqx : z - 1 ≠ x := Nat.ne_of_gt hgtx
            have hneqy : z - 1 ≠ y := Nat.ne_of_gt hgty
            simp [Lambda.subst, hzy, hzx1, hzgy, hzgtx1, hneqx, hgtx, hneqy, hgty]
          · by_cases hzgy : z > y
            · have hltx1 : z < x + 1 := by omega
              have hltx : z - 1 < x := by omega
              have hneqx : z - 1 ≠ x := ne_of_lt hltx
              have hngtx : ¬ z - 1 > x := by omega
              simp [Lambda.subst, hzy, hzx1, hzgtx1, hzgy, hneqx, hngtx]
            · have hltx : z < x := by omega
              have hneqx : z ≠ x := ne_of_lt hltx
              have hngtx : ¬ z > x := by omega
              simp [Lambda.subst, hzy, hzx1, hzgtx1, hzgy, hneqx, hngtx]
  | app t1 t2 ih1 ih2 =>
      simp [Lambda.subst, ih1 s1 s2 x y h, ih2 s1 s2 x y h]
  | lam t ih =>
      have h' := ih (s1 := Lambda.lift 1 0 s1) (s2 := Lambda.lift 1 0 s2) (x := x + 1) (y := y + 1)
          (by omega)
      have h_subst :
          Lambda.subst (Lambda.lift 1 0 s1) (x + 1) (Lambda.lift 1 0 s2) =
            Lambda.lift 1 0 (Lambda.subst s1 x s2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Lambda.lift_subst s2 s1 1 0 x (Nat.zero_le x)).symm
      have h_lift :
          Lambda.lift 1 (y + 1) (Lambda.lift 1 0 s1) =
            Lambda.lift 1 0 (Lambda.lift 1 y s1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Lambda.lift_lift s1 1 1 0 y (Nat.zero_le y)).symm
      simpa [Lambda.subst, h_subst, h_lift] using congrArg Lambda.lam h'

/-- The substitution lemma needed for the beta case of parallel substitution. -/
theorem Lambda.subst_subst_zero (t : Lambda) (s1 s2 : Lambda) (x : ℕ) :
    Lambda.subst s1 x (Lambda.subst s2 0 t) =
    Lambda.subst (Lambda.subst s1 x s2) 0 (Lambda.subst (Lambda.lift 1 0 s1) (x + 1) t) := by
  simpa using Lambda.subst_subst t s1 s2 x 0 (Nat.zero_le x)
