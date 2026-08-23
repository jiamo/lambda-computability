/-
Syntax of Gödel's System T: terms, de Bruijn lifting and substitution, and the substitution
lemmas.

The term language extends the untyped syntax of `Start/Syntax.lean` with the three constructors
that make the calculus a *typed* one with a primitive recursor:

* `Tm.zero`, `Tm.succ n` — the numerals;
* `Tm.natrec z f n` — primitive recursion, `natrec z f 0 = z` and
  `natrec z f (succ n) = f n (natrec z f n)`.

Keeping `succ` and `natrec` as genuine constructors (rather than constants applied by `app`) is
what makes the notion of *neutral* term well behaved in the strong normalization proof of
`Start/SystemT.lean`.

The de Bruijn conventions and the statements of the substitution lemmas are exactly those of
`Start/Syntax.lean`; only the extra structural cases are new.
-/

import Start.Tactics
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GodelT

/-- Terms of System T, in de Bruijn notation. -/
inductive Tm where
  | var : ℕ → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  | zero : Tm
  | succ : Tm → Tm
  | natrec : Tm → Tm → Tm → Tm
  deriving DecidableEq

/-- `lift n k t` increments all free variables of `t` that are `≥ k` by `n`. -/
def lift (n : ℕ) (k : ℕ) : Tm → Tm
  | Tm.var y => if y < k then Tm.var y else Tm.var (y + n)
  | Tm.app a b => Tm.app (lift n k a) (lift n k b)
  | Tm.lam t => Tm.lam (lift n (k + 1) t)
  | Tm.zero => Tm.zero
  | Tm.succ t => Tm.succ (lift n k t)
  | Tm.natrec z f m => Tm.natrec (lift n k z) (lift n k f) (lift n k m)

/-- `subst s x t` replaces the variable `x` in `t` by `s`, shifting the larger indices down. -/
def subst (s : Tm) (x : ℕ) : Tm → Tm
  | Tm.var y => if y = x then s else if y > x then Tm.var (y - 1) else Tm.var y
  | Tm.app a b => Tm.app (subst s x a) (subst s x b)
  | Tm.lam t => Tm.lam (subst (lift 1 0 s) (x + 1) t)
  | Tm.zero => Tm.zero
  | Tm.succ t => Tm.succ (subst s x t)
  | Tm.natrec z f m => Tm.natrec (subst s x z) (subst s x f) (subst s x m)

------------------------------------------------------------------------
-- Lift lemmas
------------------------------------------------------------------------

theorem lift_zero (k : ℕ) (t : Tm) : lift 0 k t = t := by
  induction t generalizing k with
  | var y => simp [lift]
  | app a b iha ihb => simp [lift, iha, ihb]
  | lam t ih => simp [lift, ih]
  | zero => simp [lift]
  | succ t ih => simp [lift, ih]
  | natrec z f m ihz ihf ihm => simp [lift, ihz, ihf, ihm]

theorem lift_add (n m : ℕ) (k : ℕ) (t : Tm) : lift (n + m) k t = lift n k (lift m k t) := by
  induction t generalizing k with
  | var y =>
      by_cases hy : y < k
      · simp [lift, hy]
      · have hym : ¬ y + m < k :=
          Nat.not_lt.mpr (le_trans (Nat.le_of_not_lt hy) (Nat.le_add_right y m))
        simp only [lift, hy, hym, if_false]
        congr 1
        omega
  | app a b iha ihb => simp [lift, iha, ihb]
  | lam t ih => simp [lift, ih]
  | zero => simp [lift]
  | succ t ih => simp [lift, ih]
  | natrec z f p ihz ihf ihp => simp [lift, ihz, ihf, ihp]

theorem lift_lift (t : Tm) (n m k j : ℕ) (h : k ≤ j) :
    lift n k (lift m j t) = lift m (j + n) (lift n k t) := by
  induction t generalizing k j with
  | var y =>
      by_cases hyk : y < k
      · have hyj : y < j := lt_of_lt_of_le hyk h
        have hyjn : y < j + n := lt_of_lt_of_le hyj (Nat.le_add_right j n)
        simp [lift, hyk, hyj, hyjn]
      · by_cases hyj : y < j
        · have hyjn : y + n < j + n := Nat.add_lt_add_right hyj n
          simp [lift, hyk, hyj, hyjn]
        · have hymk : ¬ y + m < k :=
            Nat.not_lt.mpr (le_trans (Nat.le_of_not_lt hyk) (Nat.le_add_right y m))
          have hynj : ¬ y + n < j + n :=
            Nat.not_lt.mpr (Nat.add_le_add_right (Nat.le_of_not_lt hyj) n)
          simp only [lift, hyk, hyj, hymk, hynj, if_false]
          congr 1
          omega
  | app a b iha ihb => simp [lift, iha _ _ h, ihb _ _ h]
  | lam t ih =>
      simpa [lift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg Tm.lam (ih (k := k + 1) (j := j + 1) (Nat.succ_le_succ h))
  | zero => simp [lift]
  | succ t ih => simp [lift, ih _ _ h]
  | natrec z f p ihz ihf ihp => simp [lift, ihz _ _ h, ihf _ _ h, ihp _ _ h]

------------------------------------------------------------------------
-- Lift-substitution interaction
------------------------------------------------------------------------

theorem lift_subst (t : Tm) (s : Tm) (n k x : ℕ) (h : k ≤ x) :
    lift n k (subst s x t) = subst (lift n k s) (x + n) (lift n k t) := by
  induction t generalizing s k x with
  | var y =>
      by_cases hxy : x = y
      · subst hxy
        have hxk : ¬ x < k := Nat.not_lt.mpr h
        simp [lift, subst, hxk]
      · by_cases hyk : y < k
        · have hyxneq : y ≠ x := fun hy => hxy hy.symm
          have hyltx : y < x := lt_of_lt_of_le hyk h
          have hygt : ¬ y > x := Nat.not_lt.mpr (Nat.le_of_lt hyltx)
          have hyneq : y ≠ x + n := ne_of_lt (lt_of_lt_of_le hyltx (Nat.le_add_right x n))
          have hyngt : ¬ y > x + n :=
            Nat.not_lt.mpr (Nat.le_of_lt (lt_of_lt_of_le hyltx (Nat.le_add_right x n)))
          simp [lift, subst, hyxneq, hyk, hygt, hyneq, hyngt]
        · by_cases hyx : y > x
          · have hyxneq : y ≠ x := fun hy => hxy hy.symm
            have hy1k : ¬ y - 1 < k :=
              Nat.not_lt.mpr (le_trans h (Nat.le_sub_one_of_lt hyx))
            have hyneq : y + n ≠ x + n := fun h' => hxy ((Nat.add_right_cancel h').symm)
            have hygt' : y + n > x + n := by simpa using Nat.add_lt_add_right hyx n
            have hypos : 1 ≤ y := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le x) hyx)
            have hsubeq : y + n - 1 = y - 1 + n := by
              rw [Nat.add_comm y n, Nat.add_sub_assoc hypos, Nat.add_comm]
            simp [lift, subst, hyxneq, hyk, hyx, hy1k, hygt', hsubeq]
          · have hyxneq : y ≠ x := fun hy => hxy hy.symm
            have hyltx : y < x := lt_of_le_of_ne (Nat.le_of_not_gt hyx) hyxneq
            have hyltxn : y + n < x + n := Nat.add_lt_add_right hyltx n
            simp [lift, subst, hyxneq, hyk, hyx]
  | app a b iha ihb => simp [lift, subst, iha, ihb, h]
  | lam t ih =>
      have h' := ih (s := lift 1 0 s) (k := k + 1) (x := x + 1) (Nat.succ_le_succ h)
      have h_lift : lift n (k + 1) (lift 1 0 s) = lift 1 0 (lift n k s) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (lift_lift s 1 n 0 k (Nat.zero_le k)).symm
      simpa [lift, subst, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h_lift] using
        congrArg Tm.lam h'
  | zero => simp [lift, subst]
  | succ t ih => simp [lift, subst, ih, h]
  | natrec z f p ihz ihf ihp => simp [lift, subst, ihz, ihf, ihp, h]

theorem subst_lift (t : Tm) (s : Tm) (x : ℕ) : subst s x (lift 1 x t) = t := by
  induction t generalizing s x with
  | var y =>
      by_cases hy : y < x
      · have hneq : y ≠ x := ne_of_lt hy
        have hngt : ¬ y > x := Nat.not_lt.mpr (Nat.le_of_lt hy)
        simp [lift, subst, hy, hneq, hngt]
      · have hgt : y + 1 > x := lt_of_le_of_lt (Nat.le_of_not_lt hy) (Nat.lt_succ_self y)
        have hneq : y + 1 ≠ x := Nat.ne_of_gt hgt
        simp [lift, subst, hy, hneq, hgt]
  | app a b iha ihb => simp [lift, subst, iha, ihb]
  | lam t ih => simpa [lift, subst] using congrArg Tm.lam (ih (lift 1 0 s) (x + 1))
  | zero => simp [lift, subst]
  | succ t ih => simp [lift, subst, ih]
  | natrec z f p ihz ihf ihp => simp [lift, subst, ihz, ihf, ihp]

theorem subst_subst (t : Tm) (s1 s2 : Tm) (x y : ℕ) (h : y ≤ x) :
    subst s1 x (subst s2 y t) =
      subst (subst s1 x s2) y (subst (lift 1 y s1) (x + 1) t) := by
  induction t generalizing s1 s2 x y with
  | var z =>
      by_cases hzy : z = y
      · subst hzy
        have hneq : z ≠ x + 1 := by omega
        have hngt : ¬ z > x + 1 := by omega
        simp [subst, hneq, hngt]
      · by_cases hzx1 : z = x + 1
        · subst hzx1
          have hgt : x + 1 > y := by omega
          have hneq : x + 1 ≠ y := by omega
          have h_inner : subst (lift 1 y s1) (x + 1) (Tm.var (x + 1)) = lift 1 y s1 := by
            simp [subst]
          have h_lhs : subst s1 x (subst s2 y (Tm.var (x + 1))) = s1 := by
            simp [subst, hneq, hgt]
          rw [h_lhs, h_inner]
          simpa using (subst_lift s1 (subst s1 x s2) y).symm
        · by_cases hzgtx1 : z > x + 1
          · have hzgy : z > y := by omega
            have hgtx : z - 1 > x := by omega
            have hgty : z - 1 > y := by omega
            have hneqx : z - 1 ≠ x := Nat.ne_of_gt hgtx
            have hneqy : z - 1 ≠ y := Nat.ne_of_gt hgty
            simp [subst, hzy, hzx1, hzgy, hzgtx1, hneqx, hgtx, hneqy, hgty]
          · by_cases hzgy : z > y
            · have hltx1 : z < x + 1 := by omega
              have hltx : z - 1 < x := by omega
              have hneqx : z - 1 ≠ x := ne_of_lt hltx
              have hngtx : ¬ z - 1 > x := by omega
              simp [subst, hzy, hzx1, hzgtx1, hzgy, hneqx, hngtx]
            · have hltx : z < x := by omega
              have hneqx : z ≠ x := ne_of_lt hltx
              have hngtx : ¬ z > x := by omega
              simp [subst, hzy, hzx1, hzgtx1, hzgy, hneqx, hngtx]
  | app a b iha ihb => simp [subst, iha s1 s2 x y h, ihb s1 s2 x y h]
  | lam t ih =>
      have h' := ih (s1 := lift 1 0 s1) (s2 := lift 1 0 s2) (x := x + 1) (y := y + 1) (by omega)
      have h_subst : subst (lift 1 0 s1) (x + 1) (lift 1 0 s2) = lift 1 0 (subst s1 x s2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (lift_subst s2 s1 1 0 x (Nat.zero_le x)).symm
      have h_lift : lift 1 (y + 1) (lift 1 0 s1) = lift 1 0 (lift 1 y s1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (lift_lift s1 1 1 0 y (Nat.zero_le y)).symm
      simpa [subst, h_subst, h_lift] using congrArg Tm.lam h'
  | zero => simp [subst]
  | succ t ih => simp [subst, ih s1 s2 x y h]
  | natrec z f p ihz ihf ihp => simp [subst, ihz s1 s2 x y h, ihf s1 s2 x y h, ihp s1 s2 x y h]

theorem subst_subst_zero (t : Tm) (s1 s2 : Tm) (x : ℕ) :
    subst s1 x (subst s2 0 t) =
      subst (subst s1 x s2) 0 (subst (lift 1 0 s1) (x + 1) t) := by
  simpa using subst_subst t s1 s2 x 0 (Nat.zero_le x)

------------------------------------------------------------------------
-- Parallel substitution
------------------------------------------------------------------------

/-- Extend an environment when passing under a binder. -/
def envCons (u : ℕ → Tm) : ℕ → Tm
  | 0 => Tm.var 0
  | k + 1 => lift 1 0 (u k)

/-- Parallel substitution of an environment into a term. -/
def substEnv (u : ℕ → Tm) : Tm → Tm
  | Tm.var n => u n
  | Tm.app a b => Tm.app (substEnv u a) (substEnv u b)
  | Tm.lam t => Tm.lam (substEnv (envCons u) t)
  | Tm.zero => Tm.zero
  | Tm.succ t => Tm.succ (substEnv u t)
  | Tm.natrec z f m => Tm.natrec (substEnv u z) (substEnv u f) (substEnv u m)

/-- Extend an environment with a term at index `0`. -/
def envScons (v : Tm) (u : ℕ → Tm) : ℕ → Tm
  | 0 => v
  | k + 1 => u k

theorem substEnv_var_id (t : Tm) : substEnv (fun k => Tm.var k) t = t := by
  have h : ∀ (t : Tm) (u : ℕ → Tm), (∀ k, u k = Tm.var k) → substEnv u t = t := by
    intro t
    induction t with
    | var n => intro u hu; simp only [substEnv, hu]
    | app a b iha ihb => intro u hu; simp only [substEnv, iha u hu, ihb u hu]
    | lam t ih =>
        intro u hu
        refine congrArg Tm.lam (ih (envCons u) ?_)
        intro k
        cases k with
        | zero => simp [envCons]
        | succ k => simp [envCons, hu, lift]
    | zero => intro u _; simp [substEnv]
    | succ t ih => intro u hu; simp only [substEnv, ih u hu]
    | natrec z f m ihz ihf ihm =>
        intro u hu; simp only [substEnv, ihz u hu, ihf u hu, ihm u hu]
  exact h t _ (fun _ => rfl)

/-- Substituting into a parallel substitution amounts to composing the environments. -/
theorem subst_substEnv (v : Tm) :
    ∀ (t : Tm) (k : ℕ) (u w : ℕ → Tm),
      (∀ j, w j = subst (lift k 0 v) k (u j)) →
      subst (lift k 0 v) k (substEnv u t) = substEnv w t := by
  intro t
  induction t with
  | var j => intro k u w hw; simp only [substEnv, hw j]
  | app a b iha ihb =>
      intro k u w hw
      simp only [substEnv, subst, iha k u w hw, ihb k u w hw]
  | lam t ih =>
      intro k u w hw
      have hlift : lift 1 0 (lift k 0 v) = lift (k + 1) 0 v := by
        rw [Nat.add_comm k 1, lift_add]
      have hstep : ∀ j, envCons w j = subst (lift (k + 1) 0 v) (k + 1) (envCons u j) := by
        intro j
        cases j with
        | zero => simp [envCons, subst]
        | succ j =>
            simp only [envCons, hw j]
            rw [← hlift, lift_subst (u j) (lift k 0 v) 1 0 k (Nat.zero_le k)]
      have := ih (k + 1) (envCons u) (envCons w) hstep
      simp only [substEnv, subst, hlift]
      exact congrArg Tm.lam this
  | zero => intro k u w _; simp [substEnv, subst]
  | succ t ih => intro k u w hw; simp only [substEnv, subst, ih k u w hw]
  | natrec z f m ihz ihf ihm =>
      intro k u w hw
      simp only [substEnv, subst, ihz k u w hw, ihf k u w hw, ihm k u w hw]

theorem subst_zero_substEnv (v : Tm) (t : Tm) (u : ℕ → Tm) :
    subst v 0 (substEnv (envCons u) t) = substEnv (envScons v u) t := by
  have key : ∀ j, envScons v u j = subst (lift 0 0 v) 0 (envCons u j) := by
    intro j
    rw [lift_zero]
    cases j with
    | zero => simp [envCons, envScons, subst]
    | succ j =>
        simp only [envCons, envScons]
        exact (subst_lift (u j) v 0).symm
  have h := subst_substEnv v t 0 (envCons u) (envScons v u) key
  rwa [lift_zero] at h

end GodelT
