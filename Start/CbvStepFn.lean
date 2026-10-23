import Start.CbvStateWord

/-!
# The CEK machine as a function
(row M25-CBV-STEP-PROG; big round 2, run 1, item W3)

`Complexity.Space.AbsMachine` (`Start/SpaceCompile.lean`) takes a step *function*
`σ → Option σ`.  The CEK transitions of `Start/CbvMachine.lean` are a relation; this module gives
the function and proves that it computes exactly the relation:

* `CEK.stepFn` — one transition, `none` on final states;
* **`CEK.stepFn_eq_some_iff`** — `stepFn s = some s'` iff `Trans l s s'` for some label `l`;
* `CEK.stepFn_eq_none_iff` — `stepFn s = none` iff `s` is final.
-/

set_option autoImplicit false

namespace CEK

open Krivine (Clos Env)

/-- **One transition of the CEK machine, as a function.** -/
def stepFn : State → Option State
  | .eval (.app t u) e k => some (.eval t e (.arg u e :: k))
  | .eval (.lam t) e k => some (.ret (Clos.mk (.lam t) e) k)
  | .eval (.var n) e k =>
    match e[n]? with
    | some c => some (.ret c k)
    | none => some (.ret (Clos.mk (.var n) e) k)
  | .ret c (.arg u e :: k) => some (.eval u e (.fn c :: k))
  | .ret v (.fn (Clos.mk (.lam t) e) :: k) => some (.eval t (v :: e) k)
  | .ret _ (.fn (Clos.mk (.var _) _) :: _) => none
  | .ret _ (.fn (Clos.mk (.app _ _) _) :: _) => none
  | .ret _ [] => none

theorem stepFn_of_trans {l : Label} {s s' : State} (h : Trans l s s') : stepFn s = some s' := by
  cases h with
  | app => rfl
  | lam => rfl
  | var n e c k h => simp [stepFn, h]
  | free n e k h => simp [stepFn, h]
  | swap => rfl
  | beta => rfl

theorem trans_of_stepFn {s s' : State} (h : stepFn s = some s') : ∃ l, Trans l s s' := by
  match s, h with
  | .eval (.app t u) e k, h => cases h; exact ⟨_, .app t u e k⟩
  | .eval (.lam t) e k, h => cases h; exact ⟨_, .lam t e k⟩
  | .eval (.var n) e k, h =>
    simp only [stepFn] at h
    cases hn : e[n]? with
    | some c => rw [hn] at h; cases h; exact ⟨_, .var n e c k hn⟩
    | none => rw [hn] at h; cases h; exact ⟨_, .free n e k hn⟩
  | .ret c (.arg u e :: k), h => cases h; exact ⟨_, .swap c u e k⟩
  | .ret v (.fn (Clos.mk (.lam t) e) :: k), h => cases h; exact ⟨_, .beta t e v k⟩

/-- **The step function computes the transition relation.** -/
theorem stepFn_eq_some_iff {s s' : State} : stepFn s = some s' ↔ ∃ l, Trans l s s' :=
  ⟨trans_of_stepFn, fun ⟨_, h⟩ => stepFn_of_trans h⟩

/-- The step function halts exactly on final states. -/
theorem stepFn_eq_none_iff {s : State} : stepFn s = none ↔ IsFinal s := by
  constructor
  · intro h l s' ht
    rw [stepFn_of_trans ht] at h
    cases h
  · intro h
    cases hs : stepFn s with
    | none => rfl
    | some s' =>
      obtain ⟨l, ht⟩ := trans_of_stepFn hs
      exact (h l s' ht).elim

end CEK
