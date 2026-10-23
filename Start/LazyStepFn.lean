import Start.LazyStateWord

/-!
# The lazy machine as a function
(row M25-CBNEED-STEP-PROG; big round 2, run 1, item W3)

`Complexity.Space.AbsMachine` takes a step function.  This module gives the transitions of the
lazy machine (`Start/LazyMachine.lean`) as a function and proves that it computes exactly the
relation:

* `Lazy.lstepFn` — one transition, `none` on final states;
* **`Lazy.lstepFn_eq_some_iff`** — `lstepFn s = some s'` iff `LStep s s'`;
* `Lazy.lstepFn_eq_none_iff` — `lstepFn s = none` iff `LFinal s`.
-/

set_option autoImplicit false

namespace Lazy

/-- **One transition of the lazy machine, as a function.** -/
def lstepFn : LState → Option LState
  | ⟨.app t u, e, S, H⟩ => some ⟨t, e, .arg H.length :: S, H ++ [.thunk ⟨u, e⟩]⟩
  | ⟨.lam t, e, .arg a :: S, H⟩ => some ⟨t, a :: e, S, H⟩
  | ⟨.lam t, e, .upd a :: S, H⟩ =>
    match H[a]? with
    | some (.hole c) => some ⟨.lam t, e, S, H.set a (.value c ⟨.lam t, e⟩)⟩
    | _ => none
  | ⟨.lam _, _, [], _⟩ => none
  | ⟨.var n, e, S, H⟩ =>
    match e[n]? with
    | some a =>
      match H[a]? with
      | some (.thunk c) => some ⟨c.code, c.env, .upd a :: S, H.set a (.hole c)⟩
      | some (.value _ v) => some ⟨v.code, v.env, S, H⟩
      | _ => none
    | none => none

theorem lstepFn_of_trans {l : LLabel} {s s' : LState} (h : LTrans l s s') :
    lstepFn s = some s' := by
  cases h with
  | app => rfl
  | beta => rfl
  | force n e S H a c he hc => simp [lstepFn, he, hc]
  | fetch n e S H a c v he hc => simp [lstepFn, he, hc]
  | update t e a S H c hc => simp [lstepFn, hc]

theorem trans_of_lstepFn {s s' : LState} (h : lstepFn s = some s') : LStep s s' := by
  obtain ⟨t, e, S, H⟩ := s
  cases t with
  | app t u => cases h; exact ⟨_, .app t u e S H⟩
  | lam t =>
    cases S with
    | nil => simp [lstepFn] at h
    | cons f S =>
      cases f with
      | arg a => cases h; exact ⟨_, .beta t e a S H⟩
      | upd a =>
        simp only [lstepFn] at h
        split at h
        · rename_i c hc
          cases h; exact ⟨_, .update t e a S H c hc⟩
        · cases h
  | var n =>
    simp only [lstepFn] at h
    split at h
    · rename_i a he
      split at h
      · rename_i c hc
        cases h; exact ⟨_, .force n e S H a c he hc⟩
      · rename_i c v hc
        cases h; exact ⟨_, .fetch n e S H a c v he hc⟩
      · cases h
    · cases h

/-- **The step function computes the transition relation.** -/
theorem lstepFn_eq_some_iff {s s' : LState} : lstepFn s = some s' ↔ LStep s s' :=
  ⟨trans_of_lstepFn, fun ⟨_, h⟩ => lstepFn_of_trans h⟩

/-- The step function halts exactly on final states. -/
theorem lstepFn_eq_none_iff {s : LState} : lstepFn s = none ↔ LFinal s := by
  constructor
  · intro h s' ⟨l, ht⟩
    rw [lstepFn_of_trans ht] at h
    cases h
  · intro h
    cases hs : lstepFn s with
    | none => rfl
    | some s' => exact (h s' (trans_of_lstepFn hs)).elim

end Lazy
