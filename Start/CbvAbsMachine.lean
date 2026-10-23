import Start.CbvStepFn
import Start.SpaceCompile

/-!
# The CEK machine as an abstract machine of the space model
(row M25-CBV-STEP-PROG; big round 2, run 1, item W3)

* `CEK.absMachine dec acc` — the abstract machine (`Complexity.Space.AbsMachine`) that starts on
  `State.init (dec x)` for an input decoder `dec`, steps by `CEK.stepFn`, and accepts by `acc`;
* **`CEK.absMachine_reaches_iff`** — its reachable states are exactly the states reached by CEK
  runs from the initial state.
-/

set_option autoImplicit false

namespace CEK

/-- The CEK machine as an abstract machine on binary inputs. -/
def absMachine (dec : List Bool → Lambda) (acc : State → Bool) :
    Complexity.Space.AbsMachine State where
  start x := State.init (dec x)
  step := stepFn
  accept := acc

theorem run_of_reflTransGen {s s' : State}
    (h : Relation.ReflTransGen (fun a b => stepFn a = some b) s s') : ∃ n b, Run n b s s' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, 0, .refl _⟩
  | head hs _ ih =>
    obtain ⟨n, b, hr⟩ := ih
    obtain ⟨l, ht⟩ := trans_of_stepFn hs
    exact ⟨_, _, .cons ht hr⟩

theorem reflTransGen_of_run {n b : ℕ} {s s' : State} (h : Run n b s s') :
    Relation.ReflTransGen (fun a b => stepFn a = some b) s s' := by
  induction h with
  | refl => exact .refl
  | cons ht _ ih => exact .head (stepFn_of_trans ht) ih

/-- **The reachable states of the abstract machine are the states reached by CEK runs.** -/
theorem absMachine_reaches_iff (dec : List Bool → Lambda) (acc : State → Bool) (x : List Bool)
    (s : State) :
    (absMachine dec acc).Reaches x s ↔ ∃ n b, Run n b (State.init (dec x)) s :=
  ⟨fun h => run_of_reflTransGen h, fun ⟨_, _, h⟩ => reflTransGen_of_run h⟩

end CEK
