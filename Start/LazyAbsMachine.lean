import Start.LazyStepFn
import Start.SpaceCompile

/-!
# The lazy machine as an abstract machine of the space model
(row M25-CBNEED-STEP-PROG; big round 2, run 1, item W3)

* `Lazy.labsMachine dec acc` — the abstract machine (`Complexity.Space.AbsMachine`) that starts on
  `LState.init (dec x)` for an input decoder `dec`, steps by `Lazy.lstepFn`, and accepts by `acc`;
* **`Lazy.labsMachine_reaches_iff`** — its reachable states are exactly the states reached by runs
  of the lazy machine from the initial state.
-/

set_option autoImplicit false

namespace Lazy

/-- The lazy machine as an abstract machine on binary inputs. -/
def labsMachine (dec : List Bool → Lambda) (acc : LState → Bool) :
    Complexity.Space.AbsMachine LState where
  start x := LState.init (dec x)
  step := lstepFn
  accept := acc

theorem lrun_of_reflTransGen {s s' : LState}
    (h : Relation.ReflTransGen (fun a b => lstepFn a = some b) s s') :
    ∃ n b fs, LRun n b fs s s' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, 0, [], .refl _⟩
  | head hs _ ih =>
    obtain ⟨n, b, fs, hr⟩ := ih
    obtain ⟨l, ht⟩ := trans_of_lstepFn hs
    exact ⟨_, _, _, .cons ht hr⟩

theorem reflTransGen_of_lrun {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') :
    Relation.ReflTransGen (fun a b => lstepFn a = some b) s s' := by
  induction h with
  | refl => exact .refl
  | cons ht _ ih => exact .head (lstepFn_of_trans ht) ih

/-- **The reachable states of the abstract machine are the states reached by lazy runs.** -/
theorem labsMachine_reaches_iff (dec : List Bool → Lambda) (acc : LState → Bool) (x : List Bool)
    (s : LState) :
    (labsMachine dec acc).Reaches x s ↔ ∃ n b fs, LRun n b fs (LState.init (dec x)) s :=
  ⟨fun h => lrun_of_reflTransGen h, fun ⟨_, _, _, h⟩ => reflTransGen_of_lrun h⟩

end Lazy
