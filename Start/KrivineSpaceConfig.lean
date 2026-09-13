/-
**The state of the Krivine machine as a configuration of the space-bounded machine model.**

`Start/KrivineSpace.lean` measures the space of an implementation state in *cells* — the number
of heap cells it keeps alive — and `Start/KrivineSpaceLog.lean` writes a state as a word with
fixed-width binary fields, which is what costs bits rather than cells.  `Start/SpaceMachine.lean`
measures the memory of an offline machine as the used length of its binary work tape
(`Complexity.Space.Config.space`).  This module joins the two measures: it puts the word of a
collected state on the work tape of a configuration and reads off what that costs.

Main definitions:

* `Krivine.Impl.spaceConfig` — the configuration whose work tape holds the binary word of the
  collected state, with both heads at the origin.

Main results:

* `Krivine.Impl.spaceConfig_space` — its memory measure is the length of that word;
* `Krivine.Impl.gcState_eq_of_spaceConfig_eq` — the configuration determines the collected state,
  so nothing is lost by moving to the tape;
* `Krivine.Impl.space_le_spaceConfig_space` — the tape holds at least one bit per live cell;
* `Krivine.Impl.spaceConfig_space_le` — and at most `(4 + |stack| + 3 · space) · (w + 1)` bits at
  width `w`;
* `Krivine.Impl.spaceConfig_space_le_widthOf` — at the width a collected state actually needs
  this is `(4 + |stack| + 3 · space) · (size (|tab| + |stack| + space) + 1)`;
* `Krivine.Impl.spaceConfig_space_le_of_budget` — **the `O(s · log s)` form**: if the code table,
  the stack and the live data all fit in a budget `S`, the tape holds at most
  `(4 * S + 4) * (Nat.size (3 * S) + 1)` bits;
* `Krivine.Impl.spaceConfig_space_le_gpeak`, `Krivine.Impl.spaceConfig_space_le_of_run_budget` —
  the same bounds **along a whole run** of the collected implementation, in terms of the peak
  live data of that run.

**Boundary.**  This is the *memory* half of the bridge between the two modules: the word of a
state is a work tape, and its length is the memory measure of `Start/SpaceMachine.lean`.  It does
*not* build a machine of that model which performs Krivine transitions on the word, so it does
not on its own place the languages decided by λ-terms inside a space bound in
`Complexity.Space.DSPACE`; that simulation is not formalised.
-/

import Start.KrivineSpaceRun
import Start.SpaceMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

open Complexity.Space (Config)

/-- The configuration of the offline machine model whose work tape holds the binary word of the
collected state, written on `w` bits per field, with both heads at the origin. -/
def spaceConfig (w : ℕ) (s : HState) : Config where
  state := 0
  inHead := 0
  tape := encStateBin w (gcState s)
  wHead := 0

@[simp] theorem spaceConfig_tape (w : ℕ) (s : HState) :
    (spaceConfig w s).tape = encStateBin w (gcState s) := rfl

/-- The memory measure of the configuration is the length of the word — one cell of the work tape
per bit, and at least the one cell the head stands on. -/
theorem spaceConfig_space (w : ℕ) (s : HState) :
    (spaceConfig w s).space = max (encStateBin w (gcState s)).length 1 := rfl

/-- **Nothing is lost on the tape**: at a width that the two collected states fit in, the
configuration determines the collected state. -/
theorem gcState_eq_of_spaceConfig_eq {w : ℕ} {s s' : HState} (h : FitsIn w (gcState s))
    (h' : FitsIn w (gcState s')) (heq : spaceConfig w s = spaceConfig w s') :
    gcState s = gcState s' :=
  encStateBin_inj h h' (congrArg Config.tape heq)

/-- The tape holds at least one bit per live cell. -/
theorem space_le_spaceConfig_space (w : ℕ) (s : HState) :
    space s ≤ (spaceConfig w s).space :=
  le_trans (space_le_encStateBin_gcState_length w s) (Nat.le_max_left _ _)

/-- The tape holds at most `(4 + |stack| + 3 · space) · (w + 1)` bits. -/
theorem spaceConfig_space_le (w : ℕ) (s : HState) :
    (spaceConfig w s).space ≤ (4 + s.stack.length + 3 * space s) * (w + 1) := by
  rw [spaceConfig_space]
  refine max_le (encStateBin_gcState_length_le w s) ?_
  have : 1 * 1 ≤ (4 + s.stack.length + 3 * space s) * (w + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- At the width a collected state actually needs, the tape holds
`(4 + |stack| + 3 · space) · (size (|tab| + |stack| + space) + 1)` bits: the cell measure of
`Start/KrivineSpace.lean` times the number of bits of an address. -/
theorem spaceConfig_space_le_widthOf (tab : Tab) (s : HState) :
    (spaceConfig (widthOf tab s) s).space
      ≤ (4 + s.stack.length + 3 * space s)
          * (Nat.size (tab.length + s.stack.length + space s) + 1) :=
  spaceConfig_space_le _ s

/-- **The logarithmic overhead, in the shape a space bound is stated in.**  If the code table, the
height of the stack and the live data of the state all fit in a budget `S`, the word of the
collected state occupies at most `(4 * S + 4) * (Nat.size (3 * S) + 1)` bits of the work tape —
that is, `O(S · log S)`. -/
theorem spaceConfig_space_le_of_budget {tab : Tab} {s : HState} {S : ℕ}
    (htab : tab.length ≤ S) (hstk : s.stack.length ≤ S) (hsp : space s ≤ S) :
    (spaceConfig (widthOf tab s) s).space ≤ (4 * S + 4) * (Nat.size (3 * S) + 1) := by
  refine le_trans (spaceConfig_space_le_widthOf tab s) (Nat.mul_le_mul ?_ ?_)
  · omega
  · exact Nat.succ_le_succ (Nat.size_le_size (by omega))

/-! ### Along a run -/

/-- Every state of a collected run is written on a work tape of at most
`(4 + |stack| + 3 · peak) · (w + 1)` bits, where `peak` is the peak live data of the run. -/
theorem spaceConfig_space_le_gpeak {tab : Tab} {n : ℕ} {s s₁ : HState} (hv : Valid tab s)
    (hc : Collected s) (hrun : grun tab n s = some s₁) :
    (spaceConfig (widthOf tab s₁) s₁).space
      ≤ (4 + s₁.stack.length + 3 * gpeak tab n s) * (widthOf tab s₁ + 1) := by
  have hcol : Collected s₁ := grun_collected n s s₁ hv hc hrun
  have hle : s₁.heap.length ≤ gpeak tab n s := heap_length_le_gpeak_of_grun n s s₁ hrun
  have hsp : space s₁ ≤ gpeak tab n s := by rw [Collected] at hcol; omega
  refine le_trans (spaceConfig_space_le (widthOf tab s₁) s₁) (Nat.mul_le_mul_right _ ?_)
  omega

/-- **The `O(s · log s)` bound along a run**: if the code table, the stacks along the run and the
peak live data all fit in a budget `S`, every state of the run is written on at most
`(4 * S + 4) * (Nat.size (3 * S) + 1)` bits of the work tape. -/
theorem spaceConfig_space_le_of_run_budget {tab : Tab} {n S : ℕ} {s s₁ : HState}
    (hv : Valid tab s) (hc : Collected s) (hrun : grun tab n s = some s₁)
    (htab : tab.length ≤ S) (hstk : s₁.stack.length ≤ S) (hpeak : gpeak tab n s ≤ S) :
    (spaceConfig (widthOf tab s₁) s₁).space ≤ (4 * S + 4) * (Nat.size (3 * S) + 1) := by
  have hcol : Collected s₁ := grun_collected n s s₁ hv hc hrun
  have hle : s₁.heap.length ≤ gpeak tab n s := heap_length_le_gpeak_of_grun n s s₁ hrun
  have hsp : space s₁ ≤ S := by rw [Collected] at hcol; omega
  exact spaceConfig_space_le_of_budget htab hstk hsp

end Impl

end Krivine
