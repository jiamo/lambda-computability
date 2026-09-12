# M13-SAVITCH-VM — a machine that executes the midpoint recursion in bounded memory

The midpoint identity (`M13-SAVITCH-REACH`) turns the search for a walk into a recursion.
Savitch's theorem is the claim that the recursion can be *executed* in small memory, which is a
claim about an implementation; `Start/SavitchVM.lean` gives one and proves it.

## The machine

* `Complexity.Savitch.Frame` — an activation record: the two endpoints of a subproblem, its depth,
  the **index** of the midpoint currently being tried, and one bit saying which leg is running.
  The index is an index into an enumeration of the vertices, which the machine never stores; this
  is the difference between a record of `O(w)` bits and a record holding the whole vertex set.
* `Complexity.Savitch.VM`, `Complexity.Savitch.step` — the states and the deterministic one-step
  function: a call at depth `0` answers immediately, a call at depth `k+1` pushes a record and
  recurses on the first leg, and a return either runs the second leg, or answers, or moves on to
  the next midpoint.
* `Complexity.Savitch.Trace r cs B s t` — the machine runs from `s` to `t` and *every state it
  passes through* carries at most `B` records.  Building the bound into the reachability relation
  is what lets correctness and the memory bound be proved by one induction.

## What is proved

* `Complexity.Savitch.trace_enter` — the loop over the midpoints, by induction on the number of
  midpoints left.
* `Complexity.Savitch.trace_call` — the machine started on a subproblem of depth `k` returns
  `Complexity.Savitch.reachL` of that subproblem, with at most `k` records alive.
* `Complexity.Savitch.reachL_eq_reachB` — with an exhaustive enumeration of the vertices the value
  it computes is the recursion of `Start/SavitchReach.lean`, hence reachability.
* `Complexity.Savitch.memBits`, `.memBits_le_of_trace`, `.memBits_le_of_visited` — the memory of a
  state in bits, and the bound `(B + 1) · (2 w + 2 d + 1)` for every state of a run.

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
