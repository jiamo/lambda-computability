# M10-LEVIN-KT

**Status:** DONE_STRONG

Levin's time-bounded complexity `Kt` and Levin's universal search, built on the step-counting
reduction that `Start/SizeExplosion.lean` introduced.

## The shared step-counting reduction — `Start/ReducesIn.lean`

`Lambda.reducesIn t u n` ("`t` reaches `u` in at most `n` β-steps") was local to
`Start/SizeExplosion.lean`.  It is now a module of its own with the API a time measure needs:
`Lambda.exists_reducesIn_of_reduces`, `reducesIn_one`, `reducesIn_trans`,
`reducesIn_app_left`, `reducesIn_app_right`, `reducesIn_app`, `reducesIn_lam`.

## `Kt` — `Start/LevinKt.lean`

* `Lambda.IsTimedProgramFor p x t` — `p` reduces to the numeral of `x` in at most `t` steps;
* `Lambda.ktSystem` — the description system whose programs are pairs `(p, t)` with size
  `size p + Nat.log 2 t`, hence
* `Lambda.kt x = min over programs of (|p| + log t)`;
* `Lambda.kt_le_of_isTimedProgramFor`, `Lambda.exists_timedProgram_of_kt` — the two directions;
* `Lambda.kolm_le_kt`, `Lambda.kt_le_kolm_add_log` — `Kt` sits above plain `K` and is bounded by
  it plus the logarithm of the running time;
* **`Lambda.kt_le_ktWith`** — the invariance theorem for `Kt`: measuring through any interpreter
  `U` costs at most an additive constant, obtained as an instance of the generic
  `Complexity.K_le_add_cost`.

## Universal search — `Start/LevinSearch.lean`

Stated for an arbitrary step-indexed `run : ℕ → ℕ → Option α` and verifier `V`:

* `Complexity.levinStage`, `Complexity.levinSearch` — the dovetailing search;
* `Complexity.levinSearch_sound` — whatever it returns is verified;
* `Complexity.levinSearch_isSome_of_run` — it does return, once some program produces a verified
  answer;
* `Complexity.searchCost_le` — the simulated cost of a stage is at most `2^(b+2)`;
* **`Complexity.levin_optimal`** — if program `p` produces a verified answer in `t` steps, the
  universal search produces a verified answer within `8 * 2^p * t` simulated steps: optimal up to
  the factor `2^p` that depends on the program but not on the input.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.ReducesIn Start.LevinKt Start.LevinSearch`
* Axioms of `Lambda.kt_le_ktWith`, `Lambda.kolm_le_kt`, `Complexity.levin_optimal`:
  `propext, Classical.choice, Quot.sound`.
