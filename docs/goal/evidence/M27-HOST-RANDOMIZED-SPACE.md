# M27-HOST-RANDOMIZED-SPACE — host randomized logarithmic space equals upstream `RL` and `BPL`

## Terminal statements

```lean
-- Start/RandUpstreamToSpaceClass.lean (does not import Start/LogspaceEquality.lean)
theorem Complexity.Space.hostRL_iff  (A : Language) : HostRL A  ↔ {x | A x} ∈ ExactDerandomization.RL
theorem Complexity.Space.hostBPL_iff (A : Language) : HostBPL A ↔ {x | A x} ∈ ExactDerandomization.BPL

-- Start/SpaceRandomizedLogspace.lean (imports Start/LogspaceTransferEquiv.lean)
theorem Complexity.Space.hostBPL_iff_logspace (A : Language) : HostBPL A ↔ LOGSPACE A
theorem Complexity.Space.hostRL_iff_logspace  (A : Language) : HostRL A  ↔ LOGSPACE A
```

`#print axioms` (all four, and the two probability equations below): each of `Complexity.Space.hostRL_iff`, `Complexity.Space.hostBPL_iff`, `Complexity.Space.hostRL_iff_logspace`, `Complexity.Space.hostBPL_iff_logspace`, `Complexity.Space.RandFromLogspace.rcompile_acceptWithin` depends on axioms: `[propext, Classical.choice, Quot.sound]` (run with `lake env lean` on a scratch file importing `Start.SpaceRandomizedLogspace`). `RandToLogspace.rcompile_acceptanceProbability` is used by `hostRL_iff`/`hostBPL_iff`, so it is covered by the same output.

Import check (no transitive import of `Start/LogspaceEquality.lean` by the modules proving
`hostRL_iff` and `hostBPL_iff`): a recursive walk of the `import` lines starting from `Start.RandUpstreamToSpaceClass` (which proves `hostRL_iff` and `hostBPL_iff`) never reaches `Start.LogspaceEquality` (result: `False`); the same holds for `Start.SpaceRandomized`. Only `Start.SpaceRandomizedLogspace` (the `LOGSPACE` corollaries) imports it, as allowed.

## The definitions, side by side (verbatim)

### Host (`Start/SpaceRandomized.lean`)

```lean
def FairCoin (M : Machine) : Prop := ∀ q a b, (M.delta q a b).length ≤ 2

def acceptWithin (M : Machine) (x : List Bool) : ℕ → Config → ℚ
  | 0, c => if M.accept c.state then 1 else 0
  | t + 1, c =>
      if M.accept c.state then 1 else
      match M.stepList x c with
      | [] => 0
      | [c'] => M.acceptWithin x t c'
      | c₁ :: c₂ :: _ => (M.acceptWithin x t c₁ + M.acceptWithin x t c₂) / 2

def RunsWithin (M : Machine) (x : List Bool) (T : ℕ) : Prop :=
  ∀ c, ¬ Reach.steps (M.Step x) (T + 1) init c

def HostBPL (A : Language) : Prop :=
  ∃ (M : Machine) (a : ℕ) (T : ℕ → ℕ),
    M.WellFormed ∧ M.FairCoin ∧ PolyBound T ∧
    M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1)) ∧
    ∀ x, M.RunsWithin x (T x.length) ∧
      (A x → (2 / 3 : ℚ) ≤ M.acceptWithin x (T x.length) init) ∧
      (¬ A x → M.acceptWithin x (T x.length) init ≤ 1 / 3)

def HostRL (A : Language) : Prop :=
  ∃ (M : Machine) (a : ℕ) (T : ℕ → ℕ),
    M.WellFormed ∧ M.FairCoin ∧ PolyBound T ∧
    M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1)) ∧
    ∀ x, M.RunsWithin x (T x.length) ∧
      (A x → (1 / 2 : ℚ) ≤ M.acceptWithin x (T x.length) init) ∧
      (¬ A x → M.acceptWithin x (T x.length) init = 0)
```

### Host machine (`Start/SpaceMachine.lean`, unchanged)

```lean
structure Config where
  /-- The control state. -/
  state : ℕ
  /-- The position of the read-only input head. -/
  inHead : ℕ
  /-- The used part of the work tape. -/
  tape : List Bool
  /-- The position of the work head. -/
  wHead : ℕ
  deriving DecidableEq, Repr, Inhabited

def Config.space (c : Config) : ℕ := max c.tape.length (c.wHead + 1)

def moveWork (i : ℕ) : Dir → ℕ
  | .left => i - 1
  | .right => i + 1
  | .stay => i

def moveIn (n i : ℕ) : Dir → ℕ
  | .left => i - 1
  | .right => min (i + 1) n
  | .stay => i

structure Machine where
  /-- The number of control states. -/
  states : ℕ
  /-- The accepting states. -/
  accept : ℕ → Bool
  /-- The transition function; the empty list means halting. -/
  delta : ℕ → Option Bool → Bool → List (ℕ × Bool × Dir × Dir)

def WellFormed : Prop :=
  0 < M.states ∧ ∀ q a b, ∀ t ∈ M.delta q a b, t.1 < M.states

def stepList (x : List Bool) (c : Config) : List Config :=
  (M.delta c.state x[c.inHead]? (c.tape.getD c.wHead false)).map fun t =>
    { state := t.1
      inHead := moveIn x.length c.inHead t.2.2.1
      tape := writeAt c.tape c.wHead t.2.1
      wHead := moveWork c.wHead t.2.2.2 }

def Step (x : List Bool) (c c' : Config) : Prop := c' ∈ M.stepList x c

def init : Config := ⟨0, 0, [], 0⟩

def SpaceBounded (s : ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (n : ℕ) (c : Config),
    Reach.steps (M.Step x) n init c → c.space ≤ s x.length

def LOGSPACE (L : Language) : Prop := ∃ a : ℕ, DSPACE (fun n => a * (Nat.log 2 (n + 1) + 1)) L
```

### Shared (`Start/SavitchReach.lean`, `Start/ComplexityClasses.lean`)

```lean
def steps (r : C → C → Prop) : ℕ → C → C → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ m, steps r n a m ∧ r m b

def PolyBound (p : ℕ → ℕ) : Prop := ∃ a k : ℕ, ∀ n, p n ≤ a * (n + 1) ^ k
```

### Upstream (`Start/LogspaceDeterministic.lean`, absorbed from openai/math)

```lean
def Direction.moveInput (d : Direction) {n : ℕ} (i : Fin (n + 2)) : Fin (n + 2) :=
  match d with
  | .left => ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  | .stay => i
  | .right => ⟨min (i.val + 1) (n + 1), by omega⟩

def readInput (x : Word) (i : Fin (x.length + 2)) : InputSymbol :=
  if i.val = 0 then .leftMarker else
    match x[i.val - 1]? with
    | some b => .bit b
    | none => .rightMarker

structure Action (q w h : ℕ) where
  nextState : Fin (q + 1)
  write : Fin w → Bool
  workMove : Fin w → Direction
  inputMove : Fin h → Direction

structure Machine (q w h : ℕ) where
  initialState : Fin (q + 1)
  output : Fin (q + 1) → Option Bool
  transition : Fin (q + 1) → (Fin h → InputSymbol) → (Fin w → Bool) → Bool →
    Action q w h

structure Configuration (q w h n : ℕ) where
  state : Fin (q + 1)
  inputPos : Fin h → Fin (n + 2)
  workPos : Fin w → ℤ
  work : Fin w → ℤ → Bool

def initial (M : Machine q w h) (n : ℕ) : Configuration q w h n where
  state := M.initialState
  inputPos := fun _ => ⟨0, by omega⟩
  workPos := fun _ => 0
  work := fun _ _ => false

def step (M : Machine q w h) (x : Word) (b : Bool)
    (c : Configuration q w h x.length) : Configuration q w h x.length :=
  match M.output c.state with
  | some _ => c
  | none =>
    let a := M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b
    { state := a.nextState
      inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
      workPos := fun k => (a.workMove k).move (c.workPos k)
      work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

def run (M : Machine q w h) (x : Word) (coins : CoinTape) :
    ℕ → Configuration q w h x.length
  | 0 => M.initial x.length
  | t + 1 => M.step x (coins t) (M.run x coins t)

def spaceThrough (M : Machine q w h) (x : Word) (coins : CoinTape) (t : ℕ) : ℕ :=
  ∑ k : Fin w, ((Finset.range (t + 1)).image
    (fun s => (M.run x coins s).workPos k)).card

def LogSpace (M : Machine q w h) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ (x : Word) (coins : CoinTape) (t : ℕ),
    M.spaceThrough x coins t ≤ c * Nat.clog 2 (x.length + 2)

def HaltsBy (M : Machine q w h) (x : Word) (t : ℕ) : Prop :=
  ∀ coins : CoinTape, ∃ b : Bool, M.output (M.run x coins t).state = some b

def extendCoins {t : ℕ} (bits : Fin t → Bool) : CoinTape :=
  fun s => if hs : s < t then bits ⟨s, hs⟩ else false

def acceptanceProbability (M : Machine q w h) (x : Word) (t : ℕ) : ℚ :=
  ((Finset.univ.filter (fun bits : Fin t → Bool =>
    M.output (M.run x (extendCoins bits) t).state = some true)).card : ℚ) /
    (2 : ℚ) ^ t

def polynomialClock (c k n : ℕ) : ℕ := c * (n + 2) ^ k

def RL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (1 / 2 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) = 0)}

def BPL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (2 / 3 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) ≤ (1 / 3 : ℚ))}
```


## The two simulations and their constants

### Host to upstream (`Start/RandSpaceToUpstream.lean`, `…Sim.lean`, `…Space.lean`)

`RandToLogspace.rcompile M` has two work tapes (the host tape cell for cell, and an origin marker
used to clamp host left moves at cell `0`), one input head (the host head shifted by one cell for
the left end marker), and states `init`, `run q`, `fix q`, `acc`, `rej`.  One host step is exactly
two upstream steps (`run`, then `fix`, which undoes a left move onto the end marker).  The `run`
step reads the coin: with one host instruction the coin is ignored; with two, `false` takes the
first and `true` the second.  Every other step ignores the coin.  There is no clock.

```lean
theorem RandToLogspace.rcompile_acceptanceProbability (hwf : M.WellFormed) (hfc : M.FairCoin)
    {T : ℕ} (hT : M.RunsWithin x T) (t : ℕ) (ht : 2 * T + 2 ≤ t) :
    (rcompile M).acceptanceProbability x t = M.acceptWithin x T init
theorem RandToLogspace.rcompile_haltsBy … : (rcompile M).HaltsBy x t      -- same hypotheses
theorem RandToLogspace.rcompile_logSpace (hwf : M.WellFormed) {a : ℕ}
    (hsp : M.SpaceBounded (fun n => a * (Nat.log 2 (n + 1) + 1))) :
    ∀ x coins t, (rcompile M).spaceThrough x coins t ≤ (2 * a + 1) * Nat.clog 2 (x.length + 2)
```

Constants: upstream time `t' = polynomialClock (2 b + 2) k n = (2 b + 2) (n + 2)^k` for a host
time bound `T n ≤ b (n + 1)^k` (this is `≥ 2 T n + 2`, `RandToLogspace.clock_ge`); upstream
`LogSpace` constant `2 a + 1` for host space `a (log₂ (n + 1) + 1)`.

Proof: `ExactDerandomization.Machine.acceptanceProbability_eq_probFrom`
(`Start/RandSpaceUpstreamProb.lean`) rewrites the counting definition as the recursion
`probFrom (t+1) c = (probFrom t (step false c) + probFrom t (step true c)) / 2`; `RandToLogspace.sim`
proves by induction on `T` that from the encoding of a host configuration all of whose runs have at
most `T` steps, `probFrom t = acceptWithin T` for every `t ≥ 2 T + 1`, case by case on the host
step (accepting: `acc`; no instruction: `rej`; one instruction: the coin is irrelevant; two
instructions: one coin, `FairCoin` excluding a third).

### Upstream to host (`Start/RandUpstreamToSpace.lean`, `…Seg.lean`, `…Sim.lean`, `…Class.lean`)

`RandFromLogspace.rcompile M c₀` reuses the register-file encoding and the transition program
`FromLogspace.stepProg` of the deterministic compiler (`Start/LogspaceToSpace*.lean`, unchanged):

```
initProg M c₀; mvR 3;
while (result register empty) {
  mvL 2; if (running flag) {
    mvR 2; flip; if (coin) { write false; mvL 3; stepProg (fixCoin M true);  mvR 3 }
                 else      { write false; mvL 3; stepProg (fixCoin M false); mvR 3 } }
  else halt }
```

`flip` is the only host state with two instructions (write `false` / write `true` on the presence
cell of the empty result register); `halt` is a halting non-accepting state, reached exactly when
the simulated machine has output `false` (so the host halts instead of looping); the accepting
state is the loop exit, reached exactly when the simulated machine has output `true`.  One fair
branching per simulated upstream step, on that step's coin.

```lean
theorem RandFromLogspace.rcompile_acceptWithin {x : Word}
    (hLS : ∀ coins t, M.spaceThrough x coins t ≤ c₀ * Nat.clog 2 (x.length + 2))
    {t₀ : ℕ} (hhalt : M.HaltsBy x t₀) :
    (rcompile M c₀).acceptWithin x (timeB M c₀ x.length) init = M.acceptanceProbability x t₀ ∧
      (rcompile M c₀).RunsWithin x (timeB M c₀ x.length) ∧
      (rcompile M c₀).SpaceBoundedOn x (spaceA q w h c₀ * (Nat.log 2 (x.length + 1) + 1))
```

Constants: host space constant `spaceA q w h c₀ = (2 c₀ + q + 7) (2 (7 + h + 2 w) + 1)` (the
constant of the deterministic compiler, `FromLogspace.spaceB_le_log`); host time
`timeB M c₀ n = (n + 2) ^ clockLen Q (spaceA q w h c₀)` with `Q = (rcompile M c₀).states` and
`clockLen Q a = Q (a + 1)² 2^a + a + 3`; `timeB n ≤ 2^K (n + 1)^K` with `K` that exponent
(`timeB_polyBound`).

Proof: `RandFromLogspace.iter_claim`, by induction on the number `r` of upstream steps within which
every coin sequence gives an output: from the loop head on `encTS M c₀ x c`, every host run ends,
every reachable host configuration fits in `spaceB` cells, and the host value after the runs end is
`M.probFrom x r c`.  Between branchings the host is deterministic; the segments are compiled
program executions (`Prog.path_of_exec`), transported by `Machine.path_transport`
(`Start/SpaceRandomizedRuns.lean`).  This gives termination with some unknown bound; then
`Machine.runsWithin_cfgBound` (pumping: a run longer than the number of configurations within the
space bound repeats one, which would give runs of every length) bounds every run by
`cfgBound ≤ timeB` (`ToLogspace.cfgBound_le_clock`), and `Machine.acceptWithin_stable` moves the
value to the clock `timeB`.

## Modelling differences (all absorbed by the two simulations)

* **Coin per step versus coin per branching.**  Upstream consumes one coin at every step
  (`run x coins (t+1) = step x (coins t) (run x coins t)`), and `acceptanceProbability x t` counts
  coin strings of length exactly `t`.  The host draws a coin only where two instructions are
  offered (`acceptWithin` halves only at `c₁ :: c₂ :: _`).  Host to upstream: coins at steps that
  do not resolve a branching are read and ignored, so both coin values give the same successor and
  contribute equally.  Upstream to host: the host branches once per simulated upstream step, even
  when the upstream transition ignores its coin (then both branches compute the same step).
* **Several input heads and work tapes versus one of each.**  Upstream: `h` input heads, `w`
  two-sided work tapes.  Host: one input head, one one-sided work tape.  Host to upstream uses
  `w = 2`, `h = 1` (tape 1 is an origin marker).  Upstream to host stores the `h` head positions
  and the `w` windowed tapes in a register file on the single host tape (the deterministic
  compiler's encoding).
* **End markers.**  Upstream input is framed by a left and a right end marker
  (`readInput`, positions `0 … n + 1`); the host input head ranges over `0 … n` with position `n`
  the end marker and no left marker.  Host to upstream shifts the head by one and repairs a left
  move onto the left marker (`fix`); upstream to host reads input symbols through counters
  (position `0` is recognized by an empty counter).
* **Accepting by reaching a state versus halting with an output.**  Host: acceptance probability is
  the probability of *reaching* an accepting state within the clock (the machine may continue
  after it); every run must end within `T` (`RunsWithin`), also on rejection.  Upstream: output
  states are absorbing, `acceptanceProbability x t` is the fraction of coin strings with output
  `true` at time `t`, and `HaltsBy x t` requires an output after `t` steps on every coin string.
  Host to upstream: an accepting host state leads to `acc`, a halting non-accepting configuration
  to `rej`.  Upstream to host: output `true` leads to the accepting final state, output `false` to
  the halting non-accepting state `halt`.
* **How time and space are counted.**  Host time: every run (every branch) has at most `T |x|`
  steps, `T` polynomially bounded (`PolyBound`, `T n ≤ b (n + 1)^k`).  Upstream time: the clock
  is `polynomialClock c k n = c (n + 2)^k`, and `HaltsBy` asks for an output at that time on every
  coin string.  Host space: the number of used cells `max tape.length (wHead + 1)` on every
  configuration reachable on some run, bounded by `a (log₂ (n + 1) + 1)`.  Upstream space:
  `spaceThrough x coins t` = sum over the work tapes of the number of distinct head positions up
  to time `t`, bounded by `c ⌈log₂ (n + 2)⌉` with `0 < c`, for every coin sequence and every `t`.
  The conversions are `log₂ (n + 1) + 1 ≤ ⌈log₂ (n + 2)⌉` (`ToLogspace.log_succ_le_clog`) and
  `FromLogspace.spaceB_le_log`.

## The probability equations (exact, as rationals)

* host to upstream: `(RandToLogspace.rcompile M).acceptanceProbability x t = M.acceptWithin x T init`
  for every `t ≥ 2 T + 2`, whenever every host run on `x` has at most `T` steps; in the class proof
  `T = T_host |x|` and `t = (2 b + 2) (|x| + 2)^k`.
* upstream to host: `(RandFromLogspace.rcompile M c₀).acceptWithin x (timeB M c₀ |x|) init =
  M.acceptanceProbability x t₀` whenever `M` has an output after `t₀` steps on every coin string
  on `x` and uses at most `c₀ ⌈log₂ (|x| + 2)⌉` cells; in the class proof `t₀ = c (|x| + 2)^k` is
  the upstream clock.
