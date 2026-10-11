import Start.SpaceRandomized
import Start.RandSpaceUpstreamProb
import Start.SpaceToLogspaceTransfer

/-!
# Host fair-coin machines into upstream probabilistic machines

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`, direction host to upstream).  A
well-formed fair-coin host machine `M` (`Start/SpaceRandomized.lean`) is compiled into an
`ExactDerandomization.Machine` (`Start/LogspaceDeterministic.lean`) `RandToLogspace.rcompile M`
with two work tapes and one input head:

* work tape `0` is the host work tape, cell for cell; work tape `1` is an origin marker, used to
  clamp the host's left moves at cell `0` (as in `Start/SpaceToLogspace.lean`);
* input head `0` is the host input head, shifted by one cell for the left end marker;
* the control states are `init`, `run q`, `fix q` for every host state `q`, and the two output
  states `acc`, `rej`.

One host step is exactly two target steps, `run → fix`.  The `run` step **reads the coin** and,
when the host offers two instructions, takes the first on `false` and the second on `true`; at
every other step the coin is ignored.  An accepting host state leads to `acc`; a halting
non-accepting host configuration leads to `rej`.  There is no clock: the host's own time bound
makes every run of the compiled machine halt.

Main results, for a host machine that is well formed and fair-coin:

* `rcompile_acceptanceProbability` — if every host run on `x` has at most `T` steps, then for
  every `t ≥ 2 T + 2`,
  `(rcompile M).acceptanceProbability x t = M.acceptWithin x T init` (an equation of rationals);
* `rcompile_haltsBy` — under the same hypothesis, the compiled machine has an output after `t`
  steps on every coin sequence;
* `rcompile_logSpace` — if `M` uses at most `s |x|` cells, every run of the compiled machine has
  `spaceThrough ≤ 2 s |x|`; for `s n = a (log₂ (n+1) + 1)` this is the upstream `LogSpace` bound
  with constant `2 a + 1`.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace RandToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput CoinTape)
open ToLogspace (hostSym dirIn dirW tapeFn originFn workOf inPos succCfg readInput_inPos
  readInput_eq_left inPos_ne_zero tapeFn_wHead originFn_wHead tapeFn_writeAt move_dirW
  moveInput_inPos workOf_zero workOf_one)

/-- Control states of the compiled machine, for `Q` host states. -/
inductive RPh (Q : ℕ) where
  | init
  | run (q : Fin Q)
  | fix (q : Fin Q)
  | acc
  | rej
  deriving DecidableEq, Fintype

instance (Q : ℕ) : Inhabited (RPh Q) := ⟨.init⟩

/-- The instruction selected by the coin `b`: the only one if there is one, the first on `false`
and the second on `true` if there are two or more. -/
def choose {α : Type} (b : Bool) : List α → Option α
  | [] => none
  | [i] => some i
  | i₁ :: i₂ :: _ => some (if b then i₂ else i₁)

theorem choose_mem {α : Type} {b : Bool} {l : List α} {i : α} (h : choose b l = some i) :
    i ∈ l := by
  match l, h with
  | [i'], h => simp only [choose, Option.some.injEq] at h; subst h; simp
  | i₁ :: i₂ :: _, h =>
      simp only [choose, Option.some.injEq] at h
      subst h
      cases b <;> simp

theorem choose_eq_none {α : Type} {b : Bool} {l : List α} : choose b l = none ↔ l = [] := by
  match l with
  | [] => simp [choose]
  | [_] => simp [choose]
  | _ :: _ :: _ => simp [choose]

/-- The action that changes nothing but the control state. -/
def ridle {Q : ℕ} (p : RPh Q) (wk : Fin 2 → Bool) : FAction (RPh Q) 2 1 where
  nextState := p
  write := wk
  workMove := fun _ => .stay
  inputMove := fun _ => .stay

variable (M : Machine)

/-- The transition table of the compiled machine; only `run` consults the coin. -/
def rtrans : RPh M.states → (Fin 1 → InputSymbol) → (Fin 2 → Bool) → Bool →
    FAction (RPh M.states) 2 1
  | .init, _, wk, _ =>
      { nextState := if h : 0 < M.states then .run ⟨0, h⟩ else .rej
        write := ![wk 0, true]
        workMove := fun _ => .stay
        inputMove := fun _ => .right }
  | .run q, inp, wk, b =>
      if M.accept q then ridle .acc wk else
      match choose b (M.delta q (hostSym (inp 0)) (wk 0)) with
      | none => ridle .rej wk
      | some (q', bw, dI, dW) =>
          { nextState := if h : q' < M.states then .fix ⟨q', h⟩ else .rej
            write := ![bw, wk 1]
            workMove := fun _ => dirW (wk 1) dW
            inputMove := fun _ => dirIn dI }
  | .fix q, inp, wk, _ =>
      if inp 0 = .leftMarker then
        { nextState := .run q
          write := wk
          workMove := fun _ => .stay
          inputMove := fun _ => .right }
      else ridle (.run q) wk
  | .acc, _, wk, _ => ridle .acc wk
  | .rej, _, wk, _ => ridle .rej wk

/-- Output states. -/
def rout {Q : ℕ} : RPh Q → Option Bool
  | .acc => some true
  | .rej => some false
  | _ => none

/-- **The compiled machine**, with control states `RPh M.states`. -/
def rfcompile : FMachine (RPh M.states) 2 1 where
  initialState := .init
  output := rout
  transition := rtrans M

/-- **The compiled machine**, numbered as an `ExactDerandomization.Machine`. -/
noncomputable def rcompile :
    ExactDerandomization.Machine (Fintype.card (RPh M.states) - 1) 2 1 :=
  (rfcompile M).toMachine

/-! ### Encodings and single steps -/

variable {M} {x : Word}

/-- The configuration in state `p` encoding the host configuration `c`, input head at `i₀`. -/
def encR {n : ℕ} (p : RPh M.states) (c : Config) (i₀ : Fin (n + 2)) :
    FConfig (RPh M.states) 2 1 n where
  state := p
  inputPos := fun _ => i₀
  workPos := fun _ => (c.wHead : ℤ)
  work := workOf c.tape

/-- The configuration in state `p` encoding `c` exactly. -/
def enc {n : ℕ} (p : RPh M.states) (c : Config) : FConfig (RPh M.states) 2 1 n :=
  encR p c (inPos n c.inHead)

/-- Shorthand for the step of the compiled machine. -/
abbrev rstep (M : Machine) (x : Word) (b : Bool) (u : FConfig (RPh M.states) 2 1 x.length) :
    FConfig (RPh M.states) 2 1 x.length :=
  (rfcompile M).step x b u

theorem rstep_out {u : FConfig (RPh M.states) 2 1 x.length} {v : Bool}
    (h : rout u.state = some v) (b : Bool) : rstep M x b u = u := by
  simp only [rstep, FMachine.step, rfcompile, h]

theorem rstep_idle {u : FConfig (RPh M.states) 2 1 x.length} {p : RPh M.states} {b : Bool}
    (h : rout u.state = none)
    (ht : rtrans M u.state (fun j => readInput x (u.inputPos j))
      (fun t => u.work t (u.workPos t)) b = ridle p (fun t => u.work t (u.workPos t))) :
    rstep M x b u = ⟨p, u.inputPos, u.workPos, u.work⟩ := by
  simp only [rstep, FMachine.step, rfcompile, h, ht, ridle]
  cases u
  simp only [FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j; rfl
  · funext t; rfl
  · funext t; simp

theorem rstep_init (hQ : 0 < M.states) (b : Bool) :
    rstep M x b ((rfcompile M).initial x.length) = enc (.run ⟨0, hQ⟩) init := by
  simp only [rstep, FMachine.step, FMachine.initial, rfcompile, rout, rtrans, hQ, dif_pos, enc,
    encR, init, FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j; simp [inPos, Direction.moveInput]
  · funext t; simp [Direction.move]
  · funext t
    fin_cases t
    · funext z; simp [workOf, tapeFn, Function.update_apply]
    · funext z
      simp only [workOf, Function.update_apply]
      by_cases hz : z = 0 <;> simp [hz, originFn]

theorem rstep_run_acc {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    (hacc : M.accept q = true) (b : Bool) :
    rstep M x b (encR (.run q) c i₀) = encR .acc c i₀ := by
  rw [rstep_idle (p := .acc) rfl (by simp only [encR, rtrans, hacc, if_true])]
  rfl

theorem rstep_run_halt {q : Fin M.states} {c : Config} {b : Bool}
    (hi : c.inHead ≤ x.length) (hacc : M.accept q = false)
    (hd : M.delta q x[c.inHead]? (c.tape.getD c.wHead false) = []) :
    rstep M x b (enc (.run q) c) = enc .rej c := by
  rw [rstep_idle (p := .rej) rfl]
  · rfl
  · simp only [enc, encR, rtrans, hacc, Bool.false_eq_true, if_false, readInput_inPos hi,
      workOf_zero, tapeFn_wHead, hd, choose]

theorem rstep_run {q : Fin M.states} {c : Config} {b : Bool}
    (hi : c.inHead ≤ x.length) (hacc : M.accept q = false) {q' : ℕ} {bw : Bool} {dI dW : Dir}
    (hd : choose b (M.delta q x[c.inHead]? (c.tape.getD c.wHead false)) = some (q', bw, dI, dW))
    (hq' : q' < M.states) :
    rstep M x b (enc (.run q) c) =
      encR (.fix ⟨q', hq'⟩) (succCfg x.length c q' bw dI dW)
        ((dirIn dI).moveInput (inPos x.length c.inHead)) := by
  simp only [rstep, FMachine.step, rfcompile, enc, encR, rout, rtrans, hacc, Bool.false_eq_true,
    if_false, readInput_inPos hi, workOf_zero, workOf_one, tapeFn_wHead, hd, hq', dif_pos,
    succCfg, FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · funext t
    simp only [originFn_wHead]
    exact move_dirW _ _
  · funext t
    fin_cases t
    · simp [tapeFn_writeAt]
    · simp

theorem rstep_fix {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)} (b : Bool)
    (hi₀ : i₀ = inPos x.length c.inHead ∨ (c.inHead = 0 ∧ i₀ = ⟨0, by omega⟩)) :
    rstep M x b (encR (.fix q) c i₀) = enc (.run q) c := by
  rcases hi₀ with rfl | ⟨h0, rfl⟩
  · rw [rstep_idle (p := .run q) rfl]
    · rfl
    · have : readInput x (inPos x.length c.inHead) ≠ .leftMarker := by
        rw [Ne, readInput_eq_left]; exact inPos_ne_zero _ _
      simp only [encR, rtrans, this, if_false]
  · have : readInput x (⟨0, by omega⟩ : Fin (x.length + 2)) = .leftMarker := by
      rw [readInput_eq_left]
    simp only [rstep, FMachine.step, rfcompile, encR, rout, rtrans, this, if_true, enc,
      FConfig.mk.injEq, true_and]
    refine ⟨?_, ?_, ?_⟩
    · funext j; ext; simp [Direction.moveInput, inPos, h0]
    · funext t; simp [Direction.move]
    · funext t; simp

end RandToLogspace

end Complexity.Space
