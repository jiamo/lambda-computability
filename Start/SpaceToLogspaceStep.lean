import Start.SpaceToLogspace
import Start.SpacePadded

/-!
# The compiled machine, one step at a time

This module is this library's own (task `M27-SPACE-MODEL-COMPILE`).  It computes every kind of
step of the compiled machine `Complexity.Space.ToLogspace.fcompile M k` on the encodings of host
configurations:

* `encR p c i₀ D` — the configuration in control state `p` encoding the host configuration `c`,
  with input head `0` at `i₀` and clock digits `D`; `enc p c D` puts head `0` on the cell
  `c.inHead + 1` corresponding to the host head;
* `stp_init` — initialisation lands on `enc (run 0) init 0`;
* `stp_run_acc`, `stp_run_halt`, `stp_run` — a `run` step accepts, rejects at a halting host
  configuration, or performs exactly the host's instruction;
* `stp_fix` — the repair of a left move onto the end marker;
* `stp_tick_inc`, `stp_tick_carry`, `stp_tick_over`, `stp_sweep_move`, `stp_sweep_done` — the
  clock.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace ToLogspace

open ExactDerandomization (Word InputSymbol Direction FMachine FAction FConfig readInput)

variable {M : Machine} {k : ℕ} {x : Word}

/-- The step of the compiled machine (it never consults its coin). -/
def stp (M : Machine) (k : ℕ) (x : Word) (u : FConfig (Ph M.states k) 2 (k + 1) x.length) :
    FConfig (Ph M.states k) 2 (k + 1) x.length :=
  (fcompile M k).step x false u

theorem run_eq (coins : ExactDerandomization.CoinTape) (t : ℕ) :
    (fcompile M k).run x coins t = (stp M k x)^[t] ((fcompile M k).initial x.length) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih]
      rfl

/-! ### Encodings -/

/-- The host work tape as a two-sided tape. -/
def tapeFn (l : List Bool) (z : ℤ) : Bool := if 0 ≤ z then l.getD z.toNat false else false

/-- The origin marker. -/
def originFn (z : ℤ) : Bool := decide (z = 0)

/-- The two work tapes of the compiled machine. -/
def workOf (l : List Bool) (t : Fin 2) : ℤ → Bool := if t.val = 0 then tapeFn l else originFn

/-- The cell of input head `0` encoding host position `i`. -/
def inPos (n i : ℕ) : Fin (n + 2) := ⟨min (i + 1) (n + 1), by omega⟩

variable (M k) in
/-- The configuration in state `p` encoding the host configuration `c`, input head `0` at `i₀`,
clock digits `D`. -/
def encR {n : ℕ} (p : Ph M.states k) (c : Config) (i₀ : Fin (n + 2)) (D : Fin k → Fin (n + 2)) :
    FConfig (Ph M.states k) 2 (k + 1) n where
  state := p
  inputPos := Fin.cons i₀ D
  workPos := fun _ => (c.wHead : ℤ)
  work := workOf c.tape

variable (M k) in
/-- The configuration in state `p` encoding `c` exactly. -/
def enc {n : ℕ} (p : Ph M.states k) (c : Config) (D : Fin k → Fin (n + 2)) :
    FConfig (Ph M.states k) 2 (k + 1) n :=
  encR M k p c (inPos n c.inHead) D

/-! ### Reading -/

theorem readInput_inPos {i : ℕ} (hi : i ≤ x.length) :
    hostSym (readInput x (inPos x.length i)) = x[i]? := by
  have hmin : min (i + 1) (x.length + 1) = i + 1 := by omega
  simp only [readInput, inPos, hmin, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
  cases x[i]? <;> rfl

theorem readInput_eq_left (v : Fin (x.length + 2)) :
    readInput x v = .leftMarker ↔ v.val = 0 := by
  unfold readInput
  by_cases hv : v.val = 0
  · simp [hv]
  · simp only [hv, if_false, iff_false]
    cases x[v.val - 1]? <;> simp

theorem readInput_eq_right (v : Fin (x.length + 2)) :
    readInput x v = .rightMarker ↔ v.val = x.length + 1 := by
  unfold readInput
  have hv2 := v.isLt
  by_cases hv : v.val = 0
  · simp [hv]
  · simp only [hv, if_false]
    rcases h : x[v.val - 1]? with _ | b
    · simp only [true_iff]
      rw [List.getElem?_eq_none_iff] at h
      omega
    · simp only [reduceCtorEq, false_iff]
      have := (List.getElem?_eq_some_iff.mp h).1
      omega

theorem inPos_ne_zero (n i : ℕ) : (inPos n i).val ≠ 0 := by
  simp [inPos]

theorem tapeFn_wHead (l : List Bool) (w : ℕ) : tapeFn l (w : ℤ) = l.getD w false := by
  simp [tapeFn]

theorem originFn_wHead (w : ℕ) : originFn (w : ℤ) = decide (w = 0) := by
  simp [originFn]

theorem tapeFn_writeAt (l : List Bool) (w : ℕ) (b : Bool) :
    Function.update (tapeFn l) (w : ℤ) b = tapeFn (writeAt l w b) := by
  funext z
  by_cases hz : z = (w : ℤ)
  · subst hz
    rw [Function.update_self]
    simp only [tapeFn, Nat.cast_nonneg, if_true, Int.toNat_natCast, getD_writeAt_self]
  · rw [Function.update_of_ne hz]
    unfold tapeFn
    by_cases h0 : 0 ≤ z
    · simp only [h0, if_true]
      have : z.toNat ≠ w := by omega
      rw [getD_writeAt_of_ne _ _ _ _ this]
    · simp [h0]

@[simp] theorem workOf_zero (l : List Bool) : workOf l 0 = tapeFn l := rfl
@[simp] theorem workOf_one (l : List Bool) : workOf l 1 = originFn := rfl

/-! ### The generic step -/

theorem stp_of_none {u : FConfig (Ph M.states k) 2 (k + 1) x.length}
    (h : out M k u.state = none) :
    stp M k x u =
      let a := trans M k u.state (fun j => readInput x (u.inputPos j)) (fun t => u.work t (u.workPos t))
      { state := a.nextState
        inputPos := fun j => (a.inputMove j).moveInput (u.inputPos j)
        workPos := fun t => (a.workMove t).move (u.workPos t)
        work := fun t => Function.update (u.work t) (u.workPos t) (a.write t) } := by
  simp only [stp, FMachine.step, fcompile, h]

theorem stp_idle {u : FConfig (Ph M.states k) 2 (k + 1) x.length} {p : Ph M.states k}
    (h : out M k u.state = none)
    (ht : trans M k u.state (fun j => readInput x (u.inputPos j))
      (fun t => u.work t (u.workPos t)) = idle p (fun t => u.work t (u.workPos t))) :
    stp M k x u = ⟨p, u.inputPos, u.workPos, u.work⟩ := by
  rw [stp_of_none h]
  simp only [ht, idle]
  cases u
  simp only [FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j; rfl
  · funext t; rfl
  · funext t; simp

theorem stp_moveHead {u : FConfig (Ph M.states k) 2 (k + 1) x.length} {p : Ph M.states k}
    {i : Fin (k + 1)} {d : Direction}
    (h : out M k u.state = none)
    (ht : trans M k u.state (fun j => readInput x (u.inputPos j))
      (fun t => u.work t (u.workPos t)) = moveHead p (fun t => u.work t (u.workPos t)) i d) :
    stp M k x u = ⟨p, Function.update u.inputPos i (d.moveInput (u.inputPos i)), u.workPos,
      u.work⟩ := by
  rw [stp_of_none h]
  simp only [ht, moveHead]
  cases u
  simp only [FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]; rfl
  · funext t; rfl
  · funext t; simp

theorem cons_update {n : ℕ} (i₀ : Fin (n + 2)) (D : Fin k → Fin (n + 2)) (j : Fin k)
    (v : Fin (n + 2)) :
    Function.update (Fin.cons i₀ D : Fin (k + 1) → Fin (n + 2)) j.succ v =
      Fin.cons i₀ (Function.update D j v) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (fun e => h (Fin.succ_injective _ e))]

theorem cons_update_zero {n : ℕ} (i₀ v : Fin (n + 2)) (D : Fin k → Fin (n + 2)) :
    Function.update (Fin.cons i₀ D : Fin (k + 1) → Fin (n + 2)) 0 v = Fin.cons v D := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

/-! ### The phases -/

theorem stp_init (hQ : 0 < M.states) :
    stp M k x ((fcompile M k).initial x.length) =
      enc M k (.run ⟨0, hQ⟩) init (fun _ => ⟨0, by omega⟩) := by
  rw [stp_of_none rfl]
  simp only [FMachine.initial, fcompile, trans, hQ, dif_pos, enc, encR, init, FConfig.mk.injEq,
    true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [inPos, Direction.moveInput]
    · simp [Direction.moveInput, Fin.succ_ne_zero]
  · funext t; simp [Direction.move]
  · funext t
    fin_cases t
    · funext z; simp [workOf, tapeFn, Function.update_apply]
    · funext z
      simp only [workOf, Function.update_apply]
      by_cases hz : z = 0 <;> simp [hz, originFn]

theorem stp_run_acc {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} (hacc : M.accept q = true) :
    stp M k x (encR M k (.run q) c i₀ D) = encR M k .acc c i₀ D := by
  rw [stp_idle (p := .acc) rfl (by simp only [encR, trans, hacc, if_true])]
  rfl

theorem stp_run_halt {q : Fin M.states} {c : Config} {D : Fin k → Fin (x.length + 2)}
    (hi : c.inHead ≤ x.length) (hacc : M.accept q = false)
    (hd : M.delta q x[c.inHead]? (c.tape.getD c.wHead false) = []) :
    stp M k x (enc M k (.run q) c D) = enc M k .rej c D := by
  rw [stp_idle (p := .rej) rfl]
  · rfl
  · simp only [enc, encR, trans, hacc, Bool.false_eq_true, if_false, Fin.cons_zero,
      readInput_inPos hi, workOf_zero, tapeFn_wHead, hd]

/-- The host successor of `c` under the instruction `(q', b, dI, dW)`. -/
def succCfg (n : ℕ) (c : Config) (q' : ℕ) (b : Bool) (dI dW : Dir) : Config :=
  { state := q'
    inHead := moveIn n c.inHead dI
    tape := writeAt c.tape c.wHead b
    wHead := moveWork c.wHead dW }

theorem move_dirW (w : ℕ) (d : Dir) :
    (dirW (decide (w = 0)) d).move (w : ℤ) = ((moveWork w d : ℕ) : ℤ) := by
  cases d with
  | left =>
      by_cases hw : w = 0
      · subst hw; simp [dirW, Direction.move, moveWork]
      · simp only [dirW, hw, decide_false, Bool.false_eq_true, if_false, Direction.move,
          moveWork]
        omega
  | right => simp [dirW, Direction.move, moveWork]
  | stay => simp [dirW, Direction.move, moveWork]

theorem stp_run {q : Fin M.states} {c : Config} {D : Fin k → Fin (x.length + 2)}
    (hi : c.inHead ≤ x.length) (hacc : M.accept q = false) {q' : ℕ} {b : Bool} {dI dW : Dir}
    {rest : List (ℕ × Bool × Dir × Dir)}
    (hd : M.delta q x[c.inHead]? (c.tape.getD c.wHead false) = (q', b, dI, dW) :: rest)
    (hq' : q' < M.states) :
    stp M k x (enc M k (.run q) c D) =
      encR M k (.fix ⟨q', hq'⟩) (succCfg x.length c q' b dI dW)
        ((dirIn dI).moveInput (inPos x.length c.inHead)) D := by
  rw [stp_of_none rfl]
  simp only [enc, encR, trans, hacc, Bool.false_eq_true, if_false, Fin.cons_zero,
    readInput_inPos hi, workOf_zero, workOf_one, tapeFn_wHead, hd, hq', dif_pos, succCfg,
    FConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_ne_zero, Direction.moveInput]
  · funext t
    simp only [originFn_wHead]
    exact move_dirW _ _
  · funext t
    fin_cases t
    · simp [tapeFn_writeAt]
    · simp

theorem stp_fix {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} (hk : 0 < k)
    (hi₀ : i₀ = inPos x.length c.inHead ∨ (c.inHead = 0 ∧ i₀ = ⟨0, by omega⟩)) :
    stp M k x (encR M k (.fix q) c i₀ D) = enc M k (.tick q ⟨0, hk⟩) c D := by
  rcases hi₀ with rfl | ⟨h0, rfl⟩
  · rw [stp_idle (p := .tick q ⟨0, hk⟩) rfl]
    · rfl
    · have : readInput x (inPos x.length c.inHead) ≠ .leftMarker := by
        rw [Ne, readInput_eq_left]; exact inPos_ne_zero _ _
      simp only [encR, trans, Fin.cons_zero, this, if_false, hk, dif_pos]
  · rw [stp_moveHead (p := .tick q ⟨0, hk⟩) (i := 0) (d := .right) rfl]
    · simp only [encR, enc, cons_update_zero, Fin.cons_zero]
      congr 2
      ext
      simp [Direction.moveInput, inPos, h0]
    · have : readInput x (⟨0, by omega⟩ : Fin (x.length + 2)) = .leftMarker := by
        rw [readInput_eq_left]
      simp only [encR, trans, Fin.cons_zero, this, if_true, hk, dif_pos]

theorem stp_tick_inc {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} {j : Fin k} (hj : (D j).val < x.length + 1) :
    stp M k x (encR M k (.tick q j) c i₀ D) =
      encR M k (.run q) c i₀ (Function.update D j ⟨(D j).val + 1, by omega⟩) := by
  have hr : readInput x (D j) ≠ .rightMarker := by rw [Ne, readInput_eq_right]; omega
  rw [stp_moveHead (p := .run q) (i := j.succ) (d := .right) rfl]
  · simp only [encR, cons_update, Fin.cons_succ]
    congr 3
    ext
    simp [Direction.moveInput]
    omega
  · simp only [encR, trans, Fin.cons_succ, hr, if_false]

theorem stp_tick_carry {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} {j : Fin k} (hj : (D j).val = x.length + 1)
    (hjk : j.val + 1 < k) :
    stp M k x (encR M k (.tick q j) c i₀ D) = encR M k (.sweep q j) c i₀ D := by
  have hr : readInput x (D j) = .rightMarker := by rw [readInput_eq_right]; exact hj
  rw [stp_idle (p := .sweep q j) rfl]
  · rfl
  · simp only [encR, trans, Fin.cons_succ, hr, if_true, hjk]

theorem stp_tick_over {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} {j : Fin k} (hj : (D j).val = x.length + 1)
    (hjk : ¬ j.val + 1 < k) :
    stp M k x (encR M k (.tick q j) c i₀ D) = encR M k .rej c i₀ D := by
  have hr : readInput x (D j) = .rightMarker := by rw [readInput_eq_right]; exact hj
  rw [stp_idle (p := .rej) rfl]
  · rfl
  · simp only [encR, trans, Fin.cons_succ, hr, if_true, hjk, if_false]

theorem stp_sweep_move {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} {j : Fin k} (hj : (D j).val ≠ 0) :
    stp M k x (encR M k (.sweep q j) c i₀ D) =
      encR M k (.sweep q j) c i₀ (Function.update D j ⟨(D j).val - 1, by omega⟩) := by
  have hr : readInput x (D j) ≠ .leftMarker := by rw [Ne, readInput_eq_left]; exact hj
  rw [stp_moveHead (p := .sweep q j) (i := j.succ) (d := .left) rfl]
  · simp only [encR, cons_update, Fin.cons_succ]
    rfl
  · simp only [encR, trans, Fin.cons_succ, hr, if_false]

theorem stp_sweep_done {q : Fin M.states} {c : Config} {i₀ : Fin (x.length + 2)}
    {D : Fin k → Fin (x.length + 2)} {j : Fin k} (hj : (D j).val = 0) (hjk : j.val + 1 < k) :
    stp M k x (encR M k (.sweep q j) c i₀ D) = encR M k (.tick q ⟨j.val + 1, hjk⟩) c i₀ D := by
  have hr : readInput x (D j) = .leftMarker := by rw [readInput_eq_left]; exact hj
  rw [stp_idle (p := .tick q ⟨j.val + 1, hjk⟩) rfl]
  · rfl
  · simp only [encR, trans, Fin.cons_succ, hr, if_true, hjk, dif_pos]

/-- Output states are fixed points. -/
theorem stp_out {u : FConfig (Ph M.states k) 2 (k + 1) x.length} {b : Bool}
    (h : out M k u.state = some b) : stp M k x u = u := by
  simp only [stp, FMachine.step, fcompile, h]

end ToLogspace

end Complexity.Space
