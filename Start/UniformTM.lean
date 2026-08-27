/-
# Turing machines run in polynomial time, through the tableau

`Start/UniformCACode.lean` compiles a cellular automaton over a fixed finite alphabet into a
P-uniform family of circuits.  This module compiles the standard sequential device into such an
automaton: a one-tape deterministic **Turing machine** with a fixed finite set of states, working
on a tape of `W` cells.  The alphabet of the automaton is `{blank bit} ∪ {bit with the head in a
state} ∪ {accept}`, so it is finite as soon as the machine is; the local rule moves the head, and
an accepting configuration turns into the accept symbol, which then travels leftwards, one cell
per step, until it reaches the first cell of the tape, where the tableau reads the verdict off.

The machine dies when its head walks off either end of the tape, and it freezes as soon as it
reaches an accepting state.  It is counted as accepting within `H` steps when the accept signal
reaches the first cell by the deadline `H`; `Complexity.tmAccBy_of_acc_le` and
`Complexity.acc_lt_of_tmAccBy` sandwich that notion between "accepts within `(H - 1) / 2` steps"
and "accepts within `H` steps", so for a machine whose verdict is settled well before the
deadline it is the usual notion.

Main definitions:

* `Complexity.TuringMachine` — a one-tape deterministic machine with finitely many states;
* `Complexity.tmConf` — the configuration after `t` steps on a tape of `W` cells;
* `Complexity.tmCA` — **the cellular automaton simulating the machine**;
* `Complexity.TMLang` — the language of the machine.

Main results:

* `Complexity.caCell_tmCA_eq` — **the automaton simulates the machine** on every cell that the
  accept signal has not yet reached;
* `Complexity.caCell_tmCA_zero_iff` — the first cell carries the accept symbol exactly when the
  machine accepts in time;
* `Complexity.pUniformDecidable_tmLang` — **the language of a Turing machine whose tape and
  running time are Cobham-computable is decided by a P-uniform circuit family**;
* `Complexity.polyManyOne_SAT_tmLang` — and therefore reduces to SAT in polynomial time.
-/
import Start.UniformCACode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- **A one-tape deterministic Turing machine** over the alphabet `Bool`, with `Q` states.  From
the current state and the bit read it computes the next state, the bit written and the direction
of the move, `true` meaning to the right. -/
structure TuringMachine where
  /-- The number of states. -/
  Q : ℕ
  /-- The next state. -/
  st : ℕ → Bool → ℕ
  /-- The bit written. -/
  wr : ℕ → Bool → Bool
  /-- The direction of the move, `true` to the right. -/
  mv : ℕ → Bool → Bool
  /-- The accepting states. -/
  acc : ℕ → Bool
  /-- There is at least one state, the initial one. -/
  Qpos : 0 < Q
  /-- The next state is a state. -/
  st_lt : ∀ s b, st s b < Q

/-! ### The alphabet of the simulating automaton -/

/-- The symbol of a cell holding the bit `b` and no head. -/
def tmN (b : Bool) : ℕ := 1 + (if b then 1 else 0)

/-- The symbol of a cell holding the bit `b` and the head in the state `s`. -/
def tmH (s : ℕ) (b : Bool) : ℕ := 3 + 2 * s + (if b then 1 else 0)

/-- The bit carried by a symbol. -/
def tmBit (x : ℕ) : Bool := decide ((x - 1) % 2 = 1)

/-- The state carried by a symbol holding the head. -/
def tmStOf (x : ℕ) : ℕ := (x - 3) / 2

@[simp] theorem tmBit_tmN (b : Bool) : tmBit (tmN b) = b := by
  cases b <;> simp [tmBit, tmN]

@[simp] theorem tmBit_tmH (s : ℕ) (b : Bool) : tmBit (tmH s b) = b := by
  cases b <;> simp [tmBit, tmH]

@[simp] theorem tmStOf_tmH (s : ℕ) (b : Bool) : tmStOf (tmH s b) = s := by
  cases b
  · simp [tmStOf, tmH]
  · simp [tmStOf, tmH]
    omega

@[simp] theorem tmN_ne_zero (b : Bool) : tmN b ≠ 0 := by cases b <;> simp [tmN]

@[simp] theorem tmH_ne_zero (s : ℕ) (b : Bool) : tmH s b ≠ 0 := by cases b <;> simp [tmH]

@[simp] theorem not_head_tmN (b : Bool) : ¬ 3 ≤ tmN b := by cases b <;> simp [tmN]

@[simp] theorem head_tmH (s : ℕ) (b : Bool) : 3 ≤ tmH s b := by
  cases b
  · simp [tmH]
  · simp [tmH]
    omega

theorem tmN_lt (M : TuringMachine) (b : Bool) : tmN b < 3 + 2 * M.Q := by
  cases b <;> simp [tmN] <;> omega

theorem tmH_lt (M : TuringMachine) {s : ℕ} (hs : s < M.Q) (b : Bool) :
    tmH s b < 3 + 2 * M.Q := by
  cases b <;> simp [tmH] <;> omega

/-! ### The local rule -/

/-- The bit a cell writes at the next step: the head, if there is one, writes the bit the machine
asks for, and otherwise the bit is unchanged. -/
def tmWrite (M : TuringMachine) (b : ℕ) : Bool :=
  if 3 ≤ b then M.wr (tmStOf b) (tmBit b) else tmBit b

/-- The local rule of the simulating automaton: the accept symbol travels leftwards, an accepting
configuration turns into the accept symbol, and otherwise the cell writes the bit its own head
asks for and receives the head of whichever neighbour is moving onto it. -/
def tmStp (M : TuringMachine) (a b c : ℕ) : ℕ :=
  if b = 0 ∨ c = 0 then 0
  else if 3 ≤ b ∧ M.acc (tmStOf b) = true then 0
  else if 3 ≤ a ∧ M.acc (tmStOf a) = false ∧ M.mv (tmStOf a) (tmBit a) = true then
    tmH (M.st (tmStOf a) (tmBit a)) (tmWrite M b)
  else if 3 ≤ c ∧ M.acc (tmStOf c) = false ∧ M.mv (tmStOf c) (tmBit c) = false then
    tmH (M.st (tmStOf c) (tmBit c)) (tmWrite M b)
  else tmN (tmWrite M b)

theorem tmStp_lt (M : TuringMachine) (a b c : ℕ) : tmStp M a b c < 3 + 2 * M.Q := by
  have hQ := M.Qpos
  rw [tmStp]
  split_ifs <;>
    first
      | omega
      | exact tmH_lt M (M.st_lt _ _) _
      | exact tmN_lt M _

theorem tmStp_of_zero (M : TuringMachine) (a : ℕ) {b c : ℕ} (h : b = 0 ∨ c = 0) :
    tmStp M a b c = 0 := by
  rw [tmStp, if_pos h]

theorem tmStp_of_acc (M : TuringMachine) (a : ℕ) {b c : ℕ} (h : ¬ (b = 0 ∨ c = 0)) (h3 : 3 ≤ b)
    (hacc : M.acc (tmStOf b) = true) : tmStp M a b c = 0 := by
  rw [tmStp, if_neg h, if_pos ⟨h3, hacc⟩]

theorem tmStp_of_left (M : TuringMachine) {a b c : ℕ} (h : ¬ (b = 0 ∨ c = 0))
    (h2 : ¬ (3 ≤ b ∧ M.acc (tmStOf b) = true)) (h3 : 3 ≤ a) (h4 : M.acc (tmStOf a) = false)
    (h5 : M.mv (tmStOf a) (tmBit a) = true) :
    tmStp M a b c = tmH (M.st (tmStOf a) (tmBit a)) (tmWrite M b) := by
  rw [tmStp, if_neg h, if_neg h2, if_pos ⟨h3, h4, h5⟩]

theorem tmStp_of_right (M : TuringMachine) {a b c : ℕ} (h : ¬ (b = 0 ∨ c = 0))
    (h2 : ¬ (3 ≤ b ∧ M.acc (tmStOf b) = true))
    (h3 : ¬ (3 ≤ a ∧ M.acc (tmStOf a) = false ∧ M.mv (tmStOf a) (tmBit a) = true))
    (h4 : 3 ≤ c) (h5 : M.acc (tmStOf c) = false) (h6 : M.mv (tmStOf c) (tmBit c) = false) :
    tmStp M a b c = tmH (M.st (tmStOf c) (tmBit c)) (tmWrite M b) := by
  rw [tmStp, if_neg h, if_neg h2, if_neg h3, if_pos ⟨h4, h5, h6⟩]

theorem tmStp_of_none (M : TuringMachine) {a b c : ℕ} (h : ¬ (b = 0 ∨ c = 0))
    (h2 : ¬ (3 ≤ b ∧ M.acc (tmStOf b) = true))
    (h3 : ¬ (3 ≤ a ∧ M.acc (tmStOf a) = false ∧ M.mv (tmStOf a) (tmBit a) = true))
    (h4 : ¬ (3 ≤ c ∧ M.acc (tmStOf c) = false ∧ M.mv (tmStOf c) (tmBit c) = false)) :
    tmStp M a b c = tmN (tmWrite M b) := by
  rw [tmStp, if_neg h, if_neg h2, if_neg h3, if_neg h4]

/-- **The cellular automaton simulating the machine.** -/
def tmCA (M : TuringMachine) : CellAuto where
  K := 3 + 2 * M.Q
  blk := tmN false
  ini := fun f b => if f then tmH 0 b else tmN b
  stp := tmStp M
  ac := fun s => decide (s = 0)
  Kpos := by omega
  blk_lt := tmN_lt M _
  ini_lt := by
    intro f b
    split
    · exact tmH_lt M M.Qpos _
    · exact tmN_lt M _
  stp_lt := tmStp_lt M

@[simp] theorem tmCA_blk (M : TuringMachine) : (tmCA M).blk = tmN false := rfl

@[simp] theorem tmCA_stp (M : TuringMachine) : (tmCA M).stp = tmStp M := rfl

@[simp] theorem tmCA_ini (M : TuringMachine) (f b : Bool) :
    (tmCA M).ini f b = if f then tmH 0 b else tmN b := rfl

@[simp] theorem tmCA_ac (M : TuringMachine) (s : ℕ) : (tmCA M).ac s = decide (s = 0) := rfl

/-! ### The machine -/

/-- **The configuration after `t` steps** on a tape of `W` cells: the contents of the tape, the
position of the head — the value `W` meaning that the head has walked off the tape and the
machine is dead — and the state.  The machine freezes as soon as it enters an accepting state. -/
def tmConf (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) : ℕ → (ℕ → Bool) × ℕ × ℕ
  | 0 => ((fun j => if j < n then bit j else false), (if 0 < n then 0 else W), 0)
  | t + 1 =>
      let c := tmConf M W n bit t
      if c.2.1 < W ∧ M.acc c.2.2 = false then
        ((fun j => if j = c.2.1 then M.wr c.2.2 (c.1 c.2.1) else c.1 j),
         (if M.mv c.2.2 (c.1 c.2.1) then c.2.1 + 1
          else if c.2.1 = 0 then W else c.2.1 - 1),
         M.st c.2.2 (c.1 c.2.1))
      else c

/-- The symbol of the cell `j` in a configuration. -/
def tmCell (c : (ℕ → Bool) × ℕ × ℕ) (j : ℕ) : ℕ :=
  if c.2.1 = j then tmH c.2.2 (c.1 j) else tmN (c.1 j)

theorem tmCell_ne_zero (c : (ℕ → Bool) × ℕ × ℕ) (j : ℕ) : tmCell c j ≠ 0 := by
  rw [tmCell]
  split <;> simp

theorem tmCell_of_head {c : (ℕ → Bool) × ℕ × ℕ} {j : ℕ} (h : c.2.1 = j) :
    tmCell c j = tmH c.2.2 (c.1 j) := if_pos h

theorem tmCell_of_ne {c : (ℕ → Bool) × ℕ × ℕ} {j : ℕ} (h : c.2.1 ≠ j) :
    tmCell c j = tmN (c.1 j) := if_neg h

theorem three_le_tmCell {c : (ℕ → Bool) × ℕ × ℕ} {j : ℕ} : 3 ≤ tmCell c j ↔ c.2.1 = j := by
  rw [tmCell]
  split
  · simp_all
  · simp_all

theorem tmWrite_tmCell_of_ne (M : TuringMachine) {c : (ℕ → Bool) × ℕ × ℕ} {j : ℕ}
    (h : c.2.1 ≠ j) : tmWrite M (tmCell c j) = c.1 j := by
  rw [tmWrite, tmCell_of_ne h, if_neg (not_head_tmN _), tmBit_tmN]

theorem tmWrite_tmCell_of_head (M : TuringMachine) {c : (ℕ → Bool) × ℕ × ℕ} {j : ℕ}
    (h : c.2.1 = j) : tmWrite M (tmCell c j) = M.wr c.2.2 (c.1 j) := by
  rw [tmWrite, tmCell_of_head h, if_pos (head_tmH _ _), tmStOf_tmH, tmBit_tmH]

/-- The machine is alive at time `t` when its head is still on the tape. -/
def tmAlive (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (t : ℕ) : Prop :=
  (tmConf M W n bit t).2.1 < W

/-- The machine has reached an accepting configuration at time `t`. -/
def tmAccAt (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (t : ℕ) : Prop :=
  tmAlive M W n bit t ∧ M.acc (tmConf M W n bit t).2.2 = true

theorem tmConf_succ_of_accAt {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t : ℕ}
    (h : tmAccAt M W n bit t) : tmConf M W n bit (t + 1) = tmConf M W n bit t := by
  rw [tmConf]
  exact if_neg (by simp [h.2])

theorem tmAccAt_succ {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t : ℕ}
    (h : tmAccAt M W n bit t) : tmAccAt M W n bit (t + 1) := by
  rw [tmAccAt, tmAlive, tmConf_succ_of_accAt h]
  exact h

theorem tmAccAt_mono {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t' t : ℕ}
    (h : tmAccAt M W n bit t') (hle : t' ≤ t) : tmAccAt M W n bit t := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact tmAccAt_succ ih

theorem tmConf_succ_of_step {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t : ℕ}
    (h1 : (tmConf M W n bit t).2.1 < W) (h2 : M.acc (tmConf M W n bit t).2.2 = false) :
    tmConf M W n bit (t + 1) =
      ((fun j => if j = (tmConf M W n bit t).2.1 then
          M.wr (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1)
        else (tmConf M W n bit t).1 j),
       (if M.mv (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) then
          (tmConf M W n bit t).2.1 + 1
        else if (tmConf M W n bit t).2.1 = 0 then W else (tmConf M W n bit t).2.1 - 1),
       M.st (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1)) := by
  rw [tmConf]
  exact if_pos ⟨h1, h2⟩

theorem tmConf_succ_of_stop {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t : ℕ}
    (h : ¬ ((tmConf M W n bit t).2.1 < W ∧ M.acc (tmConf M W n bit t).2.2 = false)) :
    tmConf M W n bit (t + 1) = tmConf M W n bit t := by
  rw [tmConf]
  exact if_neg h

/-! ### The accept signal -/

/-- **The cell `j` carries the accept symbol at time `t`**: the machine reached an accepting
configuration at some time `t'`, and the accept signal, which is created one step later at the
head and travels leftwards one cell per step, has had the time to reach the cell `j`. -/
def tmZero (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) : Prop :=
  ∃ t', tmAccAt M W n bit t' ∧ j ≤ (tmConf M W n bit t').2.1 ∧
    t' + 1 + ((tmConf M W n bit t').2.1 - j) ≤ t

theorem not_tmZero_zero {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {j : ℕ} :
    ¬ tmZero M W n bit 0 j := by
  rintro ⟨t', -, -, h⟩
  omega

theorem tmZero_succ {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t j : ℕ}
    (h : tmZero M W n bit t j) : tmZero M W n bit (t + 1) j := by
  obtain ⟨t', ha, hle, hlt⟩ := h
  exact ⟨t', ha, hle, by omega⟩

theorem tmZero_succ_left {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t j : ℕ}
    (h : tmZero M W n bit t (j + 1)) : tmZero M W n bit (t + 1) j := by
  obtain ⟨t', ha, hle, hlt⟩ := h
  exact ⟨t', ha, by omega, by omega⟩

theorem tmZero_of_accAt {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t j : ℕ}
    (h : tmAccAt M W n bit t) (hp : (tmConf M W n bit t).2.1 = j) : tmZero M W n bit (t + 1) j :=
  ⟨t, h, by omega, by omega⟩

theorem tmAccAt_of_tmZero {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t j : ℕ}
    (h : tmZero M W n bit t j) : tmAccAt M W n bit t := by
  obtain ⟨t', ha, -, hlt⟩ := h
  exact tmAccAt_mono ha (by omega)

/-- The three ways a cell can come to carry the accept symbol are the only ones. -/
theorem not_tmZero_succ {M : TuringMachine} {W n : ℕ} {bit : ℕ → Bool} {t j : ℕ}
    (hz : ¬ tmZero M W n bit t j) (hz' : ¬ (j + 1 < W ∧ tmZero M W n bit t (j + 1)))
    (ha : ¬ (tmAccAt M W n bit t ∧ (tmConf M W n bit t).2.1 = j)) :
    ¬ tmZero M W n bit (t + 1) j := by
  rintro ⟨t', hacc, hle, hlt⟩
  have hpW : (tmConf M W n bit t').2.1 < W := hacc.1
  rcases Nat.lt_or_ge (t' + 1 + ((tmConf M W n bit t').2.1 - j)) (t + 1) with h | h
  · exact hz ⟨t', hacc, hle, by omega⟩
  · rcases eq_or_lt_of_le hle with heq | hlt'
    · have htt : t' = t := by omega
      subst htt
      exact ha ⟨hacc, heq.symm⟩
    · exact hz' ⟨by omega, ⟨t', hacc, by omega, by omega⟩⟩

/-! ### The simulation -/

theorem caCell_tmCA_succ (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (t j : ℕ) :
    CircCode.caCell (tmCA M) W n bit (t + 1) j
      = tmStp M (if j = 0 then tmN false else CircCode.caCell (tmCA M) W n bit t (j - 1))
          (CircCode.caCell (tmCA M) W n bit t j)
          (if j + 1 < W then CircCode.caCell (tmCA M) W n bit t (j + 1) else tmN false) := rfl

/-- **The automaton simulates the machine**: every cell of the tape carries the accept symbol
once the accept signal has reached it, and the symbol of the machine's configuration before
that. -/
theorem caCell_tmCA_aux (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) :
    ∀ t j, j < W →
      (tmZero M W n bit t j → CircCode.caCell (tmCA M) W n bit t j = 0) ∧
      (¬ tmZero M W n bit t j →
        CircCode.caCell (tmCA M) W n bit t j = tmCell (tmConf M W n bit t) j) := by
  intro t
  induction t with
  | zero =>
      intro j hj
      refine ⟨fun hz => absurd hz not_tmZero_zero, fun _ => ?_⟩
      rw [CircCode.caCell, tmCell]
      have htape : (tmConf M W n bit 0).1 j = if j < n then bit j else false := rfl
      have hhd : (tmConf M W n bit 0).2.1 = if 0 < n then 0 else W := rfl
      have hst : (tmConf M W n bit 0).2.2 = 0 := rfl
      rw [htape, hhd, hst]
      by_cases hn : 0 < n
      · rw [if_pos hn]
        by_cases hj0 : j = 0
        · subst hj0
          simp [hn]
        · rw [if_neg (Ne.symm hj0)]
          by_cases hjn : j < n <;> simp [hjn, hj0]
      · rw [if_neg hn, if_neg (by omega : ¬ W = j)]
        simp [show ¬ j < n by omega]
  | succ t ih =>
      intro j hj
      by_cases hz : tmZero M W n bit t j
      · have h0 : CircCode.caCell (tmCA M) W n bit (t + 1) j = 0 := by
          rw [caCell_tmCA_succ, (ih j hj).1 hz, tmStp_of_zero _ _ (Or.inl rfl)]
        exact ⟨fun _ => h0, fun hn => absurd (tmZero_succ hz) hn⟩
      by_cases hz' : j + 1 < W ∧ tmZero M W n bit t (j + 1)
      · have h0 : CircCode.caCell (tmCA M) W n bit (t + 1) j = 0 := by
          rw [caCell_tmCA_succ, if_pos hz'.1, (ih (j + 1) hz'.1).1 hz'.2,
            tmStp_of_zero _ _ (Or.inr rfl)]
        exact ⟨fun _ => h0, fun hn => absurd (tmZero_succ_left hz'.2) hn⟩
      -- the middle cell simulates the machine
      have hC : CircCode.caCell (tmCA M) W n bit t j = tmCell (tmConf M W n bit t) j :=
        (ih j hj).2 hz
      have hCne : ¬ (CircCode.caCell (tmCA M) W n bit t j = 0 ∨
          (if j + 1 < W then CircCode.caCell (tmCA M) W n bit t (j + 1) else tmN false) = 0) := by
        rintro (h | h)
        · exact tmCell_ne_zero _ _ (hC ▸ h)
        · split at h
          · rename_i hjW
            have hz1 : ¬ tmZero M W n bit t (j + 1) := fun hzz => hz' ⟨hjW, hzz⟩
            exact tmCell_ne_zero _ _ ((ih (j + 1) hjW).2 hz1 ▸ h)
          · exact tmN_ne_zero _ h
      by_cases ha : tmAccAt M W n bit t ∧ (tmConf M W n bit t).2.1 = j
      · have h0 : CircCode.caCell (tmCA M) W n bit (t + 1) j = 0 := by
          rw [caCell_tmCA_succ]
          refine tmStp_of_acc _ _ hCne ?_ ?_
          · rw [hC]; exact three_le_tmCell.2 ha.2
          · rw [hC, tmCell_of_head ha.2, tmStOf_tmH]
            exact ha.1.2
        exact ⟨fun _ => h0, fun hn => absurd (tmZero_of_accAt ha.1 ha.2) hn⟩
      -- the generic case
      refine ⟨fun hzz => absurd hzz (not_tmZero_succ hz hz' ha), fun _ => ?_⟩
      rw [caCell_tmCA_succ]
      set Lv := (if j = 0 then tmN false
        else CircCode.caCell (tmCA M) W n bit t (j - 1)) with hLdef
      set Rv := (if j + 1 < W then CircCode.caCell (tmCA M) W n bit t (j + 1)
        else tmN false) with hRdef
      set Cv := CircCode.caCell (tmCA M) W n bit t j with hCdef
      have hLhead : ∀ _h3 : 3 ≤ Lv, (tmConf M W n bit t).2.1 + 1 = j ∧
          Lv = tmH (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (j - 1)) := by
        intro h3
        by_cases hj0 : j = 0
        · rw [hLdef, if_pos hj0] at h3
          exact absurd h3 (not_head_tmN _)
        · rw [hLdef, if_neg hj0] at h3 ⊢
          by_cases hzL : tmZero M W n bit t (j - 1)
          · rw [(ih (j - 1) (by omega)).1 hzL] at h3
            omega
          · rw [(ih (j - 1) (by omega)).2 hzL] at h3 ⊢
            have hp := three_le_tmCell.1 h3
            exact ⟨by omega, tmCell_of_head hp⟩
      have hRhead : ∀ _h3 : 3 ≤ Rv, (tmConf M W n bit t).2.1 = j + 1 ∧ j + 1 < W ∧
          Rv = tmH (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (j + 1)) := by
        intro h3
        by_cases hjW : j + 1 < W
        · rw [hRdef, if_pos hjW] at h3 ⊢
          rw [(ih (j + 1) hjW).2 (fun hzz => hz' ⟨hjW, hzz⟩)] at h3 ⊢
          exact ⟨three_le_tmCell.1 h3, hjW, tmCell_of_head (three_le_tmCell.1 h3)⟩
        · rw [hRdef, if_neg hjW] at h3
          exact absurd h3 (not_head_tmN _)
      have h2 : ¬ (3 ≤ Cv ∧ M.acc (tmStOf Cv) = true) := by
        rintro ⟨h3, hacc⟩
        rw [hC] at h3 hacc
        have hp : (tmConf M W n bit t).2.1 = j := three_le_tmCell.1 h3
        rw [tmCell_of_head hp, tmStOf_tmH] at hacc
        exact ha ⟨⟨by rw [tmAlive, hp]; exact hj, hacc⟩, hp⟩
      by_cases hacc : tmAccAt M W n bit t
      · -- the machine has accepted and is frozen
        have hpj : (tmConf M W n bit t).2.1 ≠ j := fun hh => ha ⟨hacc, hh⟩
        have h3 : ¬ (3 ≤ Lv ∧ M.acc (tmStOf Lv) = false ∧
            M.mv (tmStOf Lv) (tmBit Lv) = true) := by
          rintro ⟨ha3, hb3, -⟩
          rw [(hLhead ha3).2, tmStOf_tmH, hacc.2] at hb3
          simp at hb3
        have h4 : ¬ (3 ≤ Rv ∧ M.acc (tmStOf Rv) = false ∧
            M.mv (tmStOf Rv) (tmBit Rv) = false) := by
          rintro ⟨ha4, hb4, -⟩
          rw [(hRhead ha4).2.2, tmStOf_tmH, hacc.2] at hb4
          simp at hb4
        rw [tmStp_of_none M hCne h2 h3 h4, hC, tmWrite_tmCell_of_ne M hpj,
          tmConf_succ_of_accAt hacc, tmCell_of_ne hpj]
      · have hnz : ∀ i, ¬ tmZero M W n bit t i := fun i hzz => hacc (tmAccAt_of_tmZero hzz)
        by_cases hp : (tmConf M W n bit t).2.1 < W
        · -- the machine takes a step
          have haccF : M.acc (tmConf M W n bit t).2.2 = false := by
            by_contra hcon
            exact hacc ⟨hp, by simpa using hcon⟩
          have hstep := tmConf_succ_of_step hp haccF
          have htape' : (tmConf M W n bit (t + 1)).1 j = tmWrite M Cv := by
            rw [hstep, hC]
            by_cases hpj : (tmConf M W n bit t).2.1 = j
            · rw [tmWrite_tmCell_of_head M hpj]
              simp [hpj]
            · rw [tmWrite_tmCell_of_ne M hpj]
              simp [Ne.symm hpj]
          have hhead' : (tmConf M W n bit (t + 1)).2.1 =
              if M.mv (tmConf M W n bit t).2.2 ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1)
                then (tmConf M W n bit t).2.1 + 1
                else if (tmConf M W n bit t).2.1 = 0 then W
                else (tmConf M W n bit t).2.1 - 1 := by
            rw [hstep]
          have hstate' : (tmConf M W n bit (t + 1)).2.2 =
              M.st (tmConf M W n bit t).2.2
                ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) := by
            rw [hstep]
          by_cases hA : (tmConf M W n bit t).2.1 + 1 = j ∧
              M.mv (tmConf M W n bit t).2.2
                ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) = true
          · -- the head arrives from the left
            have hLv : Lv = tmH (tmConf M W n bit t).2.2
                ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) := by
              rw [hLdef, if_neg (by omega : ¬ j = 0),
                (ih (j - 1) (by omega)).2 (hnz _),
                show j - 1 = (tmConf M W n bit t).2.1 by omega]
              exact tmCell_of_head (by omega)
            have h3 : 3 ≤ Lv := by rw [hLv]; exact head_tmH _ _
            have hhd : (tmConf M W n bit (t + 1)).2.1 = j := by
              rw [hhead', if_pos hA.2]
              exact hA.1
            rw [tmStp_of_left M hCne h2 h3 (by rw [hLv, tmStOf_tmH]; exact haccF)
                (by rw [hLv, tmStOf_tmH, tmBit_tmH]; exact hA.2),
              hLv, tmStOf_tmH, tmBit_tmH, tmCell_of_head hhd, hstate', htape']
          by_cases hB : (tmConf M W n bit t).2.1 = j + 1 ∧
              M.mv (tmConf M W n bit t).2.2
                ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) = false
          · -- the head arrives from the right
            have hRv : Rv = tmH (tmConf M W n bit t).2.2
                ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) := by
              rw [hRdef, if_pos (by omega : j + 1 < W),
                (ih (j + 1) (by omega)).2 (hnz _),
                show j + 1 = (tmConf M W n bit t).2.1 by omega]
              exact tmCell_of_head rfl
            have h4 : 3 ≤ Rv := by rw [hRv]; exact head_tmH _ _
            have h3 : ¬ (3 ≤ Lv ∧ M.acc (tmStOf Lv) = false ∧
                M.mv (tmStOf Lv) (tmBit Lv) = true) := by
              rintro ⟨ha3, -, -⟩
              have := (hLhead ha3).1
              omega
            have hhd : (tmConf M W n bit (t + 1)).2.1 = j := by
              rw [hhead', hB.2]
              simp only [Bool.false_eq_true, if_false]
              rw [if_neg (by omega : ¬ (tmConf M W n bit t).2.1 = 0)]
              omega
            rw [tmStp_of_right M hCne h2 h3 h4 (by rw [hRv, tmStOf_tmH]; exact haccF)
                (by rw [hRv, tmStOf_tmH, tmBit_tmH]; exact hB.2),
              hRv, tmStOf_tmH, tmBit_tmH, tmCell_of_head hhd, hstate', htape']
          · -- no head arrives
            have h3 : ¬ (3 ≤ Lv ∧ M.acc (tmStOf Lv) = false ∧
                M.mv (tmStOf Lv) (tmBit Lv) = true) := by
              rintro ⟨ha3, -, hc3⟩
              obtain ⟨hp1, hLv⟩ := hLhead ha3
              rw [hLv, tmStOf_tmH, tmBit_tmH,
                show j - 1 = (tmConf M W n bit t).2.1 by omega] at hc3
              exact hA ⟨hp1, hc3⟩
            have h4 : ¬ (3 ≤ Rv ∧ M.acc (tmStOf Rv) = false ∧
                M.mv (tmStOf Rv) (tmBit Rv) = false) := by
              rintro ⟨ha4, -, hc4⟩
              obtain ⟨hp1, -, hRv⟩ := hRhead ha4
              rw [hRv, tmStOf_tmH, tmBit_tmH, ← hp1] at hc4
              exact hB ⟨hp1, hc4⟩
            have hhd : (tmConf M W n bit (t + 1)).2.1 ≠ j := by
              rw [hhead']
              by_cases hmv : M.mv (tmConf M W n bit t).2.2
                  ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) = true
              · rw [if_pos hmv]
                intro hcon
                exact hA ⟨hcon, hmv⟩
              · have hmv' : M.mv (tmConf M W n bit t).2.2
                    ((tmConf M W n bit t).1 (tmConf M W n bit t).2.1) = false := by
                  simpa using hmv
                rw [if_neg hmv]
                split
                · omega
                · intro hcon
                  exact hB ⟨by omega, hmv'⟩
            rw [tmStp_of_none M hCne h2 h3 h4, tmCell_of_ne hhd, htape']
        · -- the machine is dead
          have hpj : (tmConf M W n bit t).2.1 ≠ j := by omega
          have h3 : ¬ (3 ≤ Lv ∧ M.acc (tmStOf Lv) = false ∧
              M.mv (tmStOf Lv) (tmBit Lv) = true) := by
            rintro ⟨ha3, -, -⟩
            have := (hLhead ha3).1
            omega
          have h4 : ¬ (3 ≤ Rv ∧ M.acc (tmStOf Rv) = false ∧
              M.mv (tmStOf Rv) (tmBit Rv) = false) := by
            rintro ⟨ha4, -, -⟩
            obtain ⟨hp1, hjW, -⟩ := hRhead ha4
            omega
          rw [tmStp_of_none M hCne h2 h3 h4, hC, tmWrite_tmCell_of_ne M hpj,
            tmConf_succ_of_stop (fun hcon => hp hcon.1), tmCell_of_ne hpj]

/-- **The automaton simulates the machine** on every cell the accept signal has not reached. -/
theorem caCell_tmCA_eq (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) {t j : ℕ} (hj : j < W)
    (h : ¬ tmZero M W n bit t j) :
    CircCode.caCell (tmCA M) W n bit t j = tmCell (tmConf M W n bit t) j :=
  (caCell_tmCA_aux M W n bit t j hj).2 h

/-- **A cell of the automaton carries the accept symbol exactly when the accept signal has
reached it.** -/
theorem caCell_tmCA_zero_iff (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) {t j : ℕ}
    (hj : j < W) : CircCode.caCell (tmCA M) W n bit t j = 0 ↔ tmZero M W n bit t j := by
  refine ⟨fun h => ?_, (caCell_tmCA_aux M W n bit t j hj).1⟩
  by_contra hcon
  exact tmCell_ne_zero _ _ (caCell_tmCA_eq M W n bit hj hcon ▸ h)

/-! ### The language of the machine -/

/-- **The machine accepts within `H` steps**: it reaches an accepting configuration at a time `t`
early enough for the accept signal, which is created one step later at the head and travels one
cell per step, to reach the first cell of the tape by the deadline `H`. -/
def tmAccBy (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (H : ℕ) : Prop :=
  ∃ t, tmAccAt M W n bit t ∧ t + 1 + (tmConf M W n bit t).2.1 ≤ H

theorem tmZero_zero_iff (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) (H : ℕ) :
    tmZero M W n bit H 0 ↔ tmAccBy M W n bit H := by
  constructor
  · rintro ⟨t, hat, -, hle⟩
    exact ⟨t, hat, by omega⟩
  · rintro ⟨t, hat, hle⟩
    exact ⟨t, hat, Nat.zero_le _, by omega⟩

/-- **The first cell of the tableau carries the accept symbol exactly when the machine accepts
within the deadline.** -/
theorem caCell_tmCA_zero_iff_accBy (M : TuringMachine) {W : ℕ} (n : ℕ) (bit : ℕ → Bool) (H : ℕ)
    (hW : 0 < W) :
    CircCode.caCell (tmCA M) W n bit H 0 = 0 ↔ tmAccBy M W n bit H :=
  (caCell_tmCA_zero_iff M W n bit hW).trans (tmZero_zero_iff M W n bit H)

/-- The head has taken at most one step per unit of time, unless the machine is dead. -/
theorem tmHead_le (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) :
    ∀ t, (tmConf M W n bit t).2.1 ≤ t ∨ (tmConf M W n bit t).2.1 = W := by
  intro t
  induction t with
  | zero =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact Or.inr (by simp [tmConf, hn])
      · exact Or.inl (by simp [tmConf, hn])
  | succ t ih =>
      by_cases hstop : ¬ ((tmConf M W n bit t).2.1 < W ∧ M.acc (tmConf M W n bit t).2.2 = false)
      · rw [tmConf_succ_of_stop hstop]
        rcases ih with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · rw [not_not] at hstop
        rw [tmConf_succ_of_step hstop.1 hstop.2]
        have hle : (tmConf M W n bit t).2.1 ≤ t := by
          rcases ih with h | h
          · exact h
          · omega
        dsimp only
        split
        · exact Or.inl (by omega)
        · split
          · exact Or.inr rfl
          · exact Or.inl (by omega)

/-- **A machine that accepts early enough accepts within the deadline**: if it reaches an
accepting configuration within `T` steps and the deadline is at least `2 * T + 1`, the accept
signal reaches the first cell in time. -/
theorem tmAccBy_of_acc_le (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) {t T H : ℕ}
    (h : tmAccAt M W n bit t) (htT : t ≤ T) (hH : 2 * T + 1 ≤ H) : tmAccBy M W n bit H := by
  refine ⟨t, h, ?_⟩
  rcases tmHead_le M W n bit t with hle | heq
  · omega
  · have := h.1
    rw [tmAlive, heq] at this
    omega

/-- Conversely, a machine that is counted as accepting within the deadline does reach an
accepting configuration before it. -/
theorem acc_lt_of_tmAccBy (M : TuringMachine) (W n : ℕ) (bit : ℕ → Bool) {H : ℕ}
    (h : tmAccBy M W n bit H) : ∃ t < H, tmAccAt M W n bit t := by
  obtain ⟨t, hat, hle⟩ := h
  exact ⟨t, by omega, hat⟩

/-- **The language of a Turing machine** run on a tape of `w n` cells for `h n` steps. -/
def TMLang (M : TuringMachine) (w h : ℕ → ℕ) : Language :=
  fun x => tmAccBy M (w x.length) x.length (fun j => x.getD j false) (h x.length)

theorem caLang_tmCA (M : TuringMachine) {w h : ℕ → ℕ} (hw : ∀ n, 0 < w n) :
    CALang (tmCA M) w h = TMLang M w h := by
  funext x
  rw [CALang, TMLang, tmCA_ac]
  simp only [decide_eq_true_eq]
  exact propext (caCell_tmCA_zero_iff_accBy M _ _ _ (hw _))

/-- **The language of a Turing machine whose tape and running time are computed by Cobham terms
is decided by a P-uniform family of circuits**, unconditionally. -/
theorem pUniformDecidable_tmLang {M : TuringMachine} {w h : ℕ → ℕ} (hu : CAUniform w h) :
    PUniformDecidable (TMLang M w h) := by
  obtain ⟨wT, hT, hw, hwT, hhT⟩ := hu
  rw [← caLang_tmCA M hw]
  exact pUniformDecidable_caLang (A := tmCA M) ⟨wT, hT, hw, hwT, hhT⟩

/-- **The language of such a Turing machine reduces to SAT in polynomial time**,
unconditionally. -/
theorem polyManyOne_SAT_tmLang {M : TuringMachine} {w h : ℕ → ℕ} (hu : CAUniform w h) :
    TMLang M w h ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_tmLang hu)

end Complexity
