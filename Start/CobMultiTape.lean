/-
**Word-register programs run on multi-tape machines** — task `M26-UNIFY-DEPTHTHREE-COBMT`, third
layer, first part.

A word-register program (`Start/CobRegProg.lean`) is flattened into a list of low-level
instructions with jump addresses (`Complexity.CobMT.LInstr`), and one multi-tape machine
interprets such a list: one tape per register, carrying a mark at the left end and the bits of the
register after it, plus the input tape.  This module gives the machine and the behaviour of each
low-level instruction.

* `Complexity.CobMT.Sym` — the tape symbols (blank, the two bits, the left-end mark);
* `Complexity.CobMT.RepT T cells i` — the tape `T` holds the mark followed by `cells` and its head
  is at position `i`;
* `Complexity.CobMT.LInstr`, `Complexity.CobMT.machine` — the instructions and the interpreter;
* the run lemmas `run_clearI`, `run_pushI`, … — what each instruction does, and in how many steps.
-/

import Start.CobRegCost
import Start.DepthThreeMultiTapeMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobMT

open DepthThreeLowerBound

/-- The tape symbols. -/
inductive Sym where
  | blank
  | zero
  | one
  | mark
  deriving DecidableEq

instance : Fintype Sym :=
  ⟨⟨([Sym.blank, Sym.zero, Sym.one, Sym.mark] : List Sym), by decide⟩,
    fun x => by cases x <;> decide⟩

instance : Inhabited Sym := ⟨.blank⟩

/-- The symbol of a bit. -/
def bitSym (b : Bool) : Sym := if b then .one else .zero

theorem bitSym_injective : Function.Injective bitSym := by
  intro a b h; cases a <;> cases b <;> simp_all [bitSym]

theorem bitSym_ne_blank (b : Bool) : bitSym b ≠ default := by cases b <;> decide

theorem bitSym_ne_mark (b : Bool) : bitSym b ≠ .mark := by cases b <;> simp [bitSym]

theorem bitSym_ne_blank' (b : Bool) : bitSym b ≠ .blank := by cases b <;> decide

/-- The cells of a register holding the word `w`. -/
def enc (w : Word) : List Sym := w.map bitSym

/-- The symbol at position `j` of a register tape whose cells after the mark are `cells`. -/
def cellAt (cells : List Sym) (j : ℤ) : Sym :=
  if j = 0 then .mark else if 0 < j then cells.getD (j.toNat - 1) .blank else .blank

theorem cellAt_zero (cells : List Sym) : cellAt cells 0 = .mark := by simp [cellAt]

/-- **The tape `T` holds the mark followed by `cells`, with the head at position `i`.** -/
def RepT (T : Turing.Tape Sym) (cells : List Sym) (i : ℕ) : Prop :=
  ∀ j : ℤ, T.nth (j - i) = cellAt cells j

theorem RepT.head {T : Turing.Tape Sym} {cells : List Sym} {i : ℕ} (h : RepT T cells i) :
    T.head = cellAt cells i := by
  have := h i; rwa [sub_self, Turing.Tape.nth_zero] at this

theorem RepT.right {T : Turing.Tape Sym} {cells : List Sym} {i : ℕ} (h : RepT T cells i) :
    RepT (T.move .right) cells (i + 1) := by
  intro j
  rw [Turing.Tape.move_right_nth, ← h j]
  congr 1; push_cast; ring

theorem RepT.left {T : Turing.Tape Sym} {cells : List Sym} {i : ℕ} (h : RepT T cells (i + 1)) :
    RepT (T.move .left) cells i := by
  intro j
  rw [Turing.Tape.move_left_nth, ← h j]
  congr 1; push_cast; ring

theorem RepT.stay {T : Turing.Tape Sym} {cells : List Sym} {i : ℕ} (h : RepT T cells i) :
    RepT (HeadMove.stay.apply T) cells i := h

/-- The cell of index `m` (position `m + 1`). -/
def cellN (cells : List Sym) (m : ℕ) : Sym := cells.getD m .blank

theorem cellAt_succ (cells : List Sym) (m : ℕ) : cellAt cells ((m : ℤ) + 1) = cellN cells m := by
  unfold cellAt cellN
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show ((m : ℤ) + 1).toNat - 1 = m by omega]

theorem cellAt_cases (j : ℤ) :
    j = 0 ∨ j < 0 ∨ ∃ m : ℕ, j = (m : ℤ) + 1 := by
  rcases lt_trichotomy j 0 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨j.toNat - 1, by omega⟩)

theorem cellAt_neg (cells : List Sym) {j : ℤ} (h : j < 0) : cellAt cells j = .blank := by
  unfold cellAt; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem cellN_set {cells : List Sym} {k : ℕ} (hk : k < cells.length) (a : Sym) (m : ℕ) :
    cellN (cells.set k a) m = if m = k then a else cellN cells m := by
  unfold cellN
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : m = k
  · subst h; simp [hk]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem cellN_concat (cells : List Sym) (a : Sym) (m : ℕ) :
    cellN (cells ++ [a]) m = if m = cells.length then a else cellN cells m := by
  unfold cellN
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · next h => rw [ite_eq_right (by omega)]
  · next h =>
      rw [List.getElem?_singleton, List.getElem?_eq_none (by omega)]
      by_cases hm : m = cells.length
      · subst hm; simp
      · rw [ite_eq_right (by omega), ite_eq_right hm]

theorem RepT.write_set {T : Turing.Tape Sym} {cells : List Sym} {i : ℕ} (h : RepT T cells (i + 1))
    (hi : i < cells.length) (a : Sym) : RepT (T.write a) (cells.set i a) (i + 1) := by
  intro j
  rw [Turing.Tape.write_nth]
  rcases cellAt_cases j with rfl | hj | ⟨m, rfl⟩
  · rw [ite_eq_right (by omega), h 0, cellAt_zero, cellAt_zero]
  · rw [ite_eq_right (by omega), h j, cellAt_neg _ hj, cellAt_neg _ hj]
  · rw [cellAt_succ, cellN_set hi]
    by_cases hm : m = i
    · subst hm; simp
    · rw [ite_eq_right (by push_cast; omega), ite_eq_right hm, h, cellAt_succ]

theorem RepT.write_end {T : Turing.Tape Sym} {cells : List Sym} (h : RepT T cells (cells.length + 1))
    (a : Sym) : RepT (T.write a) (cells ++ [a]) (cells.length + 1) := by
  intro j
  rw [Turing.Tape.write_nth]
  rcases cellAt_cases j with rfl | hj | ⟨m, rfl⟩
  · rw [ite_eq_right (by omega), h 0, cellAt_zero, cellAt_zero]
  · rw [ite_eq_right (by omega), h j, cellAt_neg _ hj, cellAt_neg _ hj]
  · rw [cellAt_succ, cellN_concat]
    by_cases hm : m = cells.length
    · subst hm; simp
    · rw [ite_eq_right (by push_cast; omega), ite_eq_right hm, h, cellAt_succ]

theorem cellAt_append_blank (cells : List Sym) (n : ℕ) :
    cellAt (cells ++ List.replicate n .blank) = cellAt cells := by
  funext j
  rcases cellAt_cases j with rfl | hj | ⟨m, rfl⟩
  · rw [cellAt_zero, cellAt_zero]
  · rw [cellAt_neg _ hj, cellAt_neg _ hj]
  · rw [cellAt_succ, cellAt_succ]
    unfold cellN
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
    split
    · rfl
    · next h =>
        rw [List.getElem?_replicate, List.getElem?_eq_none (show cells.length ≤ m by omega)]
        split <;> rfl

theorem RepT.congr_cells {T : Turing.Tape Sym} {c c' : List Sym} {i : ℕ} (h : RepT T c i)
    (e : cellAt c = cellAt c') : RepT T c' i := fun j => by rw [h j, e]

theorem cellAt_enc_pos (w : Word) (m : ℕ) (hm : m < w.length) :
    cellAt (enc w) ((m : ℤ) + 1) = bitSym w[m] := by
  rw [cellAt_succ]
  unfold cellN enc
  rw [List.getD_eq_getElem?_getD]
  simp [hm]

theorem cellAt_enc_end (w : Word) (m : ℕ) (hm : w.length ≤ m) :
    cellAt (enc w) ((m : ℤ) + 1) = .blank := by
  rw [cellAt_succ]
  unfold cellN enc
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_eq_none (show (w.map bitSym).length ≤ m by simpa using hm)]

/-! ### The low-level instructions -/

/-- **Low-level instructions.** Registers are numbers, jump targets are addresses. -/
inductive LInstr where
  /-- Mark every register tape and copy the input into register `0`. -/
  | init
  | clear (r : ℕ)
  | push (r : ℕ) (b : Bool)
  | trunc (r s : ℕ)
  /-- Move the head of `r` one cell right. -/
  | adv (r : ℕ)
  /-- Move the head of `r` one cell left. -/
  | retreat (r : ℕ)
  /-- Move the head of `r` to its last bit (to the mark if the register is empty). -/
  | toEnd (r : ℕ)
  /-- Move the head of `r` back to the mark. -/
  | rewind (r : ℕ)
  /-- Jump on the symbol under the head of `r`: to `tEnd` on the blank or the mark, else to `t₀` or
  `t₁` on a bit. -/
  | branch (r tEnd t₀ t₁ : ℕ)
  | jmp (t : ℕ)
  /-- Halt, accepting iff the register `r` is not empty. -/
  | test (r : ℕ)

/-! ### The interpreter -/

section Machine

variable (prog : List LInstr) (N : ℕ)

/-- The tape of a register (registers from `N` on do not exist and read the input tape). -/
def reg (r : ℕ) : Option (Fin N) := if h : r < N then some ⟨r, h⟩ else none

/-- The states: an address with a micro-state, or the halting state with the answer. -/
abbrev St := (Fin prog.length × Fin 5) ⊕ Bool

/-- The state at address `t`, micro-state `m` (halting and rejecting outside the program). -/
def at_ (t m : ℕ) : St prog :=
  if h : t < prog.length ∧ m < 5 then .inl (⟨t, h.1⟩, ⟨m, h.2⟩) else .inr false

/-- No head moves. -/
def stays : Option (Fin N) → HeadMove := fun _ => .stay

/-- Write `a` on the tape `k` and move it by `d`; leave the other tapes alone. -/
def one (q : St prog) (h : Option (Fin N) → Sym) (k : Option (Fin N)) (a : Sym) (d : HeadMove) :
    Option (St prog × (Option (Fin N) → Sym) × (Option (Fin N) → HeadMove)) :=
  some (q, Function.update h k a, Function.update (stays N) k d)

/-- Move the tapes `k₁` and `k₂`. -/
def two (q : St prog) (h : Option (Fin N) → Sym) (k₁ : Option (Fin N)) (d₁ : HeadMove)
    (k₂ : Option (Fin N)) (d₂ : HeadMove) :
    Option (St prog × (Option (Fin N) → Sym) × (Option (Fin N) → HeadMove)) :=
  some (q, h, Function.update (Function.update (stays N) k₁ d₁) k₂ d₂)

/-- One micro-step of an instruction at address `a`. -/
def instrStep (I : LInstr) (a m : ℕ) (h : Option (Fin N) → Sym) :
    Option (St prog × (Option (Fin N) → Sym) × (Option (Fin N) → HeadMove)) :=
  match I with
  | .init =>
      match m with
      | 0 => some (at_ prog a 1, fun k => match k with | none => h none | some _ => .mark, stays N)
      | 1 => one prog N (at_ prog a 2) h (reg N 0) (h (reg N 0)) .right
      | 2 =>
          if h none = .blank then one prog N (at_ prog a 3) h (reg N 0) (h (reg N 0)) .left
          else some (at_ prog a 2, Function.update h (reg N 0) (h none),
            Function.update (Function.update (stays N) (reg N 0) .right) none .right)
      | _ =>
          if h (reg N 0) = .mark then some (at_ prog (a + 1) 0, h, stays N)
          else one prog N (at_ prog a 3) h (reg N 0) (h (reg N 0)) .left
  | .clear r =>
      match m with
      | 0 => one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
      | 1 =>
          if h (reg N r) = .blank then one prog N (at_ prog a 2) h (reg N r) .blank .left
          else one prog N (at_ prog a 1) h (reg N r) .blank .right
      | _ =>
          if h (reg N r) = .mark then some (at_ prog (a + 1) 0, h, stays N)
          else one prog N (at_ prog a 2) h (reg N r) (h (reg N r)) .left
  | .push r b =>
      match m with
      | 0 => one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
      | 1 =>
          if h (reg N r) = .blank then one prog N (at_ prog a 2) h (reg N r) (bitSym b) .left
          else one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
      | _ =>
          if h (reg N r) = .mark then some (at_ prog (a + 1) 0, h, stays N)
          else one prog N (at_ prog a 2) h (reg N r) (h (reg N r)) .left
  | .trunc r s =>
      match m with
      | 0 => two prog N (at_ prog a 1) h (reg N r) .right (reg N s) .right
      | 1 =>
          if h (reg N s) = .blank then some (at_ prog a 2, h, stays N)
          else if h (reg N r) = .blank then some (at_ prog a 3, h, stays N)
          else two prog N (at_ prog a 1) h (reg N r) .right (reg N s) .right
      | 2 =>
          if h (reg N r) = .blank then some (at_ prog a 3, h, stays N)
          else one prog N (at_ prog a 2) h (reg N r) .blank .right
      | 3 =>
          if h (reg N r) = .mark then some (at_ prog a 4, h, stays N)
          else one prog N (at_ prog a 3) h (reg N r) (h (reg N r)) .left
      | _ =>
          if h (reg N s) = .mark then some (at_ prog (a + 1) 0, h, stays N)
          else one prog N (at_ prog a 4) h (reg N s) (h (reg N s)) .left
  | .adv r => one prog N (at_ prog (a + 1) 0) h (reg N r) (h (reg N r)) .right
  | .retreat r => one prog N (at_ prog (a + 1) 0) h (reg N r) (h (reg N r)) .left
  | .toEnd r =>
      match m with
      | 0 => one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
      | _ =>
          if h (reg N r) = .blank then one prog N (at_ prog (a + 1) 0) h (reg N r) .blank .left
          else one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
  | .rewind r =>
      if h (reg N r) = .mark then some (at_ prog (a + 1) 0, h, stays N)
      else one prog N (at_ prog a 0) h (reg N r) (h (reg N r)) .left
  | .branch r tEnd t₀ t₁ =>
      match h (reg N r) with
      | .zero => some (at_ prog t₀ 0, h, stays N)
      | .one => some (at_ prog t₁ 0, h, stays N)
      | _ => some (at_ prog tEnd 0, h, stays N)
  | .jmp t => some (at_ prog t 0, h, stays N)
  | .test r =>
      match m with
      | 0 => one prog N (at_ prog a 1) h (reg N r) (h (reg N r)) .right
      | _ => some (.inr (decide (h (reg N r) ≠ .blank)), h, stays N)

/-- The transition table of the interpreter. -/
def code : MultiTapeCode (Option (Fin N)) Sym (St prog) := fun q h =>
  match q with
  | .inl (pc, m) => instrStep prog N (prog.get pc) pc.val m.val h
  | .inr _ => none

/-- **The interpreter of a low-level program** with `N` registers. -/
abbrev machine : FiniteMultiTapeMachine where
  K := Option (Fin N)
  inputTape := none
  Γ := Sym
  Q := St prog
  initialState := at_ prog 0 0
  inputSymbol := bitSym
  input_injective := bitSym_injective
  input_ne_blank := bitSym_ne_blank
  code := code prog N
  accept := fun q => match q with
    | .inr b => b
    | .inl _ => false

/-- Configurations of the interpreter. -/
abbrev Cfg := MultiTapeCfg (Option (Fin N)) Sym (St prog)

theorem code_at {a m : ℕ} {I : LInstr} (ha : prog[a]? = some I) (hm : m < 5)
    (h : Option (Fin N) → Sym) :
    code prog N (at_ prog a m) h = instrStep prog N I a m h := by
  have hlt : a < prog.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at ha; cases ha
  have hget : prog.get ⟨a, hlt⟩ = I := by
    rw [List.getElem?_eq_getElem hlt] at ha; exact Option.some_inj.mp ha
  simp only [at_, hlt, hm, and_self, dite_true, code, hget]

theorem step_one {c : Cfg prog N} {q : St prog} {k : Option (Fin N)} {a : Sym} {d : HeadMove}
    (h : code prog N c.q (fun k => (c.tapes k).head) =
      one prog N q (fun k => (c.tapes k).head) k a d) :
    (machine prog N).step c = some ⟨q, Function.update c.tapes k (d.apply ((c.tapes k).write a))⟩ := by
  show multiTapeStep (code prog N) c = _
  rw [multiTapeStep_eq_some h]
  simp only [multiTapeUpdate]
  congr 2
  funext k'
  by_cases hk : k' = k
  · subst hk; rw [Function.update_self, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk]
    simp only [stays, HeadMove.apply_stay, Turing.Tape.write_self]

theorem step_stay {c : Cfg prog N} {q : St prog}
    (h : code prog N c.q (fun k => (c.tapes k).head) =
      some (q, fun k => (c.tapes k).head, stays N)) :
    (machine prog N).step c = some ⟨q, c.tapes⟩ := by
  show multiTapeStep (code prog N) c = _
  rw [multiTapeStep_eq_some h]
  simp only [multiTapeUpdate, stays, HeadMove.apply_stay, Turing.Tape.write_self]

theorem step_two {c : Cfg prog N} {q : St prog} {k₁ k₂ : Option (Fin N)} {d₁ d₂ : HeadMove}
    (hk : k₁ ≠ k₂)
    (h : code prog N c.q (fun k => (c.tapes k).head) =
      two prog N q (fun k => (c.tapes k).head) k₁ d₁ k₂ d₂) :
    (machine prog N).step c = some ⟨q, Function.update (Function.update c.tapes k₁
      (d₁.apply (c.tapes k₁))) k₂ (d₂.apply (c.tapes k₂))⟩ := by
  show multiTapeStep (code prog N) c = _
  rw [multiTapeStep_eq_some h]
  simp only [multiTapeUpdate]
  congr 2
  funext k'
  simp only [Turing.Tape.write_self]
  by_cases h2 : k' = k₂
  · subst h2; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h2, Function.update_of_ne h2]
    by_cases h1 : k' = k₁
    · subst h1; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      rfl

theorem step_wtwo {c : Cfg prog N} {q : St prog} {k₁ k₂ : Option (Fin N)} {a : Sym}
    {d₁ d₂ : HeadMove} (hk : k₁ ≠ k₂)
    (h : code prog N c.q (fun k => (c.tapes k).head) =
      some (q, Function.update (fun k => (c.tapes k).head) k₁ a,
        Function.update (Function.update (stays N) k₁ d₁) k₂ d₂)) :
    (machine prog N).step c = some ⟨q, Function.update (Function.update c.tapes k₁
      (d₁.apply ((c.tapes k₁).write a))) k₂ (d₂.apply (c.tapes k₂))⟩ := by
  show multiTapeStep (code prog N) c = _
  rw [multiTapeStep_eq_some h]
  simp only [multiTapeUpdate]
  congr 2
  funext k'
  by_cases h2 : k' = k₂
  · subst h2
    rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm hk),
      Turing.Tape.write_self]
  · rw [Function.update_of_ne h2, Function.update_of_ne h2]
    by_cases h1 : k' = k₁
    · subst h1; rw [Function.update_self, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h1,
        Turing.Tape.write_self]
      rfl

end Machine

/-! ### Runs of the instructions -/

section Runs

variable {prog : List LInstr} {N : ℕ}

/-- The register cells hold no mark. -/
def NoMark (cells : List Sym) : Prop := ∀ c ∈ cells, c ≠ .mark

theorem noMark_enc (w : Word) : NoMark (enc w) := by
  intro c hc
  simp only [enc, List.mem_map] at hc
  obtain ⟨b, -, rfl⟩ := hc
  exact bitSym_ne_mark b

theorem cellAt_ne_mark {cells : List Sym} (h : NoMark cells) (m : ℕ) :
    cellAt cells ((m : ℤ) + 1) ≠ .mark := by
  rw [cellAt_succ]
  unfold cellN
  rw [List.getD_eq_getElem?_getD]
  cases hm : cells[m]? with
  | none => simp
  | some c => exact h c (List.mem_of_getElem? hm)

/-- **Rewinding**: a state that moves the head of `k` left until it reads the mark, then goes on
to `X`, takes `i + 1` steps from position `i`. -/
theorem rewind_runs {q X : St prog} {k : Option (Fin N)}
    (hm : ∀ T : Option (Fin N) → Turing.Tape Sym, (T k).head = .mark →
      (machine prog N).step ⟨q, T⟩ = some ⟨X, T⟩)
    (hl : ∀ T : Option (Fin N) → Turing.Tape Sym, (T k).head ≠ .mark →
      (machine prog N).step ⟨q, T⟩ = some ⟨q, Function.update T k ((T k).move .left)⟩)
    {cells : List Sym} (hc : NoMark cells) :
    ∀ (i : ℕ) (T : Option (Fin N) → Turing.Tape Sym), RepT (T k) cells i →
      ∃ t, RepT t cells 0 ∧ RunsIn (machine prog N).step ⟨q, T⟩ ⟨X, Function.update T k t⟩ (i + 1) := by
  intro i
  induction i with
  | zero =>
      intro T hT
      refine ⟨T k, hT, ?_⟩
      rw [Function.update_eq_self]
      exact RunsIn.single (hm T (by rw [hT.head]; exact cellAt_zero cells))
  | succ i ih =>
      intro T hT
      have hne : (T k).head ≠ .mark := by rw [hT.head]; push_cast; exact cellAt_ne_mark hc i
      obtain ⟨t, ht, hrun⟩ := ih (Function.update T k ((T k).move .left))
        (by rw [Function.update_self]; exact hT.left)
      refine ⟨t, ht, ?_⟩
      have h1 := RunsIn.single (hl T hne)
      rw [Function.update_idem] at hrun
      exact (h1.trans hrun).mono (by omega)

theorem stepAt_one {a m : ℕ} {I : LInstr} (ha : prog[a]? = some I) (hm : m < 5)
    {T : Option (Fin N) → Turing.Tape Sym} {q : St prog} {k : Option (Fin N)} {x : Sym}
    {d : HeadMove}
    (hI : instrStep prog N I a m (fun k => (T k).head) = one prog N q (fun k => (T k).head) k x d) :
    (machine prog N).step ⟨at_ prog a m, T⟩ =
      some ⟨q, Function.update T k (d.apply ((T k).write x))⟩ :=
  step_one prog N (c := ⟨at_ prog a m, T⟩) (by rw [code_at prog N ha hm]; exact hI)

theorem stepAt_stay {a m : ℕ} {I : LInstr} (ha : prog[a]? = some I) (hm : m < 5)
    {T : Option (Fin N) → Turing.Tape Sym} {q : St prog}
    (hI : instrStep prog N I a m (fun k => (T k).head) = some (q, fun k => (T k).head, stays N)) :
    (machine prog N).step ⟨at_ prog a m, T⟩ = some ⟨q, T⟩ :=
  step_stay prog N (c := ⟨at_ prog a m, T⟩) (by rw [code_at prog N ha hm]; exact hI)

theorem stepAt_two {a m : ℕ} {I : LInstr} (ha : prog[a]? = some I) (hm : m < 5)
    {T : Option (Fin N) → Turing.Tape Sym} {q : St prog} {k₁ k₂ : Option (Fin N)}
    {d₁ d₂ : HeadMove} (hk : k₁ ≠ k₂)
    (hI : instrStep prog N I a m (fun k => (T k).head) =
      two prog N q (fun k => (T k).head) k₁ d₁ k₂ d₂) :
    (machine prog N).step ⟨at_ prog a m, T⟩ = some ⟨q, Function.update (Function.update T k₁
      (d₁.apply (T k₁))) k₂ (d₂.apply (T k₂))⟩ :=
  step_two prog N (c := ⟨at_ prog a m, T⟩) hk (by rw [code_at prog N ha hm]; exact hI)

theorem update_move (T : Option (Fin N) → Turing.Tape Sym) (k : Option (Fin N)) (d : Turing.Dir) :
    Function.update T k ((match d with
      | .left => HeadMove.left
      | .right => HeadMove.right).apply ((T k).write (T k).head)) =
      Function.update T k ((T k).move d) := by
  cases d <;> simp [Turing.Tape.write_self]

/-- The list identity behind erasing a register from the left. -/
theorem erase_cells (w : Word) {j : ℕ} (hj : j < w.length) :
    (List.replicate j Sym.blank ++ (enc w).drop j).set j .blank =
      List.replicate (j + 1) Sym.blank ++ (enc w).drop (j + 1) := by
  have hd : (enc w).drop j = bitSym w[j] :: (enc w).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa [enc] using hj)]
    simp [enc]
  rw [hd, List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

/-- **Clearing a register** takes `2 |w| + 3` steps. -/
theorem run_clearI {a r : ℕ} (ha : prog[a]? = some (.clear r)) (T : Option (Fin N) → Turing.Tape Sym)
    (w : Word) (hT : RepT (T (reg N r)) (enc w) 0) :
    ∃ t, RepT t (enc []) 0 ∧ RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩
      ⟨at_ prog (a + 1) 0, Function.update T (reg N r) t⟩ (2 * w.length + 3) := by
  -- the first move
  have s0 : (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog a 1, Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
    rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T (reg N r)).head)
      (d := .right) rfl]
    simp [Turing.Tape.write_self]
  -- the erasing loop
  have loop : ∀ d j (T' : Option (Fin N) → Turing.Tape Sym), j + d = w.length →
      RepT (T' (reg N r)) (List.replicate j .blank ++ (enc w).drop j) (j + 1) →
      ∃ t, RepT t (List.replicate w.length .blank) w.length ∧
        RunsIn (machine prog N).step ⟨at_ prog a 1, T'⟩
          ⟨at_ prog a 2, Function.update T' (reg N r) t⟩ (d + 1) := by
    intro d
    induction d with
    | zero =>
        intro j T' hj hT'
        have hjn : j = w.length := by omega
        subst hjn
        rw [List.drop_eq_nil_of_le (by simp [enc]), List.append_nil] at hT'
        have hblank : (T' (reg N r)).head = .blank := by
          rw [hT'.head]; push_cast
          rw [cellAt_succ]
          simp [cellN]
        have hst : (machine prog N).step ⟨at_ prog a 1, T'⟩ =
            some ⟨at_ prog a 2, Function.update T' (reg N r)
              (((T' (reg N r)).write .blank).move .left)⟩ := by
          rw [stepAt_one ha (by norm_num) (q := at_ prog a 2) (k := reg N r) (x := .blank)
            (d := .left) (by simp only [instrStep, hblank, ite_true])]
          simp
        refine ⟨((T' (reg N r)).write .blank).move .left, ?_, RunsIn.single hst⟩
        have := (RepT.write_end (cells := List.replicate w.length Sym.blank)
          (by rw [List.length_replicate]; exact hT') Sym.blank).left
        simp only [List.length_replicate] at this
        exact this.congr_cells (by
          rw [show List.replicate w.length Sym.blank ++ [Sym.blank] =
            List.replicate w.length Sym.blank ++ List.replicate 1 Sym.blank from rfl,
            cellAt_append_blank])
    | succ d ih =>
        intro j T' hj hT'
        have hjn : j < w.length := by omega
        have hbit : (T' (reg N r)).head = bitSym w[j] := by
          rw [hT'.head]; push_cast
          rw [cellAt_succ]
          unfold cellN
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
            List.length_replicate, Nat.sub_self, List.getElem?_drop, Nat.add_zero]
          simp [enc, hjn]
        have hnb : (T' (reg N r)).head ≠ .blank := by rw [hbit]; exact bitSym_ne_blank _
        have hst : (machine prog N).step ⟨at_ prog a 1, T'⟩ =
            some ⟨at_ prog a 1, Function.update T' (reg N r)
              (((T' (reg N r)).write .blank).move .right)⟩ := by
          rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := .blank)
            (d := .right) (by simp only [instrStep, hnb, ite_false])]
          simp
        have hlen : j < (List.replicate j Sym.blank ++ (enc w).drop j).length := by
          simp [enc]; omega
        have hT2 := (hT'.write_set hlen Sym.blank).right
        rw [erase_cells w hjn] at hT2
        obtain ⟨t, ht, hrun⟩ := ih (j + 1)
          (Function.update T' (reg N r) (((T' (reg N r)).write .blank).move .right))
          (by omega) (by rw [Function.update_self]; exact hT2)
        refine ⟨t, ht, ?_⟩
        rw [Function.update_idem] at hrun
        exact ((RunsIn.single hst).trans hrun).mono (by omega)
  obtain ⟨t1, ht1, hrun1⟩ := loop w.length 0
    (Function.update T (reg N r) ((T (reg N r)).move .right)) (by omega)
    (by rw [Function.update_self]; simpa using hT.right)
  -- rewinding
  obtain ⟨t2, ht2, hrun2⟩ := rewind_runs (q := at_ prog a 2) (X := at_ prog (a + 1) 0)
    (k := reg N r)
    (fun T' hm => stepAt_stay ha (by norm_num) (by simp only [instrStep, hm, ite_true]))
    (fun T' hm => by
      rw [stepAt_one ha (by norm_num) (q := at_ prog a 2) (k := reg N r) (x := (T' (reg N r)).head)
        (d := .left) (by simp only [instrStep, hm, ite_false])]
      simp [Turing.Tape.write_self])
    (cells := List.replicate w.length .blank) (by intro c hc; rw [List.eq_of_mem_replicate hc]; decide)
    w.length (Function.update (Function.update T (reg N r) ((T (reg N r)).move .right)) (reg N r) t1)
    (by rw [Function.update_self]; exact ht1)
  refine ⟨t2, ht2.congr_cells (by
    rw [show List.replicate w.length Sym.blank = [] ++ List.replicate w.length Sym.blank from rfl,
      cellAt_append_blank]; rfl), ?_⟩
  simp only [Function.update_idem] at hrun2 hrun1
  have hall := ((RunsIn.single s0).trans hrun1).trans hrun2
  exact hall.mono (by omega)

/-- **Scanning right** over the bits of a register until the blank after them. -/
theorem scan_runs {q X : St prog} {k : Option (Fin N)} {f : Turing.Tape Sym → Turing.Tape Sym}
    (hb : ∀ T' : Option (Fin N) → Turing.Tape Sym, (T' k).head = .blank →
      (machine prog N).step ⟨q, T'⟩ = some ⟨X, Function.update T' k (f (T' k))⟩)
    (hn : ∀ T' : Option (Fin N) → Turing.Tape Sym, (T' k).head ≠ .blank →
      (machine prog N).step ⟨q, T'⟩ = some ⟨q, Function.update T' k ((T' k).move .right)⟩)
    (w : Word) : ∀ (d j : ℕ) (T' : Option (Fin N) → Turing.Tape Sym), j + d = w.length →
      RepT (T' k) (enc w) (j + 1) →
      ∃ u, RepT u (enc w) (w.length + 1) ∧
        RunsIn (machine prog N).step ⟨q, T'⟩ ⟨X, Function.update T' k (f u)⟩ (d + 1) := by
  intro d
  induction d with
  | zero =>
      intro j T' hj hT'
      have hjn : j = w.length := by omega
      subst hjn
      have hblank : (T' k).head = .blank := by
        rw [hT'.head]; push_cast; exact cellAt_enc_end w _ le_rfl
      exact ⟨T' k, hT', RunsIn.single (hb T' hblank)⟩
  | succ d ih =>
      intro j T' hj hT'
      have hjn : j < w.length := by omega
      have hnb : (T' k).head ≠ .blank := by
        rw [hT'.head]; push_cast; rw [cellAt_enc_pos w j hjn]; exact bitSym_ne_blank _
      obtain ⟨u, hu, hrun⟩ := ih (j + 1) (Function.update T' k ((T' k).move .right)) (by omega)
        (by rw [Function.update_self]; exact hT'.right)
      refine ⟨u, hu, ?_⟩
      rw [Function.update_idem] at hrun
      exact ((RunsIn.single (hn T' hnb)).trans hrun).mono (by omega)

theorem rewind_at {a m : ℕ} {I : LInstr} (ha : prog[a]? = some I) (hm : m < 5) {X : St prog}
    {r : ℕ}
    (hI : ∀ h : Option (Fin N) → Sym, instrStep prog N I a m h =
      if h (reg N r) = .mark then some (X, h, stays N)
      else one prog N (at_ prog a m) h (reg N r) (h (reg N r)) .left)
    {cells : List Sym} (hc : NoMark cells) (i : ℕ) (T : Option (Fin N) → Turing.Tape Sym)
    (hT : RepT (T (reg N r)) cells i) :
    ∃ t, RepT t cells 0 ∧ RunsIn (machine prog N).step ⟨at_ prog a m, T⟩
      ⟨X, Function.update T (reg N r) t⟩ (i + 1) :=
  rewind_runs (q := at_ prog a m) (X := X) (k := reg N r)
    (fun T' hmk => stepAt_stay ha hm (by rw [hI, ite_eq_left hmk]))
    (fun T' hmk => by
      rw [stepAt_one ha hm (q := at_ prog a m) (k := reg N r) (x := (T' (reg N r)).head)
        (d := .left) (by rw [hI, ite_eq_right hmk])]
      simp [Turing.Tape.write_self])
    hc i T hT

/-- **Appending a bit** takes `2 |w| + 3` steps. -/
theorem run_pushI {a r : ℕ} {b : Bool} (ha : prog[a]? = some (.push r b))
    (T : Option (Fin N) → Turing.Tape Sym) (w : Word) (hT : RepT (T (reg N r)) (enc w) 0) :
    ∃ t, RepT t (enc (w ++ [b])) 0 ∧ RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩
      ⟨at_ prog (a + 1) 0, Function.update T (reg N r) t⟩ (2 * w.length + 3) := by
  have s0 : (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog a 1, Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
    rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T (reg N r)).head)
      (d := .right) rfl]
    simp [Turing.Tape.write_self]
  obtain ⟨u, hu, hrun1⟩ := scan_runs (q := at_ prog a 1) (X := at_ prog a 2) (k := reg N r)
    (f := fun t => (t.write (bitSym b)).move .left)
    (fun T' hbl => by
      rw [stepAt_one ha (by norm_num) (q := at_ prog a 2) (k := reg N r) (x := bitSym b)
        (d := .left) (by simp only [instrStep, hbl, ite_true])]
      simp)
    (fun T' hbl => by
      rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T' (reg N r)).head)
        (d := .right) (by simp only [instrStep, hbl, ite_false])]
      simp [Turing.Tape.write_self])
    w w.length 0 (Function.update T (reg N r) ((T (reg N r)).move .right)) (by omega)
    (by rw [Function.update_self]; simpa using hT.right)
  have hu2 : RepT ((u.write (bitSym b)).move .left) (enc (w ++ [b])) w.length := by
    have := (RepT.write_end (cells := enc w) (by simpa [enc] using hu) (bitSym b)).left
    simpa [enc] using this
  obtain ⟨t, ht, hrun2⟩ := rewind_at (m := 2) (X := at_ prog (a + 1) 0) (r := r) ha (by norm_num)
    (fun h => rfl) (noMark_enc _) w.length
    (Function.update (Function.update T (reg N r) ((T (reg N r)).move .right)) (reg N r)
      ((u.write (bitSym b)).move .left))
    (by rw [Function.update_self]; exact hu2)
  refine ⟨t, ht, ?_⟩
  simp only [Function.update_idem] at hrun1 hrun2
  have hall := ((RunsIn.single s0).trans hrun1).trans hrun2
  exact hall.mono (by omega)

/-- Moving one cell right. -/
theorem run_advI {a r : ℕ} (ha : prog[a]? = some (.adv r)) (T : Option (Fin N) → Turing.Tape Sym) :
    (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog (a + 1) 0, Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
  rw [stepAt_one ha (by norm_num) (q := at_ prog (a + 1) 0) (k := reg N r)
    (x := (T (reg N r)).head) (d := .right) rfl]
  simp [Turing.Tape.write_self]

/-- Moving one cell left. -/
theorem run_retreatI {a r : ℕ} (ha : prog[a]? = some (.retreat r))
    (T : Option (Fin N) → Turing.Tape Sym) :
    (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog (a + 1) 0, Function.update T (reg N r) ((T (reg N r)).move .left)⟩ := by
  rw [stepAt_one ha (by norm_num) (q := at_ prog (a + 1) 0) (k := reg N r)
    (x := (T (reg N r)).head) (d := .left) rfl]
  simp [Turing.Tape.write_self]

/-- Moving to the last bit takes `|w| + 2` steps. -/
theorem run_toEndI {a r : ℕ} (ha : prog[a]? = some (.toEnd r))
    (T : Option (Fin N) → Turing.Tape Sym) (w : Word) (hT : RepT (T (reg N r)) (enc w) 0) :
    ∃ t, RepT t (enc w) w.length ∧ RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩
      ⟨at_ prog (a + 1) 0, Function.update T (reg N r) t⟩ (w.length + 2) := by
  have s0 : (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog a 1, Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
    rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T (reg N r)).head)
      (d := .right) rfl]
    simp [Turing.Tape.write_self]
  obtain ⟨u, hu, hrun1⟩ := scan_runs (q := at_ prog a 1) (X := at_ prog (a + 1) 0) (k := reg N r)
    (f := fun t => (t.write .blank).move .left)
    (fun T' hbl => by
      rw [stepAt_one ha (by norm_num) (q := at_ prog (a + 1) 0) (k := reg N r) (x := .blank)
        (d := .left) (by simp only [instrStep, hbl, ite_true])]
      simp)
    (fun T' hbl => by
      rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T' (reg N r)).head)
        (d := .right) (by simp only [instrStep, hbl, ite_false])]
      simp [Turing.Tape.write_self])
    w w.length 0 (Function.update T (reg N r) ((T (reg N r)).move .right)) (by omega)
    (by rw [Function.update_self]; simpa using hT.right)
  refine ⟨(u.write .blank).move .left, ?_, ?_⟩
  · have hb : u.head = .blank := by rw [hu.head]; push_cast; exact cellAt_enc_end w _ le_rfl
    rw [← hb, Turing.Tape.write_self]
    exact hu.left
  · simp only [Function.update_idem] at hrun1
    exact ((RunsIn.single s0).trans hrun1).mono (by omega)

/-- **The rewinding instruction** takes `i + 1` steps from position `i`. -/
theorem run_rewindI {a r : ℕ} (ha : prog[a]? = some (.rewind r)) {cells : List Sym}
    (hc : NoMark cells) (i : ℕ) (T : Option (Fin N) → Turing.Tape Sym)
    (hT : RepT (T (reg N r)) cells i) :
    ∃ t, RepT t cells 0 ∧ RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩
      ⟨at_ prog (a + 1) 0, Function.update T (reg N r) t⟩ (i + 1) :=
  rewind_at (X := at_ prog (a + 1) 0) ha (by norm_num) (fun h => rfl) hc i T hT

theorem run_branchI_bit {a r tEnd t₀ t₁ : ℕ} (ha : prog[a]? = some (.branch r tEnd t₀ t₁))
    (T : Option (Fin N) → Turing.Tape Sym) (b : Bool) (hb : (T (reg N r)).head = bitSym b) :
    (machine prog N).step ⟨at_ prog a 0, T⟩ = some ⟨at_ prog (bif b then t₁ else t₀) 0, T⟩ :=
  stepAt_stay ha (by norm_num) (by cases b <;> simp [instrStep, hb, bitSym])

theorem run_branchI_end {a r tEnd t₀ t₁ : ℕ} (ha : prog[a]? = some (.branch r tEnd t₀ t₁))
    (T : Option (Fin N) → Turing.Tape Sym)
    (hb : (T (reg N r)).head = .blank ∨ (T (reg N r)).head = .mark) :
    (machine prog N).step ⟨at_ prog a 0, T⟩ = some ⟨at_ prog tEnd 0, T⟩ :=
  stepAt_stay ha (by norm_num) (by rcases hb with hb | hb <;> simp [instrStep, hb])

theorem run_jmpI {a t : ℕ} (ha : prog[a]? = some (.jmp t)) (T : Option (Fin N) → Turing.Tape Sym) :
    (machine prog N).step ⟨at_ prog a 0, T⟩ = some ⟨at_ prog t 0, T⟩ :=
  stepAt_stay ha (by norm_num) rfl

/-- **The final test** halts in two steps, accepting iff the register is not empty. -/
theorem run_testI {a r : ℕ} (ha : prog[a]? = some (.test r)) (T : Option (Fin N) → Turing.Tape Sym)
    (w : Word) (hT : RepT (T (reg N r)) (enc w) 0) :
    ∃ T', RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩ ⟨.inr (decide (w ≠ [])), T'⟩ 2 := by
  have s0 : (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog a 1, Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
    rw [stepAt_one ha (by norm_num) (q := at_ prog a 1) (k := reg N r) (x := (T (reg N r)).head)
      (d := .right) rfl]
    simp [Turing.Tape.write_self]
  have hh : ((T (reg N r)).move .right).head ≠ .blank ↔ w ≠ [] := by
    rw [hT.right.head]
    cases w with
    | nil =>
        have h1 : cellAt (enc []) 1 = .blank := by simpa using cellAt_enc_end [] 0 (le_refl _)
        simp [h1]
    | cons b w' =>
        have h1 : cellAt (enc (b :: w')) ((0 : ℕ) + 1 : ℕ) = bitSym b := by
          have := cellAt_enc_pos (b :: w') 0 (by simp)
          simpa using this
        rw [h1]
        simpa using bitSym_ne_blank' b
  have s1 : (machine prog N).step ⟨at_ prog a 1,
      Function.update T (reg N r) ((T (reg N r)).move .right)⟩ =
      some ⟨.inr (decide (w ≠ [])), Function.update T (reg N r) ((T (reg N r)).move .right)⟩ := by
    refine stepAt_stay ha (by norm_num) ?_
    simp only [instrStep, Function.update_self]
    congr 3
    exact decide_eq_decide.mpr hh
  exact ⟨_, (RunsIn.single s0).trans (RunsIn.single s1)⟩

/-- The list identity behind erasing the tail of a register. -/
theorem erase_tail (P L : List Sym) (k j : ℕ) (hj : j < L.length) :
    (P ++ (List.replicate k Sym.blank ++ L.drop j)).set (P.length + k) Sym.blank =
      P ++ (List.replicate (k + 1) Sym.blank ++ L.drop (j + 1)) := by
  rw [List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.drop_eq_getElem_cons hj, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

/-- **Truncating `r` to the length of `s`** takes at most `3 (|r| + |s|) + 8` steps; the other
tapes are left alone. -/
theorem run_truncI {a r s : ℕ} (ha : prog[a]? = some (.trunc r s)) (hrs : reg N r ≠ reg N s)
    (T : Option (Fin N) → Turing.Tape Sym) (wr ws : Word)
    (hr : RepT (T (reg N r)) (enc wr) 0) (hs : RepT (T (reg N s)) (enc ws) 0) :
    ∃ T', RepT (T' (reg N r)) (enc (wr.take ws.length)) 0 ∧ RepT (T' (reg N s)) (enc ws) 0 ∧
      (∀ x, x ≠ reg N r → x ≠ reg N s → T' x = T x) ∧
      RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩ ⟨at_ prog (a + 1) 0, T'⟩
        (3 * (wr.length + ws.length) + 8) := by
  set m := min wr.length ws.length with hm
  -- the first move
  have s0 : (machine prog N).step ⟨at_ prog a 0, T⟩ =
      some ⟨at_ prog a 1, Function.update (Function.update T (reg N r) ((T (reg N r)).move .right))
        (reg N s) ((T (reg N s)).move .right)⟩ := by
    rw [stepAt_two ha (by norm_num) (q := at_ prog a 1) (k₁ := reg N r) (k₂ := reg N s)
      (d₁ := .right) (d₂ := .right) hrs rfl]
    simp
  set T1 := Function.update (Function.update T (reg N r) ((T (reg N r)).move .right))
    (reg N s) ((T (reg N s)).move .right)
  have hT1r : T1 (reg N r) = (T (reg N r)).move .right := by
    simp only [T1]; rw [Function.update_of_ne hrs, Function.update_self]
  have hT1s : T1 (reg N s) = (T (reg N s)).move .right := by simp only [T1]; rw [Function.update_self]
  have hT1x : ∀ x, x ≠ reg N r → x ≠ reg N s → T1 x = T x := fun x h1 h2 => by
    simp only [T1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
  -- the lockstep loop
  have lock : ∀ d j (T' : Option (Fin N) → Turing.Tape Sym), j + d = m →
      RepT (T' (reg N r)) (enc wr) (j + 1) → RepT (T' (reg N s)) (enc ws) (j + 1) →
      ∃ T'', RepT (T'' (reg N r)) (enc wr) (m + 1) ∧ RepT (T'' (reg N s)) (enc ws) (m + 1) ∧
        (∀ x, x ≠ reg N r → x ≠ reg N s → T'' x = T' x) ∧
        RunsIn (machine prog N).step ⟨at_ prog a 1, T'⟩
          ⟨if ws.length ≤ wr.length then at_ prog a 2 else at_ prog a 3, T''⟩ (d + 1) := by
    intro d
    induction d with
    | zero =>
        intro j T' hj hr' hs'
        have hjm : j = m := by omega
        subst hjm
        refine ⟨T', hr', hs', fun _ _ _ => rfl, ?_⟩
        by_cases hle : ws.length ≤ wr.length
        · have hsb : (T' (reg N s)).head = .blank := by
            rw [hs'.head]; push_cast; exact cellAt_enc_end ws _ (by omega)
          rw [ite_eq_left hle]
          exact RunsIn.single (stepAt_stay ha (by norm_num) (by simp only [instrStep, hsb, ite_true]))
        · have hsn : (T' (reg N s)).head ≠ .blank := by
            rw [hs'.head]; push_cast; rw [cellAt_enc_pos ws _ (by omega)]; exact bitSym_ne_blank' _
          have hrb : (T' (reg N r)).head = .blank := by
            rw [hr'.head]; push_cast; exact cellAt_enc_end wr _ (by omega)
          rw [ite_eq_right hle]
          exact RunsIn.single (stepAt_stay ha (by norm_num)
            (by simp only [instrStep, hsn, hrb, ite_true, ite_false]))
    | succ d ih =>
        intro j T' hj hr' hs'
        have hsn : (T' (reg N s)).head ≠ .blank := by
          rw [hs'.head]; push_cast; rw [cellAt_enc_pos ws _ (by omega)]; exact bitSym_ne_blank' _
        have hrn : (T' (reg N r)).head ≠ .blank := by
          rw [hr'.head]; push_cast; rw [cellAt_enc_pos wr _ (by omega)]; exact bitSym_ne_blank' _
        set T2 := Function.update (Function.update T' (reg N r) ((T' (reg N r)).move .right))
          (reg N s) ((T' (reg N s)).move .right)
        have hst : (machine prog N).step ⟨at_ prog a 1, T'⟩ = some ⟨at_ prog a 1, T2⟩ := by
          rw [stepAt_two ha (by norm_num) (q := at_ prog a 1) (k₁ := reg N r) (k₂ := reg N s)
            (d₁ := .right) (d₂ := .right) hrs (by simp only [instrStep, hsn, hrn, ite_false])]
          simp [T2]
        obtain ⟨T'', h1, h2, h3, hrun⟩ := ih (j + 1) T2 (by omega)
          (by simp only [T2]; rw [Function.update_of_ne hrs, Function.update_self]; exact hr'.right)
          (by simp only [T2]; rw [Function.update_self]; exact hs'.right)
        refine ⟨T'', h1, h2, fun x hx1 hx2 => ?_, ((RunsIn.single hst).trans hrun).mono (by omega)⟩
        rw [h3 x hx1 hx2]
        simp only [T2]; rw [Function.update_of_ne hx2, Function.update_of_ne hx1]
  obtain ⟨T3, h3r, h3s, h3x, hrun1⟩ := lock m 0 T1 (by omega)
    (by rw [hT1r]; simpa using hr.right) (by rw [hT1s]; simpa using hs.right)
  -- erasing the tail, when `s` is not longer than `r`
  have erase : ws.length ≤ wr.length → ∀ d j (T' : Option (Fin N) → Turing.Tape Sym),
      ws.length ≤ j → j + d = wr.length →
      RepT (T' (reg N r)) ((enc wr).take ws.length ++
        (List.replicate (j - ws.length) Sym.blank ++ (enc wr).drop j)) (j + 1) →
      ∃ T'', RepT (T'' (reg N r)) (enc (wr.take ws.length)) (wr.length + 1) ∧
        (∀ x, x ≠ reg N r → T'' x = T' x) ∧
        RunsIn (machine prog N).step ⟨at_ prog a 2, T'⟩ ⟨at_ prog a 3, T''⟩ (d + 1) := by
    intro hle d
    induction d with
    | zero =>
        intro j T' hj1 hj2 hT'
        have hjw : j = wr.length := by omega
        subst hjw
        rw [List.drop_eq_nil_of_le (by simp [enc]), List.append_nil] at hT'
        refine ⟨T', ?_, fun _ _ => rfl, ?_⟩
        · refine hT'.congr_cells ?_
          rw [cellAt_append_blank, enc, enc, List.map_take]
        · have hb : (T' (reg N r)).head = .blank := by
            rw [hT'.head, cellAt_append_blank]
            push_cast
            rw [cellAt_succ]
            unfold cellN
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [enc])]
            rfl
          exact RunsIn.single (stepAt_stay ha (by norm_num) (by simp only [instrStep, hb, ite_true]))
    | succ d ih =>
        intro j T' hj1 hj2 hT'
        have hjw : j < wr.length := by omega
        have hlenP : ((enc wr).take ws.length).length = ws.length := by simp [enc]; omega
        have hb : (T' (reg N r)).head = bitSym wr[j] := by
          rw [hT'.head]; push_cast
          rw [cellAt_succ]
          unfold cellN
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenP,
            List.getElem?_append_right (by simp), List.length_replicate,
            show j - ws.length - (j - ws.length) = 0 by omega, List.getElem?_drop, Nat.add_zero]
          simp [enc, hjw]
        have hnb : (T' (reg N r)).head ≠ .blank := by rw [hb]; exact bitSym_ne_blank' _
        set T2 := Function.update T' (reg N r) (((T' (reg N r)).write .blank).move .right)
        have hst : (machine prog N).step ⟨at_ prog a 2, T'⟩ = some ⟨at_ prog a 2, T2⟩ := by
          rw [stepAt_one ha (by norm_num) (q := at_ prog a 2) (k := reg N r) (x := .blank)
            (d := .right) (by simp only [instrStep, hnb, ite_false])]
          simp [T2]
        have hlen : j < ((enc wr).take ws.length ++
            (List.replicate (j - ws.length) Sym.blank ++ (enc wr).drop j)).length := by
          simp [enc]; omega
        have hT2 := (hT'.write_set hlen Sym.blank).right
        have heq := erase_tail ((enc wr).take ws.length) (enc wr) (j - ws.length) j
          (by simp [enc]; omega)
        rw [hlenP, show ws.length + (j - ws.length) = j by omega] at heq
        rw [heq, show j - ws.length + 1 = j + 1 - ws.length by omega] at hT2
        obtain ⟨T'', h1, h2, hrun⟩ := ih (j + 1) T2 (by omega) (by omega)
          (by simp only [T2]; rw [Function.update_self]; exact hT2)
        refine ⟨T'', h1, fun x hx => ?_, ((RunsIn.single hst).trans hrun).mono (by omega)⟩
        rw [h2 x hx]; simp only [T2]; rw [Function.update_of_ne hx]
  -- reaching state 3 with `r` at position `|r| + 1`
  have h3 : ∃ T4, RepT (T4 (reg N r)) (enc (wr.take ws.length)) (wr.length + 1) ∧
      RepT (T4 (reg N s)) (enc ws) (m + 1) ∧ (∀ x, x ≠ reg N r → x ≠ reg N s → T4 x = T x) ∧
      RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩ ⟨at_ prog a 3, T4⟩
        (1 + (m + 1) + (wr.length - ws.length + 1)) := by
    by_cases hle : ws.length ≤ wr.length
    · rw [ite_eq_left hle] at hrun1
      have hmw : m = ws.length := by omega
      obtain ⟨T4, h4r, h4x, hrun2⟩ := erase hle (wr.length - ws.length) ws.length T3 le_rfl
        (by omega)
        (by rw [Nat.sub_self, List.replicate_zero, List.nil_append, List.take_append_drop]
            rw [hmw] at h3r; exact h3r)
      refine ⟨T4, h4r, by rw [h4x _ (Ne.symm hrs)]; exact h3s, fun x h1 h2 => ?_,
        (((RunsIn.single s0).trans hrun1).trans hrun2).mono (by omega)⟩
      rw [h4x x h1, h3x x h1 h2, hT1x x h1 h2]
    · rw [ite_eq_right hle] at hrun1
      have hmw : m = wr.length := by omega
      refine ⟨T3, ?_, h3s, fun x h1 h2 => by rw [h3x x h1 h2, hT1x x h1 h2],
        ((RunsIn.single s0).trans hrun1).mono (by omega)⟩
      rw [List.take_of_length_le (by omega)]; rw [hmw] at h3r; exact h3r
  obtain ⟨T4, h4r, h4s, h4x, hrun3⟩ := h3
  -- rewinding both
  obtain ⟨tr, htr, hrun4⟩ := rewind_at (m := 3) (X := at_ prog a 4) (r := r) ha (by norm_num)
    (fun h => rfl) (noMark_enc _) (wr.length + 1) T4 h4r
  obtain ⟨ts, hts, hrun5⟩ := rewind_at (m := 4) (X := at_ prog (a + 1) 0) (r := s) ha (by norm_num)
    (fun h => rfl) (noMark_enc _) (m + 1) (Function.update T4 (reg N r) tr)
    (by rw [Function.update_of_ne hrs.symm]; exact h4s)
  refine ⟨Function.update (Function.update T4 (reg N r) tr) (reg N s) ts, ?_, ?_, ?_,
    ((hrun3.trans hrun4).trans hrun5).mono (by omega)⟩
  · rw [Function.update_of_ne hrs, Function.update_self]; exact htr
  · rw [Function.update_self]; exact hts
  · intro x h1 h2
    rw [Function.update_of_ne h2, Function.update_of_ne h1, h4x x h1 h2]

theorem default_sym : (default : Sym) = .blank := rfl

theorem mk₁_nth' (l : List Sym) (z : ℤ) :
    (Turing.Tape.mk₁ l).nth z = if 0 ≤ z then l.getI z.toNat else default := by
  cases z with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
      exact Turing.Tape.mk'_nth_nat _ _ n
  | negSucc n =>
      simp only [Int.negSucc_not_nonneg, ite_false]
      rfl

theorem reg_zero (hN : 0 < N) : reg N 0 = some ⟨0, hN⟩ := by simp [reg, hN]

theorem reg_ne_none {r : ℕ} (hr : r < N) : reg N r ≠ none := by simp [reg, hr]

theorem reg_injective {r s : ℕ} (hr : r < N) (hs : s < N) (h : reg N r = reg N s) : r = s := by
  simp only [reg, hr, hs, dite_true, Option.some.injEq, Fin.mk.injEq] at h
  exact h

/-- The input tape after `j` steps of copying. -/
def RepIn (T : Turing.Tape Sym) (x : Word) (j : ℕ) : Prop :=
  ∀ z : ℤ, T.nth (z - j) = if 0 ≤ z then (enc x).getI z.toNat else .blank

/-- **The initialisation** marks the register tapes and copies the input into register `0`, in
`2 |x| + 4` steps. -/
theorem run_initI (h0 : prog[0]? = some .init) (hN : 0 < N) (x : Word) :
    ∃ T', RepT (T' (reg N 0)) (enc x) 0 ∧ (∀ r, r < N → r ≠ 0 → RepT (T' (reg N r)) (enc []) 0) ∧
      RunsIn (machine prog N).step ⟨at_ prog 0 0, ((machine prog N).init x).tapes⟩
        ⟨at_ prog 1 0, T'⟩ (2 * x.length + 4) := by
  set T0 := ((machine prog N).init x).tapes
  have hT0in : T0 none = Turing.Tape.mk₁ (enc x) := by
    simp [T0, FiniteMultiTapeMachine.init, enc]
  have hT0reg : ∀ r, r < N → T0 (reg N r) = Turing.Tape.mk₁ [] := fun r hr => by
    simp only [T0, FiniteMultiTapeMachine.init]
    rw [ite_eq_right (reg_ne_none hr)]
  -- marking
  set T1 : Option (Fin N) → Turing.Tape Sym := fun k => match k with
    | none => T0 none
    | some _ => (T0 k).write .mark
  have s0 : (machine prog N).step ⟨at_ prog 0 0, T0⟩ = some ⟨at_ prog 0 1, T1⟩ := by
    show multiTapeStep (code prog N) _ = _
    rw [multiTapeStep_eq_some (by rw [code_at prog N h0 (by norm_num)]; rfl)]
    simp only [multiTapeUpdate, stays, HeadMove.apply_stay]
    congr 2
    funext k
    cases k with
    | none => simp [T1, Turing.Tape.write_self]
    | some f => rfl
  have hT1reg : ∀ r, r < N → RepT (T1 (reg N r)) [] 0 := fun r hr => by
    have e : T1 (reg N r) = (Turing.Tape.mk₁ []).write .mark := by
      simp only [T1, reg, hr, dite_true]
      rw [← hT0reg r hr]; simp [reg, hr]
    intro z
    rw [e, Turing.Tape.write_nth, Nat.cast_zero, sub_zero]
    by_cases hz : z = 0
    · subst hz; simp [cellAt]
    · rw [ite_eq_right hz, mk₁_nth']
      unfold cellAt
      rw [ite_eq_right hz]
      split <;> split <;> simp_all [default_sym]
  have hT1in : T1 none = Turing.Tape.mk₁ (enc x) := by simp [T1, hT0in]
  -- moving register 0 right
  set T2 := Function.update T1 (reg N 0) ((T1 (reg N 0)).move .right)
  have s1 : (machine prog N).step ⟨at_ prog 0 1, T1⟩ = some ⟨at_ prog 0 2, T2⟩ := by
    rw [stepAt_one h0 (by norm_num) (q := at_ prog 0 2) (k := reg N 0) (x := (T1 (reg N 0)).head)
      (d := .right) rfl]
    simp [T2, Turing.Tape.write_self]
  -- copying
  have copy : ∀ d j (T' : Option (Fin N) → Turing.Tape Sym), j + d = x.length →
      RepT (T' (reg N 0)) (enc (x.take j)) (j + 1) → RepIn (T' none) x j →
      ∃ T'', RepT (T'' (reg N 0)) (enc x) x.length ∧
        (∀ k, k ≠ reg N 0 → k ≠ none → T'' k = T' k) ∧
        RunsIn (machine prog N).step ⟨at_ prog 0 2, T'⟩ ⟨at_ prog 0 3, T''⟩ (d + 1) := by
    intro d
    induction d with
    | zero =>
        intro j T' hj h0' hin
        have hjx : j = x.length := by omega
        subst hjx
        rw [List.take_length] at h0'
        have hblank : (T' none).head = .blank := by
          have := hin x.length
          rw [sub_self, Turing.Tape.nth_zero, ite_eq_left (by omega)] at this
          rw [this]; simp [List.getI_eq_default, enc, default_sym]
        refine ⟨Function.update T' (reg N 0) ((T' (reg N 0)).move .left), ?_,
          fun k hk _ => by rw [Function.update_of_ne hk], RunsIn.single ?_⟩
        · rw [Function.update_self]; exact h0'.left
        · rw [stepAt_one h0 (by norm_num) (q := at_ prog 0 3) (k := reg N 0)
            (x := (T' (reg N 0)).head) (d := .left) (by simp only [instrStep, hblank, ite_true])]
          simp [Turing.Tape.write_self]
    | succ d ih =>
        intro j T' hj h0' hin
        have hjx : j < x.length := by omega
        have hbit : (T' none).head = bitSym x[j] := by
          have := hin j
          rw [sub_self, Turing.Tape.nth_zero, ite_eq_left (by omega)] at this
          rw [this]; simp [enc, List.getI_eq_getElem _ (show j < (x.map bitSym).length by simpa)]
        have hnb : (T' none).head ≠ .blank := by rw [hbit]; exact bitSym_ne_blank' _
        have hne : reg N 0 ≠ none := reg_ne_none hN
        set T3 := Function.update (Function.update T' (reg N 0)
          (((T' (reg N 0)).write (bitSym x[j])).move .right)) none ((T' none).move .right)
        have hst : (machine prog N).step ⟨at_ prog 0 2, T'⟩ = some ⟨at_ prog 0 2, T3⟩ := by
          rw [step_wtwo prog N (c := ⟨at_ prog 0 2, T'⟩) (q := at_ prog 0 2) (k₁ := reg N 0)
            (k₂ := none) (a := (T' none).head) (d₁ := .right) (d₂ := .right) hne (by
              show code prog N (at_ prog 0 2) _ = _
              rw [code_at prog N h0 (by norm_num)]
              simp only [instrStep, hnb, ite_false])]
          rw [hbit]
          rfl
        have hcells : enc (x.take j) ++ [bitSym x[j]] = enc (x.take (j + 1)) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjx, Option.toList_some]
          simp only [enc, List.map_append, List.map_cons, List.map_nil]
        have hlen : (enc (x.take j)).length = j := by simp [enc]; omega
        obtain ⟨T'', h1, h2, hrun⟩ := ih (j + 1) T3 (by omega)
          (by
            simp only [T3]
            rw [Function.update_of_ne hne, Function.update_self]
            have := (RepT.write_end (cells := enc (x.take j)) (by rw [hlen]; exact h0')
              (bitSym x[j])).right
            rw [hcells, hlen] at this
            exact this)
          (by
            simp only [T3]; rw [Function.update_self]
            intro z
            rw [Turing.Tape.move_right_nth, ← hin z]
            congr 1; push_cast; ring)
        refine ⟨T'', h1, fun k hk1 hk2 => ?_, ((RunsIn.single hst).trans hrun).mono (by omega)⟩
        rw [h2 k hk1 hk2]
        simp only [T3]; rw [Function.update_of_ne hk2, Function.update_of_ne hk1]
  obtain ⟨T4, h4, h4x, hrun2⟩ := copy x.length 0 T2 (by omega)
    (by simp only [T2]; rw [Function.update_self]; simpa [enc] using (hT1reg 0 hN).right)
    (by
      simp only [T2]; rw [Function.update_of_ne (reg_ne_none hN).symm, hT1in]
      intro z; rw [Nat.cast_zero, sub_zero, mk₁_nth']; rfl)
  -- rewinding register 0
  obtain ⟨t, ht, hrun3⟩ := rewind_at (m := 3) (X := at_ prog 1 0) (r := 0) h0 (by norm_num)
    (fun h => rfl) (noMark_enc _) x.length T4 h4
  refine ⟨Function.update T4 (reg N 0) t, by rw [Function.update_self]; exact ht,
    fun r hr hr0 => ?_, ((((RunsIn.single s0).trans (RunsIn.single s1)).trans hrun2).trans
      hrun3).mono (by omega)⟩
  have hne0 : reg N r ≠ reg N 0 := fun h => hr0 (reg_injective hr hN h)
  rw [Function.update_of_ne hne0, h4x _ hne0 (reg_ne_none hr)]
  simp only [T2]; rw [Function.update_of_ne hne0]
  exact hT1reg r hr

end Runs

end CobMT

end Complexity
