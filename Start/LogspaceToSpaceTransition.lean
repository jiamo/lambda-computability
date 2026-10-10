import Start.LogspaceToSpaceStep

/-!
# Simulating an `ExactDerandomization` machine by a host tape program: one whole transition

This library's own module (task `M27-SPACE-MODEL-COMPILE`, the upstream-to-host direction).
`FromLogspace.stepProg M` is a tape program of `Start/SpaceProg.lean` that carries out one
transition of a machine `M` of `Start/LogspaceDeterministic.lean` on the register file
`FromLogspace.encR` of `Start/LogspaceToSpace.lean`:

1. it branches on the unary control state (`Tracks.caseUnary`);
2. it reads the symbol under every input head: the head position is a bijective base-two counter,
   and `Tracks.readSym` moves the host input head there with `Tracks.seekCounter` and back;
   position `0` (the left end marker) is recognised by an empty counter (`FromLogspace.rdInput`);
3. it reads the bit under every work head, the last bit of the right register of the windowed
   tape (`FromLogspace.rdWork`);
4. at the leaf of this finite branching tree it runs the four phases of the transition found in
   the finite table `M.transition` (`FromLogspace.actProg`): write and move the work tapes, move
   the input heads, overwrite the state, update the flags.

The branching tree has one leaf for each control state and each tuple of symbols read; every leaf
is a fixed finite program, so the transition table is compiled into the host's finite control and
every host step is an ordinary step of a finite machine.

Main results:

* `FromLogspace.encC` — the register file of a configuration (`encR` of its components);
* `FromLogspace.runs_actProg` — the four phases, from `encC c` to `encC (M.step x b c)`;
* `FromLogspace.runs_stepProg` — **one full transition**: from `encC c` to
  `encC (M.step x false c)` (for every `c`; on a halted configuration the program does nothing,
  as `M.step` does);
* `FromLogspace.runs_stepProg_det` — the same for either coin, for a deterministic machine.

All specifications are `Complexity.Space.Prog.Runs` statements: every configuration on the way
uses at most `B` cells, where `B` is the explicit bound `(N + 3) (2 K + 1)` of the track layout.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace FromLogspace

open Tracks Prog
open ExactDerandomization (Word InputSymbol Direction Configuration readInput)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h)
variable {x : List Bool} {B : ℕ}

theorem wd_lt_of_hB {K N B : ℕ} (hB : (N + 3) * wd K ≤ B) : wd K < B := by
  have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
  have : 0 < wd K := by womega
  omega

/-! ### The register file of a configuration -/

/-- The input-head positions of a configuration, as a function on `ℕ` (`0` beyond `h`). -/
def posOf {n : ℕ} (c : Configuration q w h n) : ℕ → ℕ :=
  fun j => if hj : j < h then (c.inputPos ⟨j, hj⟩).val else 0

/-- The work tapes of a configuration, as a function on `ℕ` (blank beyond `w`). -/
def tpOf {n : ℕ} (c : Configuration q w h n) : ℕ → ℤ → Bool :=
  fun k => if hk : k < w then c.work ⟨k, hk⟩ else fun _ => false

/-- The work-head positions of a configuration, as a function on `ℕ` (`0` beyond `w`). -/
def hpOf {n : ℕ} (c : Configuration q w h n) : ℕ → ℤ :=
  fun k => if hk : k < w then c.workPos ⟨k, hk⟩ else 0

/-- The register file of a configuration, with the work tapes in the window `[-W, W]`. -/
def encC (W : ℤ) {n : ℕ} (c : Configuration q w h n) : ℕ → List Bool :=
  encR M W c.state c.state.val (posOf c) (tpOf c) (hpOf c)

theorem encR_congr (W : ℤ) (fs : Fin (q + 1)) (st : ℕ) {pos pos' : ℕ → ℕ}
    {tp tp' : ℕ → ℤ → Bool} {hp hp' : ℕ → ℤ}
    (hpos : ∀ j, j < h → pos j = pos' j) (htp : ∀ k, k < w → tp k = tp' k)
    (hhp : ∀ k, k < w → hp k = hp' k) :
    encR M W fs st pos tp hp = encR M W fs st pos' tp' hp' := by
  funext r
  simp only [encR]
  split_ifs <;> first
    | rfl
    | rw [hpos _ (by omega)]
    | rw [htp _ (by omega), hhp _ (by omega)]

/-! ### Reading the input symbols -/

/-- The input symbol of a bit or of the right end marker. -/
def symOf : Option Bool → InputSymbol
  | some b => .bit b
  | none => .rightMarker

/-- `readInput` on a natural-number position. -/
def readNat (x : Word) (p : ℕ) : InputSymbol := if p = 0 then .leftMarker else symOf x[p - 1]?

theorem readInput_eq (x : Word) (i : Fin (x.length + 2)) : readInput x i = readNat x i.val := by
  unfold readInput readNat
  split_ifs
  · rfl
  · cases x[i.val - 1]? <;> rfl

/-- Read the symbol under input head `j` (its position is the counter in register `rCnt j`) and
continue with `cont` applied to it; the scratch registers `3`, `4`, `5` are used and left empty. -/
def rdInput (K j : ℕ) (cont : InputSymbol → Prog) : Prog :=
  ifNE (rCnt j) (readSym K (rCnt j) 3 4 5 (fun o => cont (symOf o))) (cont .leftMarker)

theorem runs_rdInput {K : ℕ} (R : ℕ → List Bool) (j : ℕ) (hj : rCnt j < K)
    (hR3 : R 3 = []) (hR4 : R 4 = []) (hR5 : R 5 = []) (p : ℕ) (hp : R (rCnt j) = bnum p)
    (hpn : p ≤ x.length + 1) (N : ℕ) (hB : (N + 3) * wd K ≤ B)
    (hN : (bnum p).length + 1 ≤ N) (cont : InputSymbol → Prog) (s' : TState)
    (hc : Runs x B (cont (readNat x p)) ⟨lay K R, 0, 0⟩ s') :
    Runs x B (rdInput K j cont) ⟨lay K R, 0, 0⟩ s' := by
  have h5 : 5 < K := by unfold rCnt at hj; omega
  refine runs_ifNE R (rCnt j) hj (wd_lt_of_hB hB) 0 _ _ s' (fun hne => ?_) (fun he => ?_)
  · have hp0 : p ≠ 0 := by rintro rfl; exact hne (by rw [hp]; rfl)
    refine runs_readSym R (rCnt j) 3 4 5 hj (by omega) (by omega) h5 (by unfold rCnt; omega)
      (by unfold rCnt; omega) (by unfold rCnt; omega) (by omega) (by omega) (by omega) hR3 hR4
      hR5 N hB (by rw [hp]; exact hN) (by rw [hp, bval_bnum]; omega) _ s' ?_
    rw [hp, bval_bnum]
    simpa [readNat, hp0] using hc
  · have hp0 : p = 0 := by
      have := congrArg bval hp
      rw [he, bval_bnum] at this
      exact this.symm
    subst hp0
    simpa [readNat] using hc

/-! ### Reading the work symbols -/

/-- Read the last bit of register `r` (restoring it) and continue with `cont` applied to it. -/
def rdWork (K r : ℕ) (cont : Bool → Prog) : Prog :=
  popBranch K r (.seq (append K r false) (cont false)) (.seq (append K r true) (cont true))

theorem runs_rdWork {K : ℕ} (R : ℕ → List Bool) (r : ℕ) (hr : r < K) (hne : R r ≠ []) (N : ℕ)
    (hN : (R r).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) (cont : Bool → Prog)
    (s' : TState) (hc : Runs x B (cont ((R r).getLast hne)) ⟨lay K R, 0, i⟩ s') :
    Runs x B (rdWork K r cont) ⟨lay K R, 0, i⟩ s' := by
  refine runs_popBranch R r hr hne N hN hB i _ _ s' ?_
  have hlen := List.length_pos_of_ne_nil hne
  have key : ∀ β, (R r).getLast hne = β →
      Runs x B (.seq (append K r β) (cont β))
        ⟨lay K (Function.update R r (R r).dropLast), 0, i⟩ s' := by
    intro β hβ
    subst hβ
    refine (runs_append (x := x) (B := B) (Function.update R r (R r).dropLast) r hr _ N
      (by simp; omega) hB i).seq ?_
    rw [Function.update_idem, Function.update_self, List.dropLast_append_getLast,
      Function.update_eq_self]
    exact hc
  by_cases hl : (R r).getLast hne = true
  · rw [if_pos hl]; exact key true hl
  · rw [if_neg hl]; exact key false (by simpa using hl)

/-! ### The four phases of a transition -/

/-- The four phases of the transition with action `a`, given the input symbols `sym` read. -/
def actProg (a : ExactDerandomization.Action q w h) (sym : ℕ → InputSymbol) : Prog :=
  .seq (tapesOp h w (fun k => if hk : k < w then a.write ⟨k, hk⟩ else false)
      (fun k => if hk : k < w then a.workMove ⟨k, hk⟩ else .stay))
    (.seq (headsOp h w (fun j => if hj : j < h then a.inputMove ⟨j, hj⟩ else .stay) sym)
      (.seq (setState (regK h w) a.nextState.val) (setFlags (regK h w) (M.output a.nextState))))

theorem step_of_none {x : Word} (b : Bool) (c : Configuration q w h x.length)
    (hout : M.output c.state = none) :
    M.step x b c =
      { state := (M.transition c.state (fun j => readInput x (c.inputPos j))
            (fun k => c.work k (c.workPos k)) b).nextState
        inputPos := fun j => ((M.transition c.state (fun j => readInput x (c.inputPos j))
            (fun k => c.work k (c.workPos k)) b).inputMove j).moveInput (c.inputPos j)
        workPos := fun k => ((M.transition c.state (fun j => readInput x (c.inputPos j))
            (fun k => c.work k (c.workPos k)) b).workMove k).move (c.workPos k)
        work := fun k => Function.update (c.work k) (c.workPos k)
            ((M.transition c.state (fun j => readInput x (c.inputPos j))
              (fun k => c.work k (c.workPos k)) b).write k) } := by
  simp [ExactDerandomization.Machine.step, hout]

theorem length_bnum_add_one_le {p n : ℕ} (hp : p ≤ n + 1) :
    (bnum p).length + 1 ≤ Nat.log 2 (n + 2) + 1 := by
  have := length_bnum_le p
  have : Nat.log 2 (p + 1) ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  omega

theorem runs_actProg (W : ℤ) (c : Configuration q w h x.length) (b : Bool)
    (hout : M.output c.state = none) (syms : ℕ → InputSymbol)
    (hsyms : ∀ j (hj : j < h), syms j = readInput x (c.inputPos ⟨j, hj⟩))
    (N : ℕ) (hB : (N + 3) * wd (regK h w) ≤ B) (hNW : (2 * W + 1).toNat ≤ N) (hNq : q + 1 ≤ N)
    (hNp : Nat.log 2 (x.length + 2) + 1 ≤ N)
    (hwin : ∀ k : Fin w, -W ≤ c.workPos k ∧ c.workPos k ≤ W ∧
      -W ≤ (M.step x b c).workPos k ∧ (M.step x b c).workPos k ≤ W) :
    Runs x B (actProg M (M.transition c.state (fun j => readInput x (c.inputPos j))
        (fun k => c.work k (c.workPos k)) b) syms)
      ⟨lay (regK h w) (encC M W c), 0, 0⟩ ⟨lay (regK h w) (encC M W (M.step x b c)), 0, 0⟩ := by
  have hst := step_of_none M b c hout
  set a := M.transition c.state (fun j => readInput x (c.inputPos j))
    (fun k => c.work k (c.workPos k)) b with ha
  set c' := M.step x b c with hc'
  unfold actProg encC
  refine (runs_tapesOp M W c.state c.state.val (posOf c) (tpOf c) (hpOf c) N hB (tpOf c')
    (hpOf c') _ _ ?_ ?_ ?_ hNW).seq ?_
  · intro k hk; simp [tpOf, hpOf, hk, hst]
  · intro k hk; simp [hpOf, hk, hst]
  · intro k hk
    have := hwin ⟨k, hk⟩
    simpa [hpOf, hk] using this
  refine (runs_headsOp M W c.state c.state.val (posOf c) (stg w (tpOf c') (tpOf c))
    (stg w (hpOf c') (hpOf c)) N hB (posOf c') _ syms ?_ ?_).seq ?_
  · intro j hj
    have hlt := (c.inputPos ⟨j, hj⟩).isLt
    rw [hsyms j hj]
    simp only [posOf, hj, dif_pos, hst]
    refine ⟨fun hd hs => ?_, fun hd hs => ?_, fun hd => ?_, fun hd => ?_⟩
    · rw [hd]
      simp only [Direction.moveInput]
      have : (c.inputPos ⟨j, hj⟩).val = x.length + 1 := by
        unfold readInput at hs
        split_ifs at hs with h0
        cases hx : x[(c.inputPos ⟨j, hj⟩).val - 1]? with
        | some bb => rw [hx] at hs; simp at hs
        | none =>
            rw [List.getElem?_eq_none_iff] at hx
            omega
      simp only [this]; omega
    · rw [hd]
      simp only [Direction.moveInput]
      have : (c.inputPos ⟨j, hj⟩).val ≤ x.length := by
        unfold readInput at hs
        split_ifs at hs with h0
        · omega
        · cases hx : x[(c.inputPos ⟨j, hj⟩).val - 1]? with
          | some bb =>
              rw [List.getElem?_eq_some_iff] at hx
              obtain ⟨hlt', _⟩ := hx
              omega
          | none => rw [hx] at hs; simp at hs
      omega
    · rw [hd]; rfl
    · rw [hd]; rfl
  · intro j hj
    simp only [posOf, hj, dif_pos]
    exact (length_bnum_add_one_le (Nat.lt_succ_iff.mp (c.inputPos ⟨j, hj⟩).isLt)).trans hNp
  refine (runs_setState M W c.state c.state.val _ _ _ N hB a.nextState.val
    (by have := c.state.isLt; omega) (by have := a.nextState.isLt; omega)).seq ?_
  refine (runs_setFlags M W c.state a.nextState.val _ _ _ N hB a.nextState hout
    (by omega)).of_eq rfl ?_
  have hs' : c'.state = a.nextState := by rw [hst]
  rw [hs']
  congr 2
  apply encR_congr
  · intro j hj; simp [stg, hj]
  · intro k hk; simp [stg, hk]
  · intro k hk; simp [stg, hk]

/-! ### One full transition -/

/-- The leaf of the dispatch tree for the unary state value `v` and the symbols read: the four
phases of the transition in the table, or nothing if the state has an output. -/
def leafProg (v : ℕ) (syms : ℕ → InputSymbol) (bits : ℕ → Bool) : Prog :=
  if hv : v < q + 1 then
    if M.output ⟨v, hv⟩ = none then
      actProg M (M.transition ⟨v, hv⟩ (fun j => syms j) (fun k => bits k) false) syms
    else skip
  else skip

/-- **One full transition as a tape program**: branch on the state, read all input symbols and
all work symbols, and run the leaf of the finite dispatch tree. -/
def stepProg : Prog :=
  caseUnary (regK h w) 2 q (fun v =>
    readAll (rdInput (regK h w)) InputSymbol.leftMarker h (fun syms =>
      readAll (fun k => rdWork (regK h w) (rR h k)) false w (fun bits =>
        leafProg M v syms bits)))

theorem runs_stepProg (W : ℤ) (c : Configuration q w h x.length) (N : ℕ)
    (hB : (N + 3) * wd (regK h w) ≤ B) (hNW : (2 * W + 1).toNat ≤ N) (hNq : q + 1 ≤ N)
    (hNp : Nat.log 2 (x.length + 2) + 1 ≤ N)
    (hwin : ∀ k : Fin w, -W ≤ c.workPos k ∧ c.workPos k ≤ W ∧
      -W ≤ (M.step x false c).workPos k ∧ (M.step x false c).workPos k ≤ W) :
    Runs x B (stepProg M) ⟨lay (regK h w) (encC M W c), 0, 0⟩
      ⟨lay (regK h w) (encC M W (M.step x false c)), 0, 0⟩ := by
  set R := encC M W c with hR
  have hR3 : R 3 = [] := encR_S M _ _ _ _ _ _
  have hR4 : R 4 = [] := encR_C M _ _ _ _ _ _
  have hR5 : R 5 = [] := encR_OF M _ _ _ _ _ _
  unfold stepProg
  refine runs_caseUnary 2 (lt_regK (by omega)) N hB 0 q R c.state.val _ _
    (by rw [hR, encC, encR_ST]) (by have := c.state.isLt; omega)
    (by have := c.state.isLt; omega) ?_
  refine runs_readAll _ _ (fun j => readNat x (posOf c j)) _ h ?_ _ _ ?_
  · intro j hj cont s' hc
    have hpj : posOf c j = (c.inputPos ⟨j, hj⟩).val := by simp [posOf, hj]
    refine runs_rdInput R j (by unfold rCnt regK; omega) hR3 hR4 hR5 (posOf c j)
      (by rw [hR, encC, encR_cnt M W _ _ _ _ _ j hj]) (by rw [hpj]; omega) N hB
      ((length_bnum_add_one_le (by rw [hpj]; omega)).trans hNp) cont s' hc
  refine runs_readAll _ _ (fun k => tpOf c k (hpOf c k)) _ w ?_ _ _ ?_
  · intro k hk cont s' hc
    have hRk : R (rR h k) = rgtOf (tpOf c k) (hpOf c k) W := by
      rw [hR, encC, encR_R M W _ _ _ _ _ k hk]
    have hwk := hwin ⟨k, hk⟩
    have hpk : hpOf c k = c.workPos ⟨k, hk⟩ := by simp [hpOf, hk]
    have hne : R (rR h k) ≠ [] := by rw [hRk]; exact rgtOf_ne_nil _ _ _ (by rw [hpk]; exact hwk.2.1)
    refine runs_rdWork R (rR h k) (by unfold rR regK; omega) hne N
      (by rw [hRk, length_rgtOf]; omega) hB 0 cont s' ?_
    have hl : (R (rR h k)).getLast hne = tpOf c k (hpOf c k) := by
      simp only [hRk]; exact rgtOf_getLast _ _ _ (by rw [hpk]; exact hwk.2.1)
    rw [hl]; exact hc
  unfold leafProg
  rw [dif_pos c.state.isLt]
  by_cases hout : M.output c.state = none
  · rw [Fin.eta, if_pos hout]
    have e1 : (fun j : Fin h => (fun i => if i < h then readNat x (posOf c i)
        else InputSymbol.leftMarker) (j : ℕ)) = fun j => readInput x (c.inputPos j) := by
      funext j; simp [j.isLt, posOf, readInput_eq]
    have e2 : (fun k : Fin w => (fun i => if i < w then tpOf c i (hpOf c i) else false) (k : ℕ)) =
        fun k => c.work k (c.workPos k) := by
      funext k; simp [k.isLt, tpOf, hpOf]
    rw [e1, e2]
    refine runs_actProg M W c false hout _ ?_ N hB hNW hNq hNp hwin
    intro j hj; simp [hj, posOf, readInput_eq]
  · rw [Fin.eta, if_neg hout]
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hout
    rw [ExactDerandomization.Machine.step_eq_self_of_output ho]
    exact runs_skip _ 0 0

/-- For a deterministic machine the coin does not matter. -/
theorem runs_stepProg_det (hdet : M.Deterministic) (b : Bool) (W : ℤ)
    (c : Configuration q w h x.length) (N : ℕ)
    (hB : (N + 3) * wd (regK h w) ≤ B) (hNW : (2 * W + 1).toNat ≤ N) (hNq : q + 1 ≤ N)
    (hNp : Nat.log 2 (x.length + 2) + 1 ≤ N)
    (hwin : ∀ k : Fin w, -W ≤ c.workPos k ∧ c.workPos k ≤ W ∧
      -W ≤ (M.step x b c).workPos k ∧ (M.step x b c).workPos k ≤ W) :
    Runs x B (stepProg M) ⟨lay (regK h w) (encC M W c), 0, 0⟩
      ⟨lay (regK h w) (encC M W (M.step x b c)), 0, 0⟩ := by
  rw [ExactDerandomization.Machine.step_eq_of_deterministic hdet x c b false] at hwin ⊢
  exact runs_stepProg M W c N hB hNW hNq hNp hwin

end FromLogspace

end Complexity.Space
