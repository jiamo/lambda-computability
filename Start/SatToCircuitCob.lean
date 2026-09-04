/-
**The reduction of SAT to CIRCUIT-SAT is a Cobham function.**

`Start/SatToCircuit.lean` builds, from a word `u`, a Boolean circuit `Complexity.Sat.satC u` that
is satisfiable exactly when `u ∈ SAT`.  This module exhibits the map `u ↦ code of satC u` as a
Cobham (polynomial-time) term, by running the block-emitting recursion of
`Start/CobhamBlock.lean` with the three-state phase automaton of the token code: four gate tokens
are emitted at every position of `u`, and the two constant gates that start the accumulators are
appended at the right end.

The one quantity a block needs and the automaton does not carry is the number of ticks read since
the last token, which is the variable index of a literal.  It is recovered from the evaluator
`Complexity.Sat.satMachine` of `Start/Sat.lean`, run against the all-ones assignment: that run
leaves the assignment pointer at `1^{|y| - ticks}`, and dropping that many bits from `1^{|y|}`
leaves `1^{ticks}`.

Main definitions:

* `Complexity.Sat.pdelta`, `Complexity.Sat.pinc` — the phase automaton and the counter;
* `Complexity.Sat.tickT` — the Cobham term of the tick count;
* `Complexity.Sat.satCircTerm` — the Cobham term of the reduction.

Main results:

* `Complexity.Sat.eval_tickT` — the tick count is a Cobham function;
* `Complexity.Sat.eval_satCircTerm` — **the term computes the code of the circuit of a word**;
* `Complexity.polyManyOne_SAT_CSAT` — **`SAT ≤ₘᵖ CIRCUIT-SAT`**;
* `Complexity.npHard_CSAT`, `Complexity.npComplete_CSAT` — **CIRCUIT-SAT is NP-complete**.
-/

import Start.SatToCircuit
import Start.CookLevinNPHard

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Sat

open Complexity.Tseitin Complexity.CircCode

/-! ### The phase automaton -/

/-- The three phases of the token reader, as numbers. -/
def pcode : Phase → ℕ
  | .main => 0
  | .esc => 1
  | .esc2 => 2

/-- The transition function of the phase automaton, scanning from the right. -/
def pdelta (s : ℕ) (b : Bool) : ℕ :=
  if b then 0 else if s = 0 then 1 else if s = 1 then 2 else 0

theorem pdelta_lt (s : ℕ) (b : Bool) : pdelta s b < 3 := by
  rw [pdelta]
  split <;> [skip; split] <;> [skip; skip; split] <;> omega

/-- The automaton computes the phase of the decoder. -/
theorem rst_pdelta (u : Word) : rst pdelta 0 u = pcode (drun u).phase := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [rst, ih]
      have hd : drun (b :: u) = dstep b (drun u) := rfl
      rw [hd]
      cases hp : (drun u).phase <;> cases b <;> simp [pdelta, pcode, dstep, hp]

/-- Four gates are emitted at every position. -/
def pinc (_ : ℕ) (_ : Bool) : ℕ := 4

theorem pinc_le (s : ℕ) (b : Bool) : pinc s b ≤ 4 := le_rfl

theorem rcnt_pinc (u : Word) : rcnt pdelta pinc u = 4 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [rcnt, ih, pinc, List.length_cons]; omega

/-! ### The number of ticks, as a Cobham function -/

theorem ticks_le (u : Word) : (drun u).ticks ≤ u.length := by
  induction u with
  | nil => simp [drun, dinit]
  | cons b u ih =>
      have hd : drun (b :: u) = dstep b (drun u) := rfl
      rw [hd, List.length_cons]
      cases hp : (drun u).phase <;> cases b <;> simp [dstep, hp] <;> omega

/-- The Cobham term computing `1^{ticks}` from the suffix. -/
def tickT : Cob :=
  .comp Cob.dropU
    [Cob.tailN 4 (.comp satMachine [.proj 0, Cob.unary (.proj 0)]), Cob.unary (.proj 0)]

/-- **The tick count is a Cobham function of the suffix.** -/
theorem eval_tickT (y : Word) (rest : List Word) :
    tickT.eval (y :: rest) = List.replicate (drun y).ticks true := by
  have hσ : (Cob.unary (Cob.proj 0)).eval (y :: rest) = List.replicate y.length true := by
    simp
  have hm : (Cob.comp satMachine [Cob.proj 0, Cob.unary (Cob.proj 0)]).eval (y :: rest)
      = encMSt (mrun (List.replicate y.length true) y) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero, hσ]
    exact eval_satMachine y _
  have hptr : (Cob.tailN 4 (Cob.comp satMachine [Cob.proj 0, Cob.unary (Cob.proj 0)])).eval
      (y :: rest) = List.replicate (y.length - (drun y).ticks) true := by
    rw [Cob.eval_tailN, hm, mrun_eq]
    simp only [encMSt]
    rw [show (List.replicate y.length true).drop (drun y).ticks
        = List.replicate (y.length - (drun y).ticks) true from by
      simp]
    rfl
  rw [tickT]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hptr, hσ, Cob.eval_dropU,
    List.length_replicate]
  have h := ticks_le y
  rw [show (List.replicate y.length true).drop (y.length - (drun y).ticks)
      = List.replicate (y.length - (y.length - (drun y).ticks)) true from by simp]
  congr 1
  omega

/-! ### The gate tokens -/

/-- The Cobham term of a gate token: the marker, the tag in unary, and the two fields. -/
def tokT (tg : ℕ) (f₁ f₂ : Cob) : Cob :=
  Cob.catL [Cob.constT (false :: List.replicate tg true ++ [false]), f₁, Cob.constT [false], f₂]

theorem encGate_eq (g : Gate) :
    encGate g = (false :: List.replicate (tag g) true ++ [false])
      ++ List.replicate (fld1 g + 1) true ++ [false] ++ List.replicate (fld2 g + 1) true := by
  simp [encGate]

theorem eval_tokT {tg : ℕ} {f₁ f₂ : Cob} {args : List Word} (g : Gate)
    (htag : tg = tag g) (h₁ : f₁.eval args = List.replicate (fld1 g + 1) true)
    (h₂ : f₂.eval args = List.replicate (fld2 g + 1) true) :
    (tokT tg f₁ f₂).eval args = encGate g := by
  subst htag
  rw [tokT, encGate_eq]
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    Cob.eval_constT, h₁, h₂, List.append_nil]
  simp

/-- `1^{c + k}`, from the counter in the second argument. -/
def uc (k : ℕ) : Cob := Cob.pre (List.replicate k true) (.proj 1)

theorem eval_uc (k c : ℕ) (y p : Word) :
    (uc k).eval [y, List.replicate c true, p] = List.replicate (k + c) true := by
  rw [uc, Cob.eval_pre, List.replicate_add]
  simp

/-- `1^{ticks + k}`, from the suffix in the first argument. -/
def tickU (k : ℕ) : Cob := Cob.pre (List.replicate k true) tickT

theorem eval_tickU (k : ℕ) (y : Word) (rest : List Word) :
    (tickU k).eval (y :: rest) = List.replicate (k + (drun y).ticks) true := by
  rw [tickU, Cob.eval_pre, eval_tickT, List.replicate_add]

/-! ### The block of gates, as a word and as a term -/

/-- The four gates emitted at a position, read off the state `s`, the bit `b`, the variable index
`t` and the number `c` of gates already emitted.  This is `Complexity.Sat.satBlk` with its
dependence on the suffix replaced by a dependence on the data a block-emitting recursion has. -/
def cirGates (s : ℕ) (b : Bool) (t c : ℕ) : Circuit :=
  if s = 1 ∧ b = true then
    [.disj (c + 1) (c + 1), .disj c (c + 3), .neg (c + 2), .inp t]
  else if s = 2 ∧ b = true then
    [.disj (c + 1) (c + 1), .disj c (c + 3), .disj (c + 2) (c + 2), .inp t]
  else if s = 2 ∧ b = false then
    [.conj (c + 1) c, .disj (c + 2) (c + 2), .cst false, .cst false]
  else
    [.disj (c + 1) (c + 1), .disj c c, .cst false, .cst false]

/-- The block of the recursion: the code of the four gates. -/
def cirBlk (s : ℕ) (b : Bool) (y : Word) (c : ℕ) : Word :=
  encCirc (cirGates s b (drun y).ticks c)

/-- On the data the recursion supplies, the block is the block of `Start/SatToCircuit.lean`. -/
theorem cirGates_eq_satBlk (b : Bool) (y : Word) :
    cirGates (pcode (drun y).phase) b (drun y).ticks (4 * y.length) = satBlk b y := by
  rcases h : (drun y).phase with _ | _ | _
  · rw [satBlk_main y h]; simp [cirGates, pcode]
  · cases b
    · rw [satBlk_esc_false y h]; simp [cirGates, pcode]
    · rw [satBlk_esc_true y h]; simp [cirGates, pcode]
  · cases b
    · rw [satBlk_esc2_false y h]; simp [cirGates, pcode]
    · rw [satBlk_esc2_true y h]; simp [cirGates, pcode]

/-- **The recursion emits the code of the circuit**, but for the two constant gates that start the
accumulators. -/
theorem brun_cirBlk (u : Word) :
    brun pdelta pinc cirBlk u ++ encCirc [Gate.cst true, Gate.cst false] = encCirc (satC u) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [brun, rst_pdelta, rcnt_pinc, cirBlk, cirGates_eq_satBlk, satC_cons, encCirc_append,
        List.append_assoc, ih]

/-- The Cobham term of a block: the four tokens, with the fields read off the counter and the
tick count. -/
def blkT (s : ℕ) (b : Bool) : Cob :=
  if s = 1 ∧ b = true then
    Cob.catL [tokT 6 (uc 2) (uc 2), tokT 6 (uc 1) (uc 4), tokT 4 (uc 3) (Cob.constT [true]),
      tokT 1 (tickU 1) (Cob.constT [true])]
  else if s = 2 ∧ b = true then
    Cob.catL [tokT 6 (uc 2) (uc 2), tokT 6 (uc 1) (uc 4), tokT 6 (uc 3) (uc 3),
      tokT 1 (tickU 1) (Cob.constT [true])]
  else if s = 2 ∧ b = false then
    Cob.catL [tokT 5 (uc 2) (uc 1), tokT 6 (uc 3) (uc 3),
      tokT 2 (Cob.constT [true]) (Cob.constT [true]),
      tokT 2 (Cob.constT [true]) (Cob.constT [true])]
  else
    Cob.catL [tokT 6 (uc 2) (uc 2), tokT 6 (uc 1) (uc 1),
      tokT 2 (Cob.constT [true]) (Cob.constT [true]),
      tokT 2 (Cob.constT [true]) (Cob.constT [true])]

/-- **The term of a block computes the block.** -/
theorem eval_blkT (s : ℕ) (b : Bool) (y : Word) (c : ℕ) :
    (blkT s b).eval [y, List.replicate c true, []] = cirBlk s b y c := by
  have hu : ∀ k j : ℕ, k + c = j →
      (uc k).eval [y, List.replicate c true, ([] : Word)] = List.replicate j true := by
    intro k j h; rw [eval_uc, h]
  have ht : ∀ k j : ℕ, k + (drun y).ticks = j →
      (tickU k).eval [y, List.replicate c true, ([] : Word)] = List.replicate j true := by
    intro k j h; rw [eval_tickU, h]
  have hc : (Cob.constT [true]).eval [y, List.replicate c true, ([] : Word)]
      = List.replicate 1 true := by rw [Cob.eval_constT]; rfl
  rw [cirBlk, blkT, cirGates]
  split_ifs with h₁ h₂ h₃ <;>
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      eval_tokT (tg := 6) (Gate.disj (c + 1) (c + 1)) rfl (hu 2 (c + 1 + 1) (by omega))
        (hu 2 (c + 1 + 1) (by omega)),
      eval_tokT (tg := 6) (Gate.disj c (c + 3)) rfl (hu 1 (c + 1) (by omega))
        (hu 4 (c + 3 + 1) (by omega)),
      eval_tokT (tg := 6) (Gate.disj c c) rfl (hu 1 (c + 1) (by omega)) (hu 1 (c + 1) (by omega)),
      eval_tokT (tg := 6) (Gate.disj (c + 2) (c + 2)) rfl (hu 3 (c + 2 + 1) (by omega))
        (hu 3 (c + 2 + 1) (by omega)),
      eval_tokT (tg := 5) (Gate.conj (c + 1) c) rfl (hu 2 (c + 1 + 1) (by omega))
        (hu 1 (c + 1) (by omega)),
      eval_tokT (tg := 4) (Gate.neg (c + 2)) rfl (hu 3 (c + 2 + 1) (by omega)) hc,
      eval_tokT (tg := 1) (Gate.inp (drun y).ticks) rfl (ht 1 ((drun y).ticks + 1) (by omega)) hc,
      eval_tokT (tg := 2) (Gate.cst false) rfl hc hc,
      encCirc, List.append_nil]

/-- The block is short. -/
theorem length_cirBlk (s : ℕ) (b : Bool) (y : Word) (c : ℕ) :
    (cirBlk s b y c).length ≤ 8 * c + 8 * (drun y).ticks + 68 := by
  rw [cirBlk, cirGates]
  split_ifs <;>
    simp only [encCirc, List.length_append, length_encGate, tag, fld1, fld2, List.length_nil] <;>
    omega

/-! ### The term of the reduction -/

/-- **The reduction of SAT to CIRCUIT-SAT, as a Cobham term**: the blocks of the positions of the
word, followed by the code of the two constant gates. -/
def satCircTerm : Cob :=
  .comp Cob.concat
    [.comp (blkRunTerm 3 pdelta pinc blkT 4 100) [.proj 0, .empty],
      Cob.constT (encCirc [Gate.cst true, Gate.cst false])]

/-- **The term computes the code of the circuit of a word.** -/
theorem eval_satCircTerm (u : Word) : satCircTerm.eval [u] = encCirc (satC u) := by
  have hb : ∀ (s : ℕ) (b : Bool) (y : Word) (c : ℕ), c ≤ y.length * 4 →
      (cirBlk s b y c).length ≤ 100 * (y.length + ([] : Word).length + 1) := by
    intro s b y c hc
    have h₁ := length_cirBlk s b y c
    have h₂ := ticks_le y
    simp only [List.length_nil]
    omega
  have hrun : (Cob.comp (blkRunTerm 3 pdelta pinc blkT 4 100) [Cob.proj 0, Cob.empty]).eval [u]
      = brun pdelta pinc cirBlk u := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      Cob.eval_empty]
    exact eval_blkRunTerm (by omega) pdelta_lt pinc_le blkT []
      (fun s b y c => eval_blkT s b y c) hb u
  rw [satCircTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_constT, hrun]
  exact brun_cirBlk u

end Sat

/-! ### CIRCUIT-SAT is NP-complete -/

/-- **SAT reduces to CIRCUIT-SAT.** -/
theorem polyManyOne_SAT_CSAT : Sat.SAT ≤ₘᵖ CSAT :=
  ⟨Sat.satCircTerm, fun x => by rw [Sat.eval_satCircTerm, Sat.CSAT_encCirc_satC]⟩

/-- **CIRCUIT-SAT is NP-hard.** -/
theorem npHard_CSAT : NPHard CSAT := npHard_SAT.of_reduction polyManyOne_SAT_CSAT

/-- **CIRCUIT-SAT is NP-complete.** -/
theorem npComplete_CSAT : NPComplete CSAT := ⟨inNP_CSAT, npHard_CSAT⟩

end Complexity
