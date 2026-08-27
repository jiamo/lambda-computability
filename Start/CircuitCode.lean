/-
**Circuits as words, and the Tseitin translation as a block-emitting recursion.**

`Start/CobhamBlock.lean` shows that a block-emitting finite-state recursion is a Cobham
(polynomial-time) function.  This module puts a circuit into a shape such a recursion can read.

A gate is written as a self-delimiting token

  `0 1^tag 0 1^{a+1} 0 1^{b+1}`

— a marker bit, a bounded tag naming the kind of the gate, and two unary fields, each shifted by
one so that it is nonempty.  A circuit is the concatenation of the tokens of its gates, output
gate first.  A finite-state control scanning the word **from the right** therefore knows, at every
`0`, whether that `0` is the marker of a token and, if so, what the tag of the token is; the
counter of the recursion counts the markers already passed, which is exactly the identifier of the
gate whose token starts there.

The block emitted at a marker is the code of the CNF `Complexity.Tseitin.gateCnf` defining that
gate, so the output of the whole recursion is the code of `Complexity.Tseitin.defsCnf`.

Main definitions:

* `Complexity.CircCode.encGate`, `Complexity.CircCode.encCirc` — the code of a gate and of a
  circuit;
* `Complexity.CircCode.dstate`, `Complexity.CircCode.cinc`, `Complexity.CircCode.cblk` — the
  finite-state control, the counter increment and the emitted block.

Main results:

* `Complexity.CircCode.rcnt_encCirc` — the counter counts the gates;
* `Complexity.CircCode.brun_encCirc` — **the block-emitting recursion translates the code of a
  circuit into the code of its Tseitin definitions.**
-/

import Start.CobhamBlock
import Start.Tseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The code of a circuit -/

/-- The kind of a gate, as a number in `1, …, 6`. -/
def tag : Gate → ℕ
  | .inp _ => 1
  | .cst false => 2
  | .cst true => 3
  | .neg _ => 4
  | .conj _ _ => 5
  | .disj _ _ => 6

/-- The first field of a gate. -/
def fld1 : Gate → ℕ
  | .inp i => i
  | .cst _ => 0
  | .neg r => r
  | .conj r _ => r
  | .disj r _ => r

/-- The second field of a gate. -/
def fld2 : Gate → ℕ
  | .conj _ s => s
  | .disj _ s => s
  | _ => 0

/-- The gate with the given tag and fields. -/
def gateOf (t a b : ℕ) : Gate :=
  if t = 1 then .inp a
  else if t = 2 then .cst false
  else if t = 3 then .cst true
  else if t = 4 then .neg a
  else if t = 5 then .conj a b
  else .disj a b

@[simp] theorem gateOf_tag (g : Gate) : gateOf (tag g) (fld1 g) (fld2 g) = g := by
  cases g with
  | cst b => cases b <;> rfl
  | _ => rfl

theorem fld1_gateOf_le {a b n : ℕ} (t : ℕ) (ha : a ≤ n) : fld1 (gateOf t a b) ≤ n := by
  unfold gateOf
  split_ifs <;> simp [fld1, ha]

theorem fld2_gateOf_le {a b n : ℕ} (t : ℕ) (hb : b ≤ n) : fld2 (gateOf t a b) ≤ n := by
  unfold gateOf
  split_ifs <;> simp [fld2, hb]

theorem tag_le (g : Gate) : 1 ≤ tag g ∧ tag g ≤ 6 := by
  cases g with
  | cst b => cases b <;> exact ⟨by norm_num [tag], by norm_num [tag]⟩
  | _ => exact ⟨by norm_num [tag], by norm_num [tag]⟩

/-- The code of a gate: a marker bit, the tag in unary, and the two fields in unary, each shifted
by one and preceded by a separator. -/
def encGate (g : Gate) : Word :=
  false :: (List.replicate (tag g) true ++
    false :: (List.replicate (fld1 g + 1) true ++
      false :: List.replicate (fld2 g + 1) true))

theorem length_encGate (g : Gate) : (encGate g).length = tag g + fld1 g + fld2 g + 5 := by
  simp only [encGate, List.length_cons, List.length_append, List.length_replicate]
  omega

/-- The code of a circuit: the codes of its gates, output gate first. -/
def encCirc : Circuit → Word
  | [] => []
  | g :: C => encGate g ++ encCirc C

/-! ### The finite-state control -/

/-- The control of the recursion, scanning the code **from the right**.  State `0` reads the last
field of a token, state `1` the first field, state `2` starts the tag, and states `3, …, 8` have
read a tag of `1, …, 6` ones; `9` is the dead state. -/
def dstate (s : ℕ) (b : Bool) : ℕ :=
  match b, s with
  | true, 0 => 0
  | true, 1 => 1
  | true, 2 => 3
  | true, 3 => 4
  | true, 4 => 5
  | true, 5 => 6
  | true, 6 => 7
  | true, 7 => 8
  | false, 0 => 1
  | false, 1 => 2
  | false, 3 => 0
  | false, 4 => 0
  | false, 5 => 0
  | false, 6 => 0
  | false, 7 => 0
  | false, 8 => 0
  | _, _ => 9

theorem dstate_lt (s : ℕ) (b : Bool) : dstate s b < 10 := by
  unfold dstate
  split <;> omega

/-- A position carries a gate exactly when it is a `0` whose suffix has just read a tag. -/
def emits (s : ℕ) (b : Bool) : Bool := !b && decide (3 ≤ s) && decide (s ≤ 8)

/-- The counter counts the markers, that is, the gates already passed. -/
def cinc (s : ℕ) (b : Bool) : ℕ := if emits s b then 1 else 0

theorem cinc_le (s : ℕ) (b : Bool) : cinc s b ≤ 1 := by
  rw [cinc]; split <;> omega

@[simp] theorem emits_true (s : ℕ) : emits s true = false := by simp [emits]

@[simp] theorem cinc_true (s : ℕ) : cinc s true = 0 := by simp [cinc]

/-! ### Reading the fields of a token -/

/-- The first field of the token whose marker has just been passed. -/
def fldA (y : Word) : ℕ := lead1 (drop1 y).tail - 1

/-- The second field of the token whose marker has just been passed. -/
def fldB (y : Word) : ℕ := lead1 (drop1 (drop1 y).tail).tail - 1

/-- The gate whose token starts at a marker, read off the suffix. -/
def readGate (s : ℕ) (y : Word) : Gate := gateOf (s - 2) (fldA y) (fldB y)

/-- The block emitted at a position, for a given translation `F` of a gate and its identifier:
nothing except at a marker, where the gate whose token starts there is read off the suffix. -/
def gblk (F : ℕ → Gate → Word) (s : ℕ) (b : Bool) (y : Word) (c : ℕ) : Word :=
  if emits s b then F c (readGate s y) else []

/-- The concatenation of the translations of the gates of a circuit, each gate receiving its
identifier. -/
def gmap (F : ℕ → Gate → Word) : Circuit → Word
  | [] => []
  | g :: C => F C.length g ++ gmap F C

/-- The block emitted at a position by the Tseitin translation: the code of the CNF defining the
gate whose token starts there. -/
def cblk : ℕ → Bool → Word → ℕ → Word := gblk fun c g => Sat.encCnf (gateCnf c g)

/-! ### Words of ones -/

theorem lead1_replicate_append (k : ℕ) (w : Word) :
    lead1 (List.replicate k true ++ w) = k + lead1 w := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, lead1, ih]; omega

theorem drop1_replicate_append (k : ℕ) (w : Word) :
    drop1 (List.replicate k true ++ w) = drop1 w := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, drop1, ih]

@[simp] theorem drop1_false_cons (w : Word) : drop1 (false :: w) = false :: w := rfl

theorem rst_replicate_true_zero (k : ℕ) (w : Word) (h : rst dstate 0 w = 0) :
    rst dstate 0 (List.replicate k true ++ w) = 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, rst, ih]
      rfl

theorem rst_replicate_true_one (k : ℕ) (w : Word) (h : rst dstate 0 w = 1) :
    rst dstate 0 (List.replicate k true ++ w) = 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, rst, ih]
      rfl

theorem rst_replicate_true_two (k : ℕ) (hk : k ≤ 6) (w : Word) (h : rst dstate 0 w = 2) :
    rst dstate 0 (List.replicate k true ++ w) = 2 + k := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, rst, ih (by omega)]
      have hk' : k ≤ 5 := by omega
      interval_cases k <;> rfl

theorem rcnt_replicate_true (k : ℕ) (w : Word) :
    rcnt dstate cinc (List.replicate k true ++ w) = rcnt dstate cinc w := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, rcnt, cinc_true, ih]; omega

theorem brun_replicate_true (F : ℕ → Gate → Word) (k : ℕ) (w : Word) :
    brun dstate cinc (gblk F) (List.replicate k true ++ w) = brun dstate cinc (gblk F) w := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, brun, ih]
      simp [gblk]

/-! ### Cutting a token into its fields -/

section Token

variable (g : Gate) (w : Word)

/-- The last field of the token of `g`, followed by the rest of the word. -/
def tokF2 : Word := List.replicate (fld2 g + 1) true ++ w

/-- The separator before the last field. -/
def tokS2 : Word := false :: tokF2 g w

/-- The first field of the token of `g`, followed by the rest of the token. -/
def tokF1 : Word := List.replicate (fld1 g + 1) true ++ tokS2 g w

/-- The separator before the first field. -/
def tokS1 : Word := false :: tokF1 g w

/-- The tag of the token of `g`, followed by the rest of the token. -/
def tokT : Word := List.replicate (tag g) true ++ tokS1 g w

theorem encGate_append : encGate g ++ w = false :: tokT g w := by
  simp [encGate, tokT, tokS1, tokF1, tokS2, tokF2]

variable {w} (hw : rst dstate 0 w = 0)

include hw

theorem rst_tokF2 : rst dstate 0 (tokF2 g w) = 0 :=
  rst_replicate_true_zero _ _ hw

theorem rst_tokS2 : rst dstate 0 (tokS2 g w) = 1 := by
  rw [tokS2, rst, rst_tokF2 g hw]; rfl

theorem rst_tokF1 : rst dstate 0 (tokF1 g w) = 1 :=
  rst_replicate_true_one _ _ (rst_tokS2 g hw)

theorem rst_tokS1 : rst dstate 0 (tokS1 g w) = 2 := by
  rw [tokS1, rst, rst_tokF1 g hw]; rfl

theorem rst_tokT : rst dstate 0 (tokT g w) = 2 + tag g :=
  rst_replicate_true_two _ (tag_le g).2 _ (rst_tokS1 g hw)

theorem rst_encGate_append : rst dstate 0 (encGate g ++ w) = 0 := by
  rw [encGate_append, rst, rst_tokT g hw]
  obtain ⟨h1, h6⟩ := tag_le g
  interval_cases h : (tag g) <;> rfl

end Token

theorem rst_encCirc (C : Circuit) : rst dstate 0 (encCirc C) = 0 := by
  induction C with
  | nil => rfl
  | cons g C ih => rw [encCirc, rst_encGate_append g ih]

theorem lead1_encCirc (C : Circuit) : lead1 (encCirc C) = 0 := by
  cases C with
  | nil => rfl
  | cons g C => rfl

/-! ### The counter and the output on the code of a circuit -/

section Run

variable (g : Gate) {w : Word}

theorem rcnt_encGate_append (hw : rst dstate 0 w = 0) :
    rcnt dstate cinc (encGate g ++ w) = rcnt dstate cinc w + 1 := by
  have h2 : rcnt dstate cinc (tokS2 g w) = rcnt dstate cinc w := by
    rw [tokS2, rcnt, rst_tokF2 g hw, tokF2, rcnt_replicate_true]
    simp [cinc, emits]
  have h1 : rcnt dstate cinc (tokS1 g w) = rcnt dstate cinc w := by
    rw [tokS1, rcnt, rst_tokF1 g hw, tokF1, rcnt_replicate_true, h2]
    simp [cinc, emits]
  rw [encGate_append, rcnt, rst_tokT g hw, tokT, rcnt_replicate_true, h1]
  obtain ⟨ha, h6⟩ := tag_le g
  have : cinc (2 + tag g) false = 1 := by
    rw [cinc, if_pos]
    simp [emits]
    omega
  rw [this]
  omega

theorem readGate_tokT (hlead : lead1 w = 0) :
    readGate (2 + tag g) (tokT g w) = g := by
  have hA : fldA (tokT g w) = fld1 g := by
    rw [fldA, tokT, drop1_replicate_append, tokS1, drop1_false_cons]
    rw [show (false :: tokF1 g w).tail = tokF1 g w from rfl, tokF1, lead1_replicate_append]
    rw [show lead1 (tokS2 g w) = 0 from rfl]
    omega
  have hB : fldB (tokT g w) = fld2 g := by
    rw [fldB, tokT, drop1_replicate_append, tokS1, drop1_false_cons]
    rw [show (false :: tokF1 g w).tail = tokF1 g w from rfl, tokF1, drop1_replicate_append,
      tokS2, drop1_false_cons]
    rw [show (false :: tokF2 g w).tail = tokF2 g w from rfl, tokF2, lead1_replicate_append,
      hlead]
    omega
  rw [readGate, hA, hB, Nat.add_sub_cancel_left, gateOf_tag]

theorem brun_encGate_append (F : ℕ → Gate → Word) (hw : rst dstate 0 w = 0)
    (hlead : lead1 w = 0) :
    brun dstate cinc (gblk F) (encGate g ++ w)
      = F (rcnt dstate cinc w) g ++ brun dstate cinc (gblk F) w := by
  have h2 : brun dstate cinc (gblk F) (tokS2 g w) = brun dstate cinc (gblk F) w := by
    rw [tokS2, brun, rst_tokF2 g hw, tokF2, brun_replicate_true]
    simp [gblk, emits]
  have h1 : brun dstate cinc (gblk F) (tokS1 g w) = brun dstate cinc (gblk F) w := by
    rw [tokS1, brun, rst_tokF1 g hw, tokF1, brun_replicate_true, h2]
    simp [gblk, emits]
  have hcnt : rcnt dstate cinc (tokT g w) = rcnt dstate cinc w := by
    have h2' : rcnt dstate cinc (tokS2 g w) = rcnt dstate cinc w := by
      rw [tokS2, rcnt, rst_tokF2 g hw, tokF2, rcnt_replicate_true]
      simp [cinc, emits]
    rw [tokT, rcnt_replicate_true, tokS1, rcnt, rst_tokF1 g hw, tokF1, rcnt_replicate_true, h2']
    simp [cinc, emits]
  rw [encGate_append, brun, rst_tokT g hw, hcnt, tokT, brun_replicate_true, h1, gblk,
    if_pos, ← tokT, readGate_tokT g hlead]
  obtain ⟨ha, h6⟩ := tag_le g
  simp only [emits, Bool.not_false, Bool.true_and, decide_eq_true_eq, Bool.and_eq_true]
  omega

end Run

/-- The counter counts the gates. -/
theorem rcnt_encCirc (C : Circuit) : rcnt dstate cinc (encCirc C) = C.length := by
  induction C with
  | nil => rfl
  | cons g C ih =>
      rw [encCirc, rcnt_encGate_append g (rst_encCirc C), ih, List.length_cons]

/-- **A block-emitting recursion translates the code of a circuit into the concatenation of the
translations of its gates**, each gate receiving its identifier. -/
theorem brun_gmap (F : ℕ → Gate → Word) (C : Circuit) :
    brun dstate cinc (gblk F) (encCirc C) = gmap F C := by
  induction C with
  | nil => rfl
  | cons g C ih =>
      rw [encCirc, brun_encGate_append g F (rst_encCirc C) (lead1_encCirc C), ih, rcnt_encCirc,
        gmap]

/-- **The block-emitting recursion translates the code of a circuit into the code of its Tseitin
definitions.** -/
theorem brun_encCirc (C : Circuit) :
    brun dstate cinc cblk (encCirc C) = Sat.encCnf (defsCnf C) := by
  rw [cblk, brun_gmap]
  induction C with
  | nil => rfl
  | cons g C ih =>
      rw [gmap, ih, defsCnf]
      simp only [Sat.encCnf, List.flatMap_append]

end CircCode

end Complexity
