import Start.LogspaceToSpaceTape

/-!
# Simulating an `ExactDerandomization` machine by a host tape program: the register file

This library's own module (task `M27-LOGSPACE-TRANSFER`, reverse direction `L ⊆ LOGSPACE`).

A configuration of a machine of `Start/LogspaceDeterministic.lean` (`q + 1` control states, `w`
two-sided work tapes, `h` read-only input heads on the input framed by end markers) is held in a
register file of the track layout (`Start/SpaceProgLib.lean`) with `7 + h + 2 w` registers:

* `0` — the *running flag*: `[true]` while the simulated machine has no output;
* `1` — the *result*: `[true]` iff the output is `true`;
* `2` — the control state, in unary;
* `3`, `4`, `5`, `6` — scratch counter, carry, flag of the counter programs, and the input length;
* `7 + j` — the position of input head `j`, as a bijective base-two numeral;
* `7 + h + 2k`, `7 + h + 2k + 1` — work tape `k` inside the window `[-W, W]`
  (`Tracks.lftOf`, `Tracks.rgtOf`).

`FromLogspace.encR` is this encoding, for a "view" of a configuration in which the source of the
two flags, the control state, the input positions and the tapes are separate parameters, so that
the simulation of one step can update them one at a time.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace FromLogspace

open Tracks Prog
open ExactDerandomization (Word InputSymbol Direction Configuration readInput)

/-- Register of input head `j`. -/
abbrev rCnt (j : ℕ) : ℕ := 7 + j
/-- Left register of work tape `k`. -/
abbrev rL (h k : ℕ) : ℕ := 7 + h + 2 * k
/-- Right register of work tape `k`. -/
abbrev rR (h k : ℕ) : ℕ := 7 + h + 2 * k + 1
/-- The number of registers. -/
abbrev regK (h w : ℕ) : ℕ := 7 + h + 2 * w

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h)

/-- The register file of a view of a configuration. -/
def encR (W : ℤ) (fs : Fin (q + 1)) (st : ℕ) (pos : ℕ → ℕ) (tp : ℕ → ℤ → Bool) (hp : ℕ → ℤ) :
    ℕ → List Bool := fun r =>
  if r = 0 then (if M.output fs = none then [true] else [])
  else if r = 1 then (if M.output fs = some true then [true] else [])
  else if r = 2 then List.replicate st true
  else if r < 7 then []
  else if r < 7 + h then bnum (pos (r - 7))
  else if r < 7 + h + 2 * w then
    (if (r - 7 - h) % 2 = 0 then lftOf (tp ((r - 7 - h) / 2)) (hp ((r - 7 - h) / 2)) W
      else rgtOf (tp ((r - 7 - h) / 2)) (hp ((r - 7 - h) / 2)) W)
  else []

section enc
variable (W : ℤ) (fs : Fin (q + 1)) (st : ℕ) (pos : ℕ → ℕ) (tp : ℕ → ℤ → Bool) (hp : ℕ → ℤ)

@[simp] theorem encR_RF : encR M W fs st pos tp hp 0 =
    if M.output fs = none then [true] else [] := by simp [encR]
@[simp] theorem encR_RES : encR M W fs st pos tp hp 1 =
    if M.output fs = some true then [true] else [] := by simp [encR]
@[simp] theorem encR_ST : encR M W fs st pos tp hp 2 = List.replicate st true := by simp [encR]
@[simp] theorem encR_S : encR M W fs st pos tp hp 3 = [] := by simp [encR]
@[simp] theorem encR_C : encR M W fs st pos tp hp 4 = [] := by simp [encR]
@[simp] theorem encR_OF : encR M W fs st pos tp hp 5 = [] := by simp [encR]
@[simp] theorem encR_T : encR M W fs st pos tp hp 6 = [] := by simp [encR]

theorem encR_cnt (j : ℕ) (hj : j < h) : encR M W fs st pos tp hp (rCnt j) = bnum (pos j) := by
  simp only [encR, rCnt]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 2; omega

theorem encR_L (k : ℕ) (hk : k < w) :
    encR M W fs st pos tp hp (rL h k) = lftOf (tp k) (hp k) W := by
  simp only [encR, rL]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  have : (7 + h + 2 * k - 7 - h) / 2 = k := by omega
  rw [this]

theorem encR_R (k : ℕ) (hk : k < w) :
    encR M W fs st pos tp hp (rR h k) = rgtOf (tp k) (hp k) W := by
  simp only [encR, rR]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), if_neg (by omega)]
  have : (7 + h + 2 * k + 1 - 7 - h) / 2 = k := by omega
  rw [this]

theorem encR_upd_cnt (j : ℕ) (hj : j < h) (v : ℕ) :
    Function.update (encR M W fs st pos tp hp) (rCnt j) (bnum v) =
      encR M W fs st (Function.update pos j v) tp hp := by
  funext r
  by_cases hr : r = rCnt j
  · subst hr; rw [Function.update_self, encR_cnt M W _ _ _ _ _ j hj, Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [rCnt] at hr
    simp only [encR]
    split_ifs <;> try rfl
    rw [Function.update_of_ne (by omega)]

theorem encR_upd_tape (k : ℕ) (hk : k < w) (g : ℤ → Bool) (p : ℤ) :
    Function.update (Function.update (encR M W fs st pos tp hp) (rL h k) (lftOf g p W))
      (rR h k) (rgtOf g p W) =
      encR M W fs st pos (Function.update tp k g) (Function.update hp k p) := by
  funext r
  by_cases hr : r = rR h k
  · subst hr; rw [Function.update_self, encR_R M W _ _ _ _ _ k hk, Function.update_self,
      Function.update_self]
  · rw [Function.update_of_ne hr]
    by_cases hl : r = rL h k
    · subst hl; rw [Function.update_self, encR_L M W _ _ _ _ _ k hk, Function.update_self,
        Function.update_self]
    · rw [Function.update_of_ne hl]
      simp only [rL, rR] at hl hr
      simp only [encR]
      split_ifs <;> try rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem encR_upd_ST (v : ℕ) :
    Function.update (encR M W fs st pos tp hp) 2 (List.replicate v true) =
      encR M W fs v pos tp hp := by
  funext r
  by_cases hr : r = 2
  · subst hr; simp
  · rw [Function.update_of_ne hr]; simp only [encR]; split_ifs <;> first | rfl | omega

theorem encR_upd_flags (fs' : Fin (q + 1)) (hfs : M.output fs = none) :
    Function.update (Function.update (encR M W fs st pos tp hp) 0
      (if M.output fs' = none then [true] else [])) 1
      (if M.output fs' = some true then [true] else []) =
      encR M W fs' st pos tp hp := by
  funext r
  by_cases hr1 : r = 1
  · subst hr1; simp
  · rw [Function.update_of_ne hr1]
    by_cases hr0 : r = 0
    · subst hr0; simp
    · rw [Function.update_of_ne hr0]; simp only [encR]; split_ifs <;> first | rfl | omega

end enc

end FromLogspace

end Complexity.Space
