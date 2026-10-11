import Start.LogspaceToSpace

/-!
# Simulating an `ExactDerandomization` machine by a host tape program: one step

This library's own module (task `M27-LOGSPACE-TRANSFER`, reverse direction).  The tape program
`FromLogspace.act` carries out one transition of the simulated machine on the register file of
`Start/LogspaceToSpace.lean`, once the transition's action is known: it writes and moves every
work tape (`Tracks.tapeOp`), moves every input head (`Tracks.incr`/`Tracks.decr` on its
bijective numeral, with the clamping at the right end marker decided from the symbol read),
overwrites the unary control state and updates the two flags.  Each phase is specified on the
encoding `FromLogspace.encR`, one register at a time.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace FromLogspace

open Tracks Prog
open ExactDerandomization (Word InputSymbol Direction Configuration readInput)

variable {q w h : ℕ} (M : ExactDerandomization.Machine q w h)
variable {x : List Bool} {B : ℕ}

/-- The first `m` values from `f`, the rest from `g`. -/
def stg {α : Type} (m : ℕ) (f g : ℕ → α) : ℕ → α := fun k => if k < m then f k else g k

theorem stg_zero {α : Type} (f g : ℕ → α) : stg 0 f g = g := by funext k; simp [stg]

theorem stg_succ {α : Type} (m : ℕ) (f g : ℕ → α) :
    Function.update (stg m f g) m (f m) = stg (m + 1) f g := by
  funext k
  simp only [stg, Function.update_apply]
  split_ifs <;> first | (subst_vars; rfl) | omega

theorem stg_of_le {α : Type} (m : ℕ) (f g : ℕ → α) (k : ℕ) (hk : m ≤ k) : stg m f g k = g k := by
  simp [stg, show ¬ k < m by omega]

theorem lt_regK {r : ℕ} (hr : r < 7) : r < regK h w := by unfold regK; omega

/-- Overwrite the unary control state with `v`. -/
def setState (K v : ℕ) : Prog := .seq (clear K 2) (appendN K 2 true v)

/-- Update the two flags for a new output. -/
def setFlags (K : ℕ) : Option Bool → Prog
  | none => skip
  | some b => .seq (clear K 0) (if b then append K 1 true else skip)

/-- Move input head `j` in direction `d`, given the symbol `sym` it reads. -/
def headOp (K j : ℕ) (d : Direction) (sym : InputSymbol) : Prog :=
  match d with
  | .right => if sym = .rightMarker then skip else incr K (rCnt j) 4 5
  | .left => decr K (rCnt j) 4 5
  | .stay => skip

section specs

variable (W : ℤ) (fs : Fin (q + 1)) (st : ℕ) (pos : ℕ → ℕ) (tp : ℕ → ℤ → Bool) (hp : ℕ → ℤ)
variable (N : ℕ) (hB : (N + 3) * wd (regK h w) ≤ B)
include hB

theorem runs_setState (v : ℕ) (hst : st ≤ N) (hv : v ≤ N) :
    Runs x B (setState (regK h w) v) ⟨lay (regK h w) (encR M W fs st pos tp hp), 0, 0⟩
      ⟨lay (regK h w) (encR M W fs v pos tp hp), 0, 0⟩ := by
  refine (runs_clear _ 2 (lt_regK (by omega)) N (by simp [hst]) hB 0).seq ?_
  rw [show ([] : List Bool) = List.replicate 0 true from rfl, encR_upd_ST]
  refine (runs_appendN _ 2 (lt_regK (by omega)) true v N (by simp [hv]) hB 0).of_eq rfl ?_
  rw [encR_ST, List.replicate_zero, List.nil_append, encR_upd_ST]

theorem runs_setFlags (fs' : Fin (q + 1)) (hfs : M.output fs = none) (hN1 : 1 ≤ N) :
    Runs x B (setFlags (regK h w) (M.output fs')) ⟨lay (regK h w) (encR M W fs st pos tp hp), 0, 0⟩
      ⟨lay (regK h w) (encR M W fs' st pos tp hp), 0, 0⟩ := by
  rw [← encR_upd_flags M W fs st pos tp hp fs' hfs]
  have h0 : encR M W fs st pos tp hp 0 = [true] := by simp [hfs]
  have h1 : encR M W fs st pos tp hp 1 = [] := by simp [hfs]
  cases ho : M.output fs' with
  | none =>
      have e : Function.update (Function.update (encR M W fs st pos tp hp) 0
          (if (none : Option Bool) = none then [true] else []) ) 1
          (if (none : Option Bool) = some true then [true] else []) =
          encR M W fs st pos tp hp := by
        simp only [if_true, reduceCtorEq, if_false]
        rw [← h0, Function.update_eq_self, ← h1, Function.update_eq_self]
      rw [e]
      exact runs_skip _ 0 0
  | some b =>
      have e0 : (if (some b : Option Bool) = none then [true] else []) = ([] : List Bool) := by
        simp
      rw [e0]
      refine (runs_clear _ 0 (lt_regK (by omega)) N (by rw [h0]; simp; omega) hB 0).seq ?_
      cases b with
      | true =>
          refine (runs_append _ 1 (lt_regK (by omega)) true N
            (by rw [Function.update_of_ne (by omega), h1]; simp; omega) hB 0).of_eq rfl ?_
          rw [Function.update_of_ne (by omega), h1]; simp
      | false =>
          have e1 : (if (some false : Option Bool) = some true then [true] else []) =
              ([] : List Bool) := by simp
          rw [e1]
          refine (runs_skip _ 0 0).of_eq rfl ?_
          have h1' : Function.update (encR M W fs st pos tp hp) 0 [] 1 = [] := by
            rw [Function.update_of_ne (by omega), h1]
          congr 2
          funext r
          by_cases hr : r = 1
          · subst hr; rw [Function.update_self, h1']
          · rw [Function.update_of_ne hr]

end specs

section phases

variable (W : ℤ) (fs : Fin (q + 1)) (st : ℕ) (pos : ℕ → ℕ) (tp : ℕ → ℤ → Bool) (hp : ℕ → ℤ)
variable (N : ℕ) (hB : (N + 3) * wd (regK h w) ≤ B)
include hB

/-- All work tapes: write `b k` and move by `d k`. -/
def tapesOp (h w : ℕ) (b : ℕ → Bool) (d : ℕ → Direction) : Prog :=
  seqFor w (fun k => tapeOp (regK h w) (rL h k) (rR h k) (b k) (d k))

theorem runs_tapesOp (tp' : ℕ → ℤ → Bool) (hp' : ℕ → ℤ) (b : ℕ → Bool) (d : ℕ → Direction)
    (htp : ∀ k, k < w → tp' k = Function.update (tp k) (hp k) (b k))
    (hhp : ∀ k, k < w → hp' k = (d k).move (hp k))
    (hwin : ∀ k, k < w → -W ≤ hp k ∧ hp k ≤ W ∧ -W ≤ hp' k ∧ hp' k ≤ W)
    (hN : (2 * W + 1).toNat ≤ N) :
    Runs x B (tapesOp h w b d) ⟨lay (regK h w) (encR M W fs st pos tp hp), 0, 0⟩
      ⟨lay (regK h w) (encR M W fs st pos (stg w tp' tp) (stg w hp' hp)), 0, 0⟩ := by
  have := runs_seqFor (x := x) (B := B)
    (fun k => tapeOp (regK h w) (rL h k) (rR h k) (b k) (d k))
    (fun m => ⟨lay (regK h w) (encR M W fs st pos (stg m tp' tp) (stg m hp' hp)), 0, 0⟩) w
    (fun _ => rfl) (fun k hk => by
      have hl := encR_L M W fs st pos (stg k tp' tp) (stg k hp' hp) k hk
      have hr := encR_R M W fs st pos (stg k tp' tp) (stg k hp' hp) k hk
      rw [stg_of_le k tp' tp k le_rfl, stg_of_le k hp' hp k le_rfl] at hl hr
      have ht := runs_tapeOp (x := x) (B := B) _ (rL h k) (rR h k)
        (by unfold rL regK; omega) (by unfold rR regK; omega) (by unfold rL rR; omega)
        (tp k) (hp k) W hl hr (b k) (d k) ⟨(hwin k hk).1, (hwin k hk).2.1⟩
        (by rw [← hhp k hk]; exact ⟨(hwin k hk).2.2.1, (hwin k hk).2.2.2⟩) N hN hB 0
      refine ht.of_eq rfl ?_
      rw [← htp k hk, ← hhp k hk, encR_upd_tape M W _ _ _ _ _ k hk, stg_succ, stg_succ])
  rw [stg_zero, stg_zero] at this
  exact this

/-- All input heads: move head `j` by `d j`, given the symbol `sym j` it reads. -/
def headsOp (h w : ℕ) (d : ℕ → Direction) (sym : ℕ → InputSymbol) : Prog :=
  seqFor h (fun j => headOp (regK h w) j (d j) (sym j))

theorem runs_headsOp (pos' : ℕ → ℕ) (d : ℕ → Direction) (sym : ℕ → InputSymbol)
    (hmove : ∀ j, j < h →
      (d j = .right → sym j = .rightMarker → pos' j = pos j) ∧
      (d j = .right → sym j ≠ .rightMarker → pos' j = pos j + 1) ∧
      (d j = .left → pos' j = pos j - 1) ∧ (d j = .stay → pos' j = pos j))
    (hN : ∀ j, j < h → (bnum (pos j)).length + 1 ≤ N) :
    Runs x B (headsOp h w d sym) ⟨lay (regK h w) (encR M W fs st pos tp hp), 0, 0⟩
      ⟨lay (regK h w) (encR M W fs st (stg h pos' pos) tp hp), 0, 0⟩ := by
  have := runs_seqFor (x := x) (B := B) (fun j => headOp (regK h w) j (d j) (sym j))
    (fun m => ⟨lay (regK h w) (encR M W fs st (stg m pos' pos) tp hp), 0, 0⟩) h
    (fun _ => rfl) (fun j hj => by
      set R := encR M W fs st (stg j pos' pos) tp hp with hR
      have hc : R (rCnt j) = bnum (pos j) := by
        rw [hR, encR_cnt M W _ _ _ _ _ j hj, stg_of_le j pos' pos j le_rfl]
      have hRC : R 4 = [] := encR_C M W _ _ _ _ _
      have hROF : R 5 = [] := encR_OF M W _ _ _ _ _
      have hjK : rCnt j < regK h w := by unfold rCnt regK; omega
      have hfin : encR M W fs st (stg (j + 1) pos' pos) tp hp =
          Function.update R (rCnt j) (bnum (pos' j)) := by
        rw [hR, encR_upd_cnt M W _ _ _ _ _ j hj, stg_succ]
      rw [hfin]
      obtain ⟨hr1, hr2, hl, hs⟩ := hmove j hj
      unfold headOp
      cases hd : d j with
      | right =>
          by_cases hsym : sym j = .rightMarker
          · rw [if_pos hsym, hr1 hd hsym, ← hc, Function.update_eq_self]
            exact runs_skip _ 0 0
          · rw [if_neg hsym, hr2 hd hsym]
            have hi := runs_incr (x := x) (B := B) R (rCnt j) 4 5 hjK (lt_regK (by omega))
              (lt_regK (by omega)) (by unfold rCnt; omega) (by unfold rCnt; omega) (by omega)
              hRC hROF N (by rw [hc]; exact hN j hj) hB 0
            rw [hc, bincr_bnum] at hi
            exact hi
      | left =>
          rw [hl hd]
          have hi := runs_decr (x := x) (B := B) R (rCnt j) 4 5 hjK (lt_regK (by omega))
            (lt_regK (by omega)) (by unfold rCnt; omega) (by unfold rCnt; omega) (by omega)
            hRC hROF N (by rw [hc]; exact hN j hj) hB 0
          rw [hc, bdecr_bnum] at hi
          exact hi
      | stay =>
          rw [hs hd, ← hc, Function.update_eq_self]
          exact runs_skip _ 0 0)
  rw [stg_zero] at this
  exact this

end phases

end FromLogspace

end Complexity.Space
