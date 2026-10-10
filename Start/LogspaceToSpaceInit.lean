import Start.LogspaceToSpaceTransition

/-!
# Simulating an `ExactDerandomization` machine by a host tape program: initialization

This library's own module (task `M27-SPACE-MODEL-COMPILE`).  The host machine starts on a blank
work tape.  `FromLogspace.initProg M c₀` builds, from the blank tape, the register file
`FromLogspace.encC M W (M.initial n)` of the initial configuration, with the window radius

  `W = winR c₀ n = c₀ · (|bnum n| + 1)`,

where `|bnum n| = ⌊log₂ (n + 1)⌋` is the length of the bijective base-two numeral of the input
length `n`.  Since `⌊log₂ (n + 1)⌋ + 1 = ⌈log₂ (n + 2)⌉`, this is exactly `c₀ ⌈log₂ (n + 2)⌉`, the
space bound of a `LogSpace` machine with constant `c₀` (`FromLogspace.winR_eq_clog`).

The program writes the ruler, counts the input length into register `6` (`countProg`), copies the
counter to register `3`, grows every window by `c₀` cells once and once more per bit of the counter
(`growBy`, `growLoop`), returns the input head to `0` by counting the counter down (`moveBy`), and
writes the initial state and flags.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace FromLogspace

open Tracks Prog
open ExactDerandomization (Word InputSymbol Direction Configuration readInput)

variable {x : List Bool} {B : ℕ}

/-! ### The register file during initialization -/

/-- The register file during initialization: the windows of tape `k` hold `L k` and `Rr k` blanks,
registers `3` and `6` hold `c3` and `c6`, every other register is empty. -/
def initFile (h w : ℕ) (L Rr : ℕ → ℕ) (c3 c6 : List Bool) : ℕ → List Bool := fun r =>
  if r = 3 then c3 else if r = 6 then c6 else if r < 7 + h then []
  else if r < 7 + h + 2 * w then
    (if (r - 7 - h) % 2 = 0 then List.replicate (L ((r - 7 - h) / 2)) false
      else List.replicate (Rr ((r - 7 - h) / 2)) false)
  else []

section initFile

variable (h w : ℕ) (L Rr : ℕ → ℕ) (c3 c6 : List Bool)

theorem initFile_rL (k : ℕ) (hk : k < w) :
    initFile h w L Rr c3 c6 (rL h k) = List.replicate (L k) false := by
  simp only [initFile, rL]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos (by omega)]
  congr 2; omega

theorem initFile_rR (k : ℕ) (hk : k < w) :
    initFile h w L Rr c3 c6 (rR h k) = List.replicate (Rr k) false := by
  simp only [initFile, rR]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg (by omega)]
  congr 2; omega

@[simp] theorem initFile_3 : initFile h w L Rr c3 c6 3 = c3 := by simp [initFile]
@[simp] theorem initFile_6 : initFile h w L Rr c3 c6 6 = c6 := by simp [initFile]

theorem initFile_low (r : ℕ) (hr : r < 7 + h) (h3 : r ≠ 3) (h6 : r ≠ 6) :
    initFile h w L Rr c3 c6 r = [] := by
  simp [initFile, h3, h6, hr]

theorem initFile_congr {L' Rr' : ℕ → ℕ} (hL : ∀ k, k < w → L k = L' k)
    (hR : ∀ k, k < w → Rr k = Rr' k) :
    initFile h w L Rr c3 c6 = initFile h w L' Rr' c3 c6 := by
  funext r
  simp only [initFile]
  split_ifs <;> first | rfl | rw [hL _ (by omega)] | rw [hR _ (by omega)]

theorem initFile_upd_rL (k : ℕ) (hk : k < w) (m : ℕ) :
    Function.update (initFile h w L Rr c3 c6) (rL h k) (List.replicate m false) =
      initFile h w (Function.update L k m) Rr c3 c6 := by
  funext r
  by_cases hr : r = rL h k
  · subst hr; rw [Function.update_self, initFile_rL _ _ _ _ _ _ k hk, Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [rL] at hr
    simp only [initFile]
    split_ifs <;> first | rfl | (rw [Function.update_of_ne (by omega)])

theorem initFile_upd_rR (k : ℕ) (hk : k < w) (m : ℕ) :
    Function.update (initFile h w L Rr c3 c6) (rR h k) (List.replicate m false) =
      initFile h w L (Function.update Rr k m) c3 c6 := by
  funext r
  by_cases hr : r = rR h k
  · subst hr; rw [Function.update_self, initFile_rR _ _ _ _ _ _ k hk, Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [rR] at hr
    simp only [initFile]
    split_ifs <;> first | rfl | (rw [Function.update_of_ne (by omega)])

theorem initFile_upd_3 (c3' : List Bool) :
    Function.update (initFile h w L Rr c3 c6) 3 c3' = initFile h w L Rr c3' c6 := by
  funext r
  by_cases hr : r = 3
  · subst hr; simp
  · rw [Function.update_of_ne hr]; simp [initFile, hr]

theorem initFile_upd_6 (c6' : List Bool) :
    Function.update (initFile h w L Rr c3 c6) 6 c6' = initFile h w L Rr c3 c6' := by
  funext r
  by_cases hr : r = 6
  · subst hr; simp
  · rw [Function.update_of_ne hr]; simp [initFile, hr]

theorem initFile_zero : initFile h w (fun _ => 0) (fun _ => 0) [] [] = fun _ => [] := by
  funext r; simp [initFile]

end initFile

/-! ### Growing the windows -/

/-- Append `dl` blanks to every left window register and `dr` blanks to every right one. -/
def growBy (h w dl dr : ℕ) : Prog :=
  seqFor w (fun k => .seq (appendN (regK h w) (rL h k) false dl)
    (appendN (regK h w) (rR h k) false dr))

theorem runs_growBy (h w : ℕ) (a b dl dr : ℕ) (c3 c6 : List Bool) (N : ℕ)
    (hB : (N + 3) * wd (regK h w) ≤ B) (hNa : a + dl ≤ N) (hNb : b + dr ≤ N) (i : ℕ) :
    Runs x B (growBy h w dl dr)
      ⟨lay (regK h w) (initFile h w (fun _ => a) (fun _ => b) c3 c6), 0, i⟩
      ⟨lay (regK h w) (initFile h w (fun _ => a + dl) (fun _ => b + dr) c3 c6), 0, i⟩ := by
  have := runs_seqFor (x := x) (B := B) (fun k => .seq (appendN (regK h w) (rL h k) false dl)
      (appendN (regK h w) (rR h k) false dr))
    (fun m => ⟨lay (regK h w) (initFile h w (stg m (fun _ => a + dl) (fun _ => a))
      (stg m (fun _ => b + dr) (fun _ => b)) c3 c6), 0, i⟩) w (fun _ => rfl) (fun k hk => by
        set F := initFile h w (stg k (fun _ => a + dl) (fun _ => a))
          (stg k (fun _ => b + dr) (fun _ => b)) c3 c6 with hF
        have hl : F (rL h k) = List.replicate a false := by
          rw [hF, initFile_rL _ _ _ _ _ _ k hk, stg_of_le _ _ _ _ le_rfl]
        have hr : F (rR h k) = List.replicate b false := by
          rw [hF, initFile_rR _ _ _ _ _ _ k hk, stg_of_le _ _ _ _ le_rfl]
        refine (runs_appendN F (rL h k) (by unfold rL regK; omega) false dl N
          (by rw [hl]; simp; omega) hB i).seq ?_
        rw [hl, ← List.replicate_add, hF, initFile_upd_rL _ _ _ _ _ _ k hk]
        set F' := initFile h w (Function.update (stg k (fun _ => a + dl) (fun _ => a)) k (a + dl))
          (stg k (fun _ => b + dr) (fun _ => b)) c3 c6 with hF'
        have hr' : F' (rR h k) = List.replicate b false := by
          rw [hF', initFile_rR _ _ _ _ _ _ k hk, stg_of_le _ _ _ _ le_rfl]
        refine (runs_appendN F' (rR h k) (by unfold rR regK; omega) false dr N
          (by rw [hr']; simp; omega) hB i).of_eq rfl ?_
        rw [hr', ← List.replicate_add, hF', initFile_upd_rR _ _ _ _ _ _ k hk]
        have e1 := stg_succ k (fun _ => a + dl) (fun _ => a)
        have e2 := stg_succ k (fun _ => b + dr) (fun _ => b)
        rw [e1, e2])
  refine this.of_eq ?_ ?_
  · rw [stg_zero, stg_zero]
  · congr 2
    apply initFile_congr
    · intro k hk; simp [stg, hk]
    · intro k hk; simp [stg, hk]

/-! ### Counting the input length -/

/-- Count the input length into register `6`, leaving the input head at the end marker. -/
def countProg (K : ℕ) : Prog := .loop (fun a _ => a.isSome) (.seq (incr K 6 4 5) (imove .right))

theorem runs_countProg {K : ℕ} (R : ℕ → List Bool) (hK : 6 < K) (hR4 : R 4 = []) (hR5 : R 5 = [])
    (hR6 : R 6 = []) (N : ℕ) (hB : (N + 3) * wd K ≤ B)
    (hN : Nat.log 2 (x.length + 1) + 1 ≤ N) :
    Runs x B (countProg K) ⟨lay K R, 0, 0⟩
      ⟨lay K (Function.update R 6 (bnum x.length)), 0, x.length⟩ := by
  have h0 : R = Function.update R 6 (bnum 0) := by rw [show bnum 0 = [] from rfl, ← hR6,
    Function.update_eq_self]
  have := Runs.loop_stages (x := x) (B := B) (t := fun a _ => a.isSome)
    (body := .seq (incr K 6 4 5) (imove .right))
    (fun k => ⟨lay K (Function.update R 6 (bnum k)), 0, k⟩) x.length
    (fun k _ => by by_cases hk : k < x.length <;> simp [hk])
    (fun k hk => by
      have hi := runs_incr (x := x) (B := B) (Function.update R 6 (bnum k)) 6 4 5 hK (by omega)
        (by omega) (by omega) (by omega) (by omega)
        (by rw [Function.update_of_ne (by omega)]; exact hR4)
        (by rw [Function.update_of_ne (by omega)]; exact hR5) N
        (by
          rw [Function.update_self]
          have := length_bnum_le k
          have : Nat.log 2 (k + 1) ≤ Nat.log 2 (x.length + 1) := Nat.log_mono_right (by omega)
          omega) hB k
      rw [Function.update_self, Function.update_idem, bincr_bnum] at hi
      refine hi.seq ((runs_imoveR _ 0 k).of_eq rfl ?_)
      congr 1; omega)
  rw [← h0] at this
  exact this

/-! ### The window loop -/

/-- Grow every window by `c₀` cells for each bit of register `3`, emptying it. -/
def growLoop (h w c₀ : ℕ) : Prog :=
  whileNE 3 (popBranch (regK h w) 3 (growBy h w c₀ c₀) (growBy h w c₀ c₀))

theorem runs_growLoop (h w c₀ a b : ℕ) (l c6 : List Bool) (N : ℕ)
    (hB : (N + 3) * wd (regK h w) ≤ B) (hNa : a + c₀ * l.length ≤ N)
    (hNb : b + c₀ * l.length ≤ N) (hNl : l.length ≤ N) (i : ℕ) :
    Runs x B (growLoop h w c₀)
      ⟨lay (regK h w) (initFile h w (fun _ => a) (fun _ => b) l c6), 0, i⟩
      ⟨lay (regK h w) (initFile h w (fun _ => a + c₀ * l.length) (fun _ => b + c₀ * l.length)
        [] c6), 0, i⟩ := by
  have htk : ∀ k, k < l.length → l.take (l.length - k) ≠ [] := fun k hk he => by
    have := congrArg List.length he; simp at this; omega
  unfold growLoop
  have := runs_whileNE (x := x) (B := B) (K := regK h w)
    (fun k => initFile h w (fun _ => a + c₀ * k) (fun _ => b + c₀ * k) (l.take (l.length - k)) c6)
    3 l.length (by unfold regK; omega) (popBranch (regK h w) 3 (growBy h w c₀ c₀) (growBy h w c₀ c₀))
    (fun k hk => by simpa using htk k hk) (by simp) (wd_lt_of_hB hB) i (fun k hk => by
      have hne : initFile h w (fun _ => a + c₀ * k) (fun _ => b + c₀ * k)
          (l.take (l.length - k)) c6 3 ≠ [] := by simpa using htk k hk
      refine runs_popBranch _ 3 (by unfold regK; omega) hne N (by simp; omega) hB i _ _ _ ?_
      have hdl : (initFile h w (fun _ => a + c₀ * k) (fun _ => b + c₀ * k)
          (l.take (l.length - k)) c6 3).dropLast = l.take (l.length - (k + 1)) := by
        simp only [initFile_3, List.dropLast_eq_take, List.length_take, List.take_take]
        congr 1; omega
      rw [hdl, initFile_upd_3]
      have hg := runs_growBy (x := x) (B := B) h w (a + c₀ * k) (b + c₀ * k) c₀ c₀
        (l.take (l.length - (k + 1))) c6 N hB
        (by have : c₀ * (k + 1) ≤ c₀ * l.length := Nat.mul_le_mul_left _ (by omega)
            rw [Nat.mul_succ] at this; omega)
        (by have : c₀ * (k + 1) ≤ c₀ * l.length := Nat.mul_le_mul_left _ (by omega)
            rw [Nat.mul_succ] at this; omega) i
      have e1 : a + c₀ * k + c₀ = a + c₀ * (k + 1) := by ring
      have e2 : b + c₀ * k + c₀ = b + c₀ * (k + 1) := by ring
      rw [e1, e2] at hg
      split <;> exact hg)
  simpa using this

/-! ### The whole initialization -/

/-- The window radius: `c₀ (|bnum n| + 1)`. -/
def winR (c₀ n : ℕ) : ℕ := c₀ * ((bnum n).length + 1)

/-- Write the initial flags. -/
def flagsInit {q w h : ℕ} (M : ExactDerandomization.Machine q w h) : Prog :=
  .seq (if M.output M.initialState = none then append (regK h w) 0 true else skip)
    (if M.output M.initialState = some true then append (regK h w) 1 true else skip)

/-- **Initialization**: from the blank tape to the register file of the initial configuration. -/
def initProg {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (c₀ : ℕ) : Prog :=
  .seq (write true) (.seq (countProg (regK h w)) (.seq (assign (regK h w) 6 3)
    (.seq (growBy h w 0 1) (.seq (growBy h w c₀ c₀) (.seq (growLoop h w c₀)
      (.seq (moveBy (regK h w) 6 4 5 .left)
        (.seq (appendN (regK h w) 2 true M.initialState.val) (flagsInit M))))))))

theorem cells_const_false (a : ℤ) (m : ℕ) : cells (fun _ => false) a m = List.replicate m false := by
  simp [cells]

theorem encC_initial {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (W : ℕ) (n : ℕ) :
    encC M (W : ℤ) (M.initial n) =
      Function.update (Function.update (Function.update
        (initFile h w (fun _ => W) (fun _ => W + 1) [] []) 2
          (List.replicate M.initialState.val true)) 0
          (if M.output M.initialState = none then [true] else [])) 1
          (if M.output M.initialState = some true then [true] else []) := by
  funext r
  simp only [encC, encR, Function.update_apply, ExactDerandomization.Machine.initial]
  by_cases h1 : r = 1
  · subst h1; simp; congr
  by_cases h0 : r = 0
  · subst h0; simp; congr
  by_cases h2 : r = 2
  · subst h2; simp
  rw [if_neg h1, if_neg h0, if_neg h2]
  simp only [h0, h1, h2, if_false]
  simp only [initFile, posOf, tpOf, hpOf]
  split_ifs <;> first
    | rfl
    | omega
    | (simp [lftOf, rgtOf, cells_const_false]; done)

theorem runs_flagsInit {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (R : ℕ → List Bool)
    (hR0 : R 0 = []) (hR1 : R 1 = []) (N : ℕ) (hB : (N + 3) * wd (regK h w) ≤ B) (hN1 : 1 ≤ N)
    (i : ℕ) :
    Runs x B (flagsInit M) ⟨lay (regK h w) R, 0, i⟩
      ⟨lay (regK h w) (Function.update (Function.update R 0
        (if M.output M.initialState = none then [true] else [])) 1
        (if M.output M.initialState = some true then [true] else [])), 0, i⟩ := by
  have h0K : 0 < regK h w := by unfold regK; omega
  have h1K : 1 < regK h w := by unfold regK; omega
  unfold flagsInit
  rcases ho : M.output M.initialState with _ | b
  · simp only [if_true, reduceCtorEq, if_false]
    refine (runs_append R 0 h0K true N (by rw [hR0]; simp; omega) hB i).seq ?_
    refine (runs_skip _ 0 i).of_eq rfl ?_
    congr 2; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
  · cases b with
    | true =>
        simp only [reduceCtorEq, if_false, if_true]
        refine (runs_skip _ 0 i).seq ?_
        refine (runs_append R 1 h1K true N (by rw [hR1]; simp; omega) hB i).of_eq rfl ?_
        congr 2; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    | false =>
        simp only [reduceCtorEq, if_false, Option.some.injEq, Bool.false_eq_true]
        refine (runs_skip _ 0 i).seq ((runs_skip _ 0 i).of_eq rfl ?_)
        congr 2; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all

theorem runs_initProg {q w h : ℕ} (M : ExactDerandomization.Machine q w h) (c₀ : ℕ) (N : ℕ)
    (hB : (N + 3) * wd (regK h w) ≤ B) (hNW : 2 * winR c₀ x.length + 1 ≤ N) (hNq : q + 1 ≤ N)
    (hNp : Nat.log 2 (x.length + 2) + 1 ≤ N) :
    Runs x B (initProg M c₀) ⟨fun _ => false, 0, 0⟩
      ⟨lay (regK h w) (encC M (winR c₀ x.length : ℤ) (M.initial x.length)), 0, 0⟩ := by
  set n := x.length with hn
  set K := regK h w with hK
  set ℓ := (bnum n).length with hℓdef
  have hℓ : ℓ ≤ Nat.log 2 (n + 1) := length_bnum_le n
  have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  have hW : winR c₀ n = c₀ + c₀ * ℓ := by unfold winR; ring
  have h6K : 6 < K := by rw [hK]; unfold regK; omega
  have hwB := wd_lt_of_hB hB
  unfold initProg
  -- the ruler
  have s1 : Runs x B (write true) ⟨fun _ => false, 0, 0⟩
      ⟨lay K (initFile h w (fun _ => 0) (fun _ => 0) [] []), 0, 0⟩ :=
    (runs_write true (fun _ => false) 0 0).of_eq rfl (by rw [initFile_zero, ← lay_empty])
  refine s1.seq ?_
  -- counting
  have s2 := runs_countProg (x := x) (B := B) (initFile h w (fun _ => 0) (fun _ => 0) [] []) h6K
    (initFile_low _ _ _ _ _ _ 4 (by omega) (by omega) (by omega))
    (initFile_low _ _ _ _ _ _ 5 (by omega) (by omega) (by omega)) (by simp) N hB
    (by rw [← hn]; omega)
  rw [initFile_upd_6] at s2
  refine s2.seq ?_
  -- copy the counter to register 3
  have s3 := runs_assign (x := x) (B := B) (initFile h w (fun _ => 0) (fun _ => 0) [] (bnum n))
    6 3 h6K (by omega) (by omega) N (by simp; omega) (by simp) hB n
  rw [initFile_6, initFile_upd_3] at s3
  refine s3.seq ?_
  -- the windows
  have s4 := runs_growBy (x := x) (B := B) h w 0 0 0 1 (bnum n) (bnum n) N hB (by omega)
    (by omega) n
  refine s4.seq ?_
  have s5 := runs_growBy (x := x) (B := B) h w (0 + 0) (0 + 1) c₀ c₀ (bnum n) (bnum n) N hB
    (by omega) (by omega) n
  refine s5.seq ?_
  have s6 := runs_growLoop (x := x) (B := B) h w c₀ (0 + 0 + c₀) (0 + 1 + c₀) (bnum n) (bnum n)
    N hB (by rw [← hℓdef]; omega) (by rw [← hℓdef]; omega) (by rw [← hℓdef]; omega) n
  refine s6.seq ?_
  -- the input head back to the origin
  set F := initFile h w (fun _ => 0 + 0 + c₀ + c₀ * ℓ) (fun _ => 0 + 1 + c₀ + c₀ * ℓ) []
    (bnum n) with hF
  have hF4 : F 4 = [] := initFile_low _ _ _ _ _ _ 4 (by omega) (by omega) (by omega)
  have hF5 : F 5 = [] := initFile_low _ _ _ _ _ _ 5 (by omega) (by omega) (by omega)
  have hF6 : F 6 = bnum n := initFile_6 _ _ _ _ _ _
  have hw7 := wl_moveBy_left (x := x) (B := B) (K := K) F 6 6 4 5 h6K (by omega) (by omega)
    (by omega) (by omega) (by omega) hF4 hF5 N hB
    (fun l hl => by rw [hF6] at hl; omega) n (bnum n) n (bval_bnum n) (by rw [hF6])
  have s7 := runs_whileNE_of_wl h6K hwB hw7
  rw [Nat.sub_self, hF, initFile_upd_6] at s7
  refine s7.seq ?_
  -- the initial state
  set F' := initFile h w (fun _ => 0 + 0 + c₀ + c₀ * ℓ) (fun _ => 0 + 1 + c₀ + c₀ * ℓ) [] []
    with hF'
  have hF'2 : F' 2 = [] := initFile_low _ _ _ _ _ _ 2 (by omega) (by omega) (by omega)
  have s8 := runs_appendN (x := x) (B := B) F' 2 (by omega) true M.initialState.val N
    (by rw [hF'2]; have := M.initialState.isLt; simp; omega) hB 0
  rw [hF'2, List.nil_append] at s8
  rw [initFile_upd_6]
  refine s8.seq ?_
  -- the flags
  have hG0 : Function.update F' 2 (List.replicate M.initialState.val true) 0 = [] := by
    rw [Function.update_of_ne (by omega)]
    exact initFile_low _ _ _ _ _ _ 0 (by omega) (by omega) (by omega)
  have hG1 : Function.update F' 2 (List.replicate M.initialState.val true) 1 = [] := by
    rw [Function.update_of_ne (by omega)]
    exact initFile_low _ _ _ _ _ _ 1 (by omega) (by omega) (by omega)
  have s9 := runs_flagsInit (x := x) (B := B) M (Function.update F' 2
    (List.replicate M.initialState.val true)) hG0 hG1 N hB (by omega) 0
  refine s9.of_eq rfl ?_
  rw [encC_initial M (winR c₀ n) n, hF']
  congr 5
  rw [hW]
  congr 1 <;> funext _ <;> omega

end FromLogspace

end Complexity.Space
