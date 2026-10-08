import Start.DepthThreeTapeProgram
import Start.DepthThreeMachineBasic
import Lean.Elab.Tactic.Omega

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/TapeScan.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace DepthThreeLowerBound

def seesAtom (a : TapeAtom) : TapeSymbol → TapeFlags → Bool :=
  fun c _ => decide (c.1 = a)

def seesMark (m : TapeMark) : TapeSymbol → TapeFlags → Bool :=
  fun c _ => c.2 m

namespace TapeProgram

variable {Q : Type}

theorem runs_scan (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir}
    {p : TapeSymbol → TapeFlags → Bool} (h : P q = .scan d p q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) (k : ℕ)
    (hskip : ∀ i < k, p (((Turing.Tape.move d)^[i] T).head) v = false)
    (hstop : p (((Turing.Tape.move d)^[k] T).head) v = true) :
    RunsIn (Turing.TM1.step P.code) (cfg q v T)
      (cfg q' v ((Turing.Tape.move d)^[k] T)) (k + 1) := by
  induction k generalizing T with
  | zero =>
      exact RunsIn.single (step_scan_stop P h v T hstop)
  | succ k ih =>
      have hp : p T.head v = false := by
        simpa only [Function.iterate_zero_apply] using hskip 0 (Nat.zero_lt_succ k)
      have hskip' : ∀ i < k,
          p (((Turing.Tape.move d)^[i] (T.move d)).head) v = false := by
        intro i hi
        simpa only [Function.iterate_succ_apply] using hskip (i + 1) (Nat.succ_lt_succ hi)
      have hstop' : p (((Turing.Tape.move d)^[k] (T.move d)).head) v = true := by
        simpa only [Function.iterate_succ_apply] using hstop
      have hfirst := RunsIn.single (step_scan_move P h v T hp)
      have hrest := ih (T.move d) hskip' hstop'
      have hboth := hfirst.trans hrest
      simpa only [Function.iterate_succ_apply, Nat.add_comm] using hboth

theorem runs_scan_atom (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir} (a : TapeAtom)
    (h : P q = .scan d (seesAtom a) q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) (k : ℕ)
    (hskip : ∀ i < k, (((Turing.Tape.move d)^[i] T).head).1 ≠ a)
    (hstop : (((Turing.Tape.move d)^[k] T).head).1 = a) :
    RunsIn (Turing.TM1.step P.code) (cfg q v T)
      (cfg q' v ((Turing.Tape.move d)^[k] T)) (k + 1) := by
  apply runs_scan P h v T k
  · intro i hi
    simp only [seesAtom, decide_eq_false_iff_not]
    exact hskip i hi
  · simp only [seesAtom, hstop, decide_true]

theorem runs_scan_mark (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir} (m : TapeMark)
    (h : P q = .scan d (seesMark m) q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) (k : ℕ)
    (hskip : ∀ i < k, (((Turing.Tape.move d)^[i] T).head).2 m = false)
    (hstop : (((Turing.Tape.move d)^[k] T).head).2 m = true) :
    RunsIn (Turing.TM1.step P.code) (cfg q v T)
      (cfg q' v ((Turing.Tape.move d)^[k] T)) (k + 1) :=
  runs_scan P h v T k hskip hstop

end TapeProgram

end DepthThreeLowerBound

