import Mathlib.Computability.TuringMachine.Tape

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/TapeWord.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

universe uDepth1

namespace DepthThreeLowerBound

namespace TapeWord

open Turing

variable {Γ : Type uDepth1} [Inhabited Γ]

@[simp] theorem head_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).head = a := rfl

@[simp] theorem move_right_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).move Dir.right = Tape.mk₂ (a :: L) R := rfl

@[simp] theorem write_mk₂_cons (L R : List Γ) (a b : Γ) :
    (Tape.mk₂ L (a :: R)).write b = Tape.mk₂ L (b :: R) := rfl

theorem move_right_iterate_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.right)^[«prefix».length] (Tape.mk₂ L («prefix» ++ R)) =
      Tape.mk₂ («prefix».reverse ++ L) R := by
  induction «prefix» generalizing L with
  | nil => rfl
  | cons a «prefix» ih =>
    rw [List.length_cons, List.cons_append, Function.iterate_succ_apply,
      move_right_mk₂_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (a :: L)

end TapeWord

end DepthThreeLowerBound

