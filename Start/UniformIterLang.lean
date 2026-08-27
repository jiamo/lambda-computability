/-
**A language decided by iterating a P-uniform circuit.**

`Start/UniformIterate.lean` proves that the stack of polynomially many copies of a P-uniform stage
over a P-uniform base is P-uniform.  This module packages that rule as a statement about
*languages*: a device whose configuration is a word of `w n` wires, whose initial configuration is
produced by a P-uniform family and whose one-step transition is computed by a P-uniform family,
decides — after a Cobham-computable number of steps, on the last wire of its configuration — a
language that is P-uniformly decidable, hence reduces to SAT in polynomial time.

Main results:

* `Complexity.pUniformDecidable_iterLang` — **the rule**;
* `Complexity.polyManyOne_SAT_iterLang` — and the reduction to SAT it yields.
-/

import Start.UniformIterate
import Start.UniformDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-- **A language decided by iterating a P-uniform stage circuit is P-uniformly decidable.**

The configuration of the device is the word of `w n` values carried by the topmost `w n` gates of
the stack; `cd` initializes it from the input, `cb` is the one-step transition, `k n` steps are
run, and the verdict is read off the last wire of the final configuration. -/
theorem pUniformDecidable_iterLang {cb cd : ℕ → Circuit} {k w : ℕ → ℕ} {L : Language}
    (hcb : CodeUniform cb) (hcd : CodeUniform cd)
    (hwfb : ∀ n, wf (cb n)) (hwfd : ∀ n, wf (cd n))
    (hinp : ∀ n, inpsLt (w n) (cb n))
    (hwd : ∀ n, w n ≤ (cd n).length) (hwb : ∀ n, w n ≤ (cb n).length)
    (hpos : ∀ n, 0 < w n)
    {kT wT : Cob} (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true)
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hacc : ∀ (n : ℕ) (y : Word), Pinned n y →
      ((stateC y (cb n) (cd n) (w n) (k n)).getD (w n - 1) false = true ↔ L (inWord n y))) :
    PUniformDecidable L := by
  refine ⟨fun n => iterC (cb n) (cd n) (w n) (k n), fun n => ?_, fun n => ?_, fun n y hy => ?_,
    codeUniform_iterC hcb hcd hwfb hinp hwb (fun n => lt_of_lt_of_le (hpos n) (hwb n))
      (kT := kT) (wT := wT) hk hwT⟩
  · intro h
    have h' : iterC (cb n) (cd n) (w n) (k n) = [] := h
    have hle : w n ≤ (iterC (cb n) (cd n) (w n) (k n)).length := le_length_iterC (hwd n) (k n)
    rw [h', List.length_nil] at hle
    exact absurd (hpos n) (by omega)
  · exact wf_iterC (hwfb n) (hwfd n) (hinp n) (hwd n) (k n)
  · rw [out_iterC_state (hpos n) (hwd n) y (k n)]
    exact hacc n y hy

/-- **Such a language reduces to SAT in polynomial time**, unconditionally. -/
theorem polyManyOne_SAT_iterLang {cb cd : ℕ → Circuit} {k w : ℕ → ℕ} {L : Language}
    (hcb : CodeUniform cb) (hcd : CodeUniform cd)
    (hwfb : ∀ n, wf (cb n)) (hwfd : ∀ n, wf (cd n))
    (hinp : ∀ n, inpsLt (w n) (cb n))
    (hwd : ∀ n, w n ≤ (cd n).length) (hwb : ∀ n, w n ≤ (cb n).length)
    (hpos : ∀ n, 0 < w n)
    {kT wT : Cob} (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true)
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hacc : ∀ (n : ℕ) (y : Word), Pinned n y →
      ((stateC y (cb n) (cd n) (w n) (k n)).getD (w n - 1) false = true ↔ L (inWord n y))) :
    L ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable
    (pUniformDecidable_iterLang hcb hcd hwfb hwfd hinp hwd hwb hpos hk hwT hacc)

end Complexity
