/-
**P ⊆ PSPACE: Cobham terms run in polynomial space on the offline machine.**

The class `P` of the library is defined through Cobham's function algebra
(`Complexity.InP`: `L x ↔ c.eval [x] ≠ []` for a Cobham term `c`), the class `PSPACE` through
offline Turing machines with a space bound (`Complexity.Space.PSPACE`).  This file joins the two:
the tape program `Complexity.Space.cobDecider c` copies the input into a register, runs the
compiled term (`Start/CobhamSpace.lean`) into another one, and looks at the first cell of the
result; by `Complexity.Space.Prog.pspace_of_runs` (`Start/SpaceProgDecide.lean`) it decides the
language of `c` within `(Cob.spaceW c n + 3) · (2K + 1)` cells, a polynomial in `n`.

Main results:

* `Complexity.Space.runs_cobDecider` — the exact-state specification of the decider;
* `Complexity.Space.pspace_of_inP` — **P ⊆ PSPACE**.
-/

import Mathlib
import Start.CobhamSpace
import Start.SpaceProgDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space
open Prog Tracks

/-- A polynomial bound times a constant. -/
theorem PolyBound.mul_const' {p : ℕ → ℕ} (hp : PolyBound p) (w : ℕ) :
    PolyBound (fun n => p n * w) := by
  obtain ⟨a, k, ha⟩ := hp
  exact ⟨a * w, k, fun n => by
    calc p n * w ≤ a * (n + 1) ^ k * w := Nat.mul_le_mul_right _ (ha n)
      _ = a * w * (n + 1) ^ k := by ring⟩

/-- The tape program deciding the language of a Cobham term `c`: set the ruler, copy the input
into register `0`, run the compiled term into register `1`, and look at the presence bit of the
first cell of register `1`. -/
def cobDecider (c : Cob) : Prog :=
  .seq (write true) (.seq (copyInput (c.need + 2) 0)
    (.seq (compile (c.need + 2) c [0] 1 2) (mvR 3)))

theorem runs_cobDecider (c : Cob) (x : List Bool) :
    Runs x ((c.spaceW x.length + 3) * wd (c.need + 2)) (cobDecider c) ⟨fun _ => false, 0, 0⟩
      ⟨lay (c.need + 2) (Function.update (Function.update (fun _ => []) 0 x) 1 (c.eval [x])),
        3, x.length⟩ := by
  set K := c.need + 2 with hK
  set B := (c.spaceW x.length + 3) * wd K with hB
  have hle := Cob.le_spaceW c x.length
  have hB' : (x.length + 3) * wd K ≤ B := Nat.mul_le_mul_right _ (by omega)
  unfold cobDecider
  refine (runs_write true _ 0 0).seq ?_
  rw [lay_empty K]
  refine (runs_copyInput (fun _ => []) 0 (by omega) rfl x.length le_rfl hB').seq ?_
  have hc := compileOK (K := K) (x := x) (B := B) c [0] 1 2 (Function.update (fun _ => []) 0 x)
    x.length x.length (by simp) (by omega) (by simp) (by omega)
    (fun r hr => by rw [Function.update_of_ne (by omega)])
    (fun r => by rw [Function.update_apply]; split_ifs <;> simp)
    le_rfl
  simp only [List.map_cons, List.map_nil, Function.update_self] at hc
  refine hc.seq ?_
  refine (runs_mvR 3 _ 0 _ ?_).of_eq rfl (by simp)
  have : 3 < wd K := by womega
  have : wd K ≤ B :=
    le_trans (by omega) (Nat.mul_le_mul_right _ (show 1 ≤ c.spaceW x.length + 3 by omega))
  omega

/-- **P ⊆ PSPACE.** -/
theorem pspace_of_inP {L : Language} (hL : InP L) : PSPACE L := by
  obtain ⟨c, hc⟩ := hL
  refine pspace_of_runs (cobDecider c) L (fun x => (c.spaceW x.length + 3) * wd (c.need + 2))
    (fun n => (c.spaceW n + 3) * wd (c.need + 2))
    (PolyBound.mul_const' ((Cob.spaceW_polyBound c).add (polyBound_const 3)) _) _ (fun x => ?_)
    (fun x => le_rfl) (runs_cobDecider c) (fun x => ?_)
  · have : 1 ≤ wd (c.need + 2) := by womega
    nlinarith
  · dsimp only
    have := lay_pres (K := c.need + 2)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (c.eval [x])) 1 (by omega) 0
    simp only [zero_mul, zero_add, Function.update_self] at this
    rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, this, hc x, decide_eq_true_iff, List.length_pos_iff]

end Complexity.Space
