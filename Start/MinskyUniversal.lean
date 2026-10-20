/-
**A fixed universal code whose halting problem is undecidable** — task `M25-KCM-UNIVERSAL`
(round 9, part B).

The route chosen in round 9 compiles a *single fixed* universal code into a counter machine, so
that the compiler needs correctness for all codes but no computability:

* `Minsky.Universal.exists_universal_code` — there is a code `u` with
  `u.eval (Nat.pair (encode c) x) = c.eval x` for every code `c` and input `x`
  (`Nat.Partrec.Code.exists_code` applied to `n ↦ eval (ofNat n.unpair.1) n.unpair.2`, partial
  recursive by `Nat.Partrec.Code.eval_part`);
* `Minsky.Universal.universal_dom_undecidable` — for such a `u`, the halting set
  `{m | (u.eval m).Dom}` is not computable: the halting problem `ComputablePred.halting_problem`
  reduces to it by the computable map `c ↦ Nat.pair (encode c) 0`.

With a compiled machine `M_u` simulating `u`, the fixed-machine statement
`¬ ComputablePred (fun m => KM.Halts M_u (input m))` follows by composing with the primitive
recursive input map; the compilation of `u` is the open step (see
`docs/goal/evidence/M25-FSUB-UNDECIDABLE.md`, round 9).
-/

import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Universal

open Nat.Partrec

/-- **A universal code**: `u` runs the code encoded in the first component of its input on the
second component. -/
theorem exists_universal_code : ∃ u : Code, ∀ (c : Code) (x : ℕ),
    u.eval (Nat.pair (Encodable.encode c) x) = c.eval x := by
  have hf : Partrec (fun n : ℕ => (Denumerable.ofNat Code n.unpair.1).eval n.unpair.2) :=
    Code.eval_part.comp ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair)
  obtain ⟨u, hu⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  refine ⟨u, fun c x => ?_⟩
  rw [hu]
  simp

/-- **The halting problem of a universal code is undecidable.** -/
theorem universal_dom_undecidable {u : Code}
    (hu : ∀ (c : Code) (x : ℕ), u.eval (Nat.pair (Encodable.encode c) x) = c.eval x) :
    ¬ ComputablePred (fun m : ℕ => (u.eval m).Dom) := by
  rintro ⟨hd, hc⟩
  apply ComputablePred.halting_problem 0
  have heq : ∀ c : Code, (u.eval (Nat.pair (Encodable.encode c) 0)).Dom ↔ (c.eval 0).Dom := by
    intro c; rw [hu]
  refine ⟨fun c => decidable_of_iff _ (heq c), ?_⟩
  have hg : Computable (fun c : Code => Nat.pair (Encodable.encode c) 0) :=
    (Primrec₂.natPair.to_comp).comp Computable.encode (Computable.const 0)
  have := hc.comp hg
  convert this using 2 with c
  simp only [decide_eq_decide]
  exact (heq c).symm

end Universal

end Minsky
