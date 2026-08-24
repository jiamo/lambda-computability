/-
The Cook–Levin theorem: what is proved here, and what the remaining gap is.

`Start/Sat.lean` puts **SAT in NP** (`Complexity.Sat.inNP_SAT`) with an explicit Cobham verifier,
and `Start/Tseitin.lean` proves that **circuit satisfiability translates to CNF satisfiability**
(`Complexity.Tseitin.csat_iff_sat_toCnf`).  What is *not* formalized is the compilation step: that
an arbitrary Cobham verifier can be turned, uniformly and in polynomial time, into a Boolean
circuit whose satisfying inputs are exactly its accepted witnesses.

This module isolates that missing step as an explicit hypothesis `Complexity.CircuitCompilable`
and proves that it is the *only* thing missing: granted it, SAT is NP-complete
(`Complexity.npComplete_SAT_of_circuitCompilable`).  Nothing else in the library depends on the
hypothesis, and it is nowhere assumed — it appears only as an antecedent.

Main definitions:

* `Complexity.Cob.constW` — the Cobham term computing a constant word;
* `Complexity.CircuitCompilable` — the compilation step of the Cook–Levin argument.

Main results:

* `Complexity.polyManyOne_SAT_of_inP` — every language in `P` reduces to SAT (unconditionally);
* `Complexity.npHard_SAT_of_circuitCompilable`,
  `Complexity.npComplete_SAT_of_circuitCompilable` — SAT is NP-hard, hence NP-complete, as soon as
  Cobham verifiers are uniformly circuit-compilable.
-/

import Start.Tseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Constant words -/

/-- The Cobham term computing a constant word. -/
def Cob.constW : Word → Cob
  | [] => .empty
  | b :: w => .comp (.app b) [Cob.constW w]

@[simp] theorem Cob.eval_constW (w : Word) (args : List Word) :
    (Cob.constW w).eval args = w := by
  induction w with
  | nil => simp [Cob.constW]
  | cons b w ih => simp [Cob.constW, ih]

/-! ### Every language in `P` reduces to SAT -/

/-- **Every language in `P` reduces to SAT**: the reduction decides the language itself and
returns a fixed satisfiable or unsatisfiable formula.  (This is of course much weaker than
NP-hardness; it is recorded to show that the reduction machinery around `SAT` works.) -/
theorem polyManyOne_SAT_of_inP {L : Language} (h : InP L) : L ≤ₘᵖ Sat.SAT := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp Cob.iteC [c, .empty, Cob.constW [false, false, false]], fun x => ?_⟩
  have hnil : Sat.SAT [] := by
    have := Sat.SAT_encCnf_nil
    simpa [Sat.encCnf] using this
  have hbad : ¬ Sat.SAT [false, false, false] := by
    have := Sat.not_SAT_encCnf_empty_clause
    simpa [Sat.encCnf, Sat.encClause] using this
  by_cases hx : c.eval [x] = []
  · have hL : ¬ L x := fun hL => (hc x).1 hL hx
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_empty,
      Cob.eval_constW, hx]
    exact iff_of_false hL hbad
  · have hL : L x := (hc x).2 hx
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_empty,
      Cob.eval_constW, if_neg hx]
    exact iff_of_true hL hnil

/-! ### The compilation step -/

/-- **The compilation step of the Cook–Levin theorem**, as a hypothesis on a verifier `v`: there
is a family of well-formed Boolean circuits `cc x`, satisfiable exactly when `v` accepts some
witness for `x`, whose Tseitin translations are produced from `x` by a single Cobham
(polynomial-time) term `gen`.

This is precisely the part of the Cook–Levin argument that is **not** formalized in this library;
it is never assumed, only used as an antecedent below. -/
def CircuitCompilable (v : Cob) : Prop :=
  ∃ (cc : Word → Tseitin.Circuit) (gen : Cob),
    (∀ x, Tseitin.wf (cc x)) ∧
    (∀ x, Tseitin.csat (cc x) ↔ ∃ w : Word, v.eval [x, w] ≠ []) ∧
    (∀ x, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cc x)))

/-- **SAT is NP-hard as soon as Cobham verifiers are uniformly circuit-compilable.**  The proof is
the Tseitin translation: the circuit produced from `x` is satisfiable exactly when its CNF is, and
that CNF is the value of a Cobham term at `x`. -/
theorem npHard_SAT_of_circuitCompilable (H : ∀ v : Cob, CircuitCompilable v) : NPHard Sat.SAT := by
  intro L hL
  obtain ⟨v, -, -, -, -, hacc⟩ := hL
  obtain ⟨cc, gen, hwf, hsat, hgen⟩ := H v
  refine ⟨gen, fun x => ?_⟩
  rw [hacc x, ← hsat x, Tseitin.csat_iff_sat_toCnf (cc x) (hwf x), hgen x, Sat.SAT_encCnf]

/-- **Cook–Levin, modulo the compilation step**: SAT is NP-complete as soon as Cobham verifiers
are uniformly circuit-compilable.  The `InNP` half is unconditional. -/
theorem npComplete_SAT_of_circuitCompilable (H : ∀ v : Cob, CircuitCompilable v) :
    NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_circuitCompilable H⟩

/-- Under the same hypothesis, `P = NP` is equivalent to `SAT ∈ P`. -/
theorem peqNP_iff_inP_SAT_of_circuitCompilable (H : ∀ v : Cob, CircuitCompilable v) :
    PeqNP ↔ InP Sat.SAT :=
  ⟨fun h => h _ Sat.inNP_SAT,
    fun h => peqNP_of_npComplete_of_inP (npComplete_SAT_of_circuitCompilable H) h⟩

end Complexity
