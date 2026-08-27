/-
**Cook–Levin from P-uniformity of the circuit descriptions.**

`Start/CookLevinUniform.lean` reduces the missing half of Cook–Levin to
`Complexity.LengthUniform`: that a Cobham term produces, from any word of length `n`, the *code of
the CNF* of the Tseitin translation of the `n`-th acceptance circuit.  That hypothesis mixes two
things: that the circuit family is uniform, and that the translation is polynomial-time.

`Start/CobhamTseitin.lean` settles the second: the Tseitin translation is a Cobham function on the
codes of circuits.  Composing with it turns the hypothesis into the textbook one — the *circuit
description* itself is produced in polynomial time from `1^n`.

Main results:

* `Complexity.lengthUniform_of_codeUniform` — a P-uniform family of circuit descriptions is
  `LengthUniform`;
* `Complexity.npHard_SAT_of_codeUniform`, `Complexity.npComplete_SAT_of_codeUniform` — **SAT is
  NP-hard, hence NP-complete, as soon as the length-indexed acceptance circuits have P-uniform
  descriptions.**
-/

import Start.CookLevinUniform
import Start.CobhamTseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- A **length-indexed family of circuits has P-uniform descriptions** when the code of its `n`-th
member is produced by a single Cobham term from any word of length `n`. -/
def CodeUniform (cf : ℕ → Tseitin.Circuit) : Prop :=
  ∃ gen : Cob, ∀ x : Word, gen.eval [x] = CircCode.encCirc (cf x.length)

/-- **P-uniform descriptions suffice**: if the code of the `n`-th circuit is computed in
polynomial time, then so is the code of the CNF of its Tseitin translation. -/
theorem lengthUniform_of_codeUniform {cf : ℕ → Tseitin.Circuit} (h : CodeUniform cf) :
    LengthUniform cf := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨.comp CircCode.tseitinTerm [gen], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hgen]
  exact CircCode.eval_tseitinTerm _

/-- **SAT is NP-hard as soon as the length-indexed acceptance circuits have P-uniform
descriptions.**

This is `Complexity.npHard_SAT_of_lengthUniform` with the hypothesis put in its textbook form: what
has to be produced in polynomial time from `1^n` is the *description of the circuit*, not the code
of a formula. -/
theorem npHard_SAT_of_codeUniform
    (H : ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      CodeUniform cf) :
    NPHard Sat.SAT :=
  npHard_SAT_of_lengthUniform fun v p cf hwf hout hsz =>
    lengthUniform_of_codeUniform (H v p cf hwf hout hsz)

/-- **Cook–Levin from P-uniform circuit descriptions**: SAT is NP-complete as soon as the
length-indexed acceptance circuits have P-uniform descriptions.  The `InNP` half is
unconditional. -/
theorem npComplete_SAT_of_codeUniform
    (H : ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      CodeUniform cf) :
    NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_codeUniform H⟩

end Complexity
