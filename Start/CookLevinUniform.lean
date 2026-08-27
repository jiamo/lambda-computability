/-
**Cook–Levin from a length-indexed advice.**

`Start/CookLevin.lean` isolates what is missing for SAT to be NP-hard as
`Complexity.UniformlyGenerated`: that the Tseitin translation of the circuit attached to an
instance `x` is the value of a Cobham term at `x`.  That hypothesis still quantifies over the
instance.

This module removes the dependence on the instance.  The circuits built in
`Start/PinnedCircuit.lean` read the instance *off their own input*, so they depend on the length of
the instance only; the instance itself is written into the formula by the unit clauses of
`Start/PinnedCnf.lean`, and those are produced by an explicit Cobham term
(`Complexity.Tseitin.pinTerm`, `Start/CobhamPin.lean`).  What is left to assume is therefore only
that the *length-indexed* family of circuits is polynomial-time uniform — the standard
P-uniformity of a circuit family, a statement about `1^n` rather than about `x`.

Main definitions:

* `Complexity.LengthUniform` — P-uniformity of a length-indexed circuit family.

Main results:

* `Complexity.npHard_SAT_of_lengthUniform`, `Complexity.npComplete_SAT_of_lengthUniform` — SAT is
  NP-hard, hence NP-complete, as soon as the length-indexed acceptance circuits are P-uniform.
-/

import Start.CookLevin
import Start.PinnedCircuit
import Start.CobhamPin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Sat

theorem Sat.encCnf_append (F G : Cnf) : encCnf (F ++ G) = encCnf F ++ encCnf G :=
  List.flatMap_append

theorem getD_of_take_eq {y pre : Word} {off i : ℕ} (h : y.take off = pre) (hi : i < off) :
    y.getD i false = pre.getD i false := by
  rw [← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- A **length-indexed circuit family is P-uniform** when the code of the Tseitin translation of
its `n`-th member is produced by a single Cobham term from any word of length `n`. -/
def LengthUniform (cf : ℕ → Tseitin.Circuit) : Prop :=
  ∃ gen : Cob, ∀ x : Word, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cf x.length))

/-- **SAT is NP-hard as soon as the length-indexed acceptance circuits are P-uniform.**

This strengthens `Complexity.npHard_SAT_of_uniform`: the hypothesis no longer mentions the
instance at all.  The circuits `cf n` read both the instance and the witness off their own input,
so they depend on the length `n` only, and the instance is written into the formula by unit
clauses that an explicit Cobham term produces. -/
theorem npHard_SAT_of_lengthUniform
    (H : ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      LengthUniform cf) :
    NPHard Sat.SAT := by
  intro L hL
  obtain ⟨v, p, hpb, hpm, hwit, hacc⟩ := hL
  obtain ⟨sz, hsz, hC⟩ := Tseitin.exists_pinAcceptCircuit v
  choose cf hwf hlen hout using fun n : ℕ => hC n (p n)
  obtain ⟨gen, hgen⟩ := H v p cf hwf hout
    ⟨fun n => sz (n + p n), hsz.comp (MonoPoly.id'.add ⟨hpm, hpb⟩),
      fun n => le_trans (hlen n) (hsz.mono (by simp))⟩
  refine ⟨.comp Cob.concat [gen, Tseitin.pinTerm], fun x => ?_⟩
  have heval : (Cob.comp Cob.concat [gen, Tseitin.pinTerm]).eval [x]
      = Sat.encCnf (Tseitin.toCnf (cf x.length) ++ Tseitin.pinCnfW x) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hgen x,
      Tseitin.eval_pinTerm x, Sat.encCnf_append]
  rw [heval, Sat.SAT_encCnf, Tseitin.sat_append_pinCnfW _ (hwf x.length) x, hacc x]
  constructor
  · rintro ⟨w, hw⟩
    have hwlen : w.length ≤ p x.length := hwit x w hw
    set pre : Word := (List.range (2 * x.length)).map
      (fun i => if i % 2 = 0 then true else x.getD (i / 2) false) with hpre
    have hprelen : pre.length = 2 * x.length := by simp [hpre]
    obtain ⟨y, hytake, hyw⟩ :=
      Tseitin.exists_inWordAt (2 * x.length) (p x.length) w hwlen pre hprelen
    have hyget : ∀ i, i < 2 * x.length → y.getD i false = pre.getD i false :=
      fun i hi => getD_of_take_eq hytake hi
    have hpin : ∀ m, m < x.length → y.getD (2 * m) false = true ∧
        y.getD (2 * m + 1) false = x.getD m false := by
      intro m hm
      have h₁ : 2 * m < 2 * x.length := by omega
      have h₂ : 2 * m + 1 < 2 * x.length := by omega
      have hget : ∀ i, i < 2 * x.length →
          pre.getD i false = if i % 2 = 0 then true else x.getD (i / 2) false := by
        intro i hi
        rw [hpre]
        exact Tseitin.getD_range_map
          (f := fun i => if i % 2 = 0 then true else x.getD (i / 2) false) hi
      refine ⟨?_, ?_⟩
      · rw [hyget _ h₁, hget _ h₁]
        simp [Nat.mul_mod_right]
      · rw [hyget _ h₂, hget _ h₂, if_neg (by omega)]
        congr 1
        omega
    refine ⟨y, ?_, hpin⟩
    rw [hout x.length y, Tseitin.inWord_eq_of_pinned x y hpin, hyw]
    simpa using hw
  · rintro ⟨y, hy, hpin⟩
    have hx : Tseitin.inWord x.length y = x := Tseitin.inWord_eq_of_pinned x y hpin
    rw [hout x.length y, hx] at hy
    exact ⟨_, by simpa using hy⟩

/-- **Cook–Levin from a length-indexed advice**: SAT is NP-complete as soon as the length-indexed
acceptance circuits are P-uniform.  The `InNP` half is unconditional. -/
theorem npComplete_SAT_of_lengthUniform
    (H : ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      LengthUniform cf) :
    NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_lengthUniform H⟩

end Complexity
