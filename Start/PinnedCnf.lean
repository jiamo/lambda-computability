/-
**Pinning the inputs of a circuit** by unit clauses.

The Tseitin translation of a circuit (`Start/Tseitin.lean`) turns satisfiability of the circuit
into satisfiability of a CNF; the circuit input `i` becomes the CNF variable `2 * i`.  Adding a
unit clause on such a variable therefore *fixes* an input bit, and the resulting CNF is satisfiable
exactly when the circuit accepts some input with those bits.

This is what makes a *length-indexed* circuit family enough for a many-one reduction: the circuit
depends on the length of the instance only, and the instance itself is written into the formula by
unit clauses, which are cheap to produce.

The pinning used here fixes, for every position `m` of a word `u`, the input `2 * m` to `true` and
the input `2 * m + 1` to `u m`, which is exactly the pattern that
`Complexity.Tseitin.inWord_eq_of_pinned` recognizes.

Main definitions:

* `Complexity.Tseitin.pinCnfFrom`, `Complexity.Tseitin.pinCnfW` — the pinning clauses.

Main results:

* `Complexity.Tseitin.cnfValF_pinCnfFrom` — what the pinning clauses say about an assignment;
* `Complexity.Tseitin.sat_append_pinCnfW` — the translation of a circuit together with the
  pinning clauses is satisfiable exactly when the circuit accepts an input pinned that way.
-/

import Start.Tseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

open Complexity.Sat

/-! ### The pinning clauses -/

/-- The unit clauses pinning the circuit inputs `2 * d, 2 * d + 1, 2 * (d + 1), …` to the pattern
`true, s 0, true, s 1, …`.  The circuit input `i` is the CNF variable `2 * i`. -/
def pinCnfFrom : ℕ → Word → Cnf
  | _, [] => []
  | d, b :: s => [(true, 4 * d)] :: [(b, 4 * d + 2)] :: pinCnfFrom (d + 1) s

/-- The unit clauses pinning the first `2 * |u|` circuit inputs to the pattern
`true, u 0, true, u 1, …`. -/
def pinCnfW (u : Word) : Cnf := pinCnfFrom 0 u

theorem pinCnfFrom_vars : ∀ (s : Word) (d : ℕ), ∀ C ∈ pinCnfFrom d s, ∀ l ∈ C,
    l.2 < 4 * (d + s.length) + 3 := by
  intro s
  induction s with
  | nil => intro d C hC; simp [pinCnfFrom] at hC
  | cons b s ih =>
      intro d C hC l hl
      rw [pinCnfFrom, List.mem_cons, List.mem_cons] at hC
      rcases hC with rfl | rfl | hC
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        simp only [List.length_cons]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        simp only [List.length_cons]
        omega
      · have := ih (d + 1) C hC l hl
        simp only [List.length_cons]
        omega

theorem pinCnfW_vars (u : Word) : ∀ C ∈ pinCnfW u, ∀ l ∈ C, l.2 < 4 * u.length + 3 := by
  intro C hC l hl
  have := pinCnfFrom_vars u 0 C hC l hl
  omega

/-- **What the pinning clauses say**: they hold exactly when the pinned variables carry the
prescribed bits. -/
theorem cnfValF_pinCnfFrom (f : ℕ → Bool) : ∀ (s : Word) (d : ℕ),
    cnfValF f (pinCnfFrom d s) = true ↔
      ∀ m, m < s.length → f (4 * (d + m)) = true ∧ f (4 * (d + m) + 2) = s.getD m false := by
  intro s
  induction s with
  | nil => intro d; simp [pinCnfFrom]
  | cons b s ih =>
      intro d
      rw [pinCnfFrom, cnfValF_cons, cnfValF_cons, Bool.and_eq_true, Bool.and_eq_true, ih (d + 1)]
      constructor
      · rintro ⟨h1, h2, h3⟩ m hm
        match m with
        | 0 =>
            refine ⟨?_, ?_⟩
            · simpa [clauseValF, litValF] using h1
            · have : litValF f (b, 4 * d + 2) = true := by simpa [clauseValF] using h2
              simp only [litValF] at this
              cases b <;> simp_all
        | (m + 1) =>
            have := h3 m (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hm))
            rw [show d + 1 + m = d + (m + 1) by omega] at this
            simpa using this
      · intro h
        have h0 := h 0 (by simp)
        refine ⟨?_, ?_, ?_⟩
        · simpa [clauseValF, litValF] using h0.1
        · have : f (4 * d + 2) = b := by simpa using h0.2
          cases b <;> simp [clauseValF, litValF, this]
        · intro m hm
          have := h (m + 1) (by simpa using Nat.succ_lt_succ hm)
          rw [show d + (m + 1) = d + 1 + m by omega] at this
          simpa using this

/-! ### The canonical assignment satisfies the translation -/

/-- If the circuit accepts `x`, the canonical assignment attached to `x` satisfies the Tseitin
translation. -/
theorem cnfValF_toCnf_assign {C : Circuit} (hC : wf C) {x : Word} (hx : out x C = true) :
    cnfValF (assign x C) (toCnf C) = true := by
  cases C with
  | nil => simp [out] at hx
  | cons g C =>
      rw [toCnf, cnfValF_cons]
      have hval : assign x (g :: C) (2 * C.length + 1) = true := by
        rw [assign_odd]
        exact (vals_cons_getD_length x g C).trans hx
      have h1 : clauseValF (assign x (g :: C)) [(true, 2 * C.length + 1)] = true := by
        simpa [clauseValF, litValF] using hval
      have h2 : cnfValF (assign x (g :: C)) (defsCnf (g :: C)) = true :=
        cnfValF_defsCnf x (g :: C) hC _ (fun i => assign_even x (g :: C) i)
          (fun j _ => assign_odd x (g :: C) j)
      simp [h1, h2]

/-! ### Satisfiability of the pinned translation -/

/-- **The pinned translation is satisfiable exactly when the circuit accepts a pinned input.**
The formula is the Tseitin translation of `C` together with the unit clauses pinning the first
`2 * |u|` inputs to `true, u 0, true, u 1, …`. -/
theorem sat_append_pinCnfW (C : Circuit) (hC : wf C) (u : Word) :
    (∃ σ : Word, cnfVal σ (toCnf C ++ pinCnfW u) = true) ↔
      ∃ x : Word, out x C = true ∧ ∀ m, m < u.length →
        x.getD (2 * m) false = true ∧ x.getD (2 * m + 1) false = u.getD m false := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [cnfVal_eq_cnfValF, cnfValF_append, Bool.and_eq_true] at hσ
    obtain ⟨htoc, hpin⟩ := hσ
    set f : ℕ → Bool := fun i => σ.getD i false with hf
    have hpin' : ∀ m, m < u.length →
        f (4 * (0 + m)) = true ∧ f (4 * (0 + m) + 2) = u.getD m false :=
      (cnfValF_pinCnfFrom f u 0).1 hpin
    cases C with
    | nil => rw [toCnf] at htoc; simp [cnfValF, clauseValF] at htoc
    | cons g C =>
        rw [toCnf, cnfValF_cons, Bool.and_eq_true] at htoc
        obtain ⟨hout, hdefs⟩ := htoc
        set M := max (inpBound (g :: C)) (2 * u.length) with hM
        set x : Word := (List.range M).map (fun i => f (2 * i)) with hx
        have hxget : ∀ i, i < M → x.getD i false = f (2 * i) := fun i hi =>
          getD_range_map (f := fun i => f (2 * i)) hi
        refine ⟨x, ?_, ?_⟩
        · have hval := vals_of_cnfValF x (g :: C) hC f
            (fun i hi => hxget i (lt_of_lt_of_le hi (le_max_left _ _))) hdefs C.length (by simp)
          rw [vals_cons_getD_length] at hval
          have h1 : f (2 * C.length + 1) = true := by simpa [clauseValF, litValF] using hout
          rw [out, ← hval]
          exact h1
        · intro m hm
          have hb := hpin' m hm
          have h2m : 2 * m < M := by
            have : 2 * m < 2 * u.length := by omega
            omega
          have h2m1 : 2 * m + 1 < M := by
            have : 2 * m + 1 < 2 * u.length := by omega
            omega
          refine ⟨?_, ?_⟩
          · rw [hxget _ h2m, show 2 * (2 * m) = 4 * (0 + m) by omega]
            exact hb.1
          · rw [hxget _ h2m1, show 2 * (2 * m + 1) = 4 * (0 + m) + 2 by omega]
            exact hb.2
  · rintro ⟨x, hx, hpin⟩
    refine ⟨(List.range (max (varBound C) (4 * u.length + 3))).map (assign x C), ?_⟩
    rw [cnfVal_map_range (f := assign x C) ?vars, cnfValF_append, Bool.and_eq_true]
    case vars =>
      intro D hD l hl
      rw [List.mem_append] at hD
      rcases hD with hD | hD
      · have := toCnf_vars C hC D hD l hl
        omega
      · have := pinCnfW_vars u D hD l hl
        omega
    refine ⟨cnfValF_toCnf_assign hC hx, (cnfValF_pinCnfFrom (assign x C) u 0).2 fun m hm => ?_⟩
    have hb := hpin m hm
    refine ⟨?_, ?_⟩
    · rw [show 4 * (0 + m) = 2 * (2 * m) by omega, assign_even]
      exact hb.1
    · rw [show 4 * (0 + m) + 2 = 2 * (2 * m + 1) by omega, assign_even]
      exact hb.2

end Tseitin

end Complexity
