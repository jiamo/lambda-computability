/-
**Bounded-width satisfiability: `k`-SAT is NP-complete for every `k ≥ 3`.**

`Start/Sat.lean` shows that SAT — the words whose decoded conjunctive normal form is satisfiable —
is in `NP`, and `Start/CookLevinNPHard.lean` that it is NP-hard.  The classical next step is the
same statement for the *bounded width* problem: the CNFs all of whose clauses have at most three
literals.  The reduction is already available in the library: the Tseitin translation of
`Start/Tseitin.lean` emits at most three literals per clause (a gate definition is a conjunction of
implications of width two or three), so the very term that reduces CIRCUIT-SAT to SAT
(`Complexity.CircCode.tseitinTerm`) reduces CIRCUIT-SAT to 3-SAT — and to `k`-SAT for every
`k ≥ 3`.

What has to be added is the *membership* half: the words that encode a CNF of width at most `k`
must be recognised in polynomial time.  Being such a code is a regular property of the word — it
needs the phase of the token reader and the number of literals of the clause currently being read,
capped at `k + 1` — so it is decided by a finite-state automaton, and
`Start/CobhamTransducer.lean` turns such an automaton into a Cobham term.

Main definitions:

* `Complexity.Sat.tstep`, `Complexity.Sat.tdelta` — the automaton checking that every completed
  clause has at most `w` literals, and its transition function on state codes;
* `Complexity.Sat.widthTerm` — the Cobham term deciding that property;
* `Complexity.Sat.KCnfWord` — the words that decode to a CNF of width at most `w`;
* `Complexity.Sat.KSAT` — **`k`-SAT**: the words that decode to a *satisfiable* CNF of width at
  most `k`, and `Complexity.Sat.ThreeSAT` — **3-SAT**, the case `k = 3`.

Main results:

* `Complexity.InNP.inter_inP` — `NP` is closed under intersection with `P`;
* `Complexity.Tseitin.length_le_three_of_mem_toCnf` — **the Tseitin translation is a 3-CNF**;
* `Complexity.Sat.rst_tdelta` — the automaton simulates the decoder;
* `Complexity.Sat.inP_KCnfWord` — being a code of a CNF of width at most `w` is decidable in
  polynomial time;
* `Complexity.Sat.inNP_KSAT`, `Complexity.Sat.inNP_ThreeSAT` — **`k`-SAT is in NP**;
* `Complexity.polyManyOne_CSAT_KSAT` — **CIRCUIT-SAT reduces to `k`-SAT** by the Tseitin term, for
  every `k ≥ 3`;
* `Complexity.npHard_KSAT`, `Complexity.npComplete_KSAT` — **`k`-SAT is NP-hard, and NP-complete,
  for every `k ≥ 3`**, and `Complexity.npComplete_ThreeSAT` for 3-SAT.
-/

import Start.CircuitSatLang
import Start.CobhamTransducer
import Start.SatToCircuitCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### `NP` is closed under intersection with `P` -/

/-- **`NP` is closed under intersection with `P`**: run the verifier of the `NP` language and the
decision procedure of the `P` language on the same input and take the conjunction. -/
theorem InNP.inter_inP {L₁ L₂ : Language} (h₁ : InNP L₁) (h₂ : InP L₂) :
    InNP (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨v, p, hpoly, hmono, hbound, hchar⟩ := h₁
  obtain ⟨c, hc⟩ := h₂
  refine ⟨.comp .andC [.comp c [.proj 0], v], p, hpoly, hmono, ?_, ?_⟩
  · intro x w hacc
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      Cob.eval_andC] at hacc
    by_cases hx : c.eval [x] = []
    · simp [hx] at hacc
    · rw [if_neg hx] at hacc
      exact hbound x w hacc
  · intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      Cob.eval_andC]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨w, hw⟩ := (hchar x).1 h1
      exact ⟨w, by rw [if_neg ((hc x).1 h2)]; exact hw⟩
    · rintro ⟨w, hw⟩
      by_cases hx : c.eval [x] = []
      · rw [if_pos hx] at hw; exact absurd rfl hw
      · exact ⟨(hchar x).2 ⟨w, by rw [if_neg hx] at hw; exact hw⟩, (hc x).2 hx⟩

/-! ### The Tseitin translation produces a 3-CNF -/

namespace Tseitin

/-- Every defining clause of a gate has at most three literals. -/
theorem length_le_three_of_mem_gateCnf (j : ℕ) (g : Gate) {D : Sat.Clause}
    (hD : D ∈ gateCnf j g) : D.length ≤ 3 := by
  cases g <;> simp only [gateCnf, List.mem_cons, List.not_mem_nil, or_false] at hD <;>
    rcases hD with rfl | rfl | rfl <;> simp

/-- Every defining clause of a circuit has at most three literals. -/
theorem length_le_three_of_mem_defsCnf :
    ∀ (C : Circuit) {D : Sat.Clause}, D ∈ defsCnf C → D.length ≤ 3 := by
  intro C
  induction C with
  | nil => intro D hD; simp [defsCnf] at hD
  | cons g C ih =>
      intro D hD
      rw [defsCnf, List.mem_append] at hD
      rcases hD with hD | hD
      · exact length_le_three_of_mem_gateCnf _ _ hD
      · exact ih hD

/-- **The Tseitin translation of a circuit is a 3-CNF**: every clause it produces has at most
three literals. -/
theorem length_le_three_of_mem_toCnf (C : Circuit) {D : Sat.Clause} (hD : D ∈ toCnf C) :
    D.length ≤ 3 := by
  cases C with
  | nil => simp only [toCnf, List.mem_cons, List.not_mem_nil, or_false] at hD; simp [hD]
  | cons g C =>
      rw [toCnf, List.mem_cons] at hD
      rcases hD with rfl | hD
      · simp
      · exact length_le_three_of_mem_defsCnf _ hD

end Tseitin

/-! ### The automaton checking the width of the clauses -/

namespace Sat

/-- The index of a reader phase. -/
def phIdx : Phase → ℕ
  | .main => 0
  | .esc => 1
  | .esc2 => 2

/-- The phase with a given index. -/
def phOf : ℕ → Phase
  | 0 => .main
  | 1 => .esc
  | _ => .esc2

@[simp] theorem phOf_phIdx (ph : Phase) : phOf (phIdx ph) = ph := by cases ph <;> rfl

theorem phIdx_lt (ph : Phase) : phIdx ph < 3 := by cases ph <;> simp [phIdx]

/-- The abstract state of the width checker for the width bound `w`: the phase of the token reader
together with the number of literals of the clause being read, capped at `w + 1`; `none` once a
completed clause has been found to have more than `w` literals. -/
abbrev TSt := Option (Phase × ℕ)

/-- One step of the width checker for the bound `w`, reading the bit `b`.  It mirrors
`Complexity.Sat.dstep`: the literal counter is incremented when a literal token is completed, and a
clause separator either resets it or, if the clause was too wide, kills the run. -/
def tstep (w : ℕ) (b : Bool) : TSt → TSt
  | none => none
  | some (ph, k) =>
      match ph, b with
      | .main, true => some (.main, k)
      | .main, false => some (.esc, k)
      | .esc, true => some (.main, min (k + 1) (w + 1))
      | .esc, false => some (.esc2, k)
      | .esc2, true => some (.main, min (k + 1) (w + 1))
      | .esc2, false => if k ≤ w then some (.main, 0) else none

/-- The code of an abstract state: `3 * (w + 2)` is the dead state. -/
def tenc (w : ℕ) : TSt → ℕ
  | none => 3 * (w + 2)
  | some (ph, k) => 3 * min k (w + 1) + phIdx ph

/-- The number of states of the width checker for the bound `w`. -/
def tsize (w : ℕ) : ℕ := 3 * (w + 2) + 1

/-- The abstract state of a code. -/
def tdec (w : ℕ) (s : ℕ) : TSt :=
  if s < 3 * (w + 2) then some (phOf (s % 3), s / 3) else none

/-- The transition function of the width checker on state codes. -/
def tdelta (w : ℕ) (s : ℕ) (b : Bool) : ℕ := tenc w (tstep w b (tdec w s))

theorem tenc_lt (w : ℕ) (t : TSt) : tenc w t < tsize w := by
  cases t with
  | none => simp [tenc, tsize]
  | some p =>
      obtain ⟨ph, k⟩ := p
      have h1 : min k (w + 1) ≤ w + 1 := min_le_right _ _
      have h2 := phIdx_lt ph
      simp only [tenc, tsize]
      omega

theorem tdelta_lt (w : ℕ) (s : ℕ) (b : Bool) : tdelta w s b < tsize w := tenc_lt _ _

/-- The state code of the decoder for the width bound `w`: the phase and the capped number of
literals of the clause being read, unless a completed clause is already too wide. -/
def abst (w : ℕ) (d : DSt) : ℕ :=
  if ∀ C ∈ d.done, C.length ≤ w then 3 * min d.cur.length (w + 1) + phIdx d.phase
  else 3 * (w + 2)

theorem tdec_abst_of_good {w : ℕ} {d : DSt} (h : ∀ C ∈ d.done, C.length ≤ w) :
    tdec w (abst w d) = some (d.phase, min d.cur.length (w + 1)) := by
  have hph := phIdx_lt d.phase
  have hk : min d.cur.length (w + 1) ≤ w + 1 := min_le_right _ _
  have hlt : 3 * min d.cur.length (w + 1) + phIdx d.phase < 3 * (w + 2) := by omega
  have hmod : (3 * min d.cur.length (w + 1) + phIdx d.phase) % 3 = phIdx d.phase := by omega
  have hdiv : (3 * min d.cur.length (w + 1) + phIdx d.phase) / 3
      = min d.cur.length (w + 1) := by omega
  simp only [abst, if_pos h, tdec, if_pos hlt, hmod, hdiv, phOf_phIdx]

/-- A step of the decoder only ever adds clauses to the ones already read. -/
theorem mem_done_dstep (b : Bool) (d : DSt) {C : Clause} (hC : C ∈ d.done) :
    C ∈ (dstep b d).done := by
  cases hp : d.phase <;> cases b <;> simp only [dstep, hp, List.mem_cons] <;>
    first | exact hC | exact Or.inr hC

/-- **The automaton simulates the decoder**: one step of the width checker on the state code of a
decoder state is the state code of the stepped decoder state. -/
theorem tdelta_abst (w : ℕ) (b : Bool) (d : DSt) :
    tdelta w (abst w d) b = abst w (dstep b d) := by
  by_cases hgood : ∀ C ∈ d.done, C.length ≤ w
  · rw [tdelta, tdec_abst_of_good hgood]
    have hsplit : (∀ C ∈ d.cur :: d.done, C.length ≤ w) ↔ min d.cur.length (w + 1) ≤ w := by
      constructor
      · intro h
        have := h d.cur (by simp)
        omega
      · intro h C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · omega
        · exact hgood C hC
    cases hp : d.phase
    · cases b <;>
        simp only [tstep, tenc, dstep, hp, abst, phIdx, if_pos hgood] <;> omega
    · cases b <;>
        simp only [tstep, tenc, dstep, hp, abst, phIdx, if_pos hgood, List.length_cons] <;> omega
    · cases b
      · simp only [tstep, tenc, dstep, hp, abst, phIdx, hsplit]
        by_cases hm : min d.cur.length (w + 1) ≤ w <;> simp [hm]
      · simp only [tstep, tenc, dstep, hp, abst, phIdx, if_pos hgood, List.length_cons]
        omega
  · have h15 : abst w d = 3 * (w + 2) := by simp only [abst, if_neg hgood]
    have hbad : ¬ ∀ C ∈ (dstep b d).done, C.length ≤ w := by
      intro h
      exact hgood fun C hC => h C (mem_done_dstep b d hC)
    rw [h15, tdelta, tdec, if_neg (by omega), tstep, tenc, abst, if_neg hbad]

theorem rst_tdelta (w : ℕ) (u : Word) : rst (tdelta w) 0 u = abst w (drun u) := by
  induction u with
  | nil => simp [rst, abst, drun, dinit, phIdx]
  | cons b u ih =>
      have hd : drun (b :: u) = dstep b (drun u) := rfl
      rw [rst, ih, hd, tdelta_abst]

/-! ### The words that decode to a CNF of bounded width -/

/-- The words whose decoded CNF has at most `w` literals in every clause. -/
def KCnfWord (w : ℕ) : Language := fun u => ∀ C ∈ decode u, C.length ≤ w

theorem abst_ne_dead_iff (w : ℕ) (d : DSt) :
    abst w d ≠ 3 * (w + 2) ↔ ∀ C ∈ d.done, C.length ≤ w := by
  by_cases h : ∀ C ∈ d.done, C.length ≤ w
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hph := phIdx_lt d.phase
    have hk : min d.cur.length (w + 1) ≤ w + 1 := min_le_right _ _
    rw [show abst w d = 3 * min d.cur.length (w + 1) + phIdx d.phase from if_pos h]
    omega
  · simp only [abst, if_neg h, ne_eq, not_true_eq_false, false_iff]
    exact h

/-- The Cobham term deciding that a word decodes to a CNF of width at most `w`: run the width
checker and accept unless it died. -/
def widthTerm (w : ℕ) : Cob :=
  Cob.tableSel ((List.range (tsize w)).map fun s => if s = 3 * (w + 2) then Cob.empty else
    Cob.trueC) (fstStTerm (tsize w) (tdelta w))

theorem eval_widthTerm (w : ℕ) (x : Word) :
    (widthTerm w).eval [x] ≠ [] ↔ KCnfWord w x := by
  have hpos : 0 < tsize w := by simp [tsize]
  have hst : (fstStTerm (tsize w) (tdelta w)).eval [x]
      = List.replicate (rst (tdelta w) 0 x) true :=
    eval_fstStTerm hpos (tdelta_lt w) x []
  have hlt : rst (tdelta w) 0 x < tsize w := rst_lt hpos (tdelta_lt w) x
  rw [widthTerm, Cob.eval_tableSel _ _ _ _ hst]
  have hget : (((List.range (tsize w)).map fun s =>
        if s = 3 * (w + 2) then Cob.empty else Cob.trueC).getD (rst (tdelta w) 0 x) .empty)
      = if rst (tdelta w) 0 x = 3 * (w + 2) then Cob.empty else Cob.trueC := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    rfl
  rw [hget, rst_tdelta]
  by_cases h : abst w (drun x) = 3 * (w + 2)
  · rw [if_pos h]
    refine iff_of_false (by simp) ?_
    intro hx
    exact (abst_ne_dead_iff w (drun x)).2 hx h
  · rw [if_neg h]
    exact iff_of_true (by simp) ((abst_ne_dead_iff w (drun x)).1 h)

/-- **Being the code of a CNF of width at most `w` is decidable in polynomial time.** -/
theorem inP_KCnfWord (w : ℕ) : InP (KCnfWord w) :=
  ⟨widthTerm w, fun x => (eval_widthTerm w x).symm⟩

/-! ### `k`-SAT -/

/-- **`k`-SAT**: the words that decode to a satisfiable CNF all of whose clauses have at most `k`
literals. -/
def KSAT (k : ℕ) : Language := fun u => SAT u ∧ KCnfWord k u

/-- **3-SAT**: the words that decode to a satisfiable CNF of width at most three. -/
abbrev ThreeSAT : Language := KSAT 3

/-- **`k`-SAT is in NP.** -/
theorem inNP_KSAT (k : ℕ) : InNP (KSAT k) := inNP_SAT.inter_inP (inP_KCnfWord k)

/-- **3-SAT is in NP.** -/
theorem inNP_ThreeSAT : InNP ThreeSAT := inNP_KSAT 3

/-- A word encoding a CNF of width at most `k` is in `KSAT k` exactly when that CNF is
satisfiable. -/
theorem KSAT_encCnf {k : ℕ} {F : Cnf} (hk : ∀ C ∈ F, C.length ≤ k) :
    KSAT k (encCnf F) ↔ ∃ σ : Word, cnfVal σ F = true := by
  simp only [KSAT, KCnfWord, decode_encCnf, SAT_encCnf]
  exact and_iff_left hk

end Sat

/-! ### `k`-SAT is NP-complete for every `k ≥ 3` -/

open CircCode

/-- **CIRCUIT-SAT reduces to `k`-SAT** for every `k ≥ 3`, by the Tseitin term: the translation of
a circuit is a 3-CNF. -/
theorem polyManyOne_CSAT_KSAT {k : ℕ} (hk : 3 ≤ k) : CSAT ≤ₘᵖ Sat.KSAT k := by
  refine ⟨CircCode.tseitinTerm, fun x => ?_⟩
  rw [CSAT, eval_tseitinTerm_word,
    Sat.KSAT_encCnf (k := k)
      (fun _ hD => le_trans (Tseitin.length_le_three_of_mem_toCnf (gatesOf x) hD) hk),
    Tseitin.esat_iff_sat_toCnf]

/-- **`k`-SAT is NP-hard** for every `k ≥ 3`. -/
theorem npHard_KSAT {k : ℕ} (hk : 3 ≤ k) : NPHard (Sat.KSAT k) :=
  npHard_CSAT.of_reduction (polyManyOne_CSAT_KSAT hk)

/-- **`k`-SAT is NP-complete** for every `k ≥ 3`. -/
theorem npComplete_KSAT {k : ℕ} (hk : 3 ≤ k) : NPComplete (Sat.KSAT k) :=
  ⟨Sat.inNP_KSAT k, npHard_KSAT hk⟩

/-- **CIRCUIT-SAT reduces to 3-SAT**, by the Tseitin term. -/
theorem polyManyOne_CSAT_ThreeSAT : CSAT ≤ₘᵖ Sat.ThreeSAT := polyManyOne_CSAT_KSAT le_rfl

/-- **3-SAT is NP-hard.** -/
theorem npHard_ThreeSAT : NPHard Sat.ThreeSAT := npHard_KSAT le_rfl

/-- **3-SAT is NP-complete.** -/
theorem npComplete_ThreeSAT : NPComplete Sat.ThreeSAT := npComplete_KSAT le_rfl

end Complexity
