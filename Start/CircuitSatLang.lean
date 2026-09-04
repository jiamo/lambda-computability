/-
**CIRCUIT-SAT as a language, and its reduction to SAT.**

`Start/CircuitCode.lean` writes a circuit as a word and shows that the Tseitin translation of a
*code* is computed by the Cobham term `Complexity.CircCode.tseitinTerm`.  A language, however, is a
set of arbitrary words, so a decision problem about circuits has to say what an arbitrary word
means.  This module reads *every* word as a list of gates — the gates that the finite-state control
of `Start/CircuitCode.lean` recognizes in it — and takes the equation semantics of
`Start/CircuitSystem.lean` for the resulting system.

Main definitions:

* `Complexity.CircCode.gatesOf` — the gates read off an arbitrary word;
* `Complexity.CSAT` — **CIRCUIT-SAT**: the words whose gate system is satisfiable.

Main results:

* `Complexity.CircCode.brun_gblk_gatesOf`, `Complexity.CircCode.eval_tseitinTerm_word` — the
  block-emitting recursion, and hence the Tseitin term, computes the translation of the gates read
  off **any** word, not only off a code;
* `Complexity.CircCode.gatesOf_encCirc` — on a code the reading is the circuit itself, so
  `Complexity.CSAT_encCirc_wf` : a code of a well-formed circuit is in `CSAT` exactly when that
  circuit is satisfiable — the language is the usual circuit satisfiability problem;
* `Complexity.polyManyOne_CSAT_SAT` — **CIRCUIT-SAT reduces to SAT** by the Tseitin term;
* `Complexity.inNP_CSAT` — hence **CIRCUIT-SAT is in NP**.
-/

import Start.CircuitSystem
import Start.CookLevinBound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The gates read off an arbitrary word -/

/-- The gates that the control of `Start/CircuitCode.lean` reads in a word: at every position
that carries a marker, the gate whose token starts there.  On a code this is the circuit itself
(`gatesOf_encCirc`); on any other word it is whatever the control recognizes. -/
def gatesOf : Word → Circuit
  | [] => []
  | b :: x =>
      (if emits (rst dstate 0 x) b then [readGate (rst dstate 0 x) x] else []) ++ gatesOf x

/-- The counter of the recursion counts the gates read. -/
theorem length_gatesOf (x : Word) : (gatesOf x).length = rcnt dstate cinc x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      rw [gatesOf, rcnt, List.length_append, ih, cinc]
      by_cases h : emits (rst dstate 0 x) b
      · rw [if_pos h, if_pos h]
        simp
      · rw [if_neg h, if_neg h]
        simp

/-- **The block-emitting recursion translates any word gate by gate.**  This is
`Complexity.CircCode.brun_gmap` without the assumption that the word is a code. -/
theorem brun_gblk_gatesOf (F : ℕ → Gate → Word) (x : Word) :
    brun dstate cinc (gblk F) x = gmap F (gatesOf x) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      rw [brun, ih, gatesOf, gblk]
      by_cases h : emits (rst dstate 0 x) b
      · rw [if_pos h, if_pos h]
        simp only [List.singleton_append, gmap, length_gatesOf]
      · rw [if_neg h, if_neg h]
        simp

/-- On a code, the reading returns the circuit. -/
theorem gatesOf_encCirc (C : Circuit) : gatesOf (encCirc C) = C := by
  have hgmap : ∀ D : Circuit, gmap (fun _ g => encGate g) D = encCirc D := by
    intro D
    induction D with
    | nil => rfl
    | cons g D ih => rw [gmap, ih, encCirc]
  have h := brun_gblk_gatesOf (fun _ g => encGate g) (encCirc C)
  rw [brun_gmap (fun _ g => encGate g) C, hgmap, hgmap] at h
  exact encCirc_injective h.symm

/-! ### The Tseitin term on an arbitrary word -/

/-- The gate definitions of the gates read off any word. -/
theorem eval_defsTerm_word (x : Word) :
    defsTerm.eval [x] = Sat.encCnf (defsCnf (gatesOf x)) := by
  have h := eval_blkRunTerm (m := 10) (Ki := 1) (K := 79) (by norm_num) dstate_lt cinc_le blkT
    (blk := cblk) [] (fun s b y c => eval_blkT y [] s b c)
    (fun s b y c hc => length_cblk y s b c hc) x
  rw [defsTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    Cob.eval_empty]
  rw [h, cblk, brun_gblk_gatesOf]
  induction gatesOf x with
  | nil => rfl
  | cons g D ih =>
      rw [gmap, ih, defsCnf]
      simp only [Sat.encCnf, List.flatMap_append]

/-- **The Tseitin term translates any word**: it computes the code of the translation of the gate
system that the word describes. -/
theorem eval_tseitinTerm_word (x : Word) :
    tseitinTerm.eval [x] = Sat.encCnf (toCnf (gatesOf x)) := by
  have hcnt : (cntTerm 10 dstate cinc 1).eval [x] = List.replicate (gatesOf x).length true := by
    rw [eval_cntTerm (by norm_num) dstate_lt cinc_le x [], length_gatesOf]
  rw [tseitinTerm]
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
    Cob.eval_proj, List.getD_cons_zero, hcnt, eval_defsTerm_word]
  cases hg : gatesOf x with
  | nil => simp [eval_headU_nil, toCnf, Sat.encCnf, Sat.encClause, defsCnf]
  | cons g D =>
      rw [List.length_cons, eval_headU_succ, toCnf]
      simp [Sat.encCnf, Sat.encClause, Sat.encLit]

end CircCode

/-! ### The language -/

open Complexity.Tseitin Complexity.CircCode

/-- **CIRCUIT-SAT**: the words whose system of gate equations is satisfiable. -/
def CSAT : Language := fun x => Tseitin.esat (gatesOf x)

/-- On the code of a circuit, membership is satisfiability of its gate system. -/
theorem CSAT_encCirc (C : Circuit) : CSAT (encCirc C) ↔ Tseitin.esat C := by
  rw [CSAT, gatesOf_encCirc]

/-- **On codes of well-formed circuits, `CSAT` is circuit satisfiability**: the language really is
the circuit satisfiability problem. -/
theorem CSAT_encCirc_wf {C : Circuit} (hC : Tseitin.wf C) :
    CSAT (encCirc C) ↔ Tseitin.csat C := by
  rw [CSAT_encCirc, Tseitin.esat_iff_csat C hC]

/-- **CIRCUIT-SAT reduces to SAT**, by the Tseitin term. -/
theorem polyManyOne_CSAT_SAT : CSAT ≤ₘᵖ Sat.SAT := by
  refine ⟨CircCode.tseitinTerm, fun x => ?_⟩
  rw [CSAT, eval_tseitinTerm_word, Sat.SAT_encCnf, Tseitin.esat_iff_sat_toCnf]

/-- **CIRCUIT-SAT is in NP.** -/
theorem inNP_CSAT : InNP CSAT := InNP.of_reduction polyManyOne_CSAT_SAT Sat.inNP_SAT

end Complexity
