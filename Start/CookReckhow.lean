/-
**The Cook–Reckhow theorem**: `NP = coNP` if and only if some propositional proof system is
polynomially bounded.

A *propositional proof system* (Cook and Reckhow, 1979) for the unsatisfiable CNFs is a
polynomial-time function — here a Cobham term — whose range is exactly the set of codes of
unsatisfiable CNFs: its inputs are the "proofs", and the output of a proof is the formula it
refutes.  It is *polynomially bounded* when every unsatisfiable formula has a proof of length
polynomial in the length of the formula.

The CNFs and their codes are those of `Start/Sat.lean`: every word decodes to a CNF, and `UNSAT`
is the complement of `Complexity.Sat.SAT`.

Main definitions:

* `Complexity.Sat.UNSAT` — the words whose decoded CNF is unsatisfiable;
* `Complexity.IsProofSystem` — a Cobham term whose range is exactly `UNSAT`;
* `Complexity.PolyBounded` — a proof system with polynomially short proofs.

Main results:

* `Complexity.inCoNP_UNSAT` — `UNSAT ∈ coNP`;
* `Complexity.NP_eq_coNP_iff_inNP_UNSAT` — `NP = coNP` iff `UNSAT ∈ NP`;
* `Complexity.inNP_UNSAT_of_polyBounded`, `Complexity.polyBounded_of_inNP_UNSAT` — a polynomially
  bounded proof system is the same as an `NP` verifier for `UNSAT`;
* `Complexity.cook_reckhow` — **`NP = coNP` iff there is a polynomially bounded proof system**.
-/

import Start.PolyHierarchy
import Start.CookLevinNPHard
import Start.CobhamCond
import Start.BinArith

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### The language `UNSAT` -/

/-- **UNSAT**: the words whose decoded CNF is unsatisfiable. -/
def Sat.UNSAT : Language := fun u => ¬ Sat.SAT u

/-- The code `000` of the CNF with a single empty clause. -/
def unsatWord : Word := [false, false, false]

theorem unsat_unsatWord : Sat.UNSAT unsatWord := by
  rintro ⟨σ, hσ⟩
  have : Sat.decode unsatWord = [[]] := by
    have := Sat.decode_encCnf [[]]
    simpa [unsatWord, Sat.encCnf, Sat.encClause] using this
  rw [this] at hσ
  simp at hσ

/-- **`UNSAT ∈ coNP`.** -/
theorem inCoNP_UNSAT : InCoNP Sat.UNSAT := by
  change InNP (fun x => ¬ ¬ Sat.SAT x)
  rw [compl_compl_lang]
  exact Sat.inNP_SAT

/-- **`NP = coNP` iff `UNSAT ∈ NP`**: `UNSAT` is `coNP`-complete, by the reductions to `SAT`. -/
theorem NP_eq_coNP_iff_inNP_UNSAT : (∀ L, InNP L ↔ InCoNP L) ↔ InNP Sat.UNSAT := by
  constructor
  · intro h
    exact (h _).2 inCoNP_UNSAT
  · intro hU L
    constructor
    · intro hL
      obtain ⟨r, hr⟩ := npHard_SAT L hL
      refine InNP.of_reduction ⟨r, fun x => ?_⟩ hU
      exact not_congr (hr x)
    · intro hL
      obtain ⟨r, hr⟩ := npHard_SAT _ hL
      refine InNP.of_reduction ⟨r, fun x => ?_⟩ hU
      change L x ↔ ¬ Sat.SAT (r.eval [x])
      rw [← hr x, not_not]

/-! ### Proof systems -/

/-- A **propositional proof system**: a polynomial-time function (a Cobham term) whose range is
exactly the set of codes of unsatisfiable CNFs; `f π = x` reads "`π` is a proof that `x` is
unsatisfiable". -/
def IsProofSystem (f : Cob) : Prop := ∀ x, Sat.UNSAT x ↔ ∃ π, f.eval [π] = x

/-- A proof system is **polynomially bounded** when every unsatisfiable formula has a proof of
polynomial length. -/
def PolyBounded (f : Cob) : Prop :=
  ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ x, Sat.UNSAT x → ∃ π, π.length ≤ p x.length ∧ f.eval [π] = x

/-! ### Cobham terms for polynomial lengths -/

/-- The term computing `1^((|x| + 1)^k)` on the argument `x`. -/
def powT : ℕ → Cob
  | 0 => .comp (.app true) [.empty]
  | k + 1 => .comp .smash [powT k, .comp (.app true) [.proj 0]]

theorem length_eval_powT (k : ℕ) (x : Word) : ((powT k).eval [x]).length = (x.length + 1) ^ k := by
  induction k with
  | zero => simp [powT]
  | succ k ih => simp [powT, ih, pow_succ]

/-- The term computing the word `1^a`. -/
def onesT : ℕ → Cob
  | 0 => .empty
  | a + 1 => .comp (.app true) [onesT a]

theorem length_eval_onesT (a : ℕ) (args : List Word) : ((onesT a).eval args).length = a := by
  induction a with
  | zero => simp [onesT]
  | succ a ih => simp [onesT, ih]

/-- The term computing `1^(a (|x| + 1)^k)` on the argument `x`. -/
def padT (a k : ℕ) : Cob := .comp .smash [onesT a, powT k]

theorem length_eval_padT (a k : ℕ) (x : Word) :
    ((padT a k).eval [x]).length = a * (x.length + 1) ^ k := by
  simp [padT, length_eval_onesT, length_eval_powT]

/-! ### The two directions -/

/-- **A polynomially bounded proof system puts `UNSAT` in `NP`**: the verifier checks that the
proof has the polynomial length and that the proof system maps it to the input. -/
theorem inNP_UNSAT_of_polyBounded {f : Cob} (hf : IsProofSystem f) (hb : PolyBounded f) :
    InNP Sat.UNSAT := by
  obtain ⟨p, ⟨a, k, hp⟩, hpf⟩ := hb
  set V : Cob := .comp .andC [Cob.eqW (.comp f [.proj 1]) (.proj 0),
    Cob.leU (.proj 1) (.comp (padT a k) [.proj 0])] with hV
  have hacc : ∀ x π : Word, V.eval [x, π] ≠ [] ↔
      (f.eval [π] = x ∧ π.length ≤ a * (x.length + 1) ^ k) := by
    intro x π
    simp only [hV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_andC, Cob.eval_eqW,
      Cob.eval_leU, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ, length_eval_padT]
    by_cases h1 : f.eval [π] = x <;> by_cases h2 : π.length ≤ a * (x.length + 1) ^ k <;>
      simp [h1, h2, bw]
  refine ⟨V, fun n => a * (n + 1) ^ k, ⟨a, k, fun _ => le_rfl⟩, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) k)
  · intro x π hπ
    exact ((hacc x π).1 hπ).2
  · intro x
    constructor
    · intro hx
      obtain ⟨π, hlen, hπ⟩ := hpf x hx
      exact ⟨π, (hacc x π).2 ⟨hπ, le_trans hlen (hp _)⟩⟩
    · rintro ⟨π, hπ⟩
      exact (hf x).2 ⟨π, ((hacc x π).1 hπ).1⟩

/-- The proof system read off a verifier for `UNSAT`: a proof is a pair `⟨x, w⟩`; if the verifier
accepts the witness `w` for `x`, the proof proves `x`, and otherwise it proves the fixed
unsatisfiable formula `unsatWord`. -/
def proofSystemOf (v : Cob) : Cob :=
  .comp Cob.iteC [.comp v [.comp fstTerm [.proj 0, .empty], .comp sndTerm [.proj 0, .empty]],
    .comp fstTerm [.proj 0, .empty], .comp (.app false) [.comp (.app false) [.comp (.app false)
      [.empty]]]]

theorem eval_proofSystemOf (v : Cob) (π : Word) :
    (proofSystemOf v).eval [π] =
      if v.eval [fstOf π, sndOf π] = [] then unsatWord else fstOf π := by
  simp only [proofSystemOf, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, Cob.eval_empty, Cob.eval_iteC, Cob.eval_app, eval_fstTerm, eval_sndTerm]
  rfl

/-- **`UNSAT ∈ NP` gives a polynomially bounded proof system.** -/
theorem polyBounded_of_inNP_UNSAT (h : InNP Sat.UNSAT) :
    ∃ f : Cob, IsProofSystem f ∧ PolyBounded f := by
  obtain ⟨v, p, hpoly, _, hbound, hchar⟩ := h
  refine ⟨proofSystemOf v, fun x => ?_, ⟨fun n => 2 * n + 2 + p n, ?_, fun x hx => ?_⟩⟩
  · constructor
    · intro hx
      obtain ⟨w, hw⟩ := (hchar x).1 hx
      refine ⟨pairW x w, ?_⟩
      rw [eval_proofSystemOf, fstOf_pairW, sndOf_pairW, if_neg hw]
    · rintro ⟨π, rfl⟩
      rw [eval_proofSystemOf]
      split_ifs with hv
      · exact unsat_unsatWord
      · exact (hchar _).2 ⟨_, hv⟩
  · exact PolyBound.add (⟨2, 1, fun n => by ring_nf; omega⟩ : PolyBound (fun n => 2 * n + 2)) hpoly
  · obtain ⟨w, hw⟩ := (hchar x).1 hx
    refine ⟨pairW x w, ?_, ?_⟩
    · rw [length_pairW]
      have := hbound x w hw
      show 2 * x.length + 2 + w.length ≤ 2 * x.length + 2 + p x.length
      omega
    · rw [eval_proofSystemOf, fstOf_pairW, sndOf_pairW, if_neg hw]

/-- **The Cook–Reckhow theorem**: `NP = coNP` if and only if there is a polynomially bounded
propositional proof system. -/
theorem cook_reckhow :
    (∀ L, InNP L ↔ InCoNP L) ↔ ∃ f : Cob, IsProofSystem f ∧ PolyBounded f := by
  rw [NP_eq_coNP_iff_inNP_UNSAT]
  constructor
  · exact polyBounded_of_inNP_UNSAT
  · rintro ⟨f, hf, hb⟩
    exact inNP_UNSAT_of_polyBounded hf hb

end Complexity
