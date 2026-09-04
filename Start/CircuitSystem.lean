/-
**Gate systems: circuit satisfiability without a well-formedness assumption.**

`Start/Tseitin.lean` evaluates a circuit `C` by `Complexity.Tseitin.vals`, which reads the value of
a reference `r` of the gate `j` off the values already computed — so it only means what it should
when `r < j`, i.e. when the circuit is well formed (`Complexity.Tseitin.wf`), and the Tseitin
theorem `csat_iff_sat_toCnf` carries that hypothesis.  A *word* presented to a decision procedure
carries no such guarantee, so the language of codes of satisfiable circuits is awkward to reduce.

This module gives the same objects their *equation-system* semantics, which is total: a list of
gates is read as a system of Boolean equations, one per gate, and it is **satisfiable** when some
labelling of the gates and of the inputs solves the system and makes the top gate true.  Nothing is
assumed about the references.

Main definitions:

* `Complexity.Tseitin.gateValFn` — the value of a gate under a labelling of gates and inputs;
* `Complexity.Tseitin.Consistent` — a labelling solving the equations of a list of gates;
* `Complexity.Tseitin.esat` — satisfiability of the system.

Main results:

* `Complexity.Tseitin.esat_iff_sat_toCnf` — **the Tseitin translation is exactly the equation
  system**: for *every* list of gates, the system is satisfiable iff the CNF is;
* `Complexity.Tseitin.esat_iff_csat` — on a well-formed circuit the equation semantics is ordinary
  circuit satisfiability, so `esat` is a conservative extension of `csat`.
-/

import Start.Tseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

open Complexity.Sat

/-! ### The equation system of a list of gates -/

/-- The value of a gate under a labelling `f` of the gates and a labelling `xi` of the inputs. -/
def gateValFn (xi f : ℕ → Bool) : Gate → Bool
  | .inp i => xi i
  | .cst b => b
  | .neg r => !(f r)
  | .conj r s => (f r && f s)
  | .disj r s => (f r || f s)

/-- `Consistent xi f C` : the labelling `f` solves the equation of every gate of `C`, the gate at
the head of a suffix of length `k + 1` having identifier `k`. -/
def Consistent (xi f : ℕ → Bool) : Circuit → Prop
  | [] => True
  | g :: C => f C.length = gateValFn xi f g ∧ Consistent xi f C

/-- **Satisfiability of the gate system**: some labelling of gates and inputs solves all the
equations and makes the top gate true.  The empty list has no top gate and is unsatisfiable. -/
def esat : Circuit → Prop
  | [] => False
  | g :: C => ∃ xi f : ℕ → Bool, Consistent xi f (g :: C) ∧ f C.length = true

/-! ### A bound on the variables of the translation, with no hypothesis -/

/-- A bound on the variables that the defining clauses of a gate with identifier `j` mention. -/
def varB (j : ℕ) : Gate → ℕ
  | .inp i => max (2 * j + 2) (2 * i + 1)
  | .cst _ => 2 * j + 2
  | .neg r => max (2 * j + 2) (2 * r + 2)
  | .conj r s => max (2 * j + 2) (max (2 * r + 2) (2 * s + 2))
  | .disj r s => max (2 * j + 2) (max (2 * r + 2) (2 * s + 2))

/-- A bound on the variables of the whole translation. -/
def varBAll : Circuit → ℕ
  | [] => 1
  | g :: C => max (varB C.length g) (varBAll C)

theorem gateCnf_vars_varB (j : ℕ) (g : Gate) : ∀ D ∈ gateCnf j g, ∀ l ∈ D, l.2 < varB j g := by
  cases g <;>
    simp only [gateCnf, varB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] <;> omega

theorem defsCnf_vars_varBAll : ∀ C : Circuit, ∀ D ∈ defsCnf C, ∀ l ∈ D, l.2 < varBAll C := by
  intro C
  induction C with
  | nil => intro D hD; simp [defsCnf] at hD
  | cons g C ih =>
      intro D hD l hl
      rw [defsCnf, List.mem_append] at hD
      rcases hD with hD | hD
      · have := gateCnf_vars_varB C.length g D hD l hl
        simp only [varBAll]
        omega
      · have := ih D hD l hl
        simp only [varBAll]
        omega

theorem toCnf_vars_varBAll (C : Circuit) : ∀ D ∈ toCnf C, ∀ l ∈ D, l.2 < varBAll C := by
  cases C with
  | nil =>
      intro D hD l hl
      rw [toCnf, List.mem_singleton] at hD
      subst hD
      simp at hl
  | cons g C =>
      intro D hD l hl
      rw [toCnf, List.mem_cons] at hD
      rcases hD with rfl | hD
      · rw [List.mem_singleton] at hl
        subst hl
        have : 2 * C.length + 1 < varB C.length g := by cases g <;> simp only [varB] <;> omega
        simp only [varBAll]
        omega
      · exact defsCnf_vars_varBAll (g :: C) D hD l hl

/-! ### The translation is the equation system -/

/-- The labelling read off an assignment: the input `i` is the variable `2 * i` and the gate `j`
is the variable `2 * j + 1`. -/
theorem cnfValF_defsCnf_of_consistent (xi f : ℕ → Bool) :
    ∀ C : Circuit, Consistent xi f C →
      cnfValF (fun v => if v % 2 = 0 then xi (v / 2) else f (v / 2)) (defsCnf C) = true := by
  intro C
  induction C with
  | nil => intro _; rfl
  | cons g C ih =>
      rintro ⟨hg, hC⟩
      set F : ℕ → Bool := fun v => if v % 2 = 0 then xi (v / 2) else f (v / 2) with hF
      have hodd : ∀ j : ℕ, F (2 * j + 1) = f j := by
        intro j
        simp only [hF]
        rw [if_neg (by omega)]
        congr 1
        omega
      have heven : ∀ i : ℕ, F (2 * i) = xi i := by
        intro i
        simp only [hF]
        rw [if_pos (by omega)]
        congr 1
        omega
      rw [defsCnf, cnfValF_append, ih hC, Bool.and_true]
      cases g with
      | inp i =>
          rw [gateValFn] at hg
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hodd, heven, hg]
          cases xi i <;> simp
      | cst b =>
          rw [gateValFn] at hg
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hodd, hg]
          cases b <;> simp
      | neg r =>
          rw [gateValFn] at hg
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hodd, hg]
          cases f r <;> simp
      | conj r s =>
          rw [gateValFn] at hg
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hodd, hg]
          cases f r <;> cases f s <;> simp
      | disj r s =>
          rw [gateValFn] at hg
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hodd, hg]
          cases f r <;> cases f s <;> simp

/-- Conversely, a satisfying assignment of the defining clauses is a consistent labelling. -/
theorem consistent_of_cnfValF_defsCnf (F : ℕ → Bool) :
    ∀ C : Circuit, cnfValF F (defsCnf C) = true →
      Consistent (fun i => F (2 * i)) (fun j => F (2 * j + 1)) C := by
  intro C
  induction C with
  | nil => intro _; trivial
  | cons g C ih =>
      intro h
      rw [defsCnf, cnfValF_append, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      refine ⟨?_, ih htail⟩
      cases g with
      | inp i =>
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil] at hhead
          simp only [gateValFn]
          revert hhead
          cases F (2 * C.length + 1) <;> cases F (2 * i) <;> simp
      | cst b =>
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil] at hhead
          simp only [gateValFn]
          revert hhead
          cases b <;> cases F (2 * C.length + 1) <;> simp
      | neg r =>
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil] at hhead
          simp only [gateValFn]
          revert hhead
          cases F (2 * C.length + 1) <;> cases F (2 * r + 1) <;> simp
      | conj r s =>
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil] at hhead
          simp only [gateValFn]
          revert hhead
          cases F (2 * C.length + 1) <;> cases F (2 * r + 1) <;> cases F (2 * s + 1) <;> simp
      | disj r s =>
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil] at hhead
          simp only [gateValFn]
          revert hhead
          cases F (2 * C.length + 1) <;> cases F (2 * r + 1) <;> cases F (2 * s + 1) <;> simp

/-- **The Tseitin translation is exactly the equation system of the gates**: for every list of
gates — well formed or not — the system is satisfiable exactly when the CNF is. -/
theorem esat_iff_sat_toCnf (C : Circuit) :
    esat C ↔ ∃ σ : Word, cnfVal σ (toCnf C) = true := by
  cases C with
  | nil =>
      constructor
      · intro h; exact absurd h (by simp [esat])
      · rintro ⟨σ, hσ⟩
        rw [toCnf] at hσ
        simp [cnfVal, clauseVal] at hσ
  | cons g C =>
      constructor
      · rintro ⟨xi, f, hcons, htop⟩
        set F : ℕ → Bool := fun v => if v % 2 = 0 then xi (v / 2) else f (v / 2) with hF
        refine ⟨(List.range (varBAll (g :: C))).map F, ?_⟩
        rw [cnfVal_map_range (toCnf_vars_varBAll (g :: C)), toCnf, cnfValF_cons]
        have hodd : F (2 * C.length + 1) = f C.length := by
          simp only [hF]
          rw [if_neg (by omega)]
          congr 1
          omega
        have h1 : clauseValF F [(true, 2 * C.length + 1)] = true := by
          simpa [clauseValF, litValF, hodd] using htop
        have h2 : cnfValF F (defsCnf (g :: C)) = true :=
          cnfValF_defsCnf_of_consistent xi f (g :: C) hcons
        simp [h1, h2]
      · rintro ⟨σ, hσ⟩
        rw [cnfVal_eq_cnfValF] at hσ
        set F : ℕ → Bool := fun i => σ.getD i false with hF
        rw [toCnf, cnfValF_cons, Bool.and_eq_true] at hσ
        obtain ⟨hout, hdefs⟩ := hσ
        refine ⟨fun i => F (2 * i), fun j => F (2 * j + 1),
          consistent_of_cnfValF_defsCnf F (g :: C) hdefs, ?_⟩
        simpa [clauseValF, litValF] using hout

/-- On a well-formed circuit the equation semantics is ordinary circuit satisfiability. -/
theorem esat_iff_csat (C : Circuit) (hC : wf C) : esat C ↔ csat C := by
  rw [esat_iff_sat_toCnf, csat_iff_sat_toCnf C hC]

end Tseitin

end Complexity
