/-
Boolean circuits and the **Tseitin transformation**: satisfiability of a circuit is equivalent to
satisfiability of a CNF of linear size.

A circuit is a straight-line program: a list of gates, written *output first*, in which a gate may
only refer to the gates *after* it in the list.  The identifier of a gate is the number of gates
below it, so the identifiers of a suffix of the list do not change — which is what makes both the
evaluator and the translation structurally recursive.

The translation introduces one CNF variable per gate (`2 * j + 1` for the gate with identifier `j`)
and one per circuit input (`2 * i` for input `i`), and asserts the defining equivalence of every
gate together with the assertion that the output gate is true.  The resulting CNF is
*equisatisfiable* with the circuit, which is the standard second half of the Cook–Levin argument.

Main definitions:

* `Complexity.Tseitin.Gate`, `Complexity.Tseitin.Circuit` — gates and straight-line circuits;
* `Complexity.Tseitin.vals`, `Complexity.Tseitin.out` — the evaluator;
* `Complexity.Tseitin.csat` — satisfiability of a circuit;
* `Complexity.Tseitin.toCnf` — the Tseitin translation.

Main results:

* `Complexity.Tseitin.cnfValF_defsCnf` — the canonical assignment satisfies the gate definitions;
* `Complexity.Tseitin.vals_of_cnfValF` — conversely, every satisfying assignment computes the gate
  values;
* `Complexity.Tseitin.csat_iff_sat_toCnf` — **the Tseitin transformation preserves
  satisfiability**;
* `Complexity.Tseitin.length_toCnf_le` — the translation has linear size.
-/

import Start.Sat

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

open Complexity.Sat

/-! ### Assignments as functions -/

/-- The value of a literal under an assignment given as a function. -/
def litValF (f : ℕ → Bool) (l : Lit) : Bool := if l.1 then f l.2 else !(f l.2)

/-- The value of a clause under an assignment given as a function. -/
def clauseValF (f : ℕ → Bool) (C : Clause) : Bool := C.any (litValF f)

/-- The value of a CNF under an assignment given as a function. -/
def cnfValF (f : ℕ → Bool) (F : Cnf) : Bool := F.all (clauseValF f)

@[simp] theorem cnfValF_nil (f : ℕ → Bool) : cnfValF f [] = true := rfl

@[simp] theorem cnfValF_cons (f : ℕ → Bool) (C : Clause) (F : Cnf) :
    cnfValF f (C :: F) = (clauseValF f C && cnfValF f F) := rfl

@[simp] theorem cnfValF_append (f : ℕ → Bool) (F G : Cnf) :
    cnfValF f (F ++ G) = (cnfValF f F && cnfValF f G) := by
  simp [cnfValF, List.all_append]

/-- Reading an assignment off a word gives the same values. -/
theorem cnfVal_eq_cnfValF (σ : Word) (F : Cnf) :
    cnfVal σ F = cnfValF (fun i => σ.getD i false) F := rfl

theorem getD_range_map {f : ℕ → Bool} {N i : ℕ} (h : i < N) :
    ((List.range N).map f).getD i false = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem clauseVal_map_range {f : ℕ → Bool} {N : ℕ} {C : Clause} (h : ∀ l ∈ C, l.2 < N) :
    clauseVal ((List.range N).map f) C = clauseValF f C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      have hl := getD_range_map (f := f) (N := N) (i := l.2) (h l (by simp))
      rw [clauseVal_cons, clauseValF, List.any_cons, ← clauseValF,
        ih (fun l hl => h l (by simp [hl]))]
      simp only [litVal, litValF, hl]

/-- If every variable of `F` is below `N`, the word of the first `N` values of `f` gives `F` the
same value as `f` does. -/
theorem cnfVal_map_range {f : ℕ → Bool} {N : ℕ} {F : Cnf}
    (hF : ∀ C ∈ F, ∀ l ∈ C, l.2 < N) :
    cnfVal ((List.range N).map f) F = cnfValF f F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [cnfVal_cons, cnfValF_cons, clauseVal_map_range (hF C (by simp)),
        ih (fun D hD => hF D (List.mem_cons_of_mem _ hD))]

/-! ### Circuits -/

/-- A gate of a straight-line Boolean circuit.  References are identifiers of gates *below* the
gate in question. -/
inductive Gate : Type
  /-- The `i`-th input of the circuit. -/
  | inp (i : ℕ)
  /-- A constant. -/
  | cst (b : Bool)
  /-- Negation of the gate `r`. -/
  | neg (r : ℕ)
  /-- Conjunction of the gates `r` and `s`. -/
  | conj (r s : ℕ)
  /-- Disjunction of the gates `r` and `s`. -/
  | disj (r s : ℕ)
  deriving DecidableEq, Inhabited

/-- A straight-line Boolean circuit: its gates, output gate first.  The gate at the head of a
suffix of length `k + 1` has identifier `k`, and may refer only to identifiers `< k`. -/
abbrev Circuit := List Gate

/-- The value of a gate, given the values of the gates below it. -/
def gateVal (x : Word) (vs : List Bool) : Gate → Bool
  | .inp i => x.getD i false
  | .cst b => b
  | .neg r => !(vs.getD r false)
  | .conj r s => (vs.getD r false && vs.getD s false)
  | .disj r s => (vs.getD r false || vs.getD s false)

/-- The values of all the gates of a circuit, indexed by gate identifier. -/
def vals (x : Word) : Circuit → List Bool
  | [] => []
  | g :: C => vals x C ++ [gateVal x (vals x C) g]

/-- The output of a circuit. -/
def out (x : Word) : Circuit → Bool
  | [] => false
  | g :: C => gateVal x (vals x C) g

@[simp] theorem vals_length (x : Word) (C : Circuit) : (vals x C).length = C.length := by
  induction C with
  | nil => rfl
  | cons g C ih => simp [vals, ih]

theorem vals_cons_getD_lt (x : Word) (g : Gate) (C : Circuit) {j : ℕ} (h : j < C.length) :
    (vals x (g :: C)).getD j false = (vals x C).getD j false := by
  rw [vals, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
    ← List.getD_eq_getElem?_getD]

@[simp] theorem vals_cons_getD_length (x : Word) (g : Gate) (C : Circuit) :
    (vals x (g :: C)).getD C.length false = gateVal x (vals x C) g := by
  rw [vals, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- Well-formedness of a gate with identifier `j`: its references are below `j`. -/
def gateWf (j : ℕ) : Gate → Prop
  | .inp _ => True
  | .cst _ => True
  | .neg r => r < j
  | .conj r s => r < j ∧ s < j
  | .disj r s => r < j ∧ s < j

/-- Well-formedness of a circuit: every gate refers only to gates below it. -/
def wf : Circuit → Prop
  | [] => True
  | g :: C => gateWf C.length g ∧ wf C

/-- **Satisfiability of a circuit**: some input word makes its output true. -/
def csat (C : Circuit) : Prop := ∃ x : Word, out x C = true

/-! ### The Tseitin translation -/

/-- The clauses defining the gate with identifier `j`.  The gate `j` is the CNF variable
`2 * j + 1` and the circuit input `i` is the CNF variable `2 * i`. -/
def gateCnf (j : ℕ) : Gate → Cnf
  | .inp i => [[(false, 2 * j + 1), (true, 2 * i)], [(true, 2 * j + 1), (false, 2 * i)]]
  | .cst b => [[(b, 2 * j + 1)]]
  | .neg r => [[(false, 2 * j + 1), (false, 2 * r + 1)], [(true, 2 * j + 1), (true, 2 * r + 1)]]
  | .conj r s =>
      [[(false, 2 * j + 1), (true, 2 * r + 1)], [(false, 2 * j + 1), (true, 2 * s + 1)],
        [(true, 2 * j + 1), (false, 2 * r + 1), (false, 2 * s + 1)]]
  | .disj r s =>
      [[(true, 2 * j + 1), (false, 2 * r + 1)], [(true, 2 * j + 1), (false, 2 * s + 1)],
        [(false, 2 * j + 1), (true, 2 * r + 1), (true, 2 * s + 1)]]

/-- The defining clauses of all the gates of a circuit. -/
def defsCnf : Circuit → Cnf
  | [] => []
  | g :: C => gateCnf C.length g ++ defsCnf C

/-- **The Tseitin translation** of a circuit: the defining clauses of its gates together with the
assertion that the output gate is true.  The empty circuit, whose output is `false`, is translated
to the CNF consisting of the empty clause. -/
def toCnf : Circuit → Cnf
  | [] => [[]]
  | g :: C => [(true, 2 * C.length + 1)] :: defsCnf (g :: C)

/-- The translation has linear size: at most three clauses per gate, plus the output clause. -/
theorem length_toCnf_le (C : Circuit) : (toCnf C).length ≤ 3 * C.length + 1 := by
  have hd : ∀ D : Circuit, (defsCnf D).length ≤ 3 * D.length := by
    intro D
    induction D with
    | nil => simp [defsCnf]
    | cons g D ih =>
        have hg : (gateCnf D.length g).length ≤ 3 := by cases g <;> simp [gateCnf]
        rw [defsCnf, List.length_append]
        simp only [List.length_cons]
        omega
  cases C with
  | nil => simp [toCnf]
  | cons g C =>
      have h := hd (g :: C)
      simp only [List.length_cons] at h
      simp only [toCnf, List.length_cons]
      omega

/-! ### Variable bounds -/

/-- One more than the largest input index a gate reads. -/
def inpB : Gate → ℕ
  | .inp i => i + 1
  | _ => 0

/-- One more than the largest input index the circuit reads. -/
def inpBound : Circuit → ℕ
  | [] => 0
  | g :: C => max (inpB g) (inpBound C)

/-- A bound on the CNF variables the translation uses. -/
def varBound (C : Circuit) : ℕ := 2 * (C.length + inpBound C) + 2

theorem gateCnf_vars (j : ℕ) (g : Gate) (hg : gateWf j g) :
    ∀ D ∈ gateCnf j g, ∀ l ∈ D, l.2 < 2 * (j + inpB g) + 2 := by
  cases g <;> simp only [gateWf] at hg <;>
    simp only [gateCnf, inpB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] <;> omega

theorem defsCnf_vars : ∀ (C : Circuit), wf C → ∀ D ∈ defsCnf C, ∀ l ∈ D, l.2 < varBound C := by
  intro C
  induction C with
  | nil => intro _ D hD; simp [defsCnf] at hD
  | cons g C ih =>
      rintro ⟨hgw, hCw⟩ D hD l hl
      have hmono : varBound C ≤ varBound (g :: C) := by
        simp only [varBound, List.length_cons, inpBound]
        omega
      rw [defsCnf, List.mem_append] at hD
      rcases hD with hD | hD
      · have := gateCnf_vars C.length g hgw D hD l hl
        simp only [varBound, List.length_cons, inpBound]
        omega
      · exact lt_of_lt_of_le (ih hCw D hD l hl) hmono

theorem toCnf_vars (C : Circuit) (hC : wf C) : ∀ D ∈ toCnf C, ∀ l ∈ D, l.2 < varBound C := by
  cases C with
  | nil =>
      intro D hD l hl
      rw [toCnf, List.mem_cons] at hD
      rcases hD with rfl | hD
      · simp at hl
      · simp at hD
  | cons g C =>
      intro D hD l hl
      rw [toCnf, List.mem_cons] at hD
      rcases hD with rfl | hD
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        simp only [varBound, List.length_cons]
        omega
      · exact defsCnf_vars (g :: C) hC D hD l hl

/-! ### The canonical assignment -/

/-- The assignment attached to an input word: the even variables carry the input bits, the odd
variables the gate values. -/
def assign (x : Word) (C : Circuit) : ℕ → Bool := fun v =>
  if v % 2 = 0 then x.getD (v / 2) false else (vals x C).getD (v / 2) false

@[simp] theorem assign_even (x : Word) (C : Circuit) (i : ℕ) :
    assign x C (2 * i) = x.getD i false := by
  simp only [assign, if_pos (by omega : 2 * i % 2 = 0)]
  congr 1
  omega

@[simp] theorem assign_odd (x : Word) (C : Circuit) (j : ℕ) :
    assign x C (2 * j + 1) = (vals x C).getD j false := by
  simp only [assign, if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
  congr 1
  omega

/-! ### Correctness of the translation -/

/-- **The canonical assignment satisfies the defining clauses of every gate.** -/
theorem cnfValF_defsCnf (x : Word) : ∀ (C : Circuit), wf C → ∀ f : ℕ → Bool,
    (∀ i, f (2 * i) = x.getD i false) →
    (∀ j, j < C.length → f (2 * j + 1) = (vals x C).getD j false) →
    cnfValF f (defsCnf C) = true := by
  intro C
  induction C with
  | nil => intro _ _ _ _; rfl
  | cons g C ih =>
      rintro ⟨hgw, hCw⟩ f hin hg
      have hg' : ∀ j, j < C.length → f (2 * j + 1) = (vals x C).getD j false := by
        intro j hj
        rw [hg j (by simp only [List.length_cons]; omega), vals_cons_getD_lt x g C hj]
      have hhead : f (2 * C.length + 1) = gateVal x (vals x C) g := by
        rw [hg C.length (by simp), vals_cons_getD_length]
      rw [defsCnf, cnfValF_append, ih hCw f hin hg', Bool.and_true]
      cases g with
      | inp i =>
          rw [gateVal, ← hin i] at hhead
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hhead]
          cases f (2 * i) <;> simp
      | cst b =>
          rw [gateVal] at hhead
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hhead]
          cases b <;> simp
      | neg r =>
          rw [gateVal, ← hg' r hgw] at hhead
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hhead]
          cases f (2 * r + 1) <;> simp
      | conj r s =>
          rw [gateVal, ← hg' r hgw.1, ← hg' s hgw.2] at hhead
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hhead]
          cases f (2 * r + 1) <;> cases f (2 * s + 1) <;> simp
      | disj r s =>
          rw [gateVal, ← hg' r hgw.1, ← hg' s hgw.2] at hhead
          simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hhead]
          cases f (2 * r + 1) <;> cases f (2 * s + 1) <;> simp

/-- **Every satisfying assignment of the defining clauses computes the gate values** of the
circuit run on the input it describes. -/
theorem vals_of_cnfValF (x : Word) : ∀ (C : Circuit), wf C → ∀ f : ℕ → Bool,
    (∀ i, i < inpBound C → x.getD i false = f (2 * i)) →
    cnfValF f (defsCnf C) = true →
    ∀ j, j < C.length → f (2 * j + 1) = (vals x C).getD j false := by
  intro C
  induction C with
  | nil => intro _ _ _ _ j hj; simp at hj
  | cons g C ih =>
      rintro ⟨hgw, hCw⟩ f hx h j hj
      rw [defsCnf, cnfValF_append, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      have hxC : ∀ i, i < inpBound C → x.getD i false = f (2 * i) := by
        intro i hi
        exact hx i (lt_of_lt_of_le hi (le_max_right _ _))
      have ih' := ih hCw f hxC htail
      rcases Nat.lt_succ_iff_lt_or_eq.1 (by simpa using hj) with hj' | rfl
      · rw [ih' j hj', vals_cons_getD_lt x g C hj']
      · rw [vals_cons_getD_length]
        cases g with
        | inp i =>
            have hi : x.getD i false = f (2 * i) :=
              hx i (by simp only [inpBound, inpB]; omega)
            simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
              List.any_cons, List.any_nil] at hhead
            simp only [gateVal, hi]
            revert hhead
            cases f (2 * C.length + 1) <;> cases f (2 * i) <;> simp
        | cst b =>
            simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
              List.any_cons, List.any_nil] at hhead
            simp only [gateVal]
            revert hhead
            cases b <;> cases f (2 * C.length + 1) <;> simp
        | neg r =>
            have hr := ih' r hgw
            simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
              List.any_cons, List.any_nil] at hhead
            simp only [gateVal, ← hr]
            revert hhead
            cases f (2 * C.length + 1) <;> cases f (2 * r + 1) <;> simp
        | conj r s =>
            have hr := ih' r hgw.1
            have hs := ih' s hgw.2
            simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
              List.any_cons, List.any_nil] at hhead
            simp only [gateVal, ← hr, ← hs]
            revert hhead
            cases f (2 * C.length + 1) <;> cases f (2 * r + 1) <;> cases f (2 * s + 1) <;> simp
        | disj r s =>
            have hr := ih' r hgw.1
            have hs := ih' s hgw.2
            simp only [gateCnf, cnfValF, clauseValF, litValF, List.all_cons, List.all_nil,
              List.any_cons, List.any_nil] at hhead
            simp only [gateVal, ← hr, ← hs]
            revert hhead
            cases f (2 * C.length + 1) <;> cases f (2 * r + 1) <;> cases f (2 * s + 1) <;> simp

/-- **The Tseitin transformation preserves satisfiability**: a well-formed circuit is satisfiable
exactly when its translation is a satisfiable CNF. -/
theorem csat_iff_sat_toCnf (C : Circuit) (hC : wf C) :
    csat C ↔ ∃ σ : Word, cnfVal σ (toCnf C) = true := by
  constructor
  · rintro ⟨x, hx⟩
    cases C with
    | nil => simp [out] at hx
    | cons g C =>
        refine ⟨(List.range (varBound (g :: C))).map (assign x (g :: C)), ?_⟩
        rw [cnfVal_map_range (toCnf_vars (g :: C) hC), toCnf, cnfValF_cons]
        have hval : assign x (g :: C) (2 * C.length + 1) = true := by
          rw [assign_odd]
          exact (vals_cons_getD_length x g C).trans hx
        have h1 : clauseValF (assign x (g :: C)) [(true, 2 * C.length + 1)] = true := by
          simpa [clauseValF, litValF] using hval
        have h2 : cnfValF (assign x (g :: C)) (defsCnf (g :: C)) = true :=
          cnfValF_defsCnf x (g :: C) hC _ (fun i => assign_even x (g :: C) i)
            (fun j _ => assign_odd x (g :: C) j)
        simp [h1, h2]
  · rintro ⟨σ, hσ⟩
    rw [cnfVal_eq_cnfValF] at hσ
    cases C with
    | nil => simp [toCnf, cnfValF, clauseValF] at hσ
    | cons g C =>
        rw [toCnf, cnfValF_cons, Bool.and_eq_true] at hσ
        obtain ⟨hout, hdefs⟩ := hσ
        set f : ℕ → Bool := fun i => σ.getD i false with hf
        refine ⟨(List.range (inpBound (g :: C))).map (fun i => f (2 * i)), ?_⟩
        have hval := vals_of_cnfValF ((List.range (inpBound (g :: C))).map (fun i => f (2 * i)))
          (g :: C) hC f (fun i hi => getD_range_map hi) hdefs C.length (by simp)
        rw [vals_cons_getD_length] at hval
        have : f (2 * C.length + 1) = true := by
          simpa [clauseValF, litValF] using hout
        rw [out, ← hval]
        exact this

end Tseitin

end Complexity
