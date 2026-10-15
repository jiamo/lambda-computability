/-
**DAG-like (general) resolution refutations (M22-HAKEN-PHP-DAG, first exit criterion).**

In general resolution a derived clause may be used several times.  A DAG-like derivation from a
CNF `F` is a list of clauses in which every clause is a clause of `F` or the resolvent of two
earlier clauses of the list (`Complexity.Sat.DagDeriv`); a DAG-like refutation
(`Complexity.Sat.DagRefutation`) is one whose last clause is the empty clause, and its size is
the length of the list.

* `Complexity.Sat.DagDeriv.sound`, `Complexity.Sat.DagRefutation.unsat`: soundness.
* `Complexity.Sat.Deriv.toLines`: the postorder listing of a tree-like derivation; it is a
  DAG-like derivation of the same length as the tree (`Deriv.toLines_dagDeriv`,
  `Deriv.length_toLines`) ending with the derived clause.
* `Complexity.Sat.Refutation.toDag`, `Complexity.Sat.Refutation.toDag_size`: every tree-like
  refutation gives a DAG-like refutation whose size is its tree size.

The exponential lower bound for DAG-like refutations of `PHP(n+1, n)` (the second exit criterion)
is not proved here.
-/

import Start.Resolution

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Sat

/-- A clause justified from the clauses `prev` already listed: a clause of `F`, or the resolvent of
two clauses of `prev` on a variable occurring positively in the first and negatively in the
second. -/
def DagStep (F : Cnf) (prev : List Clause) (C : Clause) : Prop :=
  C ∈ F ∨ ∃ (k : ℕ) (C₁ C₂ : Clause), C₁ ∈ prev ∧ C₂ ∈ prev ∧ (true, k) ∈ C₁ ∧ (false, k) ∈ C₂ ∧
    C = resolvent k C₁ C₂

/-- DAG-like resolution derivations from `F`: lists of clauses each of which is a clause of `F` or
a resolvent of two earlier clauses. -/
inductive DagDeriv (F : Cnf) : List Clause → Prop
  | nil : DagDeriv F []
  | snoc {L : List Clause} {C : Clause} : DagDeriv F L → DagStep F L C → DagDeriv F (L ++ [C])

/-- A DAG-like refutation of `F`: a DAG-like derivation whose last clause is empty. -/
structure DagRefutation (F : Cnf) where
  /-- The clauses, in order. -/
  lines : List Clause
  /-- Each clause is initial or a resolvent of two earlier ones. -/
  valid : DagDeriv F lines
  /-- The last clause is the empty clause. -/
  last : lines.getLast? = some []

/-- The size of a DAG-like refutation: the number of its clauses. -/
def DagRefutation.size {F : Cnf} (R : DagRefutation F) : ℕ := R.lines.length

theorem DagStep.mono {F : Cnf} {L L' : List Clause} {C : Clause} (h : DagStep F L C)
    (hL : ∀ D ∈ L, D ∈ L') : DagStep F L' C := by
  rcases h with h | ⟨k, C₁, C₂, h₁, h₂, hk₁, hk₂, rfl⟩
  · exact .inl h
  · exact .inr ⟨k, C₁, C₂, hL _ h₁, hL _ h₂, hk₁, hk₂, rfl⟩

/-- Appending a DAG-like derivation to another one gives a DAG-like derivation. -/
theorem DagDeriv.append {F : Cnf} {L₁ : List Clause} (h₁ : DagDeriv F L₁) :
    ∀ {L₂ : List Clause}, DagDeriv F L₂ → DagDeriv F (L₁ ++ L₂)
  | _, .nil => by simpa using h₁
  | _, .snoc (L := L) (C := C) h hs => by
      rw [← List.append_assoc]
      exact .snoc (DagDeriv.append h₁ h)
        (hs.mono fun D hD => List.mem_append_right _ hD)

/-- **Soundness of DAG-like derivations**: an assignment satisfying `F` satisfies every listed
clause. -/
theorem DagDeriv.sound {F : Cnf} {σ : Word} (hσ : cnfVal σ F = true) :
    ∀ {L : List Clause}, DagDeriv F L → ∀ C ∈ L, clauseVal σ C = true
  | _, .nil => by simp
  | _, .snoc (L := L) (C := C) h hs => by
      intro D hD
      rcases List.mem_append.1 hD with hD | hD
      · exact DagDeriv.sound hσ h D hD
      · rw [List.mem_singleton] at hD
        subst hD
        rcases hs with hs | ⟨k, C₁, C₂, h₁, h₂, hk₁, hk₂, rfl⟩
        · exact cnfVal_eq_true.1 hσ _ hs
        · have hC := DagDeriv.sound hσ h C₁ h₁
          have hD' := DagDeriv.sound hσ h C₂ h₂
          rw [clauseVal_eq_true] at hC hD' ⊢
          obtain ⟨l, hl, hlv⟩ := hC
          obtain ⟨l', hl', hl'v⟩ := hD'
          by_cases e1 : l = (true, k)
          · by_cases e2 : l' = (false, k)
            · subst e1; subst e2
              rw [litVal_true] at hlv; rw [litVal_false, hlv] at hl'v
              exact absurd hl'v (by decide)
            · exact ⟨l', List.mem_append_right _
                (List.mem_filter.2 ⟨hl', by simpa using e2⟩), hl'v⟩
          · exact ⟨l, List.mem_append_left _ (List.mem_filter.2 ⟨hl, by simpa using e1⟩), hlv⟩

/-- **Soundness**: a CNF with a DAG-like refutation is unsatisfiable. -/
theorem DagRefutation.unsat {F : Cnf} (R : DagRefutation F) : ∀ σ, cnfVal σ F = false := by
  intro σ
  by_contra h
  have hσ : cnfVal σ F = true := by simpa using h
  have hmem : ([] : Clause) ∈ R.lines := List.mem_of_getLast? R.last
  have := R.valid.sound hσ _ hmem
  simp [clauseVal] at this

namespace Deriv

variable {F : Cnf}

/-- The postorder listing of the clauses of a tree-like derivation. -/
def toLines : {C : Clause} → Deriv F C → List Clause
  | _, ax (C := C) _ => [C]
  | _, res (C := C) (D := D) k d e _ _ => d.toLines ++ e.toLines ++ [resolvent k C D]

theorem length_toLines : ∀ {C : Clause} (d : Deriv F C), d.toLines.length = d.size
  | _, ax _ => rfl
  | _, res _ d e _ _ => by
      simp only [toLines, size, List.length_append, List.length_singleton, length_toLines d,
        length_toLines e]

theorem getLast?_toLines : ∀ {C : Clause} (d : Deriv F C), d.toLines.getLast? = some C
  | _, ax _ => rfl
  | _, res _ d e _ _ => by simp [toLines]

theorem mem_toLines {C : Clause} (d : Deriv F C) : C ∈ d.toLines :=
  List.mem_of_getLast? (getLast?_toLines d)

/-- The postorder listing is a DAG-like derivation. -/
theorem toLines_dagDeriv : ∀ {C : Clause} (d : Deriv F C), DagDeriv F d.toLines
  | _, ax h => DagDeriv.snoc (L := []) DagDeriv.nil (Or.inl h)
  | _, res k d e hk₁ hk₂ =>
      DagDeriv.snoc ((toLines_dagDeriv d).append (toLines_dagDeriv e))
        (Or.inr ⟨k, _, _, List.mem_append_left _ (mem_toLines d),
          List.mem_append_right _ (mem_toLines e), hk₁, hk₂, rfl⟩)

end Deriv

/-- The DAG-like refutation listing a tree-like refutation. -/
def Refutation.toDag {F : Cnf} (d : Refutation F) : DagRefutation F where
  lines := d.toLines
  valid := Deriv.toLines_dagDeriv d
  last := Deriv.getLast?_toLines d

/-- **Every tree-like refutation gives a DAG-like refutation of at most (here: exactly) its tree
size.** -/
theorem Refutation.toDag_size {F : Cnf} (d : Refutation F) : d.toDag.size = d.size :=
  Deriv.length_toLines d

theorem Refutation.exists_dag_size_le {F : Cnf} (d : Refutation F) :
    ∃ R : DagRefutation F, R.size ≤ d.size :=
  ⟨d.toDag, (Refutation.toDag_size d).le⟩

end Complexity.Sat
