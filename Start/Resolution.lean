/-
**Resolution refutations: soundness and refutational completeness.**

The CNFs are those of `Start/Sat.lean` (`Complexity.Sat.Cnf`, a list of clauses, a clause a list
of literals `(sign, variable)`).  A resolution derivation of a clause from a CNF
(`Complexity.Sat.Deriv F C`) is a tree whose leaves are clauses of `F` and whose inner nodes apply
the resolution rule

  `C ∋ x`,  `D ∋ ¬x`  ⟹  `(C ∖ {x}) ∪ (D ∖ {¬x})`   (`Complexity.Sat.resolvent`).

Its size (`Complexity.Sat.Deriv.size`) is the number of nodes.  A refutation is a derivation of the
empty clause.

Main results:

* `Complexity.Sat.Deriv.sound` — every assignment satisfying `F` satisfies each derived clause;
* `Complexity.Sat.unsat_of_refutation` — **soundness**: a CNF with a refutation is unsatisfiable;
* `Complexity.Sat.refutation_of_unsat` — **refutational completeness**: every unsatisfiable CNF
  has a refutation;
* `Complexity.Sat.refutation_iff_unsat` — the two together.

The completeness proof is the Davis–Putnam argument: eliminate one variable `k`, refute the two
restrictions `F|k:=true` and `F|k:=false` by induction, lift the two refutations to derivations
from `F` of a clause inside `{¬k}` and of a clause inside `{k}` (`Complexity.Sat.Deriv.lift`), and
resolve them.
-/

import Mathlib
import Start.Sat

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Sat

/-! ### The rule and the derivations -/

/-- The resolvent of `C` and `D` on the variable `k`: `C` without the literal `k`, followed by `D`
without the literal `¬k`. -/
def resolvent (k : ℕ) (C D : Clause) : Clause :=
  C.filter (· ≠ (true, k)) ++ D.filter (· ≠ (false, k))

/-- Resolution derivations of a clause from the clauses of `F`. -/
inductive Deriv (F : Cnf) : Clause → Type
  /-- A clause of `F`. -/
  | ax {C : Clause} : C ∈ F → Deriv F C
  /-- The resolution rule on the variable `k`. -/
  | res {C D : Clause} (k : ℕ) : Deriv F C → Deriv F D → (true, k) ∈ C → (false, k) ∈ D →
      Deriv F (resolvent k C D)

namespace Deriv

variable {F : Cnf}

/-- The number of nodes of a derivation. -/
def size : {C : Clause} → Deriv F C → ℕ
  | _, ax _ => 1
  | _, res _ d e _ _ => d.size + e.size + 1

end Deriv

/-- A refutation of `F`: a derivation of the empty clause. -/
abbrev Refutation (F : Cnf) : Type := Deriv F []

/-! ### Soundness -/

theorem litVal_true (σ : Word) (k : ℕ) : litVal σ (true, k) = σ.getD k false := rfl

theorem litVal_false (σ : Word) (k : ℕ) : litVal σ (false, k) = !σ.getD k false := rfl

theorem clauseVal_eq_true {σ : Word} {C : Clause} :
    clauseVal σ C = true ↔ ∃ l ∈ C, litVal σ l = true := by
  simp [clauseVal, List.any_eq_true]

theorem cnfVal_eq_true {σ : Word} {F : Cnf} :
    cnfVal σ F = true ↔ ∀ C ∈ F, clauseVal σ C = true := by
  simp [cnfVal, List.all_eq_true]

/-- **Soundness of the rule**: an assignment satisfying `F` satisfies every derived clause. -/
theorem Deriv.sound {F : Cnf} {σ : Word} (hσ : cnfVal σ F = true) :
    ∀ {C : Clause}, Deriv F C → clauseVal σ C = true
  | _, .ax h => cnfVal_eq_true.1 hσ _ h
  | _, .res k d e _ _ => by
      have hC := Deriv.sound hσ d
      have hD := Deriv.sound hσ e
      rw [clauseVal_eq_true] at hC hD ⊢
      obtain ⟨l, hl, hlv⟩ := hC
      obtain ⟨l', hl', hl'v⟩ := hD
      by_cases h1 : l = (true, k)
      · by_cases h2 : l' = (false, k)
        · subst h1; subst h2
          rw [litVal_true] at hlv; rw [litVal_false, hlv] at hl'v
          exact absurd hl'v (by decide)
        · exact ⟨l', List.mem_append_right _ (List.mem_filter.2 ⟨hl', by simpa using h2⟩), hl'v⟩
      · exact ⟨l, List.mem_append_left _ (List.mem_filter.2 ⟨hl, by simpa using h1⟩), hlv⟩

/-- **Soundness**: a CNF with a refutation is unsatisfiable. -/
theorem unsat_of_refutation {F : Cnf} (d : Refutation F) : ∀ σ, cnfVal σ F = false := by
  intro σ
  by_contra h
  have := Deriv.sound (Bool.not_eq_false _ ▸ h) d
  simp at this

/-! ### Restriction -/

/-- The assignment `σ` with the variable `k` set to `b`. -/
def upd (σ : Word) (k : ℕ) (b : Bool) : Word := (σ ++ List.replicate (k + 1) false).set k b

theorem getD_upd_self (σ : Word) (k : ℕ) (b : Bool) : (upd σ k b).getD k false = b := by
  unfold upd
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem getD_upd_ne (σ : Word) {k j : ℕ} (b : Bool) (h : j ≠ k) :
    (upd σ k b).getD j false = σ.getD j false := by
  unfold upd
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]
  by_cases h1 : j < σ.length
  · rw [List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : σ.length ≤ j),
      List.getElem?_replicate]
    split_ifs <;> rfl

theorem litVal_upd_self (σ : Word) (k : ℕ) (b : Bool) : litVal (upd σ k b) (b, k) = true := by
  cases b <;> simp [litVal, -List.getD_eq_getElem?_getD, getD_upd_self]

/-- The restriction of `F` by `k := b`: the clauses satisfied by it are dropped, and the falsified
literal is removed from the others. -/
def restrict (F : Cnf) (k : ℕ) (b : Bool) : Cnf :=
  (F.filter fun C => decide ((b, k) ∉ C)).map fun C => C.filter (· ≠ (!b, k))

/-- No literal of `C` is on the variable `k`. -/
def Avoids (k : ℕ) (C : Clause) : Prop := ∀ l ∈ C, l.2 ≠ k

theorem avoids_restrict {F : Cnf} {k : ℕ} {b : Bool} {C : Clause} (hC : C ∈ restrict F k b) :
    Avoids k C := by
  simp only [restrict, List.mem_map, List.mem_filter, decide_eq_true_eq] at hC
  obtain ⟨D, ⟨_, hbD⟩, rfl⟩ := hC
  intro l hl heq
  simp only [List.mem_filter, ne_eq, decide_eq_true_eq] at hl
  obtain ⟨hlD, hl'⟩ := hl
  obtain ⟨s, j⟩ := l
  simp only at heq
  subst heq
  cases s <;> cases b <;> simp_all

/-- On a clause avoiding `k` the value does not depend on the variable `k`. -/
theorem litVal_upd_of_ne (σ : Word) {k : ℕ} (b : Bool) {l : Lit} (h : l.2 ≠ k) :
    litVal (upd σ k b) l = litVal σ l := by
  obtain ⟨s, j⟩ := l
  simp only [litVal, getD_upd_ne σ b h]

theorem clauseVal_upd_of_avoids (σ : Word) {k : ℕ} (b : Bool) {C : Clause} (h : Avoids k C) :
    clauseVal (upd σ k b) C = clauseVal σ C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [clauseVal_cons]
      rw [litVal_upd_of_ne σ b (h l (by simp)), ih (fun l' hl' => h l' (by simp [hl']))]

/-- **Restriction preserves unsatisfiability.** -/
theorem restrict_unsat {F : Cnf} (hF : ∀ σ, cnfVal σ F = false) (k : ℕ) (b : Bool) :
    ∀ σ, cnfVal σ (restrict F k b) = false := by
  intro σ
  by_contra hσ
  rw [Bool.not_eq_false] at hσ
  apply absurd (hF (upd σ k b))
  rw [Bool.not_eq_false, cnfVal_eq_true]
  intro C hC
  by_cases hbC : (b, k) ∈ C
  · rw [clauseVal_eq_true]
    exact ⟨(b, k), hbC, litVal_upd_self σ k b⟩
  · have hmem : C.filter (· ≠ (!b, k)) ∈ restrict F k b := by
      simp only [restrict, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨C, ⟨hC, hbC⟩, rfl⟩
    have h1 := cnfVal_eq_true.1 hσ _ hmem
    rw [← clauseVal_upd_of_avoids σ b (avoids_restrict hmem), clauseVal_eq_true] at h1
    obtain ⟨l, hl, hlv⟩ := h1
    rw [clauseVal_eq_true]
    exact ⟨l, (List.mem_filter.1 hl).1, hlv⟩

/-! ### Lifting a refutation of a restriction -/

theorem Deriv.avoids {G : Cnf} {k : ℕ} (hG : ∀ C ∈ G, Avoids k C) :
    ∀ {C : Clause}, Deriv G C → Avoids k C
  | _, .ax h => hG _ h
  | _, .res j d e _ _ => by
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact Deriv.avoids hG d l (List.mem_filter.1 hl).1
      · exact Deriv.avoids hG e l (List.mem_filter.1 hl).1

/-- **Lifting.**  A derivation of `C` from `F|k:=b` gives a derivation from `F` of a clause whose
literals are those of `C` and possibly `¬b` on `k`. -/
theorem Deriv.lift {F : Cnf} {k : ℕ} {b : Bool} :
    ∀ {C : Clause}, Deriv (restrict F k b) C →
      ∃ C', Nonempty (Deriv F C') ∧ ∀ l ∈ C', l ∈ C ∨ l = (!b, k)
  | _, .ax h => by
      simp only [restrict, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
      obtain ⟨D, ⟨hD, _⟩, rfl⟩ := h
      refine ⟨D, ⟨.ax hD⟩, fun l hl => ?_⟩
      by_cases h : l = (!b, k)
      · exact Or.inr h
      · exact Or.inl (List.mem_filter.2 ⟨hl, by simpa using h⟩)
  | _, .res j d e hj hj' => by
      obtain ⟨C₁, ⟨d₁⟩, h₁⟩ := Deriv.lift d
      obtain ⟨C₂, ⟨d₂⟩, h₂⟩ := Deriv.lift e
      have hjk : j ≠ k := by
        have := Deriv.avoids (fun _ hC => avoids_restrict hC) d (true, j) hj
        simpa using this
      by_cases hC₁ : (true, j) ∈ C₁
      · by_cases hC₂ : (false, j) ∈ C₂
        · refine ⟨_, ⟨.res j d₁ d₂ hC₁ hC₂⟩, fun l hl => ?_⟩
          rcases List.mem_append.1 hl with hl | hl
          · obtain ⟨hl1, hl2⟩ := List.mem_filter.1 hl
            rcases h₁ l hl1 with h | h
            · exact Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨h, hl2⟩))
            · exact Or.inr h
          · obtain ⟨hl1, hl2⟩ := List.mem_filter.1 hl
            rcases h₂ l hl1 with h | h
            · exact Or.inl (List.mem_append_right _ (List.mem_filter.2 ⟨h, hl2⟩))
            · exact Or.inr h
        · refine ⟨C₂, ⟨d₂⟩, fun l hl => ?_⟩
          rcases h₂ l hl with h | h
          · have hne : l ≠ (false, j) := fun he => hC₂ (he ▸ hl)
            exact Or.inl (List.mem_append_right _ (List.mem_filter.2 ⟨h, by simpa using hne⟩))
          · exact Or.inr h
      · refine ⟨C₁, ⟨d₁⟩, fun l hl => ?_⟩
        rcases h₁ l hl with h | h
        · have hne : l ≠ (true, j) := fun he => hC₁ (he ▸ hl)
          exact Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨h, by simpa using hne⟩))
        · exact Or.inr h

/-! ### Completeness -/

theorem completeness_aux : ∀ (V : List ℕ) (F : Cnf), (∀ C ∈ F, ∀ l ∈ C, l.2 ∈ V) →
    (∀ σ, cnfVal σ F = false) → Nonempty (Refutation F)
  | [], F, hV, hF => by
      have hne : F ≠ [] := by
        rintro rfl
        simpa using hF []
      obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil F hne
      have hCnil : C = [] := by
        rcases C with _ | ⟨l, C⟩
        · rfl
        · exact absurd (hV _ hC l (by simp)) (by simp)
      exact ⟨.ax (hCnil ▸ hC)⟩
  | k :: V, F, hV, hF => by
      have hres : ∀ b, (∀ C ∈ restrict F k b, ∀ l ∈ C, l.2 ∈ V) := by
        intro b C hC l hl
        have h1 := avoids_restrict hC l hl
        simp only [restrict, List.mem_map, List.mem_filter, decide_eq_true_eq] at hC
        obtain ⟨D, ⟨hD, _⟩, rfl⟩ := hC
        have := hV D hD l (List.mem_filter.1 hl).1
        simp only [List.mem_cons] at this
        exact this.resolve_left h1
      obtain ⟨d₁⟩ := completeness_aux V _ (hres true) (restrict_unsat hF k true)
      obtain ⟨d₂⟩ := completeness_aux V _ (hres false) (restrict_unsat hF k false)
      obtain ⟨C₁, ⟨e₁⟩, h₁⟩ := Deriv.lift d₁
      obtain ⟨C₂, ⟨e₂⟩, h₂⟩ := Deriv.lift d₂
      simp only [List.not_mem_nil, false_or, Bool.not_true, Bool.not_false] at h₁ h₂
      rcases C₁ with _ | ⟨l₁, C₁'⟩
      · exact ⟨e₁⟩
      rcases C₂ with _ | ⟨l₂, C₂'⟩
      · exact ⟨e₂⟩
      have hm₁ : (false, k) ∈ l₁ :: C₁' := by rw [← h₁ l₁ (by simp)]; simp
      have hm₂ : (true, k) ∈ l₂ :: C₂' := by rw [← h₂ l₂ (by simp)]; simp
      have hnil : resolvent k (l₂ :: C₂') (l₁ :: C₁') = [] := by
        simp only [resolvent, List.append_eq_nil_iff, List.filter_eq_nil_iff, ne_eq,
          decide_eq_true_eq, not_not]
        exact ⟨h₂, h₁⟩
      have d := Deriv.res k e₂ e₁ hm₂ hm₁
      rw [hnil] at d
      exact ⟨d⟩

/-- The variables occurring in `F`. -/
def vars (F : Cnf) : List ℕ := F.flatMap fun C => C.map Prod.snd

theorem mem_vars {F : Cnf} {C : Clause} (hC : C ∈ F) {l : Lit} (hl : l ∈ C) : l.2 ∈ vars F := by
  simp only [vars, List.mem_flatMap, List.mem_map]
  exact ⟨C, hC, l, hl, rfl⟩

/-- **Refutational completeness**: every unsatisfiable CNF has a resolution refutation. -/
theorem refutation_of_unsat {F : Cnf} (hF : ∀ σ, cnfVal σ F = false) : Nonempty (Refutation F) :=
  completeness_aux (vars F) F (fun _ hC _ hl => mem_vars hC hl) hF

/-- **A CNF has a resolution refutation exactly when it is unsatisfiable.** -/
theorem refutation_iff_unsat (F : Cnf) : Nonempty (Refutation F) ↔ ∀ σ, cnfVal σ F = false :=
  ⟨fun ⟨d⟩ => unsat_of_refutation d, refutation_of_unsat⟩

end Complexity.Sat
