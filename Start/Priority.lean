/-
**The frame a priority construction runs in.**

Nothing in the library so far is built by a priority argument.  This file sets up the frame:
what a construction is, what a requirement is, what it means for a requirement to be met and to be
injured, and the finite injury lemma — each requirement acts finitely often, hence is injured
finitely often, hence is met from some stage on.

The use function of an oracle computation, the other half of the frame, is in
`Start/OracleUse.lean`.

* `Lambda.Priority.Construction` — a computable increasing sequence of finite approximations, and
  `Lambda.Priority.Construction.rePred_set` — **the set it enumerates is c.e.**;
* `Lambda.Priority.Requirement` — a predicate on the approximation, with
  `Lambda.Priority.Requirement.MetAt`, `.Met` and `.InjuredAt` (satisfied at a stage and no longer
  at the next), and `Lambda.Priority.Requirement.met_of_not_injured` — a requirement that is
  satisfied once and never injured again stays satisfied;
* `Lambda.Priority.Injury` — requirements linearly ordered by priority, each acting only between
  injuries, a requirement being injured exactly when a requirement of higher priority acts;
* `Lambda.Priority.Injury.acts_finite`, `.injured_finite`, `.exists_final_stage` — **the finite
  injury lemma**;
* `Lambda.Priority.Injury.requirements_met` — the conclusion a construction draws from it.
-/

import Start.PostSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Priority

/-! ### Constructions -/

/-- Membership in a list of naturals is primitive recursive in the number and the list. -/
theorem primrec_mem_list : Primrec₂ (fun (n : ℕ) (l : List ℕ) => decide (n ∈ l)) := by
  have h1 : Primrec₂ (fun (n : ℕ) (l : List ℕ) => List.idxOf n l) := Primrec.list_idxOf
  have h2 : Primrec₂ (fun (_ : ℕ) (l : List ℕ) => l.length) :=
    Primrec.list_length.comp₂ Primrec₂.right
  have hlt : Primrec₂ (fun a b : ℕ => decide (a < b)) :=
    Post.primrec_decide (p := fun p : ℕ × ℕ => p.1 < p.2) Primrec.nat_lt
  have h3 : Primrec₂ (fun (n : ℕ) (l : List ℕ) => decide (List.idxOf n l < l.length)) :=
    Primrec₂.comp hlt h1 h2
  exact h3.of_eq fun n l => by simp [List.idxOf_lt_length_iff]

/-- **A construction**: a stage-indexed sequence of finite approximations, given by a primitive
recursive list of the elements enumerated so far, which only grows. -/
structure Construction where
  /-- The finite approximation at a stage. -/
  approx : ℕ → List ℕ
  /-- The approximation only grows. -/
  mono : ∀ s, approx s ⊆ approx (s + 1)
  /-- The approximation is computed uniformly in the stage. -/
  primrec : Primrec approx

namespace Construction

variable (C : Construction)

/-- The set the construction enumerates. -/
def set : ℕ → Prop := fun n => ∃ s, n ∈ C.approx s

theorem mono_le {s t : ℕ} (h : s ≤ t) : C.approx s ⊆ C.approx t := by
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst this
      exact fun n hn => hn
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with h' | h'
      · exact fun n hn => C.mono t (ih (by omega) hn)
      · have : s = t + 1 := by omega
        subst this
        exact fun n hn => hn

/-- An element of the set appears at every late enough stage. -/
theorem mem_approx_of_set {n : ℕ} (h : C.set n) : ∃ t, ∀ s, t ≤ s → n ∈ C.approx s := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, fun s hs => C.mono_le hs ht⟩

/-- **The set a construction enumerates is c.e.** -/
theorem rePred_set : REPred C.set := by
  refine Post.rePred_of_exists_test (fun n s => decide (n ∈ C.approx s)) ?_ ?_
  · exact Primrec₂.comp primrec_mem_list Primrec₂.left (C.primrec.comp₂ Primrec₂.right)
  · intro n
    simp [set]

end Construction

/-! ### Requirements -/

/-- **A requirement**: a predicate on the stage-indexed approximation. -/
structure Requirement where
  /-- The property of an approximation that the requirement asks for. -/
  holds : List ℕ → Prop

namespace Requirement

variable (R : Requirement) (C : Construction)

/-- The requirement is satisfied by the approximation at a stage. -/
def MetAt (s : ℕ) : Prop := R.holds (C.approx s)

/-- The requirement is **met**: satisfied from some stage on. -/
def Met : Prop := ∃ t, ∀ s, t ≤ s → R.MetAt C s

/-- The requirement is **injured** at a stage: it was satisfied there and is not satisfied at the
next stage. -/
def InjuredAt (s : ℕ) : Prop := R.MetAt C s ∧ ¬ R.MetAt C (s + 1)

variable {R C}

/-- A requirement that is satisfied at a stage and never injured afterwards stays satisfied. -/
theorem metAt_of_not_injured {t : ℕ} (hmet : R.MetAt C t)
    (hinj : ∀ s, t ≤ s → ¬ R.InjuredAt C s) : ∀ s, t ≤ s → R.MetAt C s := by
  intro s hs
  induction s with
  | zero =>
      have : t = 0 := by omega
      subst this
      exact hmet
  | succ s ih =>
      rcases Nat.lt_or_ge t (s + 1) with h | h
      · have hprev : R.MetAt C s := ih (by omega)
        by_contra hcon
        exact hinj s (by omega) ⟨hprev, hcon⟩
      · have : t = s + 1 := by omega
        subst this
        exact hmet

/-- Hence such a requirement is met. -/
theorem met_of_not_injured {t : ℕ} (hmet : R.MetAt C t)
    (hinj : ∀ s, t ≤ s → ¬ R.InjuredAt C s) : R.Met C :=
  ⟨t, metAt_of_not_injured hmet hinj⟩

end Requirement

/-! ### The finite injury lemma -/

/-- **The data of a finite injury construction.**  Requirements are indexed by the naturals and
ordered by priority, a smaller index having the higher priority; `acts i s` says that the `i`-th
requirement acts at stage `s`.  The single hypothesis is the one a finite injury argument
establishes by inspection of the construction: a requirement acts twice only if a requirement of
higher priority acted in between. -/
structure Injury where
  /-- The `i`-th requirement acts at stage `s`. -/
  acts : ℕ → ℕ → Prop
  /-- Between two actions of a requirement, one of higher priority acts. -/
  betweenInjury : ∀ i s t, acts i s → acts i t → s < t →
    ∃ u, s ≤ u ∧ u < t ∧ ∃ j, j < i ∧ acts j u

namespace Injury

variable (I : Injury)

/-- A requirement is **injured** at a stage when a requirement of higher priority acts there. -/
def injured (i s : ℕ) : Prop := ∃ j, j < i ∧ I.acts j s

theorem injured_iff {i s : ℕ} : I.injured i s ↔ ∃ j, j < i ∧ I.acts j s := Iff.rfl

/-- The requirement of highest priority is never injured. -/
theorem not_injured_zero (s : ℕ) : ¬ I.injured 0 s := by
  rintro ⟨j, hj, -⟩
  omega

/-- **The finite injury lemma.**  Every requirement acts only finitely often. -/
theorem acts_finite (i : ℕ) : {s | I.acts i s}.Finite := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hinj : {s | I.injured i s}.Finite := by
      have hsub : {s | I.injured i s} ⊆ ⋃ j ∈ Finset.range i, {s | I.acts j s} := by
        rintro s ⟨j, hj, hs⟩
        exact Set.mem_biUnion (Finset.mem_range.2 hj) hs
      refine Set.Finite.subset ?_ hsub
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun j hj => ih j (Finset.mem_range.1 hj)
    obtain ⟨M, hM⟩ := hinj.bddAbove
    have hMle : ∀ u, I.injured i u → u ≤ M := fun u hu => hM hu
    have hlate : {s | I.acts i s ∧ M < s}.Subsingleton := by
      have key : ∀ s t, I.acts i s → M < s → I.acts i t → M < t → s < t → False := by
        intro s t hs hsM ht _ hst
        obtain ⟨u, hu1, hu2, j, hj, hju⟩ := I.betweenInjury i s t hs ht hst
        have : u ≤ M := hMle u ⟨j, hj, hju⟩
        omega
      rintro s ⟨hs, hsM⟩ t ⟨ht, htM⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact key s t hs hsM ht htM hlt
      · exact key t s ht htM hs hsM hlt
    refine Set.Finite.subset (Set.Finite.union (Set.finite_Iic M) hlate.finite) ?_
    intro s hs
    rcases le_or_gt s M with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hs, h⟩

/-- Hence every requirement is injured only finitely often. -/
theorem injured_finite (i : ℕ) : {s | I.injured i s}.Finite := by
  have hsub : {s | I.injured i s} ⊆ ⋃ j ∈ Finset.range i, {s | I.acts j s} := by
    rintro s ⟨j, hj, hs⟩
    exact Set.mem_biUnion (Finset.mem_range.2 hj) hs
  exact Set.Finite.subset
    (Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => I.acts_finite j) hsub

/-- **Every requirement is eventually left alone**: from some stage on it neither acts nor is
injured. -/
theorem exists_final_stage (i : ℕ) :
    ∃ t, ∀ s, t ≤ s → ¬ I.acts i s ∧ ¬ I.injured i s := by
  have hfin : ({s | I.acts i s} ∪ {s | I.injured i s}).Finite :=
    (I.acts_finite i).union (I.injured_finite i)
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨M + 1, fun s hs => ⟨fun hcon => ?_, fun hcon => ?_⟩⟩
  · have : s ≤ M := hM (Or.inl hcon)
    omega
  · have : s ≤ M := hM (Or.inr hcon)
    omega

/-- The conclusion a finite injury construction draws: if a requirement is met as soon as it is
left alone, then every requirement is met. -/
theorem requirements_met {Met : ℕ → Prop}
    (hmeet : ∀ i t, (∀ s, t ≤ s → ¬ I.acts i s ∧ ¬ I.injured i s) → Met i) : ∀ i, Met i := by
  intro i
  obtain ⟨t, ht⟩ := I.exists_final_stage i
  exact hmeet i t ht

end Injury

end Priority
end Lambda
