/-
**The deterministic fragment F<:^D and its embedding in full F<:** — task `M25-FSUB-UNDECIDABLE`
(round 6, steps D1–D2).

Pierce's reduction (two-counter machines → rowing machines → F<:^D → F<:) rests on a fragment of
F<: whose subtyping derivations are *linear*: every rule has at most one premise that is not
an axiom.  Two shapes of quantifier give linear rules in the algorithm for full F<:
(`FsubGhelli.Sub`):

* a left quantifier with bound `Top`: `∀X<:Top. S₂ <: ∀X<:T₁. T₂` has the bound subgoal
  `T₁ <: Top`, an axiom, so it holds iff `X<:T₁ ⊢ S₂ <: T₂` (`FsubRowing.sub_allTop_iff`);
* two negations `¬S = ∀X<:S. X`: `¬S <: ¬T` has the body subgoal `X<:T ⊢ X <: X`, an axiom, so it
  holds iff `T <: S` (`FsubRowing.sub_neg_iff`) — this rule *swaps the sides*.

With promotion (`FsubRowing.sub_var_iff`: a variable against a non-trivial right-hand side holds
iff its bound does) these are the rules of F<:^D.

* `FsubRowing.SubD` — subtyping of F<:^D: `Top`, reflexivity, promotion, the `Top`-bounded
  quantifier rule and the negation rule, each with one premise;
* `FsubRowing.SubD.toSub` — **D2: F<:^D subtyping embeds into full F<: subtyping** (the algorithmic
  relation `FsubGhelli.Sub`);
* `FsubRowing.SubD.linear` — F<:^D derivations are linear: a derivable goal is an axiom or has
  exactly one derivable premise, given by the deterministic step `FsubRowing.DStep`;
* `FsubRowing.subD_iff_run` — **determinism**: a goal is derivable in F<:^D iff the deterministic
  run from it reaches an axiom (`FsubRowing.DRun`); this is the form in which a machine is
  simulated (a halting run is a finite run of `DStep`);
* `FsubRowing.DStep.deterministic` — the step is a partial function;
* `FsubRowing.rowingFirstLemma_of_simulation` — `FsubGhelli.RowingFirstLemma` follows from an
  encoding of two-counter machines whose deterministic run reaches an axiom exactly on halting,
  together with conservativity of full F<: over F<:^D on the encoded goals.  That simulation is
  the first missing lemma (steps D1/D3).
-/

import Start.FsubGhelli

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FsubRowing

open FsubGhelli

/-! ### Linear rules of the algorithm for full F<: -/

/-- **Negation swaps the sides**: `¬S <: ¬T` holds in full F<: iff `T <: S` does. -/
theorem sub_neg_iff {Γ : List Ty} {S T : Ty} :
    Sub ⟨Γ, neg S, neg T⟩ ↔ Sub ⟨Γ, T, S⟩ := by
  constructor
  · intro h
    cases h with
    | all h1 _ => exact h1
  · intro h
    exact Sub.all h Sub.refl

/-- **A `Top`-bounded left quantifier**: `∀X<:Top. S₂ <: ∀X<:T₁. T₂` holds iff
`X<:T₁ ⊢ S₂ <: T₂` does. -/
theorem sub_allTop_iff {Γ : List Ty} {S₂ T₁ T₂ : Ty} :
    Sub ⟨Γ, .all .top S₂, .all T₁ T₂⟩ ↔ Sub ⟨T₁ :: Γ, S₂, T₂⟩ := by
  constructor
  · intro h
    cases h with
    | all _ h2 => exact h2
  · intro h
    exact Sub.all Sub.top h

/-- **Promotion is forced**: a variable against a right-hand side other than `Top` and itself
holds iff its bound does. -/
theorem sub_var_iff {Γ : List Ty} {i : ℕ} {T : Ty} (h1 : T ≠ .var i) (h2 : T ≠ .top) :
    Sub ⟨Γ, .var i, T⟩ ↔ ∃ B, Γ[i]? = some B ∧ Sub ⟨Γ, Ty.lift (i + 1) 0 B, T⟩ := by
  constructor
  · intro h
    cases h with
    | top => exact absurd rfl h2
    | refl => exact absurd rfl h1
    | promote hB _ _ h => exact ⟨_, hB, h⟩
  · rintro ⟨B, hB, h⟩
    exact Sub.promote hB h1 h2 h

/-! ### F<:^D -/

/-- **Subtyping of F<:^D**: the linear rules. -/
inductive SubD : Goal → Prop
  /-- `S <: Top`. -/
  | top {Γ : List Ty} {S : Ty} : SubD ⟨Γ, S, .top⟩
  /-- `X <: X`. -/
  | refl {Γ : List Ty} {i : ℕ} : SubD ⟨Γ, .var i, .var i⟩
  /-- Promotion of a variable to its bound. -/
  | promote {Γ : List Ty} {i : ℕ} {B T : Ty} : Γ[i]? = some B → T ≠ .var i → T ≠ .top →
      SubD ⟨Γ, Ty.lift (i + 1) 0 B, T⟩ → SubD ⟨Γ, .var i, T⟩
  /-- The `Top`-bounded quantifier rule (no bound comparison). -/
  | allTop {Γ : List Ty} {S₂ T₁ T₂ : Ty} : SubD ⟨T₁ :: Γ, S₂, T₂⟩ →
      SubD ⟨Γ, .all .top S₂, .all T₁ T₂⟩
  /-- The negation rule (the sides are swapped). -/
  | neg {Γ : List Ty} {S T : Ty} : SubD ⟨Γ, T, S⟩ → SubD ⟨Γ, neg S, neg T⟩

/-- **D2: F<:^D subtyping embeds into full F<: subtyping.** -/
theorem SubD.toSub {g : Goal} (h : SubD g) : Sub g := by
  induction h with
  | top => exact Sub.top
  | refl => exact Sub.refl
  | promote hB h1 h2 _ ih => exact Sub.promote hB h1 h2 ih
  | allTop _ ih => exact sub_allTop_iff.2 ih
  | neg _ ih => exact sub_neg_iff.2 ih

/-- A goal is an *axiom* of F<:^D. -/
def IsAxiom (g : Goal) : Prop := g.rhs = .top ∨ ∃ i, g.lhs = .var i ∧ g.rhs = .var i

/-- **The deterministic step of F<:^D**: the unique non-axiom premise of a goal (if a rule other
than an axiom applies).  Promotion has priority over nothing else: a variable on the left only
promotes; a `Top`-bounded quantifier against a quantifier enters the body; a negation against a
negation swaps (the cases overlap only at `∀X<:Top. X` against `¬T`, where both give the same
derivability, and the step takes the negation rule). -/
inductive DStep : Goal → Goal → Prop
  | promote {Γ : List Ty} {i : ℕ} {B T : Ty} : Γ[i]? = some B → T ≠ .var i → T ≠ .top →
      DStep ⟨Γ, .var i, T⟩ ⟨Γ, Ty.lift (i + 1) 0 B, T⟩
  | allTop {Γ : List Ty} {S₂ T₁ T₂ : Ty} : T₂ ≠ .var 0 ∨ S₂ ≠ .var 0 →
      DStep ⟨Γ, .all .top S₂, .all T₁ T₂⟩ ⟨T₁ :: Γ, S₂, T₂⟩
  | neg {Γ : List Ty} {S T : Ty} : DStep ⟨Γ, neg S, neg T⟩ ⟨Γ, T, S⟩

/-- The deterministic run from a goal reaches an axiom. -/
def DRun (g : Goal) : Prop := ∃ g', Relation.ReflTransGen DStep g g' ∧ IsAxiom g'

theorem subD_of_isAxiom {g : Goal} (h : IsAxiom g) : SubD g := by
  obtain ⟨Γ, S, T⟩ := g
  rcases h with h | ⟨i, h1, h2⟩
  · simp only at h; subst h; exact SubD.top
  · simp only at h1 h2; subst h1; subst h2; exact SubD.refl

theorem subD_of_dstep {g g' : Goal} (hs : DStep g g') (h : SubD g') : SubD g := by
  cases hs with
  | promote hB h1 h2 => exact SubD.promote hB h1 h2 h
  | allTop _ => exact SubD.allTop h
  | neg => exact SubD.neg h

/-- **F<:^D derivations are linear**: a derivable goal is an axiom or makes a deterministic step
to a derivable goal. -/
theorem SubD.linear {g : Goal} (h : SubD g) : IsAxiom g ∨ ∃ g', DStep g g' ∧ SubD g' := by
  cases h with
  | top => exact Or.inl (Or.inl rfl)
  | refl => exact Or.inl (Or.inr ⟨_, rfl, rfl⟩)
  | promote hB h1 h2 h => exact Or.inr ⟨_, DStep.promote hB h1 h2, h⟩
  | @allTop Γ S₂ T₁ T₂ h =>
      by_cases hT : T₂ = .var 0
      · by_cases hS : S₂ = .var 0
        · subst hT; subst hS
          -- `∀X<:Top. X <: ∀X<:T₁. X` is `¬Top <: ¬T₁`: take the negation step.
          exact Or.inr ⟨⟨Γ, T₁, .top⟩, DStep.neg, SubD.top⟩
        · exact Or.inr ⟨_, DStep.allTop (Or.inr hS), h⟩
      · exact Or.inr ⟨_, DStep.allTop (Or.inl hT), h⟩
  | neg h => exact Or.inr ⟨_, DStep.neg, h⟩

/-- **Determinism**: a goal is derivable in F<:^D iff the deterministic run from it reaches
an axiom. -/
theorem subD_iff_run {g : Goal} : SubD g ↔ DRun g := by
  constructor
  · intro h
    induction h with
    | top => exact ⟨_, .refl, Or.inl rfl⟩
    | refl => exact ⟨_, .refl, Or.inr ⟨_, rfl, rfl⟩⟩
    | promote hB h1 h2 _ ih =>
        obtain ⟨g', hr, ha⟩ := ih
        exact ⟨g', .head (DStep.promote hB h1 h2) hr, ha⟩
    | @allTop Γ S₂ T₁ T₂ _ ih =>
        by_cases hT : T₂ = .var 0
        · by_cases hS : S₂ = .var 0
          · subst hT; subst hS
            exact ⟨⟨Γ, T₁, .top⟩, .single DStep.neg, Or.inl rfl⟩
          · obtain ⟨g', hr, ha⟩ := ih
            exact ⟨g', .head (DStep.allTop (Or.inr hS)) hr, ha⟩
        · obtain ⟨g', hr, ha⟩ := ih
          exact ⟨g', .head (DStep.allTop (Or.inl hT)) hr, ha⟩
    | neg _ ih =>
        obtain ⟨g', hr, ha⟩ := ih
        exact ⟨g', .head DStep.neg hr, ha⟩
  · rintro ⟨g', hr, ha⟩
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact subD_of_isAxiom ha
    | head hs _ ih => exact subD_of_dstep hs ih

/-- A derivable F<:^D goal is derivable in full F<: (the run form of the embedding). -/
theorem sub_of_run {g : Goal} (h : DRun g) : Sub g := (subD_iff_run.2 h).toSub

/-- **The step of F<:^D is deterministic.** -/
theorem DStep.deterministic {g g₁ g₂ : Goal} (h₁ : DStep g g₁) (h₂ : DStep g g₂) : g₁ = g₂ := by
  cases h₁ with
  | promote hB _ _ =>
      cases h₂ with
      | promote hB' _ _ => rw [hB] at hB'; cases hB'; rfl
  | allTop h =>
      cases h₂ with
      | allTop _ => rfl
      | neg => simp at h
  | neg =>
      cases h₂ with
      | allTop h => simp at h
      | neg => rfl

/-- **Reduction of the first lemma to a simulation**: an encoding of two-counter machines whose
deterministic F<:^D run reaches an axiom exactly on halting, and on whose goals full F<: is
conservative over F<:^D, gives `FsubGhelli.RowingFirstLemma`. -/
theorem rowingFirstLemma_of_simulation
    (h : ∃ enc : CM → ℕ → ℕ → Goal, (∀ M a b, CM.Halts M a b ↔ DRun (enc M a b)) ∧
      ∀ M a b, Sub (enc M a b) → SubD (enc M a b)) :
    RowingFirstLemma := by
  obtain ⟨enc, hrun, hcons⟩ := h
  exact ⟨enc, fun M a b => ⟨fun hh => sub_of_run ((hrun M a b).1 hh),
    fun hs => (hrun M a b).2 (subD_iff_run.1 (hcons M a b hs))⟩⟩

end FsubRowing
