/-
**Route (ii) for expansion postponement in λP2 and coc: a Tait/Girard predicate on derivations**
(tasks `M29-EP-IMPREDICATIVE`, `M29-EP-CUBE-REST`, round 7).

Route (ii) proves normalization of reduction-only derivations (`HasTypeR`) into canonical ones
(`HasTypeNW`) through a predicate "good" defined by recursion on the skeleton of the type, with
Kripke-style typed candidates for the impredicative quantifier `(□,∗)`.  This module builds the
semantic side of that predicate and settles the lemma named in round 2 as the first missing one:

* `PureTypeSystem.RouteII.NormNW P Γ M T` — the base predicate: the judgement normalizes to a
  canonical (`HasTypeNW`) judgement, context, subject and type reducing to it;
* `PureTypeSystem.RouteII.NormNW.abstraction` — **the abstraction case at the base predicate,
  with the product premise handled by the predicate on the product's own derivation**: if the
  body `b : E` and the product `Π C E : s` normalize, so does `λC. b : Π C E` (no measure on the
  product is needed once the product premise carries its own predicate);
  `PureTypeSystem.RouteII.NormNW.product` — the product case;
* `PureTypeSystem.RouteII.Sk` — skeletons of types (type variables in de Bruijn form, arrows, the
  impredicative quantifier), with renaming `Sk.rename` and substitution `Sk.subst`;
* `PureTypeSystem.RouteII.IsCand P C` — **typed candidates**: sets of `HasTypeR` judgements that
  normalize and are closed under reduction of the type;
* `PureTypeSystem.RouteII.Good P s ξ` — the predicate on judgements, by recursion on the skeleton
  `s`, relative to an assignment `ξ` of candidates to type variables: at an arrow, closure under
  application to good arguments in every context extension (Kripke); at the quantifier, closure
  under application to every type argument, for **every** typed candidate interpreting the bound
  variable;
* `PureTypeSystem.RouteII.Good.isCand` — every `Good P s ξ` is a typed candidate (CR1 and closure
  under type reduction);
* `PureTypeSystem.RouteII.Good_rename` and **`PureTypeSystem.RouteII.Good_subst`** — the
  interpretation commutes with renaming and with substitution of skeletons:
  `⟦s[σ]⟧ξ = ⟦s⟧(i ↦ ⟦σ i⟧ξ)`.  `Good_inst` is the instance used at `(□,∗)`:
  `⟦τ[t/X]⟧ξ = ⟦τ⟧(ξ, X ↦ ⟦t⟧ξ)`;
* `PureTypeSystem.RouteII.Good.tyApp` — **the type-application case `(□,∗)` of the fundamental
  lemma**: a good judgement at `∀X. τ`, applied to a type argument `U`, is good at `τ[t/X]` for
  every skeleton `t` (in particular the skeleton of `U`).

The connection with the open lemma:

* `PureTypeSystem.RouteII.SortFundamental P` — the fundamental lemma of route (ii) restricted to
  sort-typed judgements and a single substitution (the instance the product premise of the
  abstraction rule needs);
* `PureTypeSystem.RouteII.hsubstSort_iff_sortFundamental` — it is **equivalent** to `HSubstSort P`,
  hence (round 5) to `HSubstPi P`, and it gives expansion postponement in every corner
  (`cube_expansionPostponement_of_sortFundamental`).

So route (ii) does not fail at `(□,∗)`: the substitution lemma for the interpretation holds (it
is `Good_subst`).  What is not built is the fundamental lemma itself, whose first missing
ingredient is the erasure of λP2 type-level terms to skeletons commuting with substitution (see
`docs/goal/evidence/M29-EP.md`, round 7).
-/

import Start.PTSExpansionPollRepair

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

namespace RouteII

/-! ### The base predicate -/

/-- The judgement `Γ ⊢ M : T` normalizes to a canonical judgement. -/
def NormNW (P : Specification Srt) (Γ : List (Expr Srt)) (M T : Expr Srt) : Prop :=
  ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧ HasTypeNW P Γ' M' T'

/-- Normalizability is invariant under reduction of the type (the canonical type is normal). -/
theorem NormNW.reduceType {P : Specification Srt} {Γ : List (Expr Srt)} {M T T₂ : Expr Srt}
    (h : NormNW P Γ M T) (hr : Reduces T T₂) : NormNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := h
  exact ⟨Γ', M', T', hc, hM, Reduces.to_normal hr hT hNW.normal.2.1, hNW⟩

theorem normal_pi_inv {C E : Expr Srt} (h : Normal (.pi C E)) : Normal C ∧ Normal E :=
  ⟨fun _ hb => h _ (.pi_domain hb), fun _ hb => h _ (.pi_body hb)⟩

/-- **The abstraction case of the fundamental lemma, at the base predicate, with the product
premise handled by the predicate on the product's own derivation**: if the body and the product
normalize, so does the abstraction. -/
theorem NormNW.abstraction {P : Specification Srt} {Γ : List (Expr Srt)} {C E b : Expr Srt}
    {s : Srt} (hb : NormNW P (C :: Γ) b E) (hp : NormNW P Γ (.pi C E) (.sort s)) :
    NormNW P Γ (.lam C b) (.pi C E) := by
  obtain ⟨Γ₁, M₁, T₁, hc₁, hM₁, hT₁, hNW₁⟩ := hp
  rw [Reduces.sort_eq hT₁] at hNW₁
  obtain ⟨C', E', rfl, hC, hE⟩ := Reduces.pi_inv hM₁
  obtain ⟨Γ₂, b', E'', hc₂, hb', hE'', hNW₂⟩ := hb
  have hnP := normal_pi_inv hNW₁.normal.1
  have hE_eq : E'' = E' :=
    (hNW₂.normal.2.1.reduces_eq (Reduces.to_normal hE'' hE hnP.2)).symm ▸ rfl
  have hΓ : Γ₂ = C' :: Γ₁ := by
    refine forall₂_reduces_unique hc₂ (.cons hC hc₁) hNW₂.normal.2.2 ?_
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hnP.1
    · exact hNW₁.normal.2.2 X hX
  subst hE_eq hΓ
  exact ⟨Γ₁, .lam C' b', .pi C' E'', hc₁, Reduces.lam hC hb', Reduces.pi hC hE,
    .abstraction hNW₂ hNW₁⟩

/-- The product case of the fundamental lemma, at the base predicate. -/
theorem NormNW.product {P : Specification Srt} {Γ : List (Expr Srt)} {A B : Expr Srt}
    {s₁ s₂ s₃ : Srt} (hA : NormNW P Γ A (.sort s₁)) (hB : NormNW P (A :: Γ) B (.sort s₂))
    (hr : P.rule s₁ s₂ s₃) : NormNW P Γ (.pi A B) (.sort s₃) := by
  obtain ⟨Γ₁, A', T₁, hc₁, hA', hT₁, hNW₁⟩ := hA
  rw [Reduces.sort_eq hT₁] at hNW₁
  obtain ⟨Γ₂, B', T₂, hc₂, hB', hT₂, hNW₂⟩ := hB
  rw [Reduces.sort_eq hT₂] at hNW₂
  have hΓ : Γ₂ = A' :: Γ₁ := by
    refine forall₂_reduces_unique hc₂ (.cons hA' hc₁) hNW₂.normal.2.2 ?_
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hNW₁.normal.1
    · exact hNW₁.normal.2.2 X hX
  subst hΓ
  exact ⟨Γ₁, .pi A' B', _, hc₁, Reduces.pi hA' hB', .refl, .product hNW₁ hNW₂ hr⟩

/-! ### The fundamental lemma at sort-typed premises is the open lemma -/

/-- **The fundamental lemma of route (ii) at sort-typed judgements, for a single substitution**:
substituting a canonical `N : A` at depth `Δ` into a canonical judgement `M : s` gives a
normalizable judgement.  This is the instance the product premise of the abstraction rule
needs. -/
def SortFundamental (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A : Expr Srt} {Δ Δ' : List (Expr Srt)} {M : Expr Srt} {s : Srt},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) M (.sort s) →
    NormNW P (Δ' ++ Γ) (M.subst (Expr.substAt N Δ.length)) (.sort s)

theorem forall₂_reduces_refl : ∀ Γ : List (Expr Srt), List.Forall₂ Reduces Γ Γ
  | [] => .nil
  | _ :: Γ => .cons .refl (forall₂_reduces_refl Γ)

theorem hsubstSort_of_sortFundamental {P : Specification Srt} (h : SortFundamental P) :
    HSubstSort P := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  obtain ⟨Γ'', M', T', hc', hM', hT', hNW⟩ := h hN hc hv hM
  rw [Reduces.sort_eq hT'] at hNW
  obtain rfl := forall₂_reduces_unique hc' (forall₂_reduces_refl _) hNW.normal.2.2
    hv.normal_entries
  exact ⟨M', hM', hNW⟩

theorem sortFundamental_of_hsubstSort {P : Specification Srt} (h : HSubstSort P) :
    SortFundamental P := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  obtain ⟨M', hM', hNW⟩ := h hN hc hv hM
  exact ⟨_, M', _, forall₂_reduces_refl _, hM', .refl, hNW⟩

/-- **Route (ii) at the product premise is the open lemma**: the fundamental lemma restricted to
sort-typed judgements is equivalent to hereditary substitution into sort-typed premises. -/
theorem hsubstSort_iff_sortFundamental (P : Specification Srt) :
    HSubstSort P ↔ SortFundamental P :=
  ⟨sortFundamental_of_hsubstSort, hsubstSort_of_sortFundamental⟩

/-- Expansion postponement in every corner from the sort-typed fundamental lemma. -/
theorem cube_expansionPostponement_of_sortFundamental (f : CubeFeatures)
    (h : SortFundamental (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f) :=
  cube_expansionPostponement_of_hsubstSort f (hsubstSort_of_sortFundamental h)

/-! ### Skeletons -/

/-- Skeletons of types: type variables (de Bruijn), arrows, and the quantifier `(□,∗)`. -/
inductive Sk where
  | base (i : ℕ)
  | arr (σ τ : Sk)
  | all (τ : Sk)
  deriving DecidableEq

/-- Lifting a renaming of skeleton variables under a binder. -/
def upR (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => r i + 1

def Sk.rename (r : ℕ → ℕ) : Sk → Sk
  | .base i => .base (r i)
  | .arr σ τ => .arr (σ.rename r) (τ.rename r)
  | .all τ => .all (τ.rename (upR r))

/-- Lifting a substitution of skeletons under a binder. -/
def upS (σ : ℕ → Sk) : ℕ → Sk
  | 0 => .base 0
  | i + 1 => (σ i).rename Nat.succ

def Sk.subst (σ : ℕ → Sk) : Sk → Sk
  | .base i => σ i
  | .arr s t => .arr (s.subst σ) (t.subst σ)
  | .all t => .all (t.subst (upS σ))

/-- The substitution of `t` for the variable `0`. -/
def single (t : Sk) : ℕ → Sk
  | 0 => t
  | i + 1 => .base i

/-! ### Typed candidates and the predicate -/

/-- Sets of judgements `Γ ⊢ M : T`. -/
abbrev Cand := List (Expr Srt) → Expr Srt → Expr Srt → Prop

/-- **Typed candidates**: reduction-only judgements that normalize, closed under reduction of
the type. -/
structure IsCand (P : Specification Srt) (C : Cand) : Prop where
  typed : ∀ {Γ M T}, C Γ M T → HasTypeR P Γ M T
  norm : ∀ {Γ M T}, C Γ M T → NormNW P Γ M T
  red : ∀ {Γ M T T'}, C Γ M T → Reduces T T' → C Γ M T'

/-- Extending a candidate assignment by the candidate of a new type variable. -/
def consC (C : Cand) (ξ : ℕ → Cand) : ℕ → Cand
  | 0 => C
  | i + 1 => ξ i

/-- The weakening renaming along a context extension `Γ₀ ++ Γ`. -/
def wk (Γ₀ : List (Expr Srt)) : ℕ → ℕ := fun n => n + Γ₀.length

/-- **The route (ii) predicate**, by recursion on the skeleton, relative to an assignment `ξ` of
typed candidates to type variables. -/
def Good (P : Specification Srt) : Sk → (ℕ → Cand) → Cand
  | .base i, ξ => ξ i
  | .arr σ τ, ξ => fun Γ M T => HasTypeR P Γ M T ∧ NormNW P Γ M T ∧
      ∀ (Γ₀ : List (Expr Srt)) (N A B : Expr Srt),
        Reduces (T.rename (wk Γ₀)) (.pi A B) → Good P σ ξ (Γ₀ ++ Γ) N A →
        Good P τ ξ (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) N) (B.instantiate N)
  | .all τ, ξ => fun Γ M T => HasTypeR P Γ M T ∧ NormNW P Γ M T ∧
      ∀ (Γ₀ : List (Expr Srt)) (U K B : Expr Srt) (C : Cand), IsCand P C →
        Reduces (T.rename (wk Γ₀)) (.pi K B) → HasTypeR P (Γ₀ ++ Γ) U K →
        Good P τ (consC C ξ) (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) U) (B.instantiate U)

/-- **Every interpretation is a typed candidate** (given candidates for the type variables). -/
theorem Good.isCand (P : Specification Srt) :
    ∀ (s : Sk) (ξ : ℕ → Cand), (∀ i, IsCand P (ξ i)) → IsCand P (Good P s ξ)
  | .base i, _, hξ => hξ i
  | .arr _ _, _, _ =>
      { typed := fun h => h.1
        norm := fun h => h.2.1
        red := fun h hr => ⟨h.1.reduces hr, h.2.1.reduceType hr, fun Γ₀ N A B hT hN =>
          h.2.2 Γ₀ N A B ((Reduces.rename hr _).trans hT) hN⟩ }
  | .all _, _, _ =>
      { typed := fun h => h.1
        norm := fun h => h.2.1
        red := fun h hr => ⟨h.1.reduces hr, h.2.1.reduceType hr, fun Γ₀ U K B C hC hT hU =>
          h.2.2 Γ₀ U K B C hC ((Reduces.rename hr _).trans hT) hU⟩ }

/-- Escape (CR1): good judgements normalize. -/
theorem Good.escape {P : Specification Srt} {s : Sk} {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P (ξ i))
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : Good P s ξ Γ M T) : NormNW P Γ M T :=
  (Good.isCand P s ξ hξ).norm h

/-! ### The interpretation commutes with renaming and substitution -/

theorem consC_comp_upR (C : Cand) (ξ : ℕ → Cand) (r : ℕ → ℕ) :
    (fun i => consC C ξ (upR r i)) = consC C (fun i => ξ (r i)) := by
  funext i; cases i <;> rfl

theorem Good_rename (P : Specification Srt) :
    ∀ (s : Sk) (r : ℕ → ℕ) (ξ : ℕ → Cand), Good P (s.rename r) ξ = Good P s (fun i => ξ (r i))
  | .base _, _, _ => rfl
  | .arr σ τ, r, ξ => by
      simp only [Sk.rename, Good, Good_rename P σ r ξ, Good_rename P τ r ξ]
  | .all τ, r, ξ => by
      simp only [Sk.rename, Good]
      funext Γ M T
      congr 1; congr 1
      apply propext
      refine forall_congr' fun Γ₀ => forall_congr' fun U => forall_congr' fun K =>
        forall_congr' fun B => forall_congr' fun C => ?_
      rw [Good_rename P τ (upR r) (consC C ξ), consC_comp_upR]

theorem consC_upS (P : Specification Srt) (C : Cand) (ξ : ℕ → Cand) (σ : ℕ → Sk) :
    (fun i => Good P (upS σ i) (consC C ξ)) = consC C (fun i => Good P (σ i) ξ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [upS, Good_rename]; rfl

/-- **The interpretation commutes with substitution of skeletons**:
`⟦s[σ]⟧ξ = ⟦s⟧(i ↦ ⟦σ i⟧ξ)`.  This is the substitution lemma for the typed-candidate
interpretation, the lemma named in round 2 as the first missing step at `(□,∗)`. -/
theorem Good_subst (P : Specification Srt) :
    ∀ (s : Sk) (σ : ℕ → Sk) (ξ : ℕ → Cand),
      Good P (s.subst σ) ξ = Good P s (fun i => Good P (σ i) ξ)
  | .base _, _, _ => rfl
  | .arr s t, σ, ξ => by
      simp only [Sk.subst, Good, Good_subst P s σ ξ, Good_subst P t σ ξ]
  | .all τ, σ, ξ => by
      simp only [Sk.subst, Good]
      funext Γ M T
      congr 1; congr 1
      apply propext
      refine forall_congr' fun Γ₀ => forall_congr' fun U => forall_congr' fun K =>
        forall_congr' fun B => forall_congr' fun C => ?_
      rw [Good_subst P τ (upS σ) (consC C ξ), consC_upS]

/-- The instance used at `(□,∗)`: `⟦τ[t/X]⟧ξ = ⟦τ⟧(ξ, X ↦ ⟦t⟧ξ)`. -/
theorem Good_inst (P : Specification Srt) (τ t : Sk) (ξ : ℕ → Cand) :
    Good P (τ.subst (single t)) ξ = Good P τ (consC (Good P t ξ) ξ) := by
  rw [Good_subst]
  congr 1
  funext i
  cases i <;> rfl

/-- **The type-application case `(□,∗)` of the fundamental lemma**: a good judgement at the
skeleton `∀X. τ`, whose type reduces to `Π K. B`, applied to a type argument `U : K`, is good at
`τ[t/X]` for every skeleton `t` (in particular the skeleton of `U`). -/
theorem Good.tyApp {P : Specification Srt} {τ : Sk} {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P (ξ i))
    (t : Sk) {Γ : List (Expr Srt)} {M T U K B : Expr Srt} (h : Good P (.all τ) ξ Γ M T)
    (hT : Reduces T (.pi K B)) (hU : HasTypeR P Γ U K) :
    Good P (τ.subst (single t)) ξ Γ (.app M U) (B.instantiate U) := by
  rw [Good_inst]
  have hw : wk ([] : List (Expr Srt)) = id := rfl
  have := h.2.2 [] U K B (Good P t ξ) (Good.isCand P t ξ hξ) (by rw [hw, Expr.rename_id]; exact hT)
    (by simpa using hU)
  rw [hw, Expr.rename_id] at this
  simpa using this

/-- The object-application case: a good judgement at an arrow skeleton, applied to a good
argument, is good at the codomain. -/
theorem Good.app {P : Specification Srt} {σ τ : Sk} {ξ : ℕ → Cand}
    {Γ : List (Expr Srt)} {M T N A B : Expr Srt} (h : Good P (.arr σ τ) ξ Γ M T)
    (hT : Reduces T (.pi A B)) (hN : Good P σ ξ Γ N A) :
    Good P τ ξ Γ (.app M N) (B.instantiate N) := by
  have hw : wk ([] : List (Expr Srt)) = id := rfl
  have := h.2.2 [] N A B (by rw [hw, Expr.rename_id]; exact hT) (by simpa using hN)
  rw [hw, Expr.rename_id] at this
  simpa using this

end RouteII

end PureTypeSystem
