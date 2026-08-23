/-
Denotational semantics of the untyped lambda calculus in Scott's graph model.

`Start/GraphModel.lean` builds the reflexive object `D = Set Tok` (the Scott-continuous
function space is a retract of `D`).  This file uses it to interpret lambda terms and proves
that the interpretation is a **model of the beta calculus**:

* `GraphModel.denot`         — the interpretation `⟦t⟧ρ : D` of a de Bruijn term in an environment;
* `GraphModel.denot_mono`, `GraphModel.denot_fin`, `GraphModel.cont_denot_cons` — the semantics
  is monotone and Scott continuous in every variable;
* `GraphModel.denot_lift`, `GraphModel.denot_subst` — the lifting and substitution lemmas;
* `GraphModel.denot_beta`    — the semantic beta rule `⟦(λt) s⟧ρ = ⟦t[s]⟧ρ`;
* `GraphModel.denot_step`, `GraphModel.denot_reduces`, `GraphModel.denot_conv` — **soundness**:
  beta reduction, and hence beta conversion, preserves denotations;
* `GraphModel.denot_omega`   — `⟦Ω⟧ρ = ∅`, proved by an infinite-descent argument on tokens;
* `GraphModel.not_conv_omega_I` — consequently `Ω` is not convertible to `I`, a *semantic* proof
  of the consistency of the beta calculus that does not use confluence.

Boundary: only beta is modelled (the graph model is not extensional, so it does not validate
eta), and no completeness/adequacy statement is proved.
-/

import Start.GraphModel
import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GraphModel

/-- Environments assign a value of the domain to every de Bruijn index. -/
abbrev Env : Type := ℕ → D

/-- Extend an environment with a new value for index `0`. -/
def cons (X : D) (ρ : Env) : Env := fun i =>
  match i with
  | 0 => X
  | (j + 1) => ρ j

@[simp] theorem cons_zero (X : D) (ρ : Env) : cons X ρ 0 = X := rfl
@[simp] theorem cons_succ (X : D) (ρ : Env) (j : ℕ) : cons X ρ (j + 1) = ρ j := rfl

theorem cons_mono {X X' : D} {ρ ρ' : Env} (hX : X ⊆ X') (hρ : ∀ i, ρ i ⊆ ρ' i) :
    ∀ i, cons X ρ i ⊆ cons X' ρ' i := by
  intro i
  cases i with
  | zero => exact hX
  | succ j => exact hρ j

/-- The finite environment given by a family of lists of tokens. -/
def approx (σ : ℕ → List Tok) : Env := fun i => lset (σ i)

@[simp] theorem approx_apply (σ : ℕ → List Tok) (i : ℕ) : approx σ i = lset (σ i) := rfl

/-- The interpretation of a lambda term in an environment. -/
def denot : Lambda → Env → D
  | Lambda.var i, ρ => ρ i
  | Lambda.app s t, ρ => appD (denot s ρ) (denot t ρ)
  | Lambda.lam s, ρ => graph (fun X => denot s (cons X ρ))

@[simp] theorem denot_var (i : ℕ) (ρ : Env) : denot (Lambda.var i) ρ = ρ i := rfl
@[simp] theorem denot_app (s t : Lambda) (ρ : Env) :
    denot (Lambda.app s t) ρ = appD (denot s ρ) (denot t ρ) := rfl
@[simp] theorem denot_lam (s : Lambda) (ρ : Env) :
    denot (Lambda.lam s) ρ = graph (fun X => denot s (cons X ρ)) := rfl

------------------------------------------------------------------------
-- Monotonicity and continuity
------------------------------------------------------------------------

theorem denot_mono (t : Lambda) {ρ ρ' : Env} (h : ∀ i, ρ i ⊆ ρ' i) :
    denot t ρ ⊆ denot t ρ' := by
  induction t generalizing ρ ρ' with
  | var i => exact h i
  | app s u ihs ihu => exact appD_mono (ihs h) (ihu h)
  | lam s ih =>
      refine graph_mono ?_
      intro X
      exact ih (cons_mono (le_refl X) h)

/-- Every token in the denotation of `t` is already produced by a finite part of the
environment: the semantics is continuous in all variables simultaneously. -/
theorem denot_fin : ∀ (t : Lambda) (ρ : Env) (b : Tok), b ∈ denot t ρ →
    ∃ σ : ℕ → List Tok, (∀ i, lset (σ i) ⊆ ρ i) ∧ b ∈ denot t (approx σ) := by
  intro t
  induction t with
  | var i =>
      intro ρ b hb
      refine ⟨fun j => if j = i then [b] else [], ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst hj
          simpa [lset] using hb
        · simp [hj]
      · simp [lset]
  | app s u ihs ihu =>
      intro ρ b hb
      obtain ⟨a, ha, harr⟩ := hb
      obtain ⟨σ₁, hσ₁, h₁⟩ := ihs ρ _ harr
      have hlist : ∀ (c : List Tok), lset c ⊆ denot u ρ →
          ∃ σ : ℕ → List Tok, (∀ i, lset (σ i) ⊆ ρ i) ∧ lset c ⊆ denot u (approx σ) := by
        intro c
        induction c with
        | nil => intro _; exact ⟨fun _ => [], by simp, by simp⟩
        | cons x c ih =>
            intro hsub
            have hx : x ∈ denot u ρ := hsub (by simp)
            have hc : lset c ⊆ denot u ρ := by
              intro y hy
              exact hsub (by simp only [mem_lset, List.mem_cons]; exact Or.inr hy)
            obtain ⟨τ₁, hτ₁, hx'⟩ := ihu ρ x hx
            obtain ⟨τ₂, hτ₂, hc'⟩ := ih hc
            refine ⟨fun i => τ₁ i ++ τ₂ i, ?_, ?_⟩
            · intro i
              rw [lset_append]
              exact Set.union_subset (hτ₁ i) (hτ₂ i)
            · intro y hy
              simp only [mem_lset, List.mem_cons] at hy
              have hle : ∀ i, approx τ₁ i ⊆ approx (fun i => τ₁ i ++ τ₂ i) i := by
                intro i
                simp only [approx_apply, lset_append]
                exact Set.subset_union_left
              have hle' : ∀ i, approx τ₂ i ⊆ approx (fun i => τ₁ i ++ τ₂ i) i := by
                intro i
                simp only [approx_apply, lset_append]
                exact Set.subset_union_right
              rcases hy with rfl | hy
              · exact denot_mono u hle hx'
              · exact denot_mono u hle' (hc' hy)
      obtain ⟨σ₂, hσ₂, h₂⟩ := hlist a ha
      refine ⟨fun i => σ₁ i ++ σ₂ i, ?_, ?_⟩
      · intro i
        rw [lset_append]
        exact Set.union_subset (hσ₁ i) (hσ₂ i)
      · have hle : ∀ i, approx σ₁ i ⊆ approx (fun i => σ₁ i ++ σ₂ i) i := by
          intro i
          simp only [approx_apply, lset_append]
          exact Set.subset_union_left
        have hle' : ∀ i, approx σ₂ i ⊆ approx (fun i => σ₁ i ++ σ₂ i) i := by
          intro i
          simp only [approx_apply, lset_append]
          exact Set.subset_union_right
        exact ⟨a, h₂.trans (denot_mono u hle'), denot_mono s hle h₁⟩
  | lam s ih =>
      intro ρ b hb
      obtain ⟨a, c, rfl, hc⟩ := hb
      obtain ⟨σ, hσ, hc'⟩ := ih (cons (lset a) ρ) c hc
      refine ⟨fun i => σ (i + 1), ?_, ?_⟩
      · intro i
        exact hσ (i + 1)
      · refine ⟨a, c, rfl, ?_⟩
        refine denot_mono s ?_ hc'
        intro i
        cases i with
        | zero => exact hσ 0
        | succ j => exact le_refl _

/-- Continuity of the semantics in the variable bound by a lambda. -/
theorem cont_denot_cons (t : Lambda) (ρ : Env) : Cont (fun X => denot t (cons X ρ)) := by
  intro Y b
  constructor
  · intro hb
    obtain ⟨σ, hσ, hb'⟩ := denot_fin t (cons Y ρ) b hb
    refine ⟨σ 0, hσ 0, ?_⟩
    refine denot_mono t ?_ hb'
    intro i
    cases i with
    | zero => exact le_refl _
    | succ j => exact hσ (j + 1)
  · rintro ⟨a, ha, hb⟩
    exact denot_mono t (cons_mono ha (fun _ => le_refl _)) hb

------------------------------------------------------------------------
-- Lifting and substitution
------------------------------------------------------------------------

theorem denot_lift (t : Lambda) (n k : ℕ) (ρ : Env) :
    denot (Lambda.lift n k t) ρ = denot t (fun i => if i < k then ρ i else ρ (i + n)) := by
  induction t generalizing k ρ with
  | var y =>
      by_cases hy : y < k <;> simp [Lambda.lift, hy]
  | app s u ihs ihu => simp [Lambda.lift, ihs, ihu]
  | lam s ih =>
      simp only [Lambda.lift, denot_lam]
      refine graph_congr ?_
      intro X
      rw [ih]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j < k
          · have : j + 1 < k + 1 := by omega
            simp [this, hj]
          · have h1 : ¬ (j + 1 < k + 1) := by omega
            have h2 : j + 1 + n = (j + n) + 1 := by omega
            simp [h1, hj, h2]

theorem denot_subst (t : Lambda) : ∀ (s : Lambda) (x : ℕ) (ρ : Env),
    denot (Lambda.subst s x t) ρ =
      denot t (fun i => if i = x then denot s ρ else if x < i then ρ (i - 1) else ρ i) := by
  induction t with
  | var y =>
      intro s x ρ
      by_cases h1 : y = x
      · simp [Lambda.subst, h1]
      · by_cases h2 : y > x
        · simp [Lambda.subst, h1, h2]
        · simp [Lambda.subst, h1, h2]
  | app u v ihu ihv =>
      intro s x ρ
      simp [Lambda.subst, ihu, ihv]
  | lam u ih =>
      intro s x ρ
      simp only [Lambda.subst, denot_lam]
      refine graph_congr ?_
      intro X
      rw [ih]
      have hs : denot (Lambda.lift 1 0 s) (cons X ρ) = denot s ρ := by
        rw [denot_lift]
        congr 1
      rw [hs]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases h1 : j = x
          · subst h1
            simp
          · by_cases h2 : x < j
            · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
              have e2 : x + 1 < j' + 1 + 1 := by omega
              have e3 : j' + 1 + 1 - 1 = j' + 1 := by omega
              simp [e2, e3, h1, h2]
            · have e2 : ¬ (x + 1 < j + 1) := by omega
              simp [e2, h1, h2]

/-- The semantic beta rule. -/
theorem denot_beta (t s : Lambda) (ρ : Env) :
    denot (Lambda.app (Lambda.lam t) s) ρ = denot (Lambda.subst s 0 t) ρ := by
  rw [denot_app, denot_lam, appD_graph_apply (cont_denot_cons t ρ), denot_subst]
  congr 1
  funext i
  cases i with
  | zero => simp
  | succ j => simp

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

/-- **Soundness**: one step of beta reduction preserves the denotation. -/
theorem denot_step {t t' : Lambda} (h : Lambda.step t t') (ρ : Env) :
    denot t ρ = denot t' ρ := by
  induction h generalizing ρ with
  | beta t₁ t₂ => exact denot_beta t₁ t₂ ρ
  | app_left t₁ t₁' t₂ _ ih => simp [ih ρ]
  | app_right t₁ t₂ t₂' _ ih => simp [ih ρ]
  | lam t t' _ ih =>
      simp only [denot_lam]
      exact graph_congr fun X => ih (cons X ρ)

theorem denot_reduces {t t' : Lambda} (h : Lambda.reduces t t') (ρ : Env) :
    denot t ρ = denot t' ρ := by
  induction h with
  | refl t => rfl
  | step t₁ t₂ t₃ hs _ ih => rw [denot_step hs ρ]; exact ih

/-- Convertible terms have the same denotation. -/
theorem denot_conv {s t : Lambda} (h : Lambda.Conv s t) (ρ : Env) : denot s ρ = denot t ρ := by
  obtain ⟨u, hs, ht⟩ := h
  rw [denot_reduces hs ρ, denot_reduces ht ρ]

------------------------------------------------------------------------
-- The denotation of Ω is empty
------------------------------------------------------------------------

/-- The syntactic size of a token. -/
def Tok.size : Tok → ℕ
  | Tok.atom _ => 1
  | Tok.arrow a b => 1 + (a.map Tok.size).sum + Tok.size b

/-- The largest size of a token in a list. -/
def maxSize : List Tok → ℕ
  | [] => 0
  | (x :: a) => max (Tok.size x) (maxSize a)

theorem size_pos (t : Tok) : 0 < Tok.size t := by
  cases t with
  | atom n => simp [Tok.size]
  | arrow a b => simp [Tok.size]

theorem maxSize_le_sum (a : List Tok) : maxSize a ≤ (a.map Tok.size).sum := by
  induction a with
  | nil => simp [maxSize]
  | cons x a ih =>
      simp only [maxSize, List.map_cons, List.sum_cons]
      have : 0 ≤ Tok.size x := Nat.zero_le _
      omega

theorem size_le_maxSize {x : Tok} {a : List Tok} (h : x ∈ a) : Tok.size x ≤ maxSize a := by
  induction a with
  | nil => cases h
  | cons y a ih =>
      simp only [List.mem_cons] at h
      simp only [maxSize]
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- The interpretation of the self-application term `λx. x x`. -/
def selfAppD : D := graph (fun X => appD X X)

theorem maxSize_lt_of_arrow (a : List Tok) (b : Tok) :
    maxSize a < Tok.size (Tok.arrow a b) := by
  have h1 := maxSize_le_sum a
  have h2 := size_pos b
  simp only [Tok.size]
  omega

/-- Infinite descent: no arrow token whose input requirement lies in `selfAppD` can itself lie
in `selfAppD`. -/
theorem arrow_notMem_selfAppD :
    ∀ (n : ℕ) (a : List Tok), maxSize a ≤ n → lset a ⊆ selfAppD →
      ∀ b : Tok, Tok.arrow a b ∉ selfAppD := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro a ha hsub b hb
      have hb' : b ∈ appD (lset a) (lset a) := (mem_graph (f := fun X => appD X X)).1 hb
      obtain ⟨a', ha', harr⟩ := hb'
      have harrD : Tok.arrow a' b ∈ selfAppD := hsub harr
      have hsub' : lset a' ⊆ selfAppD := ha'.trans hsub
      have hlt : maxSize a' < maxSize a := by
        have h1 : maxSize a' < Tok.size (Tok.arrow a' b) := maxSize_lt_of_arrow a' b
        have h2 : Tok.size (Tok.arrow a' b) ≤ maxSize a := size_le_maxSize (mem_lset.mp harr)
        omega
      exact ih (maxSize a') (by omega) a' (le_refl _) hsub' b harrD

/-- The self-application term applied to itself denotes the empty set. -/
theorem appD_selfAppD : appD selfAppD selfAppD = (∅ : D) := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, hb⟩
  exact arrow_notMem_selfAppD (maxSize a) a (le_refl _) ha b hb

@[simp] theorem denot_selfApp (ρ : Env) :
    denot (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0))) ρ = selfAppD := by
  simp [selfAppD]

/-- `⟦Ω⟧ρ = ∅`: the always-diverging term denotes the bottom element. -/
theorem denot_omega (ρ : Env) : denot Lambda.omega ρ = (∅ : D) := by
  simp only [Lambda.omega, denot_app, denot_selfApp]
  exact appD_selfAppD

/-- `⟦I⟧ρ` is not empty. -/
theorem denot_I_ne_empty (ρ : Env) : denot Lambda.I ρ ≠ (∅ : D) := by
  intro h
  have : Tok.arrow [Tok.atom 0] (Tok.atom 0) ∈ denot Lambda.I ρ := by
    simp only [Lambda.I, denot_lam, denot_var]
    exact mem_graph.2 (by simp [lset])
  rw [h] at this
  exact this

/-- **Semantic consistency of the beta calculus**: `Ω` is not convertible to `I`.  The proof
goes through the model and does not use confluence. -/
theorem not_conv_omega_I : ¬ Lambda.Conv Lambda.omega Lambda.I := by
  intro h
  have := denot_conv h (fun _ => (∅ : D))
  rw [denot_omega] at this
  exact denot_I_ne_empty (fun _ => (∅ : D)) this.symm

/-- The beta calculus is consistent: some pair of terms is not convertible. -/
theorem exists_not_conv : ∃ s t : Lambda, ¬ Lambda.Conv s t :=
  ⟨Lambda.omega, Lambda.I, not_conv_omega_I⟩

end GraphModel
