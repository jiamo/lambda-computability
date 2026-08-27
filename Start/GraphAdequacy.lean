/-
Adequacy of Scott's graph model for the untyped lambda calculus.

`Start/GraphModelSemantics.lean` interprets the untyped calculus in the graph model and proves
that interpretation *sound*: β-conversion preserves denotations and `Ω` denotes the least element
`∅`.  Nothing there rules out the possibility that other, computationally meaningful, terms also
denote `∅`.  This file proves the converse — **adequacy** — and hence pins the denotation of the
least element down exactly:

* `GraphModel.hasHnf_of_mem_denot` — if the denotation of a term contains any token at all, in
  any environment whatsoever, then the term has a **head normal form**;
* `GraphModel.exists_denot_ne_empty_of_hasHnf` — conversely a term with a head normal form has a
  nonempty denotation in a suitable environment, and `GraphModel.denot_ne_empty_of_hasHnf` gives
  it in *every* environment for a closed term;
* `GraphModel.denot_ne_empty_iff_hasHnf` — so for a closed term `⟦t⟧ρ ≠ ∅ ↔ t has a head normal
  form`: the terms denoting the least element are exactly the head-divergent ones;
* `GraphModel.hasHnf_of_solvable` — every solvable term has a head normal form, obtained from
  adequacy and soundness;
* `GraphModel.denot_eq_empty_of_not_solvable`, `GraphModel.not_solvable_of_denot_eq_empty` — the
  resulting relation between the least element and unsolvability.

The proof of adequacy is the classical computability (logical-relations) argument, carried out
directly on the tokens of the model.  `GraphModel.RealAux b t` says that the term `t` *realizes*
the token `b`: it has a head normal form, and — if `b` is a step function `a ⇒ c` — applying `t`
to any term realizing all of `a` yields a term realizing `c`.  The recursion is on the size of
the token.  Realizers are quantified over all liftings of a term, which is what makes the
relation stable under the shift that de Bruijn parallel substitution performs at a binder.

The fundamental lemma `GraphModel.realAux_substEnv` says that if an environment of terms realizes
an environment of values then every token of `⟦t⟧ρ` is realized by the corresponding substitution
instance of `t`; taking the identity substitution gives adequacy.
-/

import Start.GraphModelSemantics
import Start.HeadNormal
import Start.ParallelSubst
import Start.Solvability

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Lifting a neutral term gives a neutral term. -/
theorem Neutral.lift {t : Lambda} (h : Neutral t) (n k : ℕ) : Neutral (Lambda.lift n k t) := by
  induction h with
  | var m =>
      by_cases hm : m < k <;> simp only [Lambda.lift, hm, if_true, if_false] <;>
        exact Neutral.var _
  | app N _ ih => exact Neutral.app _ ih

end Lambda

namespace GraphModel

open Lambda

------------------------------------------------------------------------
-- Realizability
------------------------------------------------------------------------

/-- `RealAux b t`: the term `t` *realizes* the token `b`.  Realizing an atom is just having a
head normal form; realizing a step function `a ⇒ c` means in addition that applying `t` to any
term realizing every token of `a` — in every lifting — realizes `c`. -/
def RealAux : Tok → Lambda → Prop
  | Tok.atom _, t => Lambda.HasHnf t
  | Tok.arrow a c, t =>
      Lambda.HasHnf t ∧
        ∀ s : Lambda, (∀ x ∈ a, ∀ k : ℕ, RealAux x (Lambda.lift k 0 s)) →
          RealAux c (Lambda.app t s)
  termination_by b _ => b.size
  decreasing_by
    · exact lt_of_le_of_lt (size_le_maxSize (by assumption)) (maxSize_lt_of_arrow a c)
    · simp only [Tok.size]; omega

/-- A term realizes a token *stably* when all of its liftings realize it.  This is the form the
fundamental lemma needs, because parallel substitution shifts the environment at a binder. -/
def Real (b : Tok) (t : Lambda) : Prop := ∀ k : ℕ, RealAux b (Lambda.lift k 0 t)

theorem RealAux.hasHnf {b : Tok} {t : Lambda} (h : RealAux b t) : Lambda.HasHnf t := by
  cases b with
  | atom n => rwa [RealAux] at h
  | arrow a c => rw [RealAux] at h; exact h.1

theorem Real.realAux {b : Tok} {t : Lambda} (h : Real b t) : RealAux b t := by
  simpa [Lambda.lift_zero] using h 0

theorem Real.hasHnf {b : Tok} {t : Lambda} (h : Real b t) : Lambda.HasHnf t :=
  h.realAux.hasHnf

/-- Realizability is stable under the lifting that a binder performs. -/
theorem Real.lift {b : Tok} {t : Lambda} (h : Real b t) (n : ℕ) :
    Real b (Lambda.lift n 0 t) := by
  intro k
  rw [← Lambda.lift_add]
  exact h (k + n)

/-- Realizability is inherited backwards along a reduction. -/
theorem realAux_expand : ∀ {b : Tok} {t u : Lambda}, Lambda.reduces t u → RealAux b u →
    RealAux b t := by
  have key : ∀ (n : ℕ) (b : Tok), b.size ≤ n → ∀ (t u : Lambda), Lambda.reduces t u →
      RealAux b u → RealAux b t := by
    intro n
    induction n with
    | zero =>
        intro b hb
        exact absurd hb (Nat.not_le.mpr (size_pos b))
    | succ n ih =>
        intro b hb t u hr h
        cases b with
        | atom m =>
            rw [RealAux] at h ⊢
            exact Lambda.HasHnf.of_reduces hr h
        | arrow a c =>
            rw [RealAux] at h ⊢
            refine ⟨Lambda.HasHnf.of_reduces hr h.1, ?_⟩
            intro s hs
            have hcn : Tok.size c ≤ n := by
              have hlt : Tok.size c < Tok.size (Tok.arrow a c) := by
                simp only [Tok.size]; omega
              omega
            exact ih c hcn _ _ (Lambda.reduces_app_left hr) (h.2 s hs)
  intro b t u hr h
  exact key b.size b le_rfl t u hr h

/-- Every neutral term realizes every token: neutral terms are head normal forms and stay
neutral under application. -/
theorem realAux_of_neutral : ∀ (b : Tok) {t : Lambda}, Neutral t → RealAux b t := by
  have key : ∀ (n : ℕ) (b : Tok), b.size ≤ n → ∀ (t : Lambda), Neutral t → RealAux b t := by
    intro n
    induction n with
    | zero =>
        intro b hb
        exact absurd hb (Nat.not_le.mpr (size_pos b))
    | succ n ih =>
        intro b hb t hn
        cases b with
        | atom m =>
            rw [RealAux]
            exact Lambda.hasHnf_of_neutral hn
        | arrow a c =>
            rw [RealAux]
            refine ⟨Lambda.hasHnf_of_neutral hn, ?_⟩
            intro s _
            have hcn : Tok.size c ≤ n := by
              have hlt : Tok.size c < Tok.size (Tok.arrow a c) := by
                simp only [Tok.size]; omega
              omega
            exact ih c hcn _ (Neutral.app s hn)
  intro b t hn
  exact key b.size b le_rfl t hn

theorem real_of_neutral (b : Tok) {t : Lambda} (h : Neutral t) : Real b t :=
  fun k => realAux_of_neutral b (h.lift k 0)

theorem real_var (b : Tok) (n : ℕ) : Real b (Lambda.var n) :=
  real_of_neutral b (Neutral.var n)

------------------------------------------------------------------------
-- The fundamental lemma
------------------------------------------------------------------------

/-- An environment of terms realizes an environment of values. -/
def Realizes (u : ℕ → Lambda) (ρ : Env) : Prop := ∀ i, ∀ x ∈ ρ i, Real x (u i)

theorem Realizes.lift {u : ℕ → Lambda} {ρ : Env} (h : Realizes u ρ) (n : ℕ) :
    Realizes (fun i => Lambda.lift n 0 (u i)) ρ :=
  fun i x hx => (h i x hx).lift n

theorem realizes_var (ρ : Env) : Realizes (fun i => Lambda.var i) ρ :=
  fun i x _ => real_var x i

theorem Realizes.envCons {u : ℕ → Lambda} {ρ : Env} (h : Realizes u ρ) (a : List Tok) :
    Realizes (Lambda.envCons u) (cons (lset a) ρ) := by
  intro i
  cases i with
  | zero => intro x _; exact real_var x 0
  | succ j => intro x hx; exact (h j x hx).lift 1

theorem Realizes.envScons {u : ℕ → Lambda} {ρ : Env} (h : Realizes u ρ) {a : List Tok}
    {s : Lambda} (hs : ∀ x ∈ a, Real x s) : Realizes (Lambda.envScons s u) (cons (lset a) ρ) := by
  intro i
  cases i with
  | zero => intro x hx; exact hs x hx
  | succ j => intro x hx; exact h j x hx

/-- **The fundamental lemma.**  If the terms of `u` realize the values of `ρ`, then every token
of `⟦t⟧ρ` is realized by the substitution instance `t[u]`. -/
theorem realAux_substEnv : ∀ (t : Lambda) (ρ : Env) (u : ℕ → Lambda), Realizes u ρ →
    ∀ b ∈ denot t ρ, RealAux b (Lambda.substEnv u t) := by
  intro t
  induction t with
  | var i =>
      intro ρ u hu b hb
      exact (hu i b hb).realAux
  | app s w ihs ihw =>
      intro ρ u hu b hb
      obtain ⟨a, ha, harr⟩ := hb
      have hs := ihs ρ u hu (Tok.arrow a b) harr
      rw [RealAux] at hs
      refine hs.2 (Lambda.substEnv u w) ?_
      intro x hx k
      have hxd : x ∈ denot w ρ := ha (mem_lset.2 hx)
      rw [Lambda.lift_substEnv]
      exact ihw ρ (fun i => Lambda.lift k 0 (u i)) (hu.lift k) x hxd
  | lam t ih =>
      intro ρ u hu b hb
      obtain ⟨a, c, rfl, hc⟩ := hb
      rw [RealAux]
      constructor
      · exact Lambda.hasHnf_lam
          (ih (cons (lset a) ρ) (Lambda.envCons u) (hu.envCons a) c hc).hasHnf
      · intro s hs
        have hstep : Lambda.reduces
            (Lambda.app (Lambda.lam (Lambda.substEnv (Lambda.envCons u) t)) s)
            (Lambda.subst s 0 (Lambda.substEnv (Lambda.envCons u) t)) :=
          Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)
        refine realAux_expand hstep ?_
        rw [Lambda.subst_zero_substEnv]
        exact ih (cons (lset a) ρ) (Lambda.envScons s u)
          (hu.envScons (fun x hx k => hs x hx k)) c hc

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

/-- **Adequacy.**  A term whose denotation contains a token — in any environment at all — has a
head normal form. -/
theorem hasHnf_of_mem_denot {t : Lambda} {ρ : Env} {b : Tok} (hb : b ∈ denot t ρ) :
    Lambda.HasHnf t := by
  have h := realAux_substEnv t ρ (fun i => Lambda.var i) (realizes_var ρ) b hb
  rw [Lambda.substEnv_var_id] at h
  exact h.hasHnf

theorem hasHnf_of_denot_ne_empty {t : Lambda} {ρ : Env} (h : denot t ρ ≠ (∅ : D)) :
    Lambda.HasHnf t := by
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 h
  exact hasHnf_of_mem_denot hb

/-- A term with no head normal form denotes the least element in every environment. -/
theorem denot_eq_empty_of_not_hasHnf {t : Lambda} (h : ¬ Lambda.HasHnf t) (ρ : Env) :
    denot t ρ = (∅ : D) := by
  by_contra hc
  exact h (hasHnf_of_denot_ne_empty hc)

------------------------------------------------------------------------
-- The converse: head normal forms have a nonempty denotation
------------------------------------------------------------------------

/-- Every token is in the denotation of a neutral term, for a suitable environment. -/
theorem exists_env_mem_denot_of_neutral : ∀ {t : Lambda}, Neutral t → ∀ c : Tok,
    ∃ ρ : Env, c ∈ denot t ρ := by
  intro t h
  induction h with
  | var n =>
      intro c
      exact ⟨fun i => if i = n then {c} else ∅, by simp [denot]⟩
  | app N _ ih =>
      intro c
      obtain ⟨ρ, hρ⟩ := ih (Tok.arrow [] c)
      exact ⟨ρ, ⟨[], by simp, hρ⟩⟩

/-- A head normal form has a nonempty denotation in a suitable environment. -/
theorem exists_env_denot_ne_empty_of_isHnf : ∀ {t : Lambda}, Lambda.IsHnf t →
    ∃ ρ : Env, denot t ρ ≠ (∅ : D) := by
  intro t h
  induction h with
  | neutral hn =>
      obtain ⟨ρ, hρ⟩ := exists_env_mem_denot_of_neutral hn (Tok.atom 0)
      exact ⟨ρ, Set.nonempty_iff_ne_empty.1 ⟨_, hρ⟩⟩
  | @lam u _ ih =>
      obtain ⟨ρ, hρ⟩ := ih
      obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 hρ
      obtain ⟨σ, _, hc'⟩ := denot_fin u ρ c hc
      refine ⟨fun i => lset (σ (i + 1)), Set.nonempty_iff_ne_empty.1 ⟨Tok.arrow (σ 0) c, ?_⟩⟩
      refine ⟨σ 0, c, rfl, ?_⟩
      have henv : cons (lset (σ 0)) (fun i => lset (σ (i + 1))) = approx σ := by
        funext i
        cases i with
        | zero => rfl
        | succ j => rfl
      change c ∈ denot u (cons (lset (σ 0)) fun i => lset (σ (i + 1)))
      rw [henv]
      exact hc'

theorem exists_denot_ne_empty_of_hasHnf {t : Lambda} (h : Lambda.HasHnf t) :
    ∃ ρ : Env, denot t ρ ≠ (∅ : D) := by
  obtain ⟨u, hu, hhnf⟩ := h
  obtain ⟨ρ, hρ⟩ := exists_env_denot_ne_empty_of_isHnf hhnf
  exact ⟨ρ, by rw [denot_reduces hu ρ]; exact hρ⟩

/-- The theory is not vacuous in either direction: `Ω` has no head normal form, because its
denotation is the least element in every environment. -/
theorem not_hasHnf_omega : ¬ Lambda.HasHnf Lambda.omega := by
  intro h
  obtain ⟨ρ, hρ⟩ := exists_denot_ne_empty_of_hasHnf h
  exact hρ (denot_omega ρ)

------------------------------------------------------------------------
-- Closed terms: the denotation does not depend on the environment
------------------------------------------------------------------------

/-- The denotation only depends on the values of the free variables. -/
theorem denot_congr : ∀ (t : Lambda) (k : ℕ) (ρ ρ' : Env), Lambda.freeBelow k t →
    (∀ i, i < k → ρ i = ρ' i) → denot t ρ = denot t ρ' := by
  intro t
  induction t with
  | var n => intro k ρ ρ' h hρ; exact hρ n h
  | app a b iha ihb =>
      intro k ρ ρ' h hρ
      simp only [denot_app, iha k ρ ρ' h.1 hρ, ihb k ρ ρ' h.2 hρ]
  | lam t ih =>
      intro k ρ ρ' h hρ
      refine graph_congr fun X => ih (k + 1) (cons X ρ) (cons X ρ') h ?_
      intro i hi
      cases i with
      | zero => rfl
      | succ j => exact hρ j (by omega)

theorem denot_closed_congr {t : Lambda} (h : Lambda.IsClosed t) (ρ ρ' : Env) :
    denot t ρ = denot t ρ' :=
  denot_congr t 0 ρ ρ' (Lambda.freeBelow_zero_of_isClosed h) (by intro i hi; omega)

/-- For a closed term with a head normal form the denotation is nonempty in *every*
environment. -/
theorem denot_ne_empty_of_hasHnf {t : Lambda} (hcl : Lambda.IsClosed t) (h : Lambda.HasHnf t)
    (ρ : Env) : denot t ρ ≠ (∅ : D) := by
  obtain ⟨ρ', hρ'⟩ := exists_denot_ne_empty_of_hasHnf h
  rw [denot_closed_congr hcl ρ ρ']
  exact hρ'

/-- **The characterization of the least element.**  A closed term denotes `∅` exactly when it has
no head normal form. -/
theorem denot_ne_empty_iff_hasHnf {t : Lambda} (hcl : Lambda.IsClosed t) (ρ : Env) :
    denot t ρ ≠ (∅ : D) ↔ Lambda.HasHnf t :=
  ⟨fun h => hasHnf_of_denot_ne_empty h, fun h => denot_ne_empty_of_hasHnf hcl h ρ⟩

------------------------------------------------------------------------
-- Solvability
------------------------------------------------------------------------

/-- Applying a term of empty denotation to arguments cannot produce anything. -/
theorem denot_appList_eq_empty {t : Lambda} {ρ : Env} (h : denot t ρ = (∅ : D)) :
    ∀ args : List Lambda, denot (Lambda.appList t args) ρ = (∅ : D) := by
  intro args
  induction args generalizing t with
  | nil => exact h
  | cons s rest ih =>
      refine ih ?_
      rw [denot_app, h]
      ext b
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, -, hb⟩
      exact hb

/-- **Every solvable term has a head normal form**, by adequacy: a solvable term can be driven to
the identity, whose denotation is not the least element. -/
theorem hasHnf_of_solvable {t : Lambda} (h : Lambda.Solvable t) : Lambda.HasHnf t := by
  obtain ⟨args, -, hconv⟩ := h
  by_contra hc
  have hempty : denot t (fun _ => (∅ : D)) = (∅ : D) :=
    denot_eq_empty_of_not_hasHnf hc _
  have hI : denot (Lambda.appList t args) (fun _ => (∅ : D)) = denot Lambda.I (fun _ => ∅) :=
    denot_conv hconv _
  rw [denot_appList_eq_empty hempty args] at hI
  exact denot_I_ne_empty (fun _ => (∅ : D)) hI.symm

/-- Contrapositive of `hasHnf_of_solvable` for a closed term: denoting the least element makes a
term unsolvable. -/
theorem not_solvable_of_denot_eq_empty {t : Lambda} (hcl : Lambda.IsClosed t) {ρ : Env}
    (h : denot t ρ = (∅ : D)) : ¬ Lambda.Solvable t := fun hs =>
  (denot_ne_empty_iff_hasHnf hcl ρ).2 (hasHnf_of_solvable hs) h

end GraphModel
