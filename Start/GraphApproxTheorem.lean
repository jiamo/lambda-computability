/-
The approximation theorem for Scott's graph model.

`Start/GraphApprox.lean` introduces the direct approximant `ω(M)` of a term and proves the easy
half of the approximation theorem: every `⟦ω(M')⟧ρ`, for `M ↠ M'`, is contained in `⟦M⟧ρ`.  This
file proves the hard half, and hence the theorem itself:

* `GraphModel.exists_reduct_mem_denot_direct` — every token of `⟦M⟧ρ` already belongs to
  `⟦ω(M')⟧ρ` for some reduct `M'` of `M`;
* `GraphModel.denot_eq_iUnion_denot_direct` — **the approximation theorem**
  `⟦M⟧ρ = ⋃ {⟦ω(M')⟧ρ : M ↠ M'}`: the meaning of a term is exactly the union of the meanings of
  the direct approximants of its reducts;
* `GraphModel.denot_subset_of_approx_reducts`, `GraphModel.denot_eq_of_approx_reducts` — its main
  consequence: syntactic domination of the approximants is a semantic inequality, so two terms
  whose approximants dominate each other are identified by the model.

The proof is a Kripke-style computability (logical relations) argument, in the same shape as the
adequacy proof of `Start/GraphAdequacy.lean` but carrying the approximant information.  The
predicate `GraphModel.ARealAux b ρ t` says that `t` reduces to a term whose direct approximant
already contains the token `b`, *and* — when `b` is a step function `a ⇒ c` — that applying `t` to
any term satisfying every token of `a` produces a term satisfying `c`.  The recursion is on the
size of the token.  `GraphModel.AReal` closes the predicate under weakening of the environment,
which is what the shift performed by parallel substitution at a binder needs; unlike in the
adequacy proof, the *semantic* environment has to be weakened alongside the syntactic one, so
the fundamental lemma `GraphModel.arealAux_substEnv` relates two environments: `ρ`, interpreting
the free variables of the term, and `ρ'`, interpreting the target context of the substitution.

Two syntactic ingredients feed the argument: direct approximants only grow along reduction
(`GraphModel.denot_direct_reduces_mono`), and, by confluence, finitely many reducts of a term can
always be merged into a single one (`GraphModel.exists_reduct_lset_subset`).
-/

import Start.GraphApprox
import Start.ParallelSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Having a variable at the head is preserved by reduction. -/
theorem headVar_step {s s' : Lambda} (h : Lambda.step s s') (hs : headVar s = Bool.true) :
    headVar s' = Bool.true := by
  induction h with
  | beta t₁ t₂ => simp at hs
  | app_left a a' b _ ih => simpa using ih (by simpa using hs)
  | app_right a b b' _ => simpa using hs
  | lam t t' _ _ => simp at hs

/-- Direct approximants only grow along a reduction step. -/
theorem approx_direct_step : ∀ {t t' : Lambda}, Lambda.step t t' →
    Approx (direct t) (direct t') := by
  intro t t' h
  induction h with
  | beta t₁ t₂ =>
      rw [direct_app, if_neg (by simp)]
      exact Approx.omega _
  | app_left a a' b hstep ih =>
      by_cases hh : headVar a = Bool.true
      · rw [direct_app, if_pos hh, direct_app, if_pos (headVar_step hstep hh)]
        exact Approx.app ih (Approx.refl _)
      · rw [direct_app, if_neg hh]
        exact Approx.omega _
  | app_right a b b' _ ih =>
      by_cases hh : headVar a = Bool.true
      · rw [direct_app, if_pos hh, direct_app, if_pos hh]
        exact Approx.app (Approx.refl _) ih
      · rw [direct_app, if_neg hh]
        exact Approx.omega _
  | lam t t' _ ih => exact Approx.lam ih

end Lambda

namespace GraphModel

open Lambda

/-! ## Direct approximants grow along reduction -/

/-- The denotation of the direct approximant grows along a reduction step. -/
theorem denot_direct_step_mono {t t' : Lambda} (h : Lambda.step t t') (ρ : Env) :
    denot (direct t) ρ ⊆ denot (direct t') ρ :=
  denot_approx_subset (Lambda.approx_direct_step h) ρ

/-- The denotation of the direct approximant grows along reduction. -/
theorem denot_direct_reduces_mono {t t' : Lambda} (h : Lambda.reduces t t') (ρ : Env) :
    denot (direct t) ρ ⊆ denot (direct t') ρ := by
  induction h with
  | refl t => exact subset_rfl
  | step t₁ t₂ t₃ hs _ ih => exact (denot_direct_step_mono hs ρ).trans ih

/-- **Merging finitely many reducts.**  If every token of a finite list is seen by the direct
approximant of some reduct of `s`, then a single reduct of `s` sees all of them. -/
theorem exists_reduct_lset_subset (ρ : Env) : ∀ (a : List Tok) (s : Lambda),
    (∀ x ∈ a, ∃ s', Lambda.reduces s s' ∧ x ∈ denot (direct s') ρ) →
    ∃ s', Lambda.reduces s s' ∧ lset a ⊆ denot (direct s') ρ := by
  intro a
  induction a with
  | nil => intro s _; exact ⟨s, Lambda.reduces.refl s, by simp⟩
  | cons x a ih =>
      intro s hs
      obtain ⟨s₁, hs₁, hx⟩ := hs x (by simp)
      obtain ⟨s₂, hs₂, ha⟩ := ih s (fun y hy => hs y (by simp [hy]))
      obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem hs₁ hs₂
      refine ⟨w, Lambda.reduces_trans hs₁ hw₁, ?_⟩
      intro y hy
      simp only [mem_lset, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact denot_direct_reduces_mono hw₁ ρ hx
      · exact denot_direct_reduces_mono hw₂ ρ (ha (mem_lset.2 hy))

/-! ## The computability predicate -/

/-- `ARealAux b ρ t`: the term `t` reduces to one whose direct approximant already contains the
token `b`, and — if `b` is a step function `a ⇒ c` — applying `t` to any term satisfying every
token of `a` (in every weakening of the environment) satisfies `c`. -/
def ARealAux : Tok → Env → Lambda → Prop
  | Tok.atom n, ρ, t => ∃ t', Lambda.reduces t t' ∧ Tok.atom n ∈ denot (direct t') ρ
  | Tok.arrow a c, ρ, t =>
      (∃ t', Lambda.reduces t t' ∧ Tok.arrow a c ∈ denot (direct t') ρ) ∧
        ∀ s : Lambda,
          (∀ x ∈ a, ∀ (n : ℕ) (ρ' : Env), (∀ i, ρ' (i + n) = ρ i) →
            ARealAux x ρ' (Lambda.lift n 0 s)) →
          ARealAux c ρ (Lambda.app t s)
  termination_by b _ _ => b.size
  decreasing_by
    · exact lt_of_le_of_lt (size_le_maxSize (by assumption)) (maxSize_lt_of_arrow a c)
    · simp only [Tok.size]; omega

/-- The weakening-closed form of `ARealAux`: the predicate holds in every environment extending
`ρ` with `n` fresh variables, for the correspondingly lifted term. -/
def AReal (b : Tok) (ρ : Env) (t : Lambda) : Prop :=
  ∀ (n : ℕ) (ρ' : Env), (∀ i, ρ' (i + n) = ρ i) → ARealAux b ρ' (Lambda.lift n 0 t)

/-- Whatever the token, the predicate exhibits a reduct whose direct approximant sees it. -/
theorem ARealAux.direct {b : Tok} {ρ : Env} {t : Lambda} (h : ARealAux b ρ t) :
    ∃ t', Lambda.reduces t t' ∧ b ∈ denot (direct t') ρ := by
  cases b with
  | atom n => rwa [ARealAux] at h
  | arrow a c => rw [ARealAux] at h; exact h.1

theorem AReal.arealAux {b : Tok} {ρ : Env} {t : Lambda} (h : AReal b ρ t) : ARealAux b ρ t := by
  have := h 0 ρ (fun _ => rfl)
  rwa [Lambda.lift_zero] at this

/-- The predicate is closed under weakening of both the environment and the term. -/
theorem AReal.weaken {b : Tok} {ρ : Env} {t : Lambda} (h : AReal b ρ t) (n : ℕ) (ρ' : Env)
    (hρ' : ∀ i, ρ' (i + n) = ρ i) : AReal b ρ' (Lambda.lift n 0 t) := by
  intro m ρ'' hρ''
  rw [← Lambda.lift_add]
  refine h (m + n) ρ'' ?_
  intro i
  have h1 := hρ'' (i + n)
  rw [hρ' i] at h1
  rw [show i + (m + n) = i + n + m by omega]
  exact h1

/-- The predicate is inherited backwards along a reduction. -/
theorem arealAux_expand : ∀ {b : Tok} {ρ : Env} {t u : Lambda}, Lambda.reduces t u →
    ARealAux b ρ u → ARealAux b ρ t := by
  have key : ∀ (n : ℕ) (b : Tok), b.size ≤ n → ∀ (ρ : Env) (t u : Lambda), Lambda.reduces t u →
      ARealAux b ρ u → ARealAux b ρ t := by
    intro n
    induction n with
    | zero =>
        intro b hb
        exact absurd hb (Nat.not_le.mpr (size_pos b))
    | succ n ih =>
        intro b hb ρ t u hr h
        cases b with
        | atom m =>
            rw [ARealAux] at h ⊢
            obtain ⟨u', hu', hmem⟩ := h
            exact ⟨u', Lambda.reduces_trans hr hu', hmem⟩
        | arrow a c =>
            rw [ARealAux] at h ⊢
            refine ⟨?_, ?_⟩
            · obtain ⟨u', hu', hmem⟩ := h.1
              exact ⟨u', Lambda.reduces_trans hr hu', hmem⟩
            · intro s hs
              have hcn : Tok.size c ≤ n := by
                have hlt : Tok.size c < Tok.size (Tok.arrow a c) := by
                  simp only [Tok.size]; omega
                omega
              exact ih c hcn ρ _ _ (Lambda.reduces_app_left hr) (h.2 s hs)
  intro b ρ t u hr h
  exact key b.size b le_rfl ρ t u hr h

/-- A term reducing to a *neutral* term whose direct approximant sees the token satisfies the
predicate: this is the base case of the computability argument, and the only place where
confluence is used. -/
theorem arealAux_of_neutral_reduct : ∀ (b : Tok) (ρ : Env) (t : Lambda),
    (∃ t', Lambda.reduces t t' ∧ Neutral t' ∧ b ∈ denot (direct t') ρ) → ARealAux b ρ t := by
  have key : ∀ (n : ℕ) (b : Tok), b.size ≤ n → ∀ (ρ : Env) (t : Lambda),
      (∃ t', Lambda.reduces t t' ∧ Neutral t' ∧ b ∈ denot (direct t') ρ) → ARealAux b ρ t := by
    intro n
    induction n with
    | zero =>
        intro b hb
        exact absurd hb (Nat.not_le.mpr (size_pos b))
    | succ n ih =>
        intro b hb ρ t h
        obtain ⟨t₀, ht₀, hn₀, hmem⟩ := h
        cases b with
        | atom m => rw [ARealAux]; exact ⟨t₀, ht₀, hmem⟩
        | arrow a c =>
            rw [ARealAux]
            refine ⟨⟨t₀, ht₀, hmem⟩, ?_⟩
            intro s hs
            have hcn : Tok.size c ≤ n := by
              have hlt : Tok.size c < Tok.size (Tok.arrow a c) := by
                simp only [Tok.size]; omega
              omega
            have hred : ∀ x ∈ a, ∃ s', Lambda.reduces s s' ∧ x ∈ denot (direct s') ρ := by
              intro x hx
              have := hs x hx 0 ρ (fun _ => rfl)
              rw [Lambda.lift_zero] at this
              exact this.direct
            obtain ⟨s', hs', hsub⟩ := exists_reduct_lset_subset ρ a s hred
            refine ih c hcn ρ _ ⟨Lambda.app t₀ s', Lambda.reduces_app ht₀ hs',
              Neutral.app _ hn₀, ?_⟩
            rw [direct_app, if_pos (neutral_iff_headVar.1 hn₀)]
            exact ⟨a, hsub, hmem⟩
  intro b ρ t h
  exact key b.size b le_rfl ρ t h

theorem areal_var (b : Tok) (ρ : Env) (i : ℕ) (hb : b ∈ ρ i) : AReal b ρ (Lambda.var i) := by
  intro n ρ' hρ'
  refine arealAux_of_neutral_reduct b ρ' _ ⟨Lambda.lift n 0 (Lambda.var i),
    Lambda.reduces.refl _, ?_, ?_⟩
  · simp only [Lambda.lift, if_neg (Nat.not_lt_zero i)]
    exact Neutral.var _
  · simp only [Lambda.lift, if_neg (Nat.not_lt_zero i), direct_var, denot_var]
    rw [hρ' i]
    exact hb

/-! ## The fundamental lemma -/

/-- **The fundamental lemma.**  If every token of `ρ i` is satisfied by `u i` in the target
environment `ρ'`, then every token of `⟦t⟧ρ` is satisfied by the substitution instance `t[u]`
in `ρ'`. -/
theorem arealAux_substEnv : ∀ (t : Lambda) (ρ ρ' : Env) (u : ℕ → Lambda),
    (∀ i, ∀ x ∈ ρ i, AReal x ρ' (u i)) →
    ∀ b ∈ denot t ρ, ARealAux b ρ' (Lambda.substEnv u t) := by
  intro t
  induction t with
  | var i =>
      intro ρ ρ' u hu b hb
      exact (hu i b hb).arealAux
  | app s w ihs ihw =>
      intro ρ ρ' u hu b hb
      obtain ⟨a, ha, harr⟩ := hb
      have hs := ihs ρ ρ' u hu (Tok.arrow a b) harr
      rw [ARealAux] at hs
      refine hs.2 (Lambda.substEnv u w) ?_
      intro x hx n ρ'' hρ''
      rw [Lambda.lift_substEnv]
      refine ihw ρ ρ'' (fun i => Lambda.lift n 0 (u i)) ?_ x (ha (mem_lset.2 hx))
      intro i y hy
      exact (hu i y hy).weaken n ρ'' hρ''
  | lam t₀ ih =>
      intro ρ ρ' u hu b hb
      obtain ⟨a, c, rfl, hc⟩ := hb
      rw [ARealAux]
      constructor
      · have hcons : ∀ i, ∀ y ∈ cons (lset a) ρ i,
            AReal y (cons (lset a) ρ') (Lambda.envCons u i) := by
          intro i
          cases i with
          | zero =>
              intro y hy n ρ'' hρ''
              refine arealAux_of_neutral_reduct y ρ'' _ ⟨Lambda.lift n 0 (Lambda.var 0),
                Lambda.reduces.refl _, ?_, ?_⟩
              · simp only [Lambda.lift, if_neg (Nat.not_lt_zero 0)]
                exact Neutral.var _
              · simp only [Lambda.lift, if_neg (Nat.not_lt_zero 0), direct_var, denot_var]
                rw [hρ'' 0]
                exact hy
          | succ j =>
              intro y hy
              exact (hu j y hy).weaken 1 (cons (lset a) ρ') (fun _ => rfl)
        obtain ⟨T', hT', hcT'⟩ :=
          (ih (cons (lset a) ρ) (cons (lset a) ρ') (Lambda.envCons u) hcons c hc).direct
        refine ⟨Lambda.lam T', Lambda.reduces_lam hT', ?_⟩
        rw [direct_lam, denot_lam]
        exact mem_graph.2 hcT'
      · intro s hs
        have hstep : Lambda.reduces
            (Lambda.app (Lambda.lam (Lambda.substEnv (Lambda.envCons u) t₀)) s)
            (Lambda.subst s 0 (Lambda.substEnv (Lambda.envCons u) t₀)) :=
          Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)
        refine arealAux_expand hstep ?_
        rw [Lambda.subst_zero_substEnv]
        refine ih (cons (lset a) ρ) ρ' (Lambda.envScons s u) ?_ c hc
        intro i
        cases i with
        | zero => intro y hy; exact hs y hy
        | succ j => intro y hy; exact hu j y hy

/-! ## The approximation theorem -/

/-- **Completeness of approximation.**  Every token of the denotation of a term is already in the
denotation of the direct approximant of one of its reducts. -/
theorem exists_reduct_mem_denot_direct {t : Lambda} {ρ : Env} {b : Tok} (hb : b ∈ denot t ρ) :
    ∃ t', Lambda.reduces t t' ∧ b ∈ denot (direct t') ρ := by
  have h := arealAux_substEnv t ρ ρ (fun i => Lambda.var i)
    (fun i x hx => areal_var x ρ i hx) b hb
  rw [Lambda.substEnv_var_id] at h
  exact h.direct

/-- **The approximation theorem.**  The denotation of a term is the union of the denotations of
the direct approximants of its reducts. -/
theorem denot_eq_iUnion_denot_direct (t : Lambda) (ρ : Env) :
    denot t ρ = ⋃ t' ∈ {u : Lambda | Lambda.reduces t u}, denot (direct t') ρ := by
  refine Set.Subset.antisymm ?_ (iUnion_denot_direct_subset t ρ)
  intro b hb
  obtain ⟨t', ht', hmem⟩ := exists_reduct_mem_denot_direct hb
  exact Set.mem_biUnion (by exact ht') hmem

/-- **The approximants of a term are directed.**  Any two of them are dominated by a third, so
the union of `GraphModel.denot_eq_iUnion_denot_direct` really is a supremum of a directed
family. -/
theorem exists_reduct_denot_direct_sup {t t₁ t₂ : Lambda} (h₁ : Lambda.reduces t t₁)
    (h₂ : Lambda.reduces t t₂) (ρ : Env) :
    ∃ t₃, Lambda.reduces t t₃ ∧ denot (direct t₁) ρ ⊆ denot (direct t₃) ρ ∧
      denot (direct t₂) ρ ⊆ denot (direct t₃) ρ := by
  obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem h₁ h₂
  exact ⟨w, Lambda.reduces_trans h₁ hw₁, denot_direct_reduces_mono hw₁ ρ,
    denot_direct_reduces_mono hw₂ ρ⟩

/-- If every approximant of `t` is below an approximant of `u`, then `t` denotes less than `u`.
Syntactic domination of the approximants — of the Böhm trees — is a semantic inequality. -/
theorem denot_subset_of_approx_reducts {t u : Lambda}
    (h : ∀ t', Lambda.reduces t t' → ∃ u', Lambda.reduces u u' ∧ Approx (direct t') (direct u'))
    (ρ : Env) : denot t ρ ⊆ denot u ρ := by
  intro b hb
  obtain ⟨t', ht', hmem⟩ := exists_reduct_mem_denot_direct hb
  obtain ⟨u', hu', happ⟩ := h t' ht'
  exact denot_direct_reduct_subset hu' ρ (denot_approx_subset happ ρ hmem)

/-- Two terms whose approximants dominate each other have the same denotation. -/
theorem denot_eq_of_approx_reducts {t u : Lambda}
    (h₁ : ∀ t', Lambda.reduces t t' → ∃ u', Lambda.reduces u u' ∧ Approx (direct t') (direct u'))
    (h₂ : ∀ u', Lambda.reduces u u' → ∃ t', Lambda.reduces t t' ∧ Approx (direct u') (direct t'))
    (ρ : Env) : denot t ρ = denot u ρ :=
  Set.Subset.antisymm (denot_subset_of_approx_reducts h₁ ρ)
    (denot_subset_of_approx_reducts h₂ ρ)

end GraphModel
