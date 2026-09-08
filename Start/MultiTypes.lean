/-
**Multi types: non-idempotent intersection types measure head reduction.**

`Start/IntersectionTypes.lean` builds the *idempotent* intersection types, whose typability
characterises head normalisation qualitatively.  This module builds the **non-idempotent** system
— de Carvalho's *multi types* — where an intersection is a finite **multiset** rather than a set,
so nothing is duplicated for free and a derivation carries quantitative information: its size
strictly decreases along head reduction, and therefore bounds the number of head steps.

* `Multi.Sty`, `Multi.MTy`, `Multi.Ctx` — strict types, multi types (a list of strict types read
  as their multiset) and contexts (a multiset of strict types for each de Bruijn index);
* `Multi.Deriv`, `Multi.DerivList` — the type assignment, with the size of the derivation as an
  index; contexts are *outputs*: there is no weakening, and the context of an application is the
  sum of the contexts of the two premises;
* `Multi.substitution` — **the quantitative substitution lemma**: the derivation of `M[N/x]` has
  size `n + m - |a|`, where `a` is the multi type used at `x`;
* `Multi.subject_reduction_hstep` — **quantitative subject reduction**: a head step strictly
  decreases the size of the derivation;
* `Multi.hasHnf_of_typable` — hence a typable term is head normalising;
* `Multi.hnIn_of_deriv` — a derivation of size `n` reaches a head normal form in at most `n` head
  steps, the quantitative content of the system;
* `Multi.typable_of_isHnf` — head normal forms are typable, so the system is not vacuous;
* `Multi.not_typable_omega` — `Ω` has no derivation.

**Boundary.** Subject *expansion* is not proved here, so de Carvalho's exact equality — the size
of a derivation equals the number of head steps to the head normal form plus the size of a
derivation for that head normal form — is not claimed.  What is proved is the upper bound
(`hnIn_of_deriv`) together with typability of head normal forms (`typable_of_isHnf`), i.e. the
characterisation of head normalisation by typability plus a quantitative bound in one direction.
-/

import Start.HeadReduction
import Start.Recursion
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Multi

/-! ### Types and contexts -/

/-- A **strict multi type**: an atom, or an arrow whose source is a finite multiset of strict
types, presented as a list. -/
inductive Sty : Type
  | atom : Sty
  | arrow : List Sty → Sty → Sty

/-- A **multi type**: a list of strict types, read as their multiset. -/
abbrev MTy : Type := List Sty

/-- A context assigns a multiset of strict types to every de Bruijn index. -/
abbrev Ctx : Type := ℕ → Multiset Sty

/-- The empty context. -/
def emp : Ctx := fun _ => 0

/-- The pointwise sum of two contexts. -/
def add (Γ Δ : Ctx) : Ctx := fun i => Γ i + Δ i

/-- The context assigning `σ` to `x` and nothing to any other index. -/
def single (x : ℕ) (σ : Sty) : Ctx := fun i => if i = x then {σ} else 0

/-- Extend a context with a multi type for the index `0`. -/
def push (a : Multiset Sty) (Γ : Ctx) : Ctx := fun i => if i = 0 then a else Γ (i - 1)

/-- Delete the slot `x` of a context, shifting the higher slots down. -/
def del (x : ℕ) (Γ : Ctx) : Ctx := fun i => if i < x then Γ i else Γ (i + 1)

/-- Insert an empty slot at position `x`, shifting the higher slots up. -/
def ins (x : ℕ) (Γ : Ctx) : Ctx := fun i =>
  if i < x then Γ i else if i = x then 0 else Γ (i - 1)

/-! ### The type assignment -/

/-! **Type assignment with multi types**, with the size of the derivation as the last index.
The context is an output: a variable is typed in the context that assigns it exactly the type
used, and an application sums the contexts of its premises, so nothing is duplicated.
`DerivList Γ N a n` types `N` once for every component of the multi type `a`.

The **size** counts the applications of the abstraction and the application rule; the variable
axioms count `0`.  That is the measure for which head reduction is exact: a head step removes one
abstraction rule and one application rule and nothing else, so the size drops by exactly `2`
(`subject_reduction_hstep`).  Counting the axioms too would only give an inequality, because a
head step also duplicates or erases the axioms typing the substituted variable. -/
mutual
inductive Deriv : Ctx → Lambda → Sty → ℕ → Prop
  | var (x : ℕ) (σ : Sty) : Deriv (single x σ) (Lambda.var x) σ 0
  | lam {Γ : Ctx} {a : MTy} {M : Lambda} {τ : Sty} {n : ℕ} :
      Deriv (push (↑a) Γ) M τ n → Deriv Γ (Lambda.lam M) (Sty.arrow a τ) (n + 1)
  | app {Γ Δ : Ctx} {M N : Lambda} {a : MTy} {τ : Sty} {n m : ℕ} :
      Deriv Γ M (Sty.arrow a τ) n → DerivList Δ N a m →
      Deriv (add Γ Δ) (Lambda.app M N) τ (n + m + 1)
inductive DerivList : Ctx → Lambda → MTy → ℕ → Prop
  | nil {N : Lambda} : DerivList emp N [] 0
  | cons {Γ Δ : Ctx} {N : Lambda} {σ : Sty} {a : MTy} {n m : ℕ} :
      Deriv Γ N σ n → DerivList Δ N a m → DerivList (add Γ Δ) N (σ :: a) (n + m)
end

/-- A term is **typable** when it has a derivation. -/
def Typable (M : Lambda) : Prop := ∃ Γ σ n, Deriv Γ M σ n

/-! ### Basic laws of contexts -/

theorem add_emp (Γ : Ctx) : add Γ emp = Γ := by
  funext i; simp [add, emp]

theorem emp_add (Γ : Ctx) : add emp Γ = Γ := by
  funext i; simp [add, emp]

theorem add_comm (Γ Δ : Ctx) : add Γ Δ = add Δ Γ := by
  funext i; simp [add, _root_.add_comm]

theorem add_assoc (Γ Δ Θ : Ctx) : add (add Γ Δ) Θ = add Γ (add Δ Θ) := by
  funext i; simp [add, _root_.add_assoc]

theorem add_rearrange (Γ₁ Δ₁ Γ₂ Δ₂ : Ctx) :
    add (add Γ₁ Δ₁) (add Γ₂ Δ₂) = add (add Γ₁ Γ₂) (add Δ₁ Δ₂) := by
  funext i
  simp only [add]
  ac_rfl

/-- The tactic that proves the pointwise identities between contexts below: unfold, split every
test, and settle each branch by arithmetic. -/
macro "ctx_ext" : tactic =>
  `(tactic| (funext i
             simp only [add, emp, single, push, del, ins]
             split_ifs <;>
               first
                 | rfl
                 | (congr 1; omega)
                 | (exfalso; omega)
                 | simp))

theorem push_add (a b : Multiset Sty) (Γ Δ : Ctx) :
    add (push a Γ) (push b Δ) = push (a + b) (add Γ Δ) := by
  ctx_ext

theorem del_add (x : ℕ) (Γ Δ : Ctx) : del x (add Γ Δ) = add (del x Γ) (del x Δ) := by
  ctx_ext

theorem del_emp (x : ℕ) : del x emp = emp := by
  ctx_ext

theorem del_push (x : ℕ) (a : Multiset Sty) (Γ : Ctx) :
    del (x + 1) (push a Γ) = push a (del x Γ) := by
  ctx_ext

theorem del_zero_push (a : Multiset Sty) (Γ : Ctx) : del 0 (push a Γ) = Γ := by
  ctx_ext

theorem del_single_self (x : ℕ) (σ : Sty) : del x (single x σ) = emp := by
  ctx_ext

theorem del_single_lt {y x : ℕ} (h : y < x) (σ : Sty) : del x (single y σ) = single y σ := by
  ctx_ext

theorem del_single_gt {y x : ℕ} (h : x < y) (σ : Sty) : del x (single y σ) = single (y - 1) σ := by
  ctx_ext

theorem ins_add (x : ℕ) (Γ Δ : Ctx) : ins x (add Γ Δ) = add (ins x Γ) (ins x Δ) := by
  ctx_ext

theorem ins_emp (x : ℕ) : ins x emp = emp := by
  ctx_ext

theorem ins_zero (Γ : Ctx) : ins 0 Γ = push 0 Γ := by
  ctx_ext

theorem ins_push (x : ℕ) (a : Multiset Sty) (Γ : Ctx) :
    ins (x + 1) (push a Γ) = push a (ins x Γ) := by
  ctx_ext

theorem ins_single_lt {y x : ℕ} (h : y < x) (σ : Sty) : ins x (single y σ) = single y σ := by
  ctx_ext

theorem ins_single_ge {y x : ℕ} (h : x ≤ y) (σ : Sty) : ins x (single y σ) = single (y + 1) σ := by
  ctx_ext

/-! ### Inversion, splitting and permutation for lists of derivations -/

theorem DerivList.nil_inv {Δ : Ctx} {N : Lambda} {m : ℕ} (h : DerivList Δ N [] m) :
    Δ = emp ∧ m = 0 := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

theorem DerivList.cons_inv {Δ : Ctx} {N : Lambda} {σ : Sty} {a : MTy} {m : ℕ}
    (h : DerivList Δ N (σ :: a) m) :
    ∃ Γ₁ Δ₁ n₁ m₁, Δ = add Γ₁ Δ₁ ∧ Deriv Γ₁ N σ n₁ ∧ DerivList Δ₁ N a m₁ ∧ m = n₁ + m₁ := by
  cases h with
  | cons hd ht => exact ⟨_, _, _, _, rfl, hd, ht, rfl⟩

theorem DerivList.split {Δ : Ctx} {N : Lambda} {m : ℕ} :
    ∀ {a b : MTy}, DerivList Δ N (a ++ b) m →
      ∃ Δ₁ Δ₂ m₁ m₂, Δ = add Δ₁ Δ₂ ∧ DerivList Δ₁ N a m₁ ∧ DerivList Δ₂ N b m₂ ∧
        m = m₁ + m₂ := by
  intro a
  induction a generalizing Δ m with
  | nil =>
      intro b h
      exact ⟨emp, Δ, 0, m, (emp_add Δ).symm, DerivList.nil, h, (Nat.zero_add m).symm⟩
  | cons σ a ih =>
      intro b h
      obtain ⟨Γ₁, Δ₁, n₁, m₁, rfl, hd, ht, rfl⟩ := DerivList.cons_inv h
      obtain ⟨Δ₁₁, Δ₁₂, m₁₁, m₁₂, rfl, ht₁, ht₂, rfl⟩ := ih ht
      refine ⟨add Γ₁ Δ₁₁, Δ₁₂, n₁ + m₁₁, m₁₂, ?_, DerivList.cons hd ht₁, ht₂, by omega⟩
      rw [add_assoc]

theorem DerivList.append {Δ₁ Δ₂ : Ctx} {N : Lambda} {m₁ m₂ : ℕ} :
    ∀ {a b : MTy}, DerivList Δ₁ N a m₁ → DerivList Δ₂ N b m₂ →
      DerivList (add Δ₁ Δ₂) N (a ++ b) (m₁ + m₂) := by
  intro a
  induction a generalizing Δ₁ m₁ with
  | nil =>
      intro b h₁ h₂
      obtain ⟨rfl, rfl⟩ := DerivList.nil_inv h₁
      simpa [emp_add] using h₂
  | cons σ a ih =>
      intro b h₁ h₂
      obtain ⟨Γ, Δ, n, m, rfl, hd, ht, rfl⟩ := DerivList.cons_inv h₁
      have := DerivList.cons hd (ih ht h₂)
      rw [← add_assoc] at this
      simpa [Nat.add_assoc] using this

theorem DerivList.perm {Δ : Ctx} {N : Lambda} {m : ℕ} :
    ∀ {a b : MTy}, a.Perm b → DerivList Δ N a m → DerivList Δ N b m := by
  intro a b hp
  induction hp generalizing Δ m with
  | nil => exact fun h => h
  | cons σ _ ih =>
      intro h
      obtain ⟨Γ₁, Δ₁, n₁, m₁, rfl, hd, ht, rfl⟩ := DerivList.cons_inv h
      exact DerivList.cons hd (ih ht)
  | swap σ τ l =>
      intro h
      obtain ⟨Γ₁, Δ₁, n₁, m₁, rfl, hd, ht, rfl⟩ := DerivList.cons_inv h
      obtain ⟨Γ₂, Δ₂, n₂, m₂, rfl, hd₂, ht₂, rfl⟩ := DerivList.cons_inv ht
      have h' := DerivList.cons hd₂ (DerivList.cons hd ht₂)
      have hctx : add Γ₂ (add Γ₁ Δ₂) = add Γ₁ (add Γ₂ Δ₂) := by
        rw [← add_assoc, ← add_assoc, add_comm Γ₂ Γ₁]
      have hnum : n₂ + (n₁ + m₂) = n₁ + (n₂ + m₂) := by omega
      rw [hctx, hnum] at h'
      exact h'
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-! ### Lifting -/

theorem lifting : ∀ {Γ : Ctx} {M : Lambda} {τ : Sty} {n : ℕ}, Deriv Γ M τ n →
    ∀ x : ℕ, Deriv (ins x Γ) (Lambda.lift 1 x M) τ n := by
  intro Γ M τ n h
  induction h using Deriv.rec
    (motive_2 := fun Γ N a m _ => ∀ x : ℕ, DerivList (ins x Γ) (Lambda.lift 1 x N) a m) with
  | var y σ =>
      intro x
      by_cases hy : y < x
      · rw [ins_single_lt hy]
        simpa [Lambda.lift, hy] using Deriv.var y σ
      · rw [ins_single_ge (Nat.not_lt.1 hy)]
        simpa [Lambda.lift, hy] using Deriv.var (y + 1) σ
  | lam _ ih =>
      intro x
      have ih' := ih (x + 1)
      rw [ins_push] at ih'
      simpa [Lambda.lift] using Deriv.lam ih'
  | app _ _ ihM ihN =>
      intro x
      have := Deriv.app (ihM x) (ihN x)
      rw [← ins_add] at this
      simpa [Lambda.lift] using this
  | nil =>
      rename_i x
      rw [ins_emp]
      exact DerivList.nil
  | cons _ _ ihd iht =>
      rename_i x
      have := DerivList.cons (ihd x) (iht x)
      rw [← ins_add] at this
      exact this

theorem lifting_list : ∀ {a : MTy} {Γ : Ctx} {N : Lambda} {m : ℕ}, DerivList Γ N a m →
    ∀ x : ℕ, DerivList (ins x Γ) (Lambda.lift 1 x N) a m := by
  intro a
  induction a with
  | nil =>
      intro Γ N m h x
      obtain ⟨rfl, rfl⟩ := DerivList.nil_inv h
      rw [ins_emp]
      exact DerivList.nil
  | cons σ a ih =>
      intro Γ N m h x
      obtain ⟨Γ₁, Δ₁, n₁, m₁, rfl, hd, ht, rfl⟩ := DerivList.cons_inv h
      rw [ins_add]
      exact DerivList.cons (lifting hd x) (ih ht x)

/-! ### The main results -/

/-- **The quantitative substitution lemma**, for a derivation and for a list of derivations at
once.  Substituting `N` for `x` in `M` replaces the axioms that type `x` by the derivations of
`N`, and those axioms do not count, so the sizes simply add: the derivation of `M[N/x]` has size
`n + m`. -/
theorem substitution : ∀ {Γ : Ctx} {M : Lambda} {τ : Sty} {n : ℕ}, Deriv Γ M τ n →
    ∀ (x : ℕ) (a : MTy) (Δ : Ctx) (N : Lambda) (m : ℕ), Γ x = ↑a → DerivList Δ N a m →
      ∃ p, Deriv (add (del x Γ) Δ) (Lambda.subst N x M) τ p ∧ p = n + m := by
  intro Γ M τ n h
  induction h using Deriv.rec
    (motive_2 := fun Γ P c k _ => ∀ (x : ℕ) (a : MTy) (Δ : Ctx) (N : Lambda) (m : ℕ),
      Γ x = ↑a → DerivList Δ N a m →
        ∃ p, DerivList (add (del x Γ) Δ) (Lambda.subst N x P) c p ∧ p = k + m) with
  | var y σ =>
      intro x a Δ N m hx hlist
      by_cases hyx : y = x
      · subst hyx
        have ha : a = [σ] := by
          have : (↑a : Multiset Sty) = {σ} := by
            rw [← hx]; simp [single]
          exact Multiset.coe_eq_singleton.1 this
        subst ha
        obtain ⟨Γ₁, Δ₁, n₁, m₁, rfl, hd, ht, rfl⟩ := DerivList.cons_inv hlist
        obtain ⟨rfl, rfl⟩ := DerivList.nil_inv ht
        refine ⟨n₁, ?_, by omega⟩
        rw [del_single_self, emp_add, add_emp]
        simpa [Lambda.subst] using hd
      · have hxy : x ≠ y := fun h => hyx h.symm
        have ha : a = [] := by
          have : (↑a : Multiset Sty) = 0 := by
            rw [← hx]; simp [single, hxy]
          exact (Multiset.coe_eq_zero a).1 this
        subst ha
        obtain ⟨rfl, rfl⟩ := DerivList.nil_inv hlist
        refine ⟨0, ?_, by simp⟩
        rcases Nat.lt_or_ge y x with hlt | hge
        · rw [del_single_lt hlt, add_emp]
          have hgt : ¬ y > x := by omega
          simpa [Lambda.subst, hyx, hgt] using Deriv.var y σ
        · have hgt : y > x := by omega
          rw [del_single_gt hgt, add_emp]
          simpa [Lambda.subst, hyx, hgt] using Deriv.var (y - 1) σ
  | @lam Γ₀ b M₀ τ₀ n₀ _ ih =>
      intro x a Δ N m hx hlist
      have hx' : (push (↑b) Γ₀) (x + 1) = ↑a := by simpa [push] using hx
      obtain ⟨p, hp, hsize⟩ :=
        ih (x + 1) a (ins 0 Δ) (Lambda.lift 1 0 N) m hx' (lifting_list hlist 0)
      rw [del_push, ins_zero, push_add] at hp
      refine ⟨p + 1, ?_, by omega⟩
      have := Deriv.lam (a := b) (by simpa using hp)
      simpa [Lambda.subst] using this
  | @app Γ₁ Γ₂ M₁ M₂ c τ₀ n₁ n₂ _ _ ihM ihN =>
      intro x a Δ N m hx hlist
      refine ?_
      have hsplit : (↑a : Multiset Sty) = Γ₁ x + Γ₂ x := by rw [← hx]; rfl
      have hperm : a.Perm ((Γ₁ x).toList ++ (Γ₂ x).toList) := by
        refine Multiset.coe_eq_coe.1 ?_
        rw [hsplit, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      obtain ⟨Δ₁, Δ₂, m₁, m₂, rfl, hl₁, hl₂, rfl⟩ :=
        DerivList.split (DerivList.perm hperm hlist)
      obtain ⟨p₁, hp₁, hs₁⟩ := ihM x (Γ₁ x).toList Δ₁ N m₁ (by simp) hl₁
      obtain ⟨p₂, hp₂, hs₂⟩ := ihN x (Γ₂ x).toList Δ₂ N m₂ (by simp) hl₂
      refine ⟨p₁ + p₂ + 1, ?_, by omega⟩
      have := Deriv.app hp₁ hp₂
      rw [add_rearrange, ← del_add] at this
      simpa [Lambda.subst] using this
  | nil =>
      rename_i N₀ x a Δ N m hx hlist
      have ha : a = [] := by
        have : (↑a : Multiset Sty) = 0 := by rw [← hx]; rfl
        exact (Multiset.coe_eq_zero a).1 this
      subst ha
      obtain ⟨rfl, rfl⟩ := DerivList.nil_inv hlist
      refine ⟨0, ?_, by simp⟩
      rw [del_emp, add_emp]
      exact DerivList.nil
  | @cons Γ₁ Γ₂ N₀ σ c n₁ n₂ _ _ ihd iht =>
      rename_i x a Δ N m hx hlist
      have hsplit : (↑a : Multiset Sty) = Γ₁ x + Γ₂ x := by rw [← hx]; rfl
      have hperm : a.Perm ((Γ₁ x).toList ++ (Γ₂ x).toList) := by
        refine Multiset.coe_eq_coe.1 ?_
        rw [hsplit, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      obtain ⟨Δ₁, Δ₂, m₁, m₂, rfl, hl₁, hl₂, rfl⟩ :=
        DerivList.split (DerivList.perm hperm hlist)
      obtain ⟨p₁, hp₁, hs₁⟩ := ihd x (Γ₁ x).toList Δ₁ N m₁ (by simp) hl₁
      obtain ⟨p₂, hp₂, hs₂⟩ := iht x (Γ₂ x).toList Δ₂ N m₂ (by simp) hl₂
      refine ⟨p₁ + p₂, ?_, by omega⟩
      have := DerivList.cons hp₁ hp₂
      rw [add_rearrange, ← del_add] at this
      exact this

/-- Quantitative subject reduction for a weak head step. -/
theorem subject_reduction_wstep : ∀ {M M' : Lambda}, Lambda.wstep M M' →
    ∀ {Γ : Ctx} {τ : Sty} {n : ℕ}, Deriv Γ M τ n → ∃ p, Deriv Γ M' τ p ∧ p < n := by
  intro M M' hs
  induction hs with
  | beta P Q =>
      intro Γ τ n h
      cases h with
      | @app Γ₁ Γ₂ _ _ c _ n₁ n₂ hM hN =>
          cases hM with
          | @lam _ _ _ _ n₁' hP =>
              obtain ⟨p, hp, hsize⟩ := substitution hP 0 c Γ₂ Q n₂ (by simp [push]) hN
              rw [del_zero_push] at hp
              exact ⟨p, hp, by omega⟩
  | app N _ ih =>
      intro Γ τ n h
      cases h with
      | @app Γ₁ Γ₂ _ _ c _ n₁ n₂ hM hN =>
          obtain ⟨p, hp, hlt⟩ := ih hM
          exact ⟨p + n₂ + 1, Deriv.app hp hN, by omega⟩

/-- **Quantitative subject reduction**: a head step strictly decreases the size of the
derivation, the context and the type being unchanged. -/
theorem subject_reduction_hstep : ∀ {M M' : Lambda}, Lambda.hstep M M' →
    ∀ {Γ : Ctx} {τ : Sty} {n : ℕ}, Deriv Γ M τ n → ∃ p, Deriv Γ M' τ p ∧ p < n := by
  intro M M' hs
  induction hs with
  | weak hw =>
      intro Γ τ n h
      exact subject_reduction_wstep hw h
  | lam _ ih =>
      intro Γ τ n h
      cases h with
      | @lam Γ₀ a P τ₀ n₀ hP =>
          obtain ⟨p, hp, hlt⟩ := ih hP
          exact ⟨p + 1, Deriv.lam hp, by omega⟩

/-- A typable term reaches a head normal form: the size of its derivation bounds the number of
head reduction steps that remain. -/
theorem hasHeadEval_of_deriv : ∀ (n : ℕ) {Γ : Ctx} {M : Lambda} {τ : Sty}, Deriv Γ M τ n →
    Lambda.HasHeadEval M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro Γ M τ h
      by_cases hnf : Lambda.IsHnf M
      · exact Lambda.hasHeadEval_of_isHnf hnf
      · obtain ⟨M', hst⟩ := Lambda.exists_hstep_of_not_isHnf hnf
        obtain ⟨p, hp, hlt⟩ := subject_reduction_hstep hst h
        exact Lambda.hasHeadEval_of_hstep hst (ih p hlt hp)

/-- **A typable term is head normalising.** -/
theorem hasHnf_of_typable {M : Lambda} (h : Typable M) : Lambda.HasHnf M := by
  obtain ⟨Γ, σ, n, hd⟩ := h
  exact Lambda.hasHnf_of_hasHeadEval (hasHeadEval_of_deriv n hd)

/-- Every neutral term has every strict type, in a suitable context. -/
theorem exists_deriv_of_neutral {M : Lambda} (h : Lambda.Neutral M) (σ : Sty) :
    ∃ Γ n, Deriv Γ M σ n := by
  induction h generalizing σ with
  | var y => exact ⟨single y σ, 0, Deriv.var y σ⟩
  | app N _ ih =>
      obtain ⟨Γ, n, hd⟩ := ih (Sty.arrow [] σ)
      exact ⟨add Γ emp, n + 0 + 1, Deriv.app hd DerivList.nil⟩

/-- **Head normal forms are typable**, so the system is not vacuous. -/
theorem typable_of_isHnf {M : Lambda} (h : Lambda.IsHnf M) : Typable M := by
  induction h with
  | neutral hn =>
      obtain ⟨Γ, n, hd⟩ := exists_deriv_of_neutral hn Sty.atom
      exact ⟨Γ, Sty.atom, n, hd⟩
  | lam _ ih =>
      obtain ⟨Γ, σ, n, hd⟩ := ih
      refine ⟨fun j => Γ (j + 1), Sty.arrow (Γ 0).toList σ, n + 1, ?_⟩
      have hctx : push (↑((Γ 0).toList)) (fun j => Γ (j + 1)) = Γ := by
        funext i
        cases i with
        | zero => simp [push]
        | succ j => simp [push]
      exact Deriv.lam (by rw [hctx]; exact hd)

/-- **The size of a derivation bounds the number of head steps to the head normal form**: a term
with a derivation of size `n` reaches a head normal form in at most `n` steps. -/
theorem hnIn_of_deriv : ∀ (n : ℕ) {Γ : Ctx} {M : Lambda} {τ : Sty}, Deriv Γ M τ n →
    Lambda.HNIn n M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro Γ M τ h
      by_cases hnf : Lambda.IsHnf M
      · cases n with
        | zero => exact hnf
        | succ k => exact Lambda.hnIn_mono (Nat.zero_le _) (show Lambda.HNIn 0 M from hnf)
      · obtain ⟨M', hst⟩ := Lambda.exists_hstep_of_not_isHnf hnf
        obtain ⟨p, hp, hlt⟩ := subject_reduction_hstep hst h
        cases n with
        | zero => omega
        | succ k =>
            refine Or.inr ⟨M', hst, ?_⟩
            exact Lambda.hnIn_mono (by omega) (ih p hlt hp)

/-! ### A term looping on itself is untypable -/

/-- Quantitative subject reduction rules out any derivation for a term that head-reduces to
itself: the size of the derivation would have to decrease strictly forever. -/
theorem no_deriv_of_hstep_self {M : Lambda} (h : Lambda.hstep M M) :
    ∀ (n : ℕ) {Γ : Ctx} {τ : Sty}, ¬ Deriv Γ M τ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro Γ τ hd
      obtain ⟨p, hp, hlt⟩ := subject_reduction_hstep h hd
      exact ih p hlt hp

/-- `Ω = (λx. x x) (λx. x x)` is a head step away from itself. -/
theorem hstep_omega_omega : Lambda.hstep Lambda.omega Lambda.omega := by
  have hb := Lambda.wstep.beta (Lambda.app (Lambda.var 0) (Lambda.var 0))
      (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0)))
  refine Lambda.hstep.weak ?_
  convert hb using 1
  · rfl
  · simp [Lambda.omega, Lambda.subst]

/-- **`Ω` is not typable**: the paradigmatic diverging term has no multi-type derivation. -/
theorem not_typable_omega : ¬ Typable Lambda.omega := by
  rintro ⟨Γ, τ, n, hd⟩
  exact no_deriv_of_hstep_self hstep_omega_omega n hd

end Multi
