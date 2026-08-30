/-
Infinite Böhm trees, as directed sets of finite approximants.

`Start/BohmTree.lean` and the separation theorem work with the *finite* Böhm trees of normal
terms.  A term without a normal form still has a Böhm tree, an infinite one, and the standard way
to present it without coinduction is by its **finite approximants**: the direct approximants
`ω(M')` of the reducts `M ↠ M'`, which form a directed set in the approximation order
`Lambda.Approx` (`Start/GraphApprox.lean`).  Two terms have the same Böhm tree exactly when these
two sets are cofinal in each other.

* `Lambda.BohmTree M = { ω(M') | M ↠ M' }` — the tree, as its set of finite approximants;
* `Lambda.BohmLe`, `Lambda.BohmEq` — domination and equality of Böhm trees.

The approximation order `Lambda.Approx` of this development uses the diverging term `Ω` as its
bottom element, and `Ω` is itself an application, so `Approx` is *not* transitive in general.  It
**is** transitive on direct approximants, and that is the technical heart of the file:

* `Lambda.direct_ne_lam_of_headVar`, `Lambda.direct_ne_omega_of_headVar` — in a direct
  approximant, the function part of an application is never an abstraction and never `Ω`;
* `Lambda.eq_omega_of_approx_direct_omega` — hence a direct approximant below `Ω` *is* `Ω`;
* `Lambda.approx_direct_trans` — transitivity of the approximation order on direct approximants;
* `Lambda.approx_direct_reduces` — direct approximants only grow along a reduction.

The consequences:

* `Lambda.bohmEq_of_conv` — Böhm trees are β-conversion invariants;
* `Lambda.BohmLe.trans`, `Lambda.BohmEq.trans` — Böhm tree equality is an equivalence relation;
* `Lambda.denot_le_of_bohmLe`, `Lambda.graph_of_bohmEq` — **Böhm tree equality is contained in
  the theory of the graph model**, by the approximation theorem;
* `Lambda.bohmEq_omega_app_omega_I`, `Lambda.exists_bohmEq_not_conv` — and it contains
  β-conversion *strictly*: `Ω` and `Ω I` have the same Böhm tree, namely `⊥`.

Together with `Start/LambdaTheory.lean` this places Böhm tree equality in the chain

    B  ⊊  BT  ⊆  Th(𝒫ω)  ⊊  Th(D∞)  =  H* .
-/

import Start.LambdaTheory
import Start.GraphApproxTheorem

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

open GraphModel

/-! ### The shape of a direct approximant -/

/-- `Ω = Ω' Ω'` with `Ω' = λx. x x`. -/
theorem omega_eq_app :
    Lambda.omega =
      Lambda.app (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0)))
        (Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0))) := rfl

@[simp] theorem direct_omega : direct Lambda.omega = Lambda.omega := rfl

@[simp] theorem direct_app_omega (t : Lambda) :
    direct (Lambda.app Lambda.omega t) = Lambda.omega := rfl

/-- A term with a variable head has a direct approximant which is not an abstraction. -/
theorem direct_ne_lam_of_headVar :
    ∀ {s : Lambda}, headVar s = Bool.true → ∀ u : Lambda, direct s ≠ Lambda.lam u := by
  intro s
  induction s with
  | var n => intro _ u; simp
  | lam t _ => intro h; simp at h
  | app t v _ _ =>
      intro h u
      rw [direct_app, if_pos (by simpa using h)]
      simp

/-- A term with a variable head has a direct approximant which is not `Ω`. -/
theorem direct_ne_omega_of_headVar :
    ∀ {s : Lambda}, headVar s = Bool.true → direct s ≠ Lambda.omega := by
  intro s
  induction s with
  | var n => intro _; simp [Lambda.omega]
  | lam t _ => intro h; simp at h
  | app t v _ _ =>
      intro h
      have ht : headVar t = Bool.true := by simpa using h
      rw [direct_app, if_pos ht, omega_eq_app]
      intro hcon
      exact direct_ne_lam_of_headVar ht _ (Lambda.app.inj hcon).1

/-! ### Inversion lemmas for the approximation order -/

theorem approx_lam_inv {a u : Lambda} (h : Approx a (Lambda.lam u)) :
    a = Lambda.omega ∨ ∃ a', a = Lambda.lam a' ∧ Approx a' u := by
  cases h with
  | omega _ => exact Or.inl rfl
  | lam h => exact Or.inr ⟨_, rfl, h⟩

theorem approx_app_inv {a s t : Lambda} (h : Approx a (Lambda.app s t)) :
    a = Lambda.omega ∨ ∃ a₁ a₂, a = Lambda.app a₁ a₂ ∧ Approx a₁ s ∧ Approx a₂ t := by
  cases h with
  | omega _ => exact Or.inl rfl
  | app h₁ h₂ => exact Or.inr ⟨_, _, rfl, h₁, h₂⟩

private theorem approx_app_left_inv_aux : ∀ {x c : Lambda}, Approx x c → ∀ a b : Lambda,
    x = Lambda.app a b →
      x = Lambda.omega ∨ ∃ c₁ c₂, c = Lambda.app c₁ c₂ ∧ Approx a c₁ ∧ Approx b c₂ := by
  intro x c h
  cases h with
  | omega t => intro a b _; exact Or.inl rfl
  | var n => intro a b hx; exact absurd hx (by simp)
  | @app a' b' s t h₁ h₂ =>
      intro a b hx
      obtain ⟨e₁, e₂⟩ := Lambda.app.inj hx
      subst e₁; subst e₂
      exact Or.inr ⟨s, t, rfl, h₁, h₂⟩
  | lam _ => intro a b hx; exact absurd hx (by simp)

/-- Inversion on the *left* of the approximation order, at an application.  The first disjunct is
needed because `Ω` is itself an application. -/
theorem approx_app_left_inv {a b c : Lambda} (h : Approx (Lambda.app a b) c) :
    Lambda.app a b = Lambda.omega ∨ ∃ c₁ c₂, c = Lambda.app c₁ c₂ ∧ Approx a c₁ ∧ Approx b c₂ :=
  approx_app_left_inv_aux h a b rfl

/-- A direct approximant which is an application comes from an application with a variable
head — unless it is `Ω`. -/
theorem direct_eq_app_inv : ∀ {r a b : Lambda}, direct r = Lambda.app a b →
    direct r = Lambda.omega ∨ ∃ v w, a = direct v ∧ b = direct w ∧ headVar v = Bool.true := by
  intro r
  cases r with
  | var n => intro a b h; exact absurd h (by simp)
  | lam s => intro a b h; exact absurd h (by simp)
  | app v w =>
      intro a b h
      by_cases hv : headVar v = Bool.true
      · rw [direct_app, if_pos hv] at h
        obtain ⟨e₁, e₂⟩ := Lambda.app.inj h
        exact Or.inr ⟨v, w, e₁.symm, e₂.symm, hv⟩
      · exact Or.inl (by rw [direct_app, if_neg hv])

theorem direct_eq_lam_inv : ∀ {r a : Lambda}, direct r = Lambda.lam a →
    ∃ w, r = Lambda.lam w ∧ a = direct w := by
  intro r
  cases r with
  | var n => intro a h; exact absurd h (by simp)
  | lam s => intro a h; exact ⟨s, rfl, (Lambda.lam.inj h).symm⟩
  | app v w =>
      intro a h
      by_cases hv : headVar v = Bool.true
      · rw [direct_app, if_pos hv] at h; exact absurd h (by simp)
      · rw [direct_app, if_neg hv] at h; exact absurd h (by simp [Lambda.omega])

/-- **A direct approximant below `Ω` is `Ω`.** -/
theorem eq_omega_of_approx_direct_omega {r : Lambda} (h : Approx (direct r) Lambda.omega) :
    direct r = Lambda.omega := by
  rcases approx_app_inv (omega_eq_app ▸ h) with h' | ⟨a₁, a₂, ha, ha₁, -⟩
  · exact h'
  · rcases direct_eq_app_inv ha with h'' | ⟨v, w, rfl, -, hv⟩
    · exact h''
    · rcases approx_lam_inv ha₁ with h'' | ⟨a', ha', -⟩
      · exact absurd h'' (direct_ne_omega_of_headVar hv)
      · exact absurd ha' (direct_ne_lam_of_headVar hv a')

/-! ### Transitivity of the approximation order on direct approximants -/

theorem approx_direct_trans : ∀ (t r c : Lambda),
    Approx (direct r) (direct t) → Approx (direct t) c → Approx (direct r) c := by
  intro t
  induction t with
  | var n =>
      intro r c h₁ h₂
      rw [direct_var] at h₁ h₂
      cases h₂ with
      | var m => exact h₁
  | lam s ih =>
      intro r c h₁ h₂
      rw [direct_lam] at h₁ h₂
      rcases approx_lam_inv h₁ with h' | ⟨a', ha', ha⟩
      · rw [h']; exact Approx.omega _
      · cases h₂ with
        | lam hb =>
            obtain ⟨w, hrw, rfl⟩ := direct_eq_lam_inv ha'
            rw [ha']
            exact Approx.lam (ih w _ ha hb)
  | app s u ihs ihu =>
      intro r c h₁ h₂
      by_cases hs : headVar s = Bool.true
      · rw [direct_app, if_pos hs] at h₁ h₂
        rcases approx_app_left_inv h₂ with heq | ⟨c₁, c₂, rfl, hc₁, hc₂⟩
        · rw [omega_eq_app] at heq
          exact absurd (Lambda.app.inj heq).1 (direct_ne_lam_of_headVar hs _)
        · rcases approx_app_inv h₁ with h' | ⟨a₁, a₂, ha, ha₁, ha₂⟩
          · rw [h']; exact Approx.omega _
          · rcases direct_eq_app_inv ha with h'' | ⟨v, w, rfl, rfl, -⟩
            · rw [h'']; exact Approx.omega _
            · rw [ha]
              exact Approx.app (ihs v c₁ ha₁ hc₁) (ihu w c₂ ha₂ hc₂)
      · rw [direct_app, if_neg hs] at h₁
        rw [eq_omega_of_approx_direct_omega h₁]
        exact Approx.omega _

/-- **Direct approximants only grow along a reduction.** -/
theorem approx_direct_reduces {t u : Lambda} (h : Lambda.reduces t u) :
    Approx (direct t) (direct u) := by
  induction h with
  | refl v => exact Approx.refl (direct v)
  | @step a b c hab _ ih => exact approx_direct_trans b a (direct c) (approx_direct_step hab) ih

/-! ### The Böhm tree of a term -/

/-- **The Böhm tree of `M`**, presented by its finite approximants: the direct approximants of
the reducts of `M`.  They form a directed set in the approximation order. -/
def BohmTree (M : Lambda) : Set Lambda := {A | ∃ M', Lambda.reduces M M' ∧ A = direct M'}

theorem direct_mem_bohmTree {M M' : Lambda} (h : Lambda.reduces M M') :
    direct M' ∈ BohmTree M := ⟨M', h, rfl⟩

/-- `M`'s Böhm tree is dominated by `N`'s: every finite approximant of `M` is below one of
`N`. -/
def BohmLe (M N : Lambda) : Prop :=
  ∀ A ∈ BohmTree M, ∃ B ∈ BohmTree N, Approx A B

/-- Two terms have the same Böhm tree when their approximant sets are cofinal in each other. -/
def BohmEq (M N : Lambda) : Prop := BohmLe M N ∧ BohmLe N M

theorem bohmLe_iff {M N : Lambda} :
    BohmLe M N ↔
      ∀ M', Lambda.reduces M M' → ∃ N', Lambda.reduces N N' ∧ Approx (direct M') (direct N') := by
  constructor
  · intro h M' hM'
    obtain ⟨B, ⟨N', hN', rfl⟩, hAB⟩ := h (direct M') (direct_mem_bohmTree hM')
    exact ⟨N', hN', hAB⟩
  · rintro h A ⟨M', hM', rfl⟩
    obtain ⟨N', hN', hA⟩ := h M' hM'
    exact ⟨direct N', direct_mem_bohmTree hN', hA⟩

theorem BohmLe.refl (M : Lambda) : BohmLe M M :=
  bohmLe_iff.2 fun M' hM' => ⟨M', hM', Approx.refl _⟩

theorem BohmLe.trans {M N P : Lambda} (h₁ : BohmLe M N) (h₂ : BohmLe N P) : BohmLe M P := by
  refine bohmLe_iff.2 fun M' hM' => ?_
  obtain ⟨N', hN', hMN⟩ := bohmLe_iff.1 h₁ M' hM'
  obtain ⟨P', hP', hNP⟩ := bohmLe_iff.1 h₂ N' hN'
  exact ⟨P', hP', approx_direct_trans N' M' (direct P') hMN hNP⟩

theorem BohmEq.refl (M : Lambda) : BohmEq M M := ⟨BohmLe.refl M, BohmLe.refl M⟩

theorem BohmEq.symm {M N : Lambda} (h : BohmEq M N) : BohmEq N M := ⟨h.2, h.1⟩

theorem BohmEq.trans {M N P : Lambda} (h₁ : BohmEq M N) (h₂ : BohmEq N P) : BohmEq M P :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-! ### Böhm trees are conversion invariants -/

theorem bohmLe_of_reduces {M N : Lambda} (h : Lambda.reduces M N) : BohmLe M N :=
  bohmLe_iff.2 fun M' hM' => by
    obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem hM' h
    exact ⟨w, hw₂, approx_direct_reduces hw₁⟩

theorem bohmGe_of_reduces {M N : Lambda} (h : Lambda.reduces M N) : BohmLe N M :=
  bohmLe_iff.2 fun N' hN' => ⟨N', Lambda.reduces_trans h hN', Approx.refl _⟩

theorem bohmEq_of_reduces {M N : Lambda} (h : Lambda.reduces M N) : BohmEq M N :=
  ⟨bohmLe_of_reduces h, bohmGe_of_reduces h⟩

/-- **Böhm tree equality contains β-conversion.** -/
theorem bohmEq_of_conv {M N : Lambda} (h : Conv M N) : BohmEq M N := by
  obtain ⟨u, h₁, h₂⟩ := h
  exact (bohmEq_of_reduces h₁).trans (bohmEq_of_reduces h₂).symm

/-! ### The graph model factors through the Böhm tree -/

/-- Domination of Böhm trees is a semantic inequality — the approximation theorem. -/
theorem denot_le_of_bohmLe {M N : Lambda} (h : BohmLe M N) (ρ : Env) : denot M ρ ⊆ denot N ρ :=
  denot_subset_of_approx_reducts (bohmLe_iff.1 h) ρ

/-- **Böhm tree equality is contained in the theory of the graph model.** -/
theorem graph_of_bohmEq {M N : Lambda} (h : BohmEq M N) (ρ : Env) : denot M ρ = denot N ρ :=
  Set.Subset.antisymm (denot_le_of_bohmLe h.1 ρ) (denot_le_of_bohmLe h.2 ρ)

/-! ### The containment of `B` is strict -/

/-- The Böhm tree of `Ω` is `⊥`: its only approximant is `Ω` itself. -/
theorem bohmTree_omega : BohmTree Lambda.omega = {Lambda.omega} := by
  ext A
  constructor
  · rintro ⟨M', hM', rfl⟩
    rw [reduces_omega_eq hM' rfl]
    exact rfl
  · rintro rfl
    exact ⟨Lambda.omega, Lambda.reduces.refl _, rfl⟩

/-- The Böhm tree of `Ω I` is `⊥` as well. -/
theorem bohmTree_app_omega_I : BohmTree (Lambda.app Lambda.omega Lambda.I) = {Lambda.omega} := by
  ext A
  constructor
  · rintro ⟨M', hM', rfl⟩
    rw [LambdaTheory.reduces_omega_app_I_eq hM' rfl]
    exact rfl
  · rintro rfl
    exact ⟨Lambda.app Lambda.omega Lambda.I, Lambda.reduces.refl _, rfl⟩

/-- `Ω` and `Ω I` have the same Böhm tree, although they are not β-convertible. -/
theorem bohmEq_omega_app_omega_I : BohmEq Lambda.omega (Lambda.app Lambda.omega Lambda.I) := by
  constructor <;> refine fun A hA => ⟨A, ?_, Approx.refl A⟩
  · rw [bohmTree_app_omega_I]; rwa [bohmTree_omega] at hA
  · rw [bohmTree_omega]; rwa [bohmTree_app_omega_I] at hA

/-- **Böhm tree equality is strictly coarser than β-conversion.** -/
theorem exists_bohmEq_not_conv :
    ∃ M N : Lambda, IsClosed M ∧ IsClosed N ∧ BohmEq M N ∧ ¬ Conv M N :=
  ⟨Lambda.omega, Lambda.app Lambda.omega Lambda.I, omega_closed,
    LambdaTheory.app_omega_I_closed, bohmEq_omega_app_omega_I,
    LambdaTheory.not_conv_omega_app_omega_I⟩

/-- **The place of Böhm tree equality in the chain**: it is an equivalence relation containing
β-conversion strictly and contained in the theory of the graph model, which by
`Start/LambdaTheory.lean` is strictly contained in `Th(D∞) = H*`. -/
theorem bohmEq_between_beta_and_graph :
    (∀ M N : Lambda, Conv M N → BohmEq M N) ∧
      (∀ M N : Lambda, BohmEq M N → ∀ ρ : Env, denot M ρ = denot N ρ) ∧
      (∃ M N : Lambda, BohmEq M N ∧ ¬ Conv M N) :=
  ⟨fun _ _ h => bohmEq_of_conv h, fun _ _ h => graph_of_bohmEq h,
    ⟨Lambda.omega, Lambda.app Lambda.omega Lambda.I, bohmEq_omega_app_omega_I,
      LambdaTheory.not_conv_omega_app_omega_I⟩⟩

end Lambda

end
