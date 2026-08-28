/-
# η-equal Böhm trees have the same denotation in `D∞`

`Start/BohmEta.lean` compares two Böhm trees of normal forms after η-expanding each node to the
common arity, naming variables by *tags* rather than by de Bruijn indices; `Lambda.TagEq` is the
resulting notion of η-equality.  This file is the semantic counterpart: two η-equal tagged trees
denote the same element of Scott's `D∞`.

The proof is a size induction on the pair of trees which mirrors, step by step, the syntactic
descent of `Start/BohmEta.lean`.  At each node both denotations are fed the same stack of `m`
arguments (`m` the common η-expanded arity), which is legitimate because `D∞` is extensional
(`ScottDinf.dinf_ext_dappN`); the node then exposes its head variable applied to its arguments
followed by the η-extra variables, and the induction hypothesis applies to the arguments.

* `ScottDinf.argEnvD`, `ScottDinf.argDepth` — the semantic counterparts of `Lambda.argEnvOf`;
* `ScottDinf.envStack_match` — matching tags name equal values in matching environments;
* `ScottDinf.ddenot_toTerm_eq_of_tagEq` — **η-equal closed Böhm trees are equal in `D∞`**.
-/

import Start.DinfApply
import Start.BohmEta

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ScottDinf

open Lambda

noncomputable section

/-! ## Environments for the arguments of an η-expanded node -/

/-- The environment in which the `r`-th argument of an η-expanded node is interpreted: one of the
arguments actually present is read inside the binders of the node, while an argument supplied by
the η-expansion is the corresponding element of the argument stack. -/
def argEnvD (A : ℕ → Dinf) (b e : ℕ) (ρ : DEnv) (k r : ℕ) : DEnv :=
  if r < k then envStack A b e ρ else fun _ => A (k + e - 1 - r)

/-- The free-variable depth of the `r`-th argument of an η-expanded node. -/
def argDepth (b d k r : ℕ) : ℕ := if r < k then b + d else 1

/-- The denotation of the tree `node 0 0 []`, the variable introduced by an η-expansion. -/
theorem ddenot_leaf (ρ : DEnv) : ddenot (BohmNF.node 0 0 []).toTerm ρ = ρ 0 := by
  rw [BohmNF.toTerm_node, List.map_nil, Lambda.lamN_zero, Lambda.appList_nil, ddenot_var]

/-! ## Matching tags name matching values -/

/-- Inside two nodes that have been η-expanded to the same arity, two variables carrying the same
tag denote the same value. -/
theorem envStack_match {base b₁ e₁ b₂ e₂ d₁ d₂ i j : ℕ} {τ₁ τ₂ : ℕ → ℕ} {ρ₁ ρ₂ : DEnv}
    {A : ℕ → Dinf} (hm : b₁ + e₁ = b₂ + e₂)
    (hτ₁ : ∀ i, i < d₁ → τ₁ i < base) (hτ₂ : ∀ j, j < d₂ → τ₂ j < base)
    (hmatch : ∀ i j, i < d₁ → j < d₂ → τ₁ i = τ₂ j → ρ₁ i = ρ₂ j)
    (hi : i < b₁ + d₁) (hj : j < b₂ + d₂)
    (h : expEnv base τ₁ b₁ e₁ i = expEnv base τ₂ b₂ e₂ j) :
    envStack A b₁ e₁ ρ₁ i = envStack A b₂ e₂ ρ₂ j := by
  unfold expEnv at h
  unfold envStack
  by_cases h1 : i < b₁ <;> by_cases h2 : j < b₂
  · rw [if_pos h1, if_pos h2] at h ⊢
    congr 1
    omega
  · rw [if_pos h1, if_neg h2] at h
    have := hτ₂ (j - b₂) (by omega)
    exact absurd h (by omega)
  · rw [if_neg h1, if_pos h2] at h
    have := hτ₁ (i - b₁) (by omega)
    exact absurd h (by omega)
  · rw [if_neg h1, if_neg h2] at h ⊢
    exact hmatch _ _ (by omega) (by omega) h

/-- The tags used inside the `r`-th argument of an η-expanded node stay below the new base. -/
theorem argEnvOf_lt_of_depth {base b e d r : ℕ} {τ : ℕ → ℕ} {as : List BohmNF}
    (hτ : ∀ i, i < d → τ i < base) (hr : r < as.length + e) :
    ∀ i, i < argDepth b d as.length r → argEnvOf base τ b e as r i < base + (b + e) := by
  intro i hi
  rw [argEnvOf]
  by_cases hlt : r < as.length
  · rw [if_pos hlt, expEnv]
    rw [argDepth, if_pos hlt] at hi
    by_cases hib : i < b
    · rw [if_pos hib]; omega
    · rw [if_neg hib]
      have := hτ (i - b) (by omega)
      omega
  · rw [if_neg hlt]
    omega

/-- The free variables of the `r`-th argument of an η-expanded node stay below `argDepth`. -/
theorem freeVarsBelow_argTreeOf {b h d : ℕ} {as : List BohmNF}
    (hx : BohmNF.FreeVarsBelow d (.node b h as)) (r : ℕ) :
    BohmNF.FreeVarsBelow (argDepth b d as.length r) (argTreeOf as r) := by
  cases hx with
  | @node d b h as _ hargs =>
      by_cases hr : r < as.length
      · rw [argTreeOf, dif_pos hr, argDepth, if_pos hr]
        exact hargs _ (List.getElem_mem _)
      · rw [argTreeOf, dif_neg hr, argDepth, if_neg hr]
        exact .node (by omega) (by intro a ha; exact absurd ha List.not_mem_nil)

/-- The cross-condition of the induction, propagated to the arguments of a node. -/
theorem argEnvD_match {base b₁ e₁ b₂ e₂ d₁ d₂ r i j : ℕ} {τ₁ τ₂ : ℕ → ℕ} {ρ₁ ρ₂ : DEnv}
    {as₁ as₂ : List BohmNF} {A : ℕ → Dinf}
    (hm : b₁ + e₁ = b₂ + e₂) (hlen : as₁.length + e₁ = as₂.length + e₂)
    (hτ₁ : ∀ i, i < d₁ → τ₁ i < base) (hτ₂ : ∀ j, j < d₂ → τ₂ j < base)
    (hmatch : ∀ i j, i < d₁ → j < d₂ → τ₁ i = τ₂ j → ρ₁ i = ρ₂ j)
    (hi : i < argDepth b₁ d₁ as₁.length r) (hj : j < argDepth b₂ d₂ as₂.length r)
    (h : argEnvOf base τ₁ b₁ e₁ as₁ r i = argEnvOf base τ₂ b₂ e₂ as₂ r j) :
    argEnvD A b₁ e₁ ρ₁ as₁.length r i = argEnvD A b₂ e₂ ρ₂ as₂.length r j := by
  rw [argEnvOf, argEnvOf] at h
  rw [argEnvD, argEnvD]
  rw [argDepth] at hi hj
  by_cases h1 : r < as₁.length <;> by_cases h2 : r < as₂.length
  · rw [if_pos h1, if_pos h2] at h ⊢
    rw [if_pos h1] at hi
    rw [if_pos h2] at hj
    exact envStack_match hm hτ₁ hτ₂ hmatch hi hj h
  · rw [if_pos h1, if_neg h2] at h ⊢
    rw [if_pos h1] at hi
    rw [expEnv] at h
    rw [envStack]
    by_cases hib : i < b₁
    · rw [if_pos hib] at h ⊢
      congr 1
      omega
    · rw [if_neg hib] at h
      have := hτ₁ (i - b₁) (by omega)
      exact absurd h (by omega)
  · rw [if_neg h1, if_pos h2] at h ⊢
    rw [if_pos h2] at hj
    rw [expEnv] at h
    rw [envStack]
    by_cases hjb : j < b₂
    · rw [if_pos hjb] at h ⊢
      congr 1
      omega
    · rw [if_neg hjb] at h
      have := hτ₂ (j - b₂) (by omega)
      exact absurd h (by omega)
  · rw [if_neg h1, if_neg h2] at h ⊢
    congr 1
    omega

/-! ## Feeding a stack of arguments to a node -/

/-- Feeding `b + e` arguments to the term of a node with `b` binders exposes the head variable
applied to the arguments of the node followed by the `e` arguments of the η-expansion. -/
theorem dappN_ddenot_node {b h e : ℕ} {as : List BohmNF} (ρ : DEnv) (A : ℕ → Dinf) :
    dappN (ddenot (BohmNF.node b h as).toTerm ρ) A (b + e)
      = dappSeq (envStack A b e ρ h)
          (fun r => ddenot (argTreeOf as r).toTerm (argEnvD A b e ρ as.length r))
          (as.length + e) := by
  have hG : ∀ r, ∀ _ : r < (as.map BohmNF.toTerm).length,
      (fun r => ddenot (argTreeOf as r).toTerm (argEnvD A b e ρ as.length r)) r
        = ddenot ((as.map BohmNF.toTerm)[r]) (envStack A b e ρ) := by
    intro r hr
    have hr' : r < as.length := by simpa using hr
    simp only [argTreeOf, dif_pos hr', argEnvD, if_pos hr', List.getElem_map]
  have h1 : ddenot (Lambda.appList (Lambda.var h) (as.map BohmNF.toTerm)) (envStack A b e ρ)
      = dappSeq (envStack A b e ρ h)
          (fun r => ddenot (argTreeOf as r).toTerm (argEnvD A b e ρ as.length r)) as.length := by
    rw [ddenot_appList _ _ _ _ hG, ddenot_var, List.length_map]
  rw [BohmNF.toTerm_node, dappN_lamN, h1, dappN_eq_dappSeq, dappSeq_add]
  refine dappSeq_congr rfl ?_
  intro s hs
  have hns : ¬ as.length + s < as.length := by omega
  simp only [argTreeOf, dif_neg hns, argEnvD, if_neg hns]
  rw [ddenot_leaf]
  congr 1
  omega

/-! ## η-equal trees are equal in `D∞` -/

theorem ddenot_toTerm_eq_of_tagEq_aux : ∀ (n : ℕ) {x y : BohmNF}, x.size + y.size ≤ n →
    ∀ {base d₁ d₂ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {ρ₁ ρ₂ : DEnv},
      TagEq base τ₁ x τ₂ y → BohmNF.FreeVarsBelow d₁ x → BohmNF.FreeVarsBelow d₂ y →
      (∀ i, i < d₁ → τ₁ i < base) → (∀ j, j < d₂ → τ₂ j < base) →
      (∀ i j, i < d₁ → j < d₂ → τ₁ i = τ₂ j → ρ₁ i = ρ₂ j) →
      ddenot x.toTerm ρ₁ = ddenot y.toTerm ρ₂ := by
  intro n
  induction n with
  | zero =>
      intro x y hn
      have := x.size_pos
      have := y.size_pos
      omega
  | succ n ih =>
      intro x y hn base d₁ d₂ τ₁ τ₂ ρ₁ ρ₂ hteq hx hy hτ₁ hτ₂ hmatch
      cases hteq with
      | @node base τ₁ τ₂ b₁ h₁ e₁ b₂ h₂ e₂ as₁ as₂ hmin hm hhead hlen hargs =>
          have hh₁ : h₁ < b₁ + d₁ := by cases hx with | node hh _ => exact hh
          have hh₂ : h₂ < b₂ + d₂ := by cases hy with | node hh _ => exact hh
          refine dinf_ext_dappN (b₁ + e₁) _ _ fun A => ?_
          conv_rhs => rw [hm]
          rw [dappN_ddenot_node ρ₁ A, dappN_ddenot_node ρ₂ A, ← hlen]
          refine dappSeq_congr ?_ ?_
          · exact envStack_match hm hτ₁ hτ₂ hmatch hh₁ hh₂ hhead
          · intro r hr
            have hsize : (argTreeOf as₁ r).size + (argTreeOf as₂ r).size ≤ n := by
              have hn₁ := BohmNF.size_argTreeOf as₁ r b₁ h₁
              have hn₂ := BohmNF.size_argTreeOf as₂ r b₂ h₂
              by_cases h1 : r < as₁.length
              · have := BohmNF.size_argTreeOf_lt (b := b₁) (h := h₁) h1
                omega
              · by_cases h2 : r < as₂.length
                · have := BohmNF.size_argTreeOf_lt (b := b₂) (h := h₂) h2
                  omega
                · rcases hmin with rfl | rfl <;> omega
            exact ih hsize (hargs r hr) (freeVarsBelow_argTreeOf hx r)
              (freeVarsBelow_argTreeOf hy r)
              (argEnvOf_lt_of_depth hτ₁ hr)
              (by
                have := argEnvOf_lt_of_depth (b := b₂) (e := e₂) (d := d₂) (as := as₂) hτ₂
                  (show r < as₂.length + e₂ by omega)
                rw [hm]
                exact this)
              (fun i j hi hj hij => argEnvD_match hm hlen hτ₁ hτ₂ hmatch hi hj hij)

/-- **η-equal closed Böhm trees have the same denotation in `D∞`.** -/
theorem ddenot_toTerm_eq_of_tagEq {x y : BohmNF} (hx : BohmNF.FreeVarsBelow 0 x)
    (hy : BohmNF.FreeVarsBelow 0 y) (h : TagEq 0 (fun _ => 0) x (fun _ => 0) y) (ρ₁ ρ₂ : DEnv) :
    ddenot x.toTerm ρ₁ = ddenot y.toTerm ρ₂ :=
  ddenot_toTerm_eq_of_tagEq_aux (x.size + y.size) le_rfl h hx hy
    (fun _ hi => absurd hi (by omega)) (fun _ hj => absurd hj (by omega))
    (fun _ _ hi _ _ => absurd hi (by omega))

end

end ScottDinf
