/-
# Spines, stacks of arguments and finite levels in `D∞`

`Start/DinfApply.lean` provides the calculus of iterated application (`ScottDinf.dappSeq`,
`ScottDinf.dappN`, `ScottDinf.envStack`) that is used to compare two Böhm trees node by node.
Comparing an *approximant* against an *arbitrary term* — the semantic half of Wadsworth's
theorem — needs three further ingredients, which is what this file supplies.

* **Order extensionality.**  `ScottDinf.le_of_forall_Phi_le` and `ScottDinf.le_of_forall_dappN`:
  an inequality in `D∞` may be checked after feeding any fixed number of arguments to both sides.
* **Stripping binders one finite level at a time.**  `ScottDinf.theta_add_le_of_forall_dappN`
  iterates `ScottDinf.theta_succ_le_of_forall_psi`: to prove `theta (q + j) x ≤ v` it is enough
  to compare `x` and `v` after feeding `j` arguments, at the cost of `j` levels — and the
  arguments so produced come from the finite levels, so they are their own approximations.
* **The base level.**  `ScottDinf.app_zero_dappSeq_le`: at level `0` the comparison tolerates a
  *shorter* spine on the left, because applying an argument only increases the base component.

Finally `ScottDinf.dappN_ddenot_spine` is the term-level counterpart of
`ScottDinf.dappN_ddenot_node`: feeding `b + e` arguments to `λ…λ. x M₁ … M_k` exposes the head
variable applied to the arguments of the node followed by the `e` variables of the η-expansion.
-/

import Start.DinfApprox
import Start.DinfEtaLimit
import Start.DinfBohmEta
import Start.TagFail

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

open Lambda

noncomputable section

/-! ## Order extensionality -/

/-- **`D∞` is order-extensional**: an inequality may be checked on all arguments. -/
theorem le_of_forall_Phi_le {x v : Dinf} (h : ∀ a : Dinf, Phi x a ≤ Phi v a) : x ≤ v := by
  have hf : Phi x ≤ Phi v := h
  have h' := Phi_le_iff.mp hf
  rwa [Psi_Phi] at h'

/-- Iterated application is monotone. -/
theorem dappSeq_mono {x y : Dinf} {F G : ℕ → Dinf} (hxy : x ≤ y) (hFG : ∀ r, F r ≤ G r) :
    ∀ n : ℕ, dappSeq x F n ≤ dappSeq y G n := by
  intro n
  induction n with
  | zero => exact hxy
  | succ n ih =>
      rw [dappSeq_succ, dappSeq_succ]
      exact le_trans (Phi_mono ih _) ((Phi (dappSeq y G n)).monotone (hFG n))

/-- Iterated application is monotone in the arguments actually used. -/
theorem dappSeq_le_of_lt {x : Dinf} {F G : ℕ → Dinf} :
    ∀ {n : ℕ}, (∀ r, r < n → F r ≤ G r) → dappSeq x F n ≤ dappSeq x G n := by
  intro n
  induction n with
  | zero => intro _; exact le_refl _
  | succ n ih =>
      intro h
      rw [dappSeq_succ, dappSeq_succ]
      exact le_trans (Phi_mono (ih fun r hr => h r (by omega)) _)
        ((Phi (dappSeq x G n)).monotone (h n (by omega)))

/-- Feeding a stack of arguments is monotone. -/
theorem dappN_mono {x y : Dinf} (A : ℕ → Dinf) (hxy : x ≤ y) :
    ∀ m : ℕ, dappN x A m ≤ dappN y A m := by
  intro m
  induction m generalizing x y with
  | zero => exact hxy
  | succ m ih => exact ih (Phi_mono hxy _)

/-- **Order extensionality for a stack of arguments.** -/
theorem le_of_forall_dappN {m : ℕ} {x v : Dinf} (h : ∀ A : ℕ → Dinf, dappN x A m ≤ dappN v A m) :
    x ≤ v := by
  induction m generalizing x v with
  | zero => exact h (fun _ => Dinf.botDinf)
  | succ m ih =>
      refine le_of_forall_Phi_le fun a => ?_
      refine ih fun A => ?_
      have hA' := h (fun i => if i = m then a else A i)
      rw [dappN_succ, dappN_succ, if_pos rfl] at hA'
      rwa [dappN_congr (A := fun i => if i = m then a else A i) (B := A)
          (fun k hk => if_neg (by omega)),
        dappN_congr (A := fun i => if i = m then a else A i) (B := A)
          (fun k hk => if_neg (by omega))] at hA'

/-! ## Stripping binders, one finite level at a time -/

/-- **Feeding `j` arguments costs `j` levels.**  To prove `theta (q + j) x ≤ v` it suffices to
compare the two sides after feeding `j` arguments, keeping only level `q`.  The arguments that
have to be considered all come from a finite level — `A i` from level `q + i` — hence are their
own approximation there. -/
theorem theta_add_le_of_forall_dappN {q : ℕ} : ∀ (j : ℕ) {x v : Dinf},
    (∀ A : ℕ → Dinf, (∀ i, i < j → theta (q + i) (A i) = A i) →
      theta q (dappN x A j) ≤ dappN v A j) → theta (q + j) x ≤ v := by
  intro j
  induction j with
  | zero => intro x v h; exact h (fun _ => Dinf.botDinf) (fun i hi => absurd hi (by omega))
  | succ j ih =>
      intro x v h
      rw [show q + (j + 1) = (q + j) + 1 from by omega]
      refine theta_succ_le_of_forall_psi fun z => ?_
      refine ih (x := Phi x (psiFun (q + j) z)) (v := Phi v (psiFun (q + j) z)) ?_
      intro A hA
      have hA' := h (fun i => if i = j then psiFun (q + j) z else A i) ?_
      · rw [dappN_succ, dappN_succ, if_pos rfl] at hA'
        rwa [dappN_congr (A := fun i => if i = j then psiFun (q + j) z else A i) (B := A)
            (fun k hk => if_neg (by omega)),
          dappN_congr (A := fun i => if i = j then psiFun (q + j) z else A i) (B := A)
            (fun k hk => if_neg (by omega))] at hA'
      · intro i hi
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          exact theta_psiFun _ z
        · simp only [if_neg hij]
          exact hA i (by omega)

/-! ## The base level -/

/-- At the base level, applying one more argument only increases the value. -/
theorem app_zero_dappSeq_le_of_le (x : Dinf) (G : ℕ → Dinf) :
    ∀ (j m : ℕ), j ≤ m → (dappSeq x G j).app 0 ≤ (dappSeq x G m).app 0 := by
  intro j m hjm
  induction m, hjm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih => exact le_trans ih (app_zero_le _ _)

/-- **The base level tolerates a shorter spine.**  At level `0` a spine may be compared with a
longer one, as long as the arguments it does have are dominated. -/
theorem app_zero_dappSeq_le {x : Dinf} {F G : ℕ → Dinf} {j m : ℕ} (hjm : j ≤ m)
    (hFG : ∀ r, r < j → F r ≤ G r) :
    (dappSeq x F j).app 0 ≤ (dappSeq x G m).app 0 := by
  exact le_trans (Dinf.le_def.mp (dappSeq_le_of_lt hFG) 0)
    (app_zero_dappSeq_le_of_le x G j m hjm)

/-! ## Splitting an abstraction prefix -/

theorem _root_.Lambda.lamN_add : ∀ (a b : ℕ) (t : Lambda),
    Lambda.lamN (a + b) t = Lambda.lamN a (Lambda.lamN b t) := by
  intro a
  induction a with
  | zero => intro b t; rw [Nat.zero_add, Lambda.lamN_zero]
  | succ a ih =>
      intro b t
      rw [show a + 1 + b = (a + b) + 1 from by omega, Lambda.lamN_succ, Lambda.lamN_succ, ih]

/-! ## Denotations of abstractions at the base level -/

/-- At the base level an abstraction is its body with the bound variable set to `⊥`. -/
theorem ddenot_lamN_app_zero : ∀ (c : ℕ) (t : Lambda) (ρ : DEnv),
    (ddenot (Lambda.lamN c t) ρ).app 0
      = (ddenot t (envStack (fun _ => Dinf.botDinf) c 0 ρ)).app 0 := by
  intro c
  induction c with
  | zero => intro t ρ; rw [Lambda.lamN_zero, envStack_zero]
  | succ c ih =>
      intro t ρ
      rw [Lambda.lamN_succ, ddenot_lam_app_zero, psiFun_botD, ih]
      congr 2
      exact envStack_succ (fun _ => Dinf.botDinf) c 0 ρ

/-! ## Feeding a stack of arguments to a spine -/

/-- The denotation of the variable introduced by an η-expansion. -/
theorem ddenot_argTerm_leaf (ρ : DEnv) : ddenot (Lambda.var 0) ρ = ρ 0 := rfl

/-- **Feeding `b + e` arguments to a spine.**  The term `λ…λ. x M₁ … M_k` with `b` binders, fed
`b + e` arguments, exposes the head variable applied to the arguments of the node followed by
the `e` variables supplied by the η-expansion. -/
theorem dappN_ddenot_spine {b h e : ℕ} {as : List Lambda} (ρ : DEnv) (A : ℕ → Dinf) :
    dappN (ddenot (Lambda.lamN b (Lambda.appList (Lambda.var h) as)) ρ) A (b + e)
      = dappSeq (envStack A b e ρ h)
          (fun r => ddenot (argTermOf as r) (argEnvD A b e ρ as.length r))
          (as.length + e) := by
  have hG : ∀ r, ∀ _ : r < as.length,
      (fun r => ddenot (argTermOf as r) (argEnvD A b e ρ as.length r)) r
        = ddenot as[r] (envStack A b e ρ) := by
    intro r hr
    simp only [argTermOf, dif_pos hr, argEnvD, if_pos hr]
  have h1 : ddenot (Lambda.appList (Lambda.var h) as) (envStack A b e ρ)
      = dappSeq (envStack A b e ρ h)
          (fun r => ddenot (argTermOf as r) (argEnvD A b e ρ as.length r)) as.length := by
    rw [ddenot_appList _ _ _ _ hG, ddenot_var]
  rw [dappN_lamN, h1, dappN_eq_dappSeq, dappSeq_add]
  refine dappSeq_congr rfl ?_
  intro s hs
  have hns : ¬ as.length + s < as.length := by omega
  simp only [argTermOf, dif_neg hns, argEnvD, if_neg hns]
  rw [ddenot_argTerm_leaf]
  congr 1
  omega

end

end ScottDinf
