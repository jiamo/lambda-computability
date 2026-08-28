/-
# The semantic half of Wadsworth's theorem: absence of a failure witness is an inequality

`Start/DinfWadsworthSharp.lean` reduces full abstraction of `D∞` to one purely semantic
principle, `ScottDinf.TagBelowSound`: if the comparison of two closed terms admits no finite
failure witness `Lambda.TagFail`, then the first is below the second in `D∞`.  This file proves
that principle.

The proof has two halves, which correspond to the two ways the comparison can descend.

* **A variable below a term** (`ScottDinf.theta_le_ddenot_of_not_tagFail_var`).  When the left
  hand side is one of the variables introduced by an η-expansion, no syntax is left on the left
  and the term on the right may be an *infinite* η-expansion of that variable, as `D∞` identifies
  the two (`Start/DinfEtaLimit.lean`).  The comparison is therefore carried out level by level in
  the inverse limit: `ScottDinf.theta_add_le_of_forall_dappN` feeds the binders of the node to
  both sides at the cost of one level per binder, and the arguments so produced come from a
  finite level, so the induction hypothesis applies to them verbatim.  When the node has more
  binders than there are levels left, the comparison bottoms out at level `0`, where a shorter
  spine is always dominated (`ScottDinf.app_zero_dappSeq_le`).
* **An approximant below a term**.  Here the left hand side is a finite approximant, so the
  descent is a structural induction; `D∞` being order-extensional
  (`ScottDinf.le_of_forall_dappN`), the two nodes may be compared after feeding them the same
  stack of arguments.

The approximation theorem (`ScottDinf.isLUB_ddenot_direct`) then lifts the second statement from
approximants to arbitrary terms.
-/

import Start.DinfSpine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ScottDinf

open Lambda

noncomputable section

/-! ## A variable below a term -/

/-- **A variable below a term.**  If the comparison of a single variable, named by the tag `t`,
against the term `N` admits no failure witness, then the value of that variable is below the
denotation of `N` at every finite level.

This is the point at which the comparison cannot be structural: `N` may be an infinite
η-expansion of the variable, in which case no finite part of `N` witnesses the inequality.  The
induction is therefore on the level `n` of the inverse limit. -/
theorem theta_le_ddenot_of_not_tagFail_var :
    ∀ (n : ℕ) {base t d₂ : ℕ} {τ₂ : ℕ → ℕ} {Y : Dinf} {N : Lambda} {ρ₂ : DEnv},
      ¬ Lambda.TagFail base (fun _ => t) (Lambda.var 0) τ₂ N →
      t < base → Lambda.freeBelow d₂ N → (∀ j, j < d₂ → τ₂ j < base) →
      (∀ j, j < d₂ → τ₂ j = t → ρ₂ j = Y) →
      theta n Y ≤ ddenot N ρ₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro base t d₂ τ₂ Y N ρ₂ hfail ht hfree hτ₂ hmatch
    have hleft : Lambda.reduces (Lambda.var 0)
        (Lambda.lamN 0 (Lambda.appList (Lambda.var 0) [])) := .refl _
    have hhnf : Lambda.HasHnf N := by
      by_contra hc
      exact hfail (Lambda.TagFail.nohnf hleft hc)
    obtain ⟨m, h₂, as₂, hN⟩ := Lambda.exists_spine_of_hasHnf hhnf
    have hfreeN : Lambda.freeBelow (d₂ + m) (Lambda.appList (Lambda.var h₂) as₂) :=
      (Lambda.freeBelow_lamN_iff m).1 (Lambda.freeBelow_reduces hN d₂ hfree)
    obtain ⟨hh₂, hargs₂⟩ := (Lambda.freeBelow_appList_iff as₂).1 hfreeN
    have hh₂' : h₂ < d₂ + m := hh₂
    -- no root failure: the head tags agree and the η-expanded arities agree
    have hroot : Lambda.headTag base (fun _ => t) 0 0 m = Lambda.headTag base τ₂ m h₂ 0 ∧
        ([] : List Lambda).length + m = as₂.length + 0 := by
      by_contra hc
      exact hfail (Lambda.TagFail.root (e₁ := m) (e₂ := 0) hleft hN (Or.inr rfl) (by omega)
        (by tauto))
    have hlen : as₂.length = m := by
      have h := hroot.2
      simp only [List.length_nil, Nat.zero_add, Nat.add_zero] at h
      omega
    have hL : Lambda.headTag base (fun _ => t) 0 0 m = t := by
      rw [Lambda.headTag, Lambda.expEnv, if_neg (by omega : ¬ (0 : ℕ) < 0)]
    have hR : Lambda.headTag base τ₂ m h₂ 0
        = if h₂ < m then base + 0 + h₂ else τ₂ (h₂ - m) := by
      rw [Lambda.headTag, Lambda.expEnv]
    have htag : t = (if h₂ < m then base + 0 + h₂ else τ₂ (h₂ - m)) := by
      rw [← hL, ← hR]; exact hroot.1
    have hh2m : m ≤ h₂ := by
      by_contra hlt
      rw [if_pos (by omega : h₂ < m)] at htag
      omega
    have htau : τ₂ (h₂ - m) = t := by
      rw [if_neg (by omega : ¬ h₂ < m)] at htag
      exact htag.symm
    have hheadY : ρ₂ (h₂ - m) = Y := hmatch _ (by omega) htau
    -- the induction hypothesis, applied to the `r`-th argument of the node
    have argle : ∀ (σ : DEnv) (y : Dinf) (r k : ℕ), r < m → k < n →
        σ (m - 1 - r) = y → (∀ i, σ (m + i) = ρ₂ i) →
        theta k y ≤ ddenot (Lambda.argTermOf as₂ r) σ := by
      intro σ y r k hr hk hσ hσ'
      have hd : ¬ Lambda.TagFail (base + (0 + m)) (Lambda.argEnvT base (fun _ => t) 0 m 0 r)
          (Lambda.argTermOf [] r) (Lambda.argEnvT base τ₂ m 0 as₂.length r)
          (Lambda.argTermOf as₂ r) := by
        intro hc
        exact hfail (Lambda.TagFail.arg (e₁ := m) (e₂ := 0) hleft hN (Or.inr rfl) (by omega)
          hroot.1 (by omega) (by omega) hc)
      rw [show Lambda.argEnvT base (fun _ => t) 0 m 0 r = fun _ => base + (0 + m - 1 - r) from by
            rw [Lambda.argEnvT, if_neg (by omega)],
        show Lambda.argTermOf ([] : List Lambda) r = Lambda.var 0 from by
            rw [Lambda.argTermOf, dif_neg (by simp)],
        show Lambda.argEnvT base τ₂ m 0 as₂.length r = Lambda.expEnv base τ₂ m 0 from by
            rw [Lambda.argEnvT, if_pos (by omega)]] at hd
      refine ih k hk (d₂ := d₂ + m) hd (by omega) ?_ ?_ ?_
      · have hterm : Lambda.argTermOf as₂ r = as₂[r]'(by omega) := by
          rw [Lambda.argTermOf, dif_pos (by omega)]
        rw [hterm]
        exact hargs₂ _ (List.getElem_mem _)
      · intro j hj
        rw [Lambda.expEnv]
        by_cases hjm : j < m
        · rw [if_pos hjm]; omega
        · rw [if_neg hjm]
          have := hτ₂ (j - m) (by omega)
          omega
      · intro j hj hje
        rw [Lambda.expEnv] at hje
        by_cases hjm : j < m
        · rw [if_pos hjm] at hje
          have hjeq : j = m - 1 - r := by omega
          subst hjeq
          exact hσ
        · rw [if_neg hjm] at hje
          have := hτ₂ (j - m) (by omega)
          omega
    rw [ddenot_reduces hN ρ₂]
    have hmain : ∀ A : ℕ → Dinf, (∀ i, i < n → theta (0 + i) (A i) = A i) →
        theta 0 (dappN Y A n) ≤
          dappN (ddenot (Lambda.lamN m (Lambda.appList (Lambda.var h₂) as₂)) ρ₂) A n := by
      intro A hA
      simp only [Nat.zero_add] at hA
      by_cases hmn : m ≤ n
      · -- enough levels: feed all the binders of the node to both sides
        obtain ⟨e, rfl⟩ : ∃ e, n = m + e := ⟨n - m, by omega⟩
        have hhead : envStack A m e ρ₂ h₂ = Y := by
          rw [envStack, if_neg (by omega : ¬ h₂ < m), hheadY]
        rw [dappN_ddenot_spine ρ₂ A, hlen, hhead, dappN_eq_dappSeq]
        refine le_trans (theta_le 0 _) (dappSeq_le_of_lt ?_)
        intro r hr
        by_cases hrm : r < m
        · have hval : envStack A m e ρ₂ (m - 1 - r) = A (m + e - 1 - r) := by
            rw [envStack, if_pos (by omega)]
            congr 1
            omega
          have hkey := argle (envStack A m e ρ₂) (A (m + e - 1 - r)) r (m + e - 1 - r)
            hrm (by omega) hval
            (fun i => by rw [envStack, if_neg (by omega), Nat.add_sub_cancel_left])
          rw [hA _ (by omega)] at hkey
          rw [argEnvD, if_pos (by omega)]
          exact hkey
        · rw [argEnvD, if_neg (by omega), Lambda.argTermOf, dif_neg (by omega), ddenot_var]
      · -- not enough levels: the comparison bottoms out at level `0`
        obtain ⟨c, rfl⟩ : ∃ c, m = n + c := ⟨m - n, by omega⟩
        obtain ⟨B, hBval⟩ : ∃ B : ℕ → Dinf, ∀ k, B k = if k < c then Dinf.botDinf else A (k - c) :=
          ⟨_, fun _ => rfl⟩
        have henv : envStack (fun _ => Dinf.botDinf) c 0 (envStack A n 0 ρ₂)
            = envStack B (n + c) 0 ρ₂ := by
          funext i
          simp only [envStack, Nat.zero_add]
          by_cases hic : i < c
          · rw [if_pos hic, if_pos (by omega : i < n + c), hBval, if_pos hic]
          · rw [if_neg hic]
            by_cases him : i < n + c
            · rw [if_pos (by omega : i - c < n), if_pos him, hBval, if_neg hic]
            · rw [if_neg (by omega : ¬ i - c < n), if_neg him]
              congr 1
              omega
        have hstrip : dappN (ddenot (Lambda.lamN (n + c)
            (Lambda.appList (Lambda.var h₂) as₂)) ρ₂) A n
            = ddenot (Lambda.lamN c (Lambda.appList (Lambda.var h₂) as₂))
                (envStack A n 0 ρ₂) := by
          rw [Lambda.lamN_add]
          have h1 := dappN_lamN n 0 (Lambda.lamN c (Lambda.appList (Lambda.var h₂) as₂)) ρ₂ A
          rw [Nat.add_zero, dappN_zero] at h1
          exact h1
        have hhead : envStack B (n + c) 0 ρ₂ h₂ = Y := by
          rw [envStack, if_neg (by omega : ¬ h₂ < n + c), hheadY]
        have hspine : ddenot (Lambda.appList (Lambda.var h₂) as₂) (envStack B (n + c) 0 ρ₂)
            = dappSeq Y (fun r => ddenot (Lambda.argTermOf as₂ r)
                (argEnvD B (n + c) 0 ρ₂ as₂.length r)) (as₂.length + 0) := by
          have h1 := dappN_ddenot_spine (b := n + c) (h := h₂) (e := 0) (as := as₂) ρ₂ B
          rw [dappN_lamN, dappN_zero, hhead] at h1
          exact h1
        rw [hstrip, theta_le_iff, ddenot_lamN_app_zero, henv, hspine, dappN_eq_dappSeq, hlen]
        refine app_zero_dappSeq_le (by omega) ?_
        intro r hr
        have hval : envStack B (n + c) 0 ρ₂ (n + c - 1 - r) = A (n - 1 - r) := by
          rw [envStack, if_pos (by omega), Nat.zero_add, hBval,
            if_neg (by omega : ¬ n + c - 1 - r < c)]
          congr 1
          omega
        have hkey := argle (envStack B (n + c) 0 ρ₂) (A (n - 1 - r)) r (n - 1 - r)
          (by omega) (by omega) hval
          (fun i => by rw [envStack, if_neg (by omega), Nat.add_sub_cancel_left])
        rw [hA _ (by omega)] at hkey
        rw [argEnvD, if_pos (by omega)]
        exact hkey
    have hgoal := theta_add_le_of_forall_dappN (q := 0) n hmain
    rwa [Nat.zero_add] at hgoal

/-- **A variable below a term.**  Absence of a failure witness for the comparison of a tagged
variable against a term is exactly the inequality in `D∞`. -/
theorem le_ddenot_of_not_tagFail_var {base t d₂ : ℕ} {τ₂ : ℕ → ℕ} {Y : Dinf} {N : Lambda}
    {ρ₂ : DEnv} (hfail : ¬ Lambda.TagFail base (fun _ => t) (Lambda.var 0) τ₂ N)
    (ht : t < base) (hfree : Lambda.freeBelow d₂ N) (hτ₂ : ∀ j, j < d₂ → τ₂ j < base)
    (hmatch : ∀ j, j < d₂ → τ₂ j = t → ρ₂ j = Y) : Y ≤ ddenot N ρ₂ :=
  le_of_forall_theta_le fun n =>
    theta_le_ddenot_of_not_tagFail_var n hfail ht hfree hτ₂ hmatch

end

end ScottDinf
