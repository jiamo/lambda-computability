/-
# Wadsworth's theorem: `D∞` is fully abstract for the untyped λ-calculus

`Start/DinfWadsworthSharp.lean` reduces full abstraction of `D∞` to the single semantic principle
`ScottDinf.TagBelowSound`: if the comparison of two closed terms admits no finite failure witness
`Lambda.TagFail`, then the first is below the second in `D∞`.  `Start/DinfTagBelow.lean` proves the
hard half of that principle, the one that no structural induction can reach — a *variable* below a
term, where the term may be an infinite η-expansion of the variable.  This file supplies the other
half and assembles the theorem.

* `ScottDinf.le_ddenot_of_not_tagFail_approx` — **an approximant below a term**.  The left hand
  side is a finite approximant `A` of the direct approximant of `M`, so the descent is a size
  induction on `A`, driven by the shape lemma `Lambda.approx_direct_shape`; `D∞` being
  order-extensional (`ScottDinf.le_of_forall_dappN`), the two nodes are compared after feeding
  them the same stack of arguments.  The arguments supplied by the η-expansion are exactly the
  variables handled by `ScottDinf.le_ddenot_of_not_tagFail_var`.
* `ScottDinf.tagBelowSound` — **`ScottDinf.TagBelowSound`, proved**.  The approximation theorem
  `ScottDinf.isLUB_ddenot_direct` lifts the previous statement from approximants to arbitrary
  terms.
* `ScottDinf.separatesApprox`, `ScottDinf.ddenot_le_iff_not_tagFail_unconditional`,
  `ScottDinf.obsEqHnf_iff_ddenot_eq` — the consequences, now unconditional: the separation
  principle of `Start/DinfWadsworth.lean`, the characterisation of the `D∞` order by absence of a
  failure witness, and **Wadsworth's full abstraction theorem** for arbitrary closed terms.
-/

import Start.DinfTagBelow
import Start.ApproxShape
import Start.DinfWadsworthSharp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-- A failure witness against a reduct is a failure witness against the term. -/
theorem tagFail_of_reduces {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M M' N : Lambda}
    (h : Lambda.reduces M M') (hf : TagFail base τ₁ M' τ₂ N) : TagFail base τ₁ M τ₂ N := by
  cases hf with
  | nohnf hM hN => exact TagFail.nohnf (Lambda.reduces_trans h hM) hN
  | root hM hN hmin hm hne =>
      exact TagFail.root (Lambda.reduces_trans h hM) hN hmin hm hne
  | arg hM hN hmin hm hhead hlen hr hd =>
      exact TagFail.arg (Lambda.reduces_trans h hM) hN hmin hm hhead hlen hr hd

/-- The free variables of the `r`-th argument of an η-expanded node stay below
`ScottDinf.argDepth`. -/
theorem freeBelow_argTermOf {b h d : ℕ} {as : List Lambda}
    (hx : freeBelow d (lamN b (appList (Lambda.var h) as))) (r : ℕ) :
    freeBelow (ScottDinf.argDepth b d as.length r) (argTermOf as r) := by
  have hb := (freeBelow_lamN_iff b).1 hx
  obtain ⟨-, hargs⟩ := (freeBelow_appList_iff as).1 hb
  by_cases hr : r < as.length
  · rw [argTermOf, dif_pos hr, ScottDinf.argDepth, if_pos hr]
    have := hargs _ (List.getElem_mem hr)
    exact freeBelow_mono (by omega) this
  · rw [argTermOf, dif_neg hr, ScottDinf.argDepth, if_neg hr]
    exact (by omega : (0 : ℕ) < 1)

/-- The tags used inside the `r`-th argument of an η-expanded node stay below the new base. -/
theorem argEnvT_lt_of_depth {base b e d k r : ℕ} {τ : ℕ → ℕ}
    (hτ : ∀ i, i < d → τ i < base) (hr : r < k + e) :
    ∀ i, i < ScottDinf.argDepth b d k r → argEnvT base τ b e k r i < base + (b + e) := by
  intro i hi
  rw [argEnvT]
  by_cases hlt : r < k
  · rw [if_pos hlt, expEnv]
    rw [ScottDinf.argDepth, if_pos hlt] at hi
    by_cases hib : i < b
    · rw [if_pos hib]; omega
    · rw [if_neg hib]
      have := hτ (i - b) (by omega)
      omega
  · rw [if_neg hlt]
    omega

end Lambda

namespace ScottDinf

open Lambda

noncomputable section

/-! ## Monotonicity of a spine -/

/-- Iterated application is monotone in the head and in the arguments actually used. -/
theorem dappSeq_mono_lt {x y : Dinf} {F G : ℕ → Dinf} (hxy : x ≤ y) :
    ∀ {n : ℕ}, (∀ r, r < n → F r ≤ G r) → dappSeq x F n ≤ dappSeq y G n := by
  intro n
  induction n with
  | zero => intro _; exact hxy
  | succ n ih =>
      intro h
      rw [dappSeq_succ, dappSeq_succ]
      exact le_trans (Phi_mono (ih fun r hr => h r (by omega)) _)
        ((Phi (dappSeq y G n)).monotone (h n (by omega)))

/-! ## The cross-condition, propagated to the arguments of a node -/

/-- Matching tags name equal values, inside the `r`-th argument of two η-expanded nodes.  This is
`ScottDinf.argEnvD_match` for terms: only the arities of the two nodes matter. -/
theorem argEnvD_match_len {base b₁ e₁ b₂ e₂ d₁ d₂ k₁ k₂ r i j : ℕ} {τ₁ τ₂ : ℕ → ℕ} {ρ₁ ρ₂ : DEnv}
    {A : ℕ → Dinf} (hm : b₁ + e₁ = b₂ + e₂) (hlen : k₁ + e₁ = k₂ + e₂)
    (hτ₁ : ∀ i, i < d₁ → τ₁ i < base) (hτ₂ : ∀ j, j < d₂ → τ₂ j < base)
    (hmatch : ∀ i j, i < d₁ → j < d₂ → τ₁ i = τ₂ j → ρ₁ i = ρ₂ j)
    (hi : i < argDepth b₁ d₁ k₁ r) (hj : j < argDepth b₂ d₂ k₂ r)
    (h : Lambda.argEnvT base τ₁ b₁ e₁ k₁ r i = Lambda.argEnvT base τ₂ b₂ e₂ k₂ r j) :
    argEnvD A b₁ e₁ ρ₁ k₁ r i = argEnvD A b₂ e₂ ρ₂ k₂ r j := by
  rw [Lambda.argEnvT, Lambda.argEnvT] at h
  rw [argEnvD, argEnvD]
  rw [argDepth] at hi hj
  by_cases h1 : r < k₁ <;> by_cases h2 : r < k₂
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

/-! ## An approximant below a term -/

/-- **An approximant below a term.**  If `A` approximates the direct approximant of `M` and the
comparison of `M` against `N` admits no failure witness, then `A` is below `N` in `D∞`, in any two
environments which give equal values to variables carrying equal tags.

The descent is a size induction on `A`: the shape lemma `Lambda.approx_direct_shape` either
dominates `A` by an unsolvable term — in which case `A` denotes `⊥` — or exposes a common spine
for `A` and `M`, whose arguments are compared after feeding both sides the same stack. -/
theorem le_ddenot_of_not_tagFail_approx : ∀ (n : ℕ) {A : Lambda}, Lambda.size A ≤ n →
    ∀ {base d₁ d₂ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M N : Lambda} {ρ₁ ρ₂ : DEnv},
      Lambda.Approx A (Lambda.direct M) →
      ¬ Lambda.TagFail base τ₁ M τ₂ N →
      Lambda.freeBelow d₁ M → Lambda.freeBelow d₂ N →
      (∀ i, i < d₁ → τ₁ i < base) → (∀ j, j < d₂ → τ₂ j < base) →
      (∀ i j, i < d₁ → j < d₂ → τ₁ i = τ₂ j → ρ₁ i = ρ₂ j) →
      ddenot A ρ₁ ≤ ddenot N ρ₂ := by
  intro n
  induction n with
  | zero =>
      intro A hsize
      have := Lambda.size_pos A
      omega
  | succ n ih =>
      intro A hsize base d₁ d₂ τ₁ τ₂ M N ρ₁ ρ₂ happrox hfail hM hN hτ₁ hτ₂ hmatch
      rcases Lambda.approx_direct_shape A (Lambda.direct M) happrox M rfl with
        ⟨C, hAC, hC⟩ | ⟨b, h, as, bs, rfl, hMeq, hall⟩
      · have h1 : ddenot A ρ₁ ≤ ddenot C ρ₁ := ddenot_approx_le hAC ρ₁
        have h2 : ddenot C ρ₁ = Dinf.botDinf := by
          by_contra hc
          exact hC (hasHnf_of_ddenot_ne_botDinf hc)
        rw [h2] at h1
        exact le_trans h1 (Dinf.botDinf_le _)
      · subst hMeq
        have hlenab : as.length = bs.length := hall.length_eq
        -- the right hand side has a head normal form
        have hhnf : Lambda.HasHnf N := by
          by_contra hc
          exact hfail (Lambda.TagFail.nohnf (.refl _) hc)
        obtain ⟨b₂, h₂, as₂, hNred⟩ := Lambda.exists_spine_of_hasHnf hhnf
        obtain ⟨e₁, e₂, hmin, hm⟩ : ∃ e₁ e₂ : ℕ, (e₁ = 0 ∨ e₂ = 0) ∧ b + e₁ = b₂ + e₂ :=
          ⟨b₂ - b, b - b₂, by omega, by omega⟩
        -- no failure at the root: the head tags agree and the η-expanded arities agree
        have hroot : Lambda.headTag base τ₁ b h e₁ = Lambda.headTag base τ₂ b₂ h₂ e₂ ∧
            bs.length + e₁ = as₂.length + e₂ := by
          by_contra hc
          exact hfail (Lambda.TagFail.root (.refl _) hNred hmin hm (by tauto))
        -- free variable bookkeeping
        have hfreeM : Lambda.freeBelow (d₁ + b) (Lambda.appList (Lambda.var h) bs) :=
          (Lambda.freeBelow_lamN_iff b).1 hM
        obtain ⟨hh₁, -⟩ := (Lambda.freeBelow_appList_iff bs).1 hfreeM
        have hh₁' : h < d₁ + b := hh₁
        have hNfree : Lambda.freeBelow d₂ (Lambda.lamN b₂ (Lambda.appList (Lambda.var h₂) as₂)) :=
          Lambda.freeBelow_reduces hNred d₂ hN
        have hfreeN : Lambda.freeBelow (d₂ + b₂) (Lambda.appList (Lambda.var h₂) as₂) :=
          (Lambda.freeBelow_lamN_iff b₂).1 hNfree
        obtain ⟨hh₂, -⟩ := (Lambda.freeBelow_appList_iff as₂).1 hfreeN
        have hh₂' : h₂ < d₂ + b₂ := hh₂
        -- the comparison of the two nodes
        rw [ddenot_reduces hNred ρ₂]
        refine le_of_forall_dappN (m := b + e₁) fun A' => ?_
        rw [dappN_ddenot_spine ρ₁ A']
        conv_rhs => rw [hm]
        rw [dappN_ddenot_spine ρ₂ A', hlenab, hroot.2]
        refine dappSeq_mono_lt
          (le_of_eq (envStack_match hm hτ₁ hτ₂ hmatch (by omega) (by omega) hroot.1)) ?_
        intro r hr
        -- the tags and environments inside the `r`-th argument
        have hτ₁' : ∀ i, i < argDepth b d₁ bs.length r →
            Lambda.argEnvT base τ₁ b e₁ bs.length r i < base + (b + e₁) :=
          Lambda.argEnvT_lt_of_depth hτ₁ (by omega)
        have hτ₂' : ∀ j, j < argDepth b₂ d₂ as₂.length r →
            Lambda.argEnvT base τ₂ b₂ e₂ as₂.length r j < base + (b + e₁) := by
          intro j hj
          have := Lambda.argEnvT_lt_of_depth (b := b₂) (e := e₂) (d := d₂) (k := as₂.length)
            hτ₂ (show r < as₂.length + e₂ by omega) j hj
          omega
        have hmatch' : ∀ i j, i < argDepth b d₁ bs.length r → j < argDepth b₂ d₂ as₂.length r →
            Lambda.argEnvT base τ₁ b e₁ bs.length r i
              = Lambda.argEnvT base τ₂ b₂ e₂ as₂.length r j →
            argEnvD A' b e₁ ρ₁ bs.length r i = argEnvD A' b₂ e₂ ρ₂ as₂.length r j :=
          fun i j hi hj hij => argEnvD_match_len hm hroot.2 hτ₁ hτ₂ hmatch hi hj hij
        have hfreeArg₂ : Lambda.freeBelow (argDepth b₂ d₂ as₂.length r)
            (Lambda.argTermOf as₂ r) := Lambda.freeBelow_argTermOf hNfree r
        -- the failure witness that would come from the `r`-th argument
        have hargfail : ¬ Lambda.TagFail (base + (b + e₁))
            (Lambda.argEnvT base τ₁ b e₁ bs.length r) (Lambda.argTermOf bs r)
            (Lambda.argEnvT base τ₂ b₂ e₂ as₂.length r) (Lambda.argTermOf as₂ r) := by
          intro hc
          exact hfail (Lambda.TagFail.arg (.refl _) hNred hmin hm hroot.1 hroot.2 (by omega) hc)
        by_cases hrk : r < bs.length
        · -- an argument of the node: the induction hypothesis applies
          have hAr : Lambda.Approx (Lambda.argTermOf as r)
              (Lambda.direct (Lambda.argTermOf bs r)) := by
            have hra : r < as.length := by omega
            have := hall.get (by omega) (by omega)
            rw [List.get_eq_getElem, List.get_eq_getElem] at this
            rw [Lambda.argTermOf, dif_pos hra, Lambda.argTermOf, dif_pos hrk]
            exact this
          have hsz : Lambda.size (Lambda.argTermOf as r) ≤ n := by
            have hra : r < as.length := by omega
            have hmem : as[r] ∈ as := List.getElem_mem hra
            have h1 := Lambda.size_lt_appList as (Lambda.var h) as[r] hmem
            have h2 := Lambda.size_lamN b (Lambda.appList (Lambda.var h) as)
            rw [Lambda.argTermOf, dif_pos hra]
            omega
          have hfreeArg₁ : Lambda.freeBelow (argDepth b d₁ bs.length r)
              (Lambda.argTermOf bs r) := Lambda.freeBelow_argTermOf hM r
          exact ih hsz hAr hargfail hfreeArg₁ hfreeArg₂ hτ₁' hτ₂' hmatch'
        · -- a variable supplied by the η-expansion
          have hrk' : ¬ r < as.length := by omega
          rw [Lambda.argTermOf, dif_neg hrk', argEnvD, if_neg hrk, ddenot_var]
          have hleft : Lambda.argTermOf bs r = Lambda.var 0 := by
            rw [Lambda.argTermOf, dif_neg hrk]
          have htagl : Lambda.argEnvT base τ₁ b e₁ bs.length r
              = fun _ => base + (bs.length + e₁ - 1 - r) := by
            rw [Lambda.argEnvT, if_neg hrk]
          rw [hleft, htagl] at hargfail
          refine le_ddenot_of_not_tagFail_var (base := base + (b + e₁)) hargfail (by omega)
            hfreeArg₂ hτ₂' ?_
          intro j hj hjt
          have hi0 : (0 : ℕ) < argDepth b d₁ bs.length r := by
            rw [argDepth, if_neg hrk]; omega
          have hkey := hmatch' 0 j hi0 hj (by rw [htagl]; exact hjt.symm)
          rw [argEnvD, if_neg hrk] at hkey
          rw [← hkey]

/-! ## The semantic principle, proved -/

/-- **The semantic half of Wadsworth's theorem.**  If the comparison of two closed terms admits no
finite failure witness, then the first is below the second in `D∞`.  This is
`ScottDinf.TagBelowSound`, which `Start/DinfWadsworthSharp.lean` left as the last open
statement. -/
theorem tagBelowSound : TagBelowSound := by
  intro M N hMc hNc hfail ρ
  refine (isLUB_ddenot_direct M ρ).2 ?_
  rintro x ⟨M', hM', rfl⟩
  refine le_ddenot_of_not_tagFail_approx (Lambda.size (Lambda.direct M')) le_rfl
    (Lambda.Approx.refl _) (fun hc => hfail (Lambda.tagFail_of_reduces hM' hc))
    (Lambda.freeBelow_zero_of_isClosed (hMc.reduces hM'))
    (Lambda.freeBelow_zero_of_isClosed hNc)
    (fun _ hi => absurd hi (by omega)) (fun _ hj => absurd hj (by omega))
    (fun _ _ hi _ _ => absurd hi (by omega))

/-! ## The consequences, unconditionally -/

/-- **The separation principle for approximants** of `Start/DinfWadsworth.lean`, proved. -/
theorem separatesApprox : SeparatesApprox := separatesApprox_of_tagBelowSound tagBelowSound

/-- Absence of a finite failure witness *characterises* the `D∞` order between closed terms. -/
theorem ddenot_le_iff_not_tagFail_unconditional {M N : Lambda} (hM : Lambda.IsClosed M)
    (hN : Lambda.IsClosed N) :
    (∀ ρ : DEnv, ddenot M ρ ≤ ddenot N ρ) ↔ ¬ Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N :=
  ddenot_le_iff_not_tagFail tagBelowSound hM hN

/-- **Wadsworth's theorem.**  Two closed terms are observationally equivalent — no context
distinguishes them by head normalisation — exactly when they have the same denotation in Scott's
`D∞`. -/
theorem obsEqHnf_iff_ddenot_eq {M N : Lambda} (hMc : Lambda.IsClosed M)
    (hNc : Lambda.IsClosed N) :
    Lambda.ObsEqHnf M N ↔ ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ :=
  obsEqHnf_iff_ddenot_eq_of_tagBelowSound tagBelowSound hMc hNc

/-- **Observational equivalence has a finite-witness characterisation.**  Two closed terms are
observationally equivalent exactly when neither comparison admits a failure witness.  Neither side
mentions contexts or the model: `Lambda.TagFail` is a syntactic relation whose witnesses are
finite. -/
theorem obsEqHnf_iff_not_tagFail {M N : Lambda} (hMc : Lambda.IsClosed M)
    (hNc : Lambda.IsClosed N) :
    Lambda.ObsEqHnf M N ↔
      ¬ Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N ∧
        ¬ Lambda.TagFail 0 (fun _ => 0) N (fun _ => 0) M := by
  rw [obsEqHnf_iff_ddenot_eq hMc hNc]
  constructor
  · intro h
    exact ⟨(ddenot_le_iff_not_tagFail_unconditional hMc hNc).1 fun ρ => le_of_eq (h ρ),
      (ddenot_le_iff_not_tagFail_unconditional hNc hMc).1 fun ρ => le_of_eq (h ρ).symm⟩
  · rintro ⟨h₁, h₂⟩ ρ
    exact le_antisymm
      ((ddenot_le_iff_not_tagFail_unconditional hMc hNc).2 h₁ ρ)
      ((ddenot_le_iff_not_tagFail_unconditional hNc hMc).2 h₂ ρ)

end

end ScottDinf
