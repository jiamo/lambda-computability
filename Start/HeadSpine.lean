/-
# Spines, unsolvability under substitution, and one-sided separation

This module collects the syntactic facts about head normal forms that the term-level Böhm-out
of `Start/BohmTermOut.lean` needs, and which the tree-level development of `Start/BohmOut.lean`
did not: there the two objects compared were *trees*, here one of them is an arbitrary term, so
its nodes have to be produced by head reduction and its unsolvable subterms have to stay
unsolvable when the surrounding variables are instantiated.

* `Lambda.exists_spine_of_hasHnf` — a head normalizing term reduces to a spine
  `λx₁ … x_b. x_h M₁ … M_k`, and `Lambda.hasHnf_lamN_appList` is the converse;
* `Lambda.HasHnf.reduces` — head normalizability is inherited *forwards* along a reduction
  (by confluence), the companion of `Lambda.HasHnf.of_reduces`;
* `Lambda.not_hasHnf_appList` — an unsolvable term stays unsolvable when applied to arguments;
* `Lambda.hasHnf_of_hasHnf_csub` — and when its free variables are replaced by closed terms;
* `Lambda.SepDiv` — the one-sided separation used for approximants: a list of closed arguments
  on which the first term head-converges while the second head-diverges.  `Lambda.SepDiv.of_reduces`
  transports it along a common list of arguments and `Lambda.SepDiv.of_separable` produces it from
  the two-sided `Lambda.Separable` of `Start/Bohm.lean`.
-/

import Start.BohmOut
import Start.HnfSolvable

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Spines -/

theorem neutral_appList : ∀ (l : List Lambda) {t : Lambda}, Neutral t → Neutral (appList t l) := by
  intro l
  induction l with
  | nil => intro t h; exact h
  | cons a l ih => intro t h; exact ih (Neutral.app a h)

theorem isHnf_lamN_appList (b h : ℕ) (as : List Lambda) :
    IsHnf (lamN b (appList (Lambda.var h) as)) := by
  induction b with
  | zero => exact IsHnf.neutral (neutral_appList as (Neutral.var h))
  | succ b ih => exact IsHnf.lam ih

theorem hasHnf_lamN_appList (b h : ℕ) (as : List Lambda) :
    HasHnf (lamN b (appList (Lambda.var h) as)) :=
  hasHnf_of_isHnf (isHnf_lamN_appList b h as)

/-- **A head normalizing term reduces to a spine.** -/
theorem exists_spine_of_hasHnf {M : Lambda} (h : HasHnf M) :
    ∃ (b k : ℕ) (as : List Lambda), Lambda.reduces M (lamN b (appList (Lambda.var k) as)) := by
  obtain ⟨u, hu, hhnf⟩ := h
  obtain ⟨n, v, rfl, hv⟩ := exists_lamN_neutral hhnf
  obtain ⟨k, args, rfl⟩ := exists_appList_var hv
  exact ⟨n, k, args, hu⟩

/-! ## Head normalizability along reductions and applications -/

/-- Head normalizability is inherited forwards along a reduction. -/
theorem HasHnf.reduces {M M' : Lambda} (h : HasHnf M) (hr : Lambda.reduces M M') : HasHnf M' := by
  obtain ⟨u, hu, hhnf⟩ := h
  obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem hu hr
  exact ⟨w, hw₂, (hhnf.reduces_shape hw₁).1⟩

/-- An unsolvable term stays unsolvable when applied to arguments. -/
theorem not_hasHnf_appList {M : Lambda} (h : ¬ HasHnf M) (l : List Lambda) :
    ¬ HasHnf (appList M l) := fun hc => h (hasHnf_appList_left l hc)

/-! ## Unsolvability is preserved by substitution of closed terms -/

theorem lift_var_lt {n k y : ℕ} (h : y < k) :
    Lambda.lift n k (Lambda.var y) = Lambda.var y := by
  simp [Lambda.lift, h]

theorem lift_var_ge {n k y : ℕ} (h : k ≤ y) :
    Lambda.lift n k (Lambda.var y) = Lambda.var (y + n) := by
  have : ¬ y < k := by omega
  simp [Lambda.lift, this]

theorem subst_var_lt {s : Lambda} {x y : ℕ} (h : y < x) :
    Lambda.subst s x (Lambda.var y) = Lambda.var y := by
  have h1 : y ≠ x := by omega
  have h2 : ¬ y > x := by omega
  simp [Lambda.subst, h1, h2]

theorem subst_var_self {s : Lambda} {x : ℕ} : Lambda.subst s x (Lambda.var x) = s := by
  simp [Lambda.subst]

theorem subst_var_gt {s : Lambda} {x y : ℕ} (h : x < y) :
    Lambda.subst s x (Lambda.var y) = Lambda.var (y - 1) := by
  have h1 : y ≠ x := by omega
  simp [Lambda.subst, h1, h]

theorem csub_lift {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) :
    ∀ (Q : Lambda) (j k : ℕ), j ≤ k →
      csub ρ (k + 1) (Lambda.lift 1 j Q) = Lambda.lift 1 j (csub ρ k Q) := by
  intro Q
  induction Q with
  | var n =>
      intro j k hjk
      by_cases h1 : n < j
      · rw [lift_var_lt h1, csub_var_lt (by omega), csub_var_lt (by omega), lift_var_lt h1]
      · rw [lift_var_ge (by omega)]
        by_cases h2 : n < k
        · rw [csub_var_lt (by omega), csub_var_lt h2, lift_var_ge (by omega)]
        · rw [csub_var_ge (by omega), csub_var_ge (by omega),
            show n + 1 - (k + 1) = n - k from by omega, Lambda.lift_closed (hρ _)]
  | app a b iha ihb =>
      intro j k hjk
      rw [Lambda.lift, csub_app, csub_app, iha j k hjk, ihb j k hjk, Lambda.lift]
  | lam t ih =>
      intro j k hjk
      rw [Lambda.lift, csub_lam hρ, csub_lam hρ, ih (j + 1) (k + 1) (by omega), Lambda.lift]

theorem csub_subst {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) :
    ∀ (P Q : Lambda) (j k : ℕ), j ≤ k →
      csub ρ k (Lambda.subst Q j P) = Lambda.subst (csub ρ k Q) j (csub ρ (k + 1) P) := by
  intro P
  induction P with
  | var n =>
      intro Q j k hjk
      rcases Nat.lt_trichotomy n j with h | h | h
      · rw [subst_var_lt h, csub_var_lt (by omega), csub_var_lt (by omega), subst_var_lt h]
      · subst h
        rw [subst_var_self, csub_var_lt (by omega), subst_var_self]
      · rw [subst_var_gt h]
        by_cases h2 : n ≤ k
        · rw [csub_var_lt (by omega), csub_var_lt (by omega), subst_var_gt h]
        · rw [csub_var_ge (by omega), csub_var_ge (by omega),
            show n - 1 - k = n - (k + 1) from by omega]
          exact (Lambda.IsClosed_imp_subst_eq (hρ _) _ _).symm
  | app a b iha ihb =>
      intro Q j k hjk
      rw [Lambda.subst, csub_app, csub_app, iha Q j k hjk, ihb Q j k hjk, Lambda.subst]
  | lam t ih =>
      intro Q j k hjk
      rw [Lambda.subst, csub_lam hρ, csub_lam hρ, ih (Lambda.lift 1 0 Q) (j + 1) (k + 1) (by omega),
        Lambda.subst, csub_lift hρ Q 0 k (by omega)]

theorem wstep_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {M M' : Lambda}
    (h : wstep M M') : ∀ k : ℕ, wstep (csub ρ k M) (csub ρ k M') := by
  induction h with
  | beta P Q =>
      intro k
      rw [csub_app, csub_lam hρ, csub_subst hρ P Q 0 k (Nat.zero_le k)]
      exact wstep.beta _ _
  | app N _ ih => intro k; exact wstep.app _ (ih k)

theorem hstep_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {M M' : Lambda}
    (h : hstep M M') : ∀ k : ℕ, hstep (csub ρ k M) (csub ρ k M') := by
  induction h with
  | weak hw => intro k; exact hstep.weak (wstep_csub hρ hw k)
  | lam _ ih =>
      intro k
      rw [csub_lam hρ, csub_lam hρ]
      exact hstep.lam (ih (k + 1))

theorem hasHeadEval_of_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) :
    ∀ (n : ℕ) {P : Lambda} {k : ℕ}, HNIn n (csub ρ k P) → HasHeadEval P := by
  intro n
  induction n with
  | zero =>
      intro P k h
      by_contra hc
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf (fun hP => hc (hasHeadEval_of_isHnf hP))
      exact not_hstep_of_isHnf h _ (hstep_csub hρ hP' k)
  | succ n ih =>
      intro P k h
      by_cases hP : IsHnf P
      · exact hasHeadEval_of_isHnf hP
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf hP
      rcases h with h | ⟨w, hs, hw⟩
      · exact absurd (hstep_csub hρ hP' k) (not_hstep_of_isHnf h _)
      · have hwe : w = csub ρ k P' := hstep_deterministic hs (hstep_csub hρ hP' k)
        subst hwe
        exact hasHeadEval_of_hstep hP' (ih hw)

/-- **Unsolvability is preserved by substitution of closed terms.** -/
theorem hasHnf_of_hasHnf_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {P : Lambda}
    {k : ℕ} (h : HasHnf (csub ρ k P)) : HasHnf P := by
  obtain ⟨n, hn⟩ := hasHeadEval_of_hasHnf h
  exact hasHnf_of_hasHeadEval (hasHeadEval_of_csub hρ n hn)

/-! ## One-sided separation -/

/-- `SepDiv M N`: some list of closed arguments makes `M` head-converge and `N` head-diverge.
This is the one-sided form of `Lambda.Separable` which the comparison of an approximant with an
arbitrary term produces, since the approximant side may be `Ω`. -/
def SepDiv (M N : Lambda) : Prop :=
  ∃ l : List Lambda, (∀ a ∈ l, Lambda.IsClosed a) ∧ HasHnf (appList M l) ∧ ¬ HasHnf (appList N l)

/-- One-sided separability is inherited along a common list of closed arguments. -/
theorem SepDiv.of_reduces {M N M' N' : Lambda} (l : List Lambda)
    (hl : ∀ a ∈ l, Lambda.IsClosed a) (hM : Lambda.reduces (appList M l) M')
    (hN : Lambda.reduces (appList N l) N') (h : SepDiv M' N') : SepDiv M N := by
  obtain ⟨args, hcl, hM', hN'⟩ := h
  refine ⟨l ++ args, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · exact hcl a ha
  · rw [appList_append]
    exact HasHnf.of_reduces (reduces_appList hM args) hM'
  · rw [appList_append]
    exact fun hc => hN' (hc.reduces (reduces_appList hN args))

/-- Two-sided separation gives one-sided separation: the context `X a₁ … a_k Ω I` converges on
the side that produces `false` and diverges on the side that produces `true`. -/
theorem SepDiv.of_separable {M N : Lambda} (h : Separable N M) : SepDiv M N := by
  obtain ⟨args, hcl, hN, hM⟩ := h
  refine ⟨args ++ [Lambda.omega, Lambda.I], ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hcl a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact omega_closed
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact I_closed
        · exact absurd ha List.not_mem_nil
  · rw [appList_append]
    refine HasHnf.of_reduces (reduces_appList hM [Lambda.omega, Lambda.I]) ?_
    exact HasHnf.of_reduces (Lambda.false_works _ _) (hasHnf_of_isHnf (IsHnf.lam
      (IsHnf.neutral (Neutral.var 0))))
  · rw [appList_append]
    intro hc
    have h1 : Lambda.reduces (appList (appList N args) [Lambda.omega, Lambda.I]) Lambda.omega :=
      Lambda.reduces_trans (reduces_appList hN [Lambda.omega, Lambda.I]) (Lambda.true_works _ _)
    exact GraphModel.not_hasHnf_omega (hc.reduces h1)

end Lambda

end
