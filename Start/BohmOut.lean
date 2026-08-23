/-
# Böhm out: transporting a deep difference to the root

`Start/Bohm.lean` proves Böhm's separation theorem for two normal forms whose Böhm trees differ
at the *root*.  This module supplies the missing ingredient, the "Böhm out" transformation, which
brings a difference occurring deeper inside the two trees up to the root.

The technique used here is the *tagged tuple* substitution: every bound variable in scope is
replaced by a closed term

    Gᵢ = λ u₁ … u_K w. w u₁ … u_K ⟨i⟩

which stores the arguments it receives, together with a tag `⟨i⟩` identifying the variable, and
hands them all to its last argument.  Because `Gᵢ` loses no information, a *closed* applicative
context suffices to walk down the tree — no fresh variables are needed — and at the end the tag
identifies the head while the number of stored arguments identifies the arity.
-/

import Start.Bohm
import Start.SelfInterpreter

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Structural closedness helpers -/

theorem freeBelow_mono : ∀ {t : Lambda} {k l : ℕ}, k ≤ l → freeBelow k t → freeBelow l t := by
  intro t
  induction t with
  | var n => intro k l hkl h; exact lt_of_lt_of_le h hkl
  | app a b iha ihb => intro k l hkl h; exact ⟨iha hkl h.1, ihb hkl h.2⟩
  | lam t ih => intro k l hkl h; exact ih (Nat.succ_le_succ hkl) h

theorem freeBelow_lift : ∀ {t : Lambda} {k : ℕ}, freeBelow k t → ∀ j,
    freeBelow (k + 1) (Lambda.lift 1 j t) := by
  intro t
  induction t with
  | var n =>
      intro k h j
      by_cases hn : n < j
      · simp only [Lambda.lift, if_pos hn]
        exact Nat.lt_succ_of_lt h
      · simp only [Lambda.lift, if_neg hn]
        exact Nat.succ_lt_succ h
  | app a b iha ihb => intro k h j; exact ⟨iha h.1 j, ihb h.2 j⟩
  | lam t ih => intro k h j; exact ih (k := k + 1) h (j + 1)

theorem isClosedAt_of_freeBelow :
    ∀ {t : Lambda} {k : ℕ}, freeBelow k t → Lambda.IsClosedAt t k := by
  intro t
  induction t with
  | var n =>
      intro k h
      exact Lambda.IsClosedAt_var n k h
  | app a b iha ihb => intro k h; exact Lambda.IsClosedAt_app (iha h.1) (ihb h.2)
  | lam t ih => intro k h; exact Lambda.IsClosedAt_lam (ih h)

theorem isClosed_of_freeBelow_zero {t : Lambda} (h : freeBelow 0 t) : Lambda.IsClosed t :=
  (Lambda.IsClosedAt_zero_iff_IsClosed t).1 (isClosedAt_of_freeBelow h)

theorem freeBelow_lamN_iff : ∀ (n : ℕ) {t : Lambda} {k : ℕ},
    freeBelow k (lamN n t) ↔ freeBelow (k + n) t := by
  intro n
  induction n with
  | zero => intro t k; simp
  | succ n ih =>
      intro t k
      rw [lamN_succ]
      change freeBelow (k + 1) (lamN n t) ↔ _
      rw [ih (k := k + 1), show k + 1 + n = k + (n + 1) from by omega]

theorem freeBelow_lamN (n : ℕ) {t : Lambda} {k : ℕ} (h : freeBelow (k + n) t) :
    freeBelow k (lamN n t) := (freeBelow_lamN_iff n).2 h

theorem freeBelow_appList_iff : ∀ (l : List Lambda) {t : Lambda} {k : ℕ},
    freeBelow k (appList t l) ↔ freeBelow k t ∧ ∀ a ∈ l, freeBelow k a := by
  intro l
  induction l with
  | nil => intro t k; simp [appList]
  | cons a l ih =>
      intro t k
      rw [appList_cons, ih]
      constructor
      · rintro ⟨⟨ht, ha⟩, hl⟩
        refine ⟨ht, ?_⟩
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ha
        · exact hl b hb
      · rintro ⟨ht, hl⟩
        exact ⟨⟨ht, hl a List.mem_cons_self⟩,
          fun b hb => hl b (List.mem_cons_of_mem a hb)⟩

theorem freeBelow_appList (l : List Lambda) {t : Lambda} {k : ℕ} (ht : freeBelow k t)
    (hl : ∀ a ∈ l, freeBelow k a) : freeBelow k (appList t l) :=
  (freeBelow_appList_iff l).2 ⟨ht, hl⟩

/-! ## Parallel substitution by closed terms -/

/-- The environment substituting `ρ (j - k)` for the free variable `j ≥ k`, and leaving the
variables `< k` (those bound by the `k` enclosing abstractions) alone. -/
def csubEnv (ρ : ℕ → Lambda) (k : ℕ) : ℕ → Lambda :=
  fun j => if j < k then Lambda.var j else ρ (j - k)

/-- `csub ρ k t` substitutes the *closed* terms `ρ 0, ρ 1, …` for the free variables
`k, k + 1, …` of `t`, keeping the variables `< k` as they are.  Since the substituted terms are
closed, no lifting is involved. -/
def csub (ρ : ℕ → Lambda) (k : ℕ) (t : Lambda) : Lambda := substEnv (csubEnv ρ k) t

@[simp] theorem csub_var (ρ : ℕ → Lambda) (k j : ℕ) :
    csub ρ k (Lambda.var j) = csubEnv ρ k j := rfl

theorem csub_var_lt {ρ : ℕ → Lambda} {k j : ℕ} (h : j < k) :
    csub ρ k (Lambda.var j) = Lambda.var j := by
  simp [csub, substEnv, csubEnv, h]

theorem csub_var_ge {ρ : ℕ → Lambda} {k j : ℕ} (h : k ≤ j) :
    csub ρ k (Lambda.var j) = ρ (j - k) := by
  have : ¬ j < k := by omega
  simp [csub, substEnv, csubEnv, this]

@[simp] theorem csub_app (ρ : ℕ → Lambda) (k : ℕ) (a b : Lambda) :
    csub ρ k (Lambda.app a b) = Lambda.app (csub ρ k a) (csub ρ k b) := rfl

theorem envCons_csubEnv {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (k : ℕ) :
    envCons (csubEnv ρ k) = csubEnv ρ (k + 1) := by
  funext j
  cases j with
  | zero => simp [envCons, csubEnv]
  | succ j =>
      by_cases hj : j < k
      · have hj' : j + 1 < k + 1 := by omega
        simp [envCons, csubEnv, hj, hj', Lambda.lift]
      · have hj' : ¬ j + 1 < k + 1 := by omega
        simp only [envCons, csubEnv, hj, hj', if_false]
        rw [Lambda.lift_closed (hρ _) 1 0]
        congr 1
        omega

theorem csub_lam {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (k : ℕ) (t : Lambda) :
    csub ρ k (Lambda.lam t) = Lambda.lam (csub ρ (k + 1) t) := by
  rw [csub, substEnv, envCons_csubEnv hρ]
  rfl

theorem csub_lamN {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) :
    ∀ (n k : ℕ) (t : Lambda), csub ρ k (lamN n t) = lamN n (csub ρ (k + n) t) := by
  intro n
  induction n with
  | zero => intro k t; simp
  | succ n ih =>
      intro k t
      rw [lamN_succ, csub_lam hρ, ih, lamN_succ, show k + 1 + n = k + (n + 1) from by omega]

theorem csub_appList (ρ : ℕ → Lambda) (k : ℕ) :
    ∀ (l : List Lambda) (t : Lambda),
      csub ρ k (appList t l) = appList (csub ρ k t) (l.map (csub ρ k)) := by
  intro l
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; rw [appList_cons, ih, List.map_cons, appList_cons, csub_app]

theorem freeBelow_substEnv : ∀ (t : Lambda) (u : ℕ → Lambda) (m : ℕ),
    (∀ j, freeBelow m (u j)) → freeBelow m (substEnv u t) := by
  intro t
  induction t with
  | var n => intro u m hu; exact hu n
  | app a b iha ihb => intro u m hu; exact ⟨iha u m hu, ihb u m hu⟩
  | lam t ih =>
      intro u m hu
      refine ih (envCons u) (m + 1) ?_
      intro j
      cases j with
      | zero => exact Nat.succ_pos m
      | succ j => exact freeBelow_lift (hu j) 0

theorem freeBelow_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (k : ℕ) (t : Lambda) :
    freeBelow k (csub ρ k t) := by
  refine freeBelow_substEnv t _ k ?_
  intro j
  by_cases hj : j < k
  · simp only [csubEnv, if_pos hj]
    exact hj
  · simp only [csubEnv, hj, if_false]
    exact freeBelow_mono (Nat.zero_le k) (freeBelow_zero_of_isClosed (hρ _))

theorem isClosed_csub_zero {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (t : Lambda) :
    Lambda.IsClosed (csub ρ 0 t) :=
  isClosed_of_freeBelow_zero (freeBelow_csub hρ 0 t)

/-! ## Consuming the binders -/

/-- Extending an environment of closed terms by one entry, used for one β-step. -/
def consEnv (a : Lambda) (ρ : ℕ → Lambda) : ℕ → Lambda
  | 0 => a
  | j + 1 => ρ j

/-- Extending an environment of closed terms by the `b` innermost binders, which get the values
`g 0, …, g (b-1)`. -/
def extendEnv (g : ℕ → Lambda) (b : ℕ) (ρ : ℕ → Lambda) : ℕ → Lambda :=
  fun j => if j < b then g j else ρ (j - b)

theorem extendEnv_zero (g : ℕ → Lambda) (ρ : ℕ → Lambda) : extendEnv g 0 ρ = ρ := by
  funext j; simp [extendEnv]

theorem isClosed_consEnv {a : Lambda} {ρ : ℕ → Lambda} (ha : Lambda.IsClosed a)
    (hρ : ∀ j, Lambda.IsClosed (ρ j)) : ∀ j, Lambda.IsClosed (consEnv a ρ j) := by
  intro j; cases j with
  | zero => exact ha
  | succ j => exact hρ j

theorem isClosed_extendEnv {g ρ : ℕ → Lambda} (hg : ∀ j, Lambda.IsClosed (g j))
    (hρ : ∀ j, Lambda.IsClosed (ρ j)) (b : ℕ) : ∀ j, Lambda.IsClosed (extendEnv g b ρ j) := by
  intro j
  by_cases hj : j < b <;> simp only [extendEnv, hj, if_true, if_false]
  · exact hg j
  · exact hρ _

/-- One β-step of the application of an abstraction to a closed argument, in terms of `csub`. -/
theorem subst_csub_succ {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {a : Lambda}
    (ha : Lambda.IsClosed a) :
    ∀ (t : Lambda) (k : ℕ), Lambda.subst a k (csub ρ (k + 1) t) = csub (consEnv a ρ) k t := by
  intro t
  induction t with
  | var n =>
      intro k
      rcases Nat.lt_trichotomy n k with h | h | h
      · rw [csub_var_lt (by omega), csub_var_lt h]
        have h1 : n ≠ k := by omega
        have h2 : ¬ n > k := by omega
        simp [Lambda.subst, h1, h2]
      · subst h
        rw [csub_var_lt (by omega), csub_var_ge (le_refl n)]
        simp [Lambda.subst, consEnv]
      · rw [csub_var_ge (by omega), csub_var_ge (by omega)]
        have : n - (k + 1) = (n - k) - 1 := by omega
        rw [this]
        have hcons : consEnv a ρ (n - k) = ρ (n - k - 1) := by
          obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
          rw [hm]; rfl
        rw [hcons, hρ _]
  | app x y ihx ihy => intro k; rw [csub_app, Lambda.subst, ihx, ihy, csub_app]
  | lam t ih =>
      intro k
      rw [csub_lam hρ, Lambda.subst, Lambda.lift_closed ha, ih (k + 1),
        csub_lam (isClosed_consEnv ha hρ)]

/-- **Applying the binders.**  An `b`-fold abstraction whose body is a `csub`-instance, applied to
the `b` closed arguments `argsFor g b`, reduces to the instance in which the `b` binders have been
given the values `g 0, …, g (b-1)`. -/
theorem reduces_appList_csub {g : ℕ → Lambda} (hg : ∀ j, Lambda.IsClosed (g j)) :
    ∀ (b : ℕ) (ρ : ℕ → Lambda), (∀ j, Lambda.IsClosed (ρ j)) → ∀ (t : Lambda),
      Lambda.reduces (appList (lamN b (csub ρ b t)) (argsFor g b))
        (csub (extendEnv g b ρ) 0 t) := by
  intro b
  induction b with
  | zero =>
      intro ρ _ t
      rw [extendEnv_zero]
      exact .refl _
  | succ b ih =>
      intro ρ hρ t
      rw [argsFor, appList_cons]
      have hstep : Lambda.reduces (Lambda.app (lamN (b + 1) (csub ρ (b + 1) t)) (g b))
          (lamN b (csub (consEnv (g b) ρ) b t)) := by
        refine .step _ _ _ (.beta _ _) ?_
        rw [subst_lamN (hg b) b 0 (csub ρ (b + 1) t), Nat.zero_add,
          subst_csub_succ hρ (hg b) t b]
        exact .refl _
      refine Lambda.reduces_trans (reduces_appList hstep (argsFor g b)) ?_
      have := ih (consEnv (g b) ρ) (isClosed_consEnv (hg b) hρ) t
      have henv : extendEnv g b (consEnv (g b) ρ) = extendEnv g (b + 1) ρ := by
        funext j
        by_cases hj : j < b
        · simp [extendEnv, hj, show j < b + 1 from by omega]
        · by_cases hj' : j = b
          · subst hj'
            simp [extendEnv, consEnv]
          · have h1 : ¬ j < b + 1 := by omega
            have h2 : ∃ m, j - b = m + 1 := ⟨j - b - 1, by omega⟩
            obtain ⟨m, hm⟩ := h2
            simp only [extendEnv, hj, h1, if_false, hm]
            change ρ m = ρ (j - (b + 1))
            congr 1
            omega
      rwa [henv] at this

/-! ## Projections -/

theorem getD_argsFor (f : ℕ → Lambda) : ∀ (n p : ℕ), p < n →
    (argsFor f n).getD p (Lambda.var 0) = f (n - 1 - p) := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
      intro p h
      cases p with
      | zero => simp [argsFor]
      | succ p =>
          rw [argsFor, List.getD_cons_succ, ih p (by omega)]
          congr 1
          omega

theorem substDown_var : ∀ (u : List Lambda), (∀ a ∈ u, Lambda.IsClosed a) → ∀ (j : ℕ),
    j < u.length → substDown u (Lambda.var j) = u.getD (u.length - 1 - j) (Lambda.var 0) := by
  intro u
  induction u with
  | nil => intro _ j hj; simp at hj
  | cons a u ih =>
      intro hcl j hj
      rw [substDown_cons]
      rcases Nat.lt_or_ge j u.length with h | h
      · have hne : j ≠ u.length := by omega
        have hgt : ¬ j > u.length := by omega
        have hsub : Lambda.subst a u.length (Lambda.var j) = Lambda.var j := by
          simp [Lambda.subst, hne, hgt]
        rw [hsub, ih (fun b hb => hcl b (List.mem_cons_of_mem a hb)) j h]
        have hidx : (a :: u).length - 1 - j = (u.length - 1 - j) + 1 := by
          simp only [List.length_cons]; omega
        rw [hidx, List.getD_cons_succ]
      · have hje : j = u.length := by simp only [List.length_cons] at hj; omega
        have hsub : Lambda.subst a u.length (Lambda.var j) = a := by
          simp [Lambda.subst, hje]
        rw [hsub, substDown_closed (hcl a List.mem_cons_self)]
        have hidx : (a :: u).length - 1 - j = 0 := by simp only [List.length_cons]; omega
        rw [hidx, List.getD_cons_zero]

/-- `projSel n i = λ z₁ … zₙ. zᵢ` selects the `i`-th of `n` arguments. -/
def projSel (n i : ℕ) : Lambda := lamN n (Lambda.var (n - 1 - i))

theorem freeBelow_projSel {n i : ℕ} (h : i < n) : freeBelow 0 (projSel n i) := by
  refine freeBelow_lamN n ?_
  change n - 1 - i < 0 + n
  omega

theorem isClosed_projSel {n i : ℕ} (h : i < n) : Lambda.IsClosed (projSel n i) :=
  isClosed_of_freeBelow_zero (freeBelow_projSel h)

/-- The projection applied to `n` closed arguments returns the `i`-th one. -/
theorem reduces_appList_projSel {n i : ℕ} (hi : i < n) (l : List Lambda)
    (hl : ∀ a ∈ l, Lambda.IsClosed a) (hlen : l.length = n) :
    Lambda.reduces (appList (projSel n i) l) (l.getD i (Lambda.var 0)) := by
  have hred := reduces_appList_lamN hl (Lambda.var (n - 1 - i))
  rw [hlen, substDown_var l hl (n - 1 - i) (by omega)] at hred
  have hidx : l.length - 1 - (n - 1 - i) = i := by omega
  rwa [hidx] at hred

/-! ## Tagged tuples -/

/-- `tagTuple B K i = λ u₁ … u_K w. w u₁ … u_K ⟨i⟩` stores the `K` arguments it receives together
with the tag `⟨i⟩ = projSel B i` identifying the variable it stands for, and hands them all to
its last argument.  It is the substituent used by the Böhm-out transformation: it destroys no
information. -/
def tagTuple (B K i : ℕ) : Lambda :=
  lamN (K + 1) (appList (Lambda.var 0)
    (argsFor (fun k => Lambda.var (k + 1)) K ++ [projSel B i]))

theorem isClosed_tagTuple {B K i : ℕ} (hi : i < B) : Lambda.IsClosed (tagTuple B K i) := by
  refine isClosed_of_freeBelow_zero (freeBelow_lamN (K + 1) ?_)
  refine freeBelow_appList _ (show 0 < 0 + (K + 1) from by omega) ?_
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨k, hk, rfl⟩ := mem_argsFor ha
    change k + 1 < 0 + (K + 1)
    omega
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact freeBelow_mono (Nat.zero_le _) (freeBelow_projSel hi)
    · exact absurd ha List.not_mem_nil

/-- **The tuple unfolds.**  Given `K` closed arguments and one further closed argument `W`, the
tagged tuple hands `W` all the stored arguments followed by its tag. -/
theorem reduces_appList_tagTuple {B K i : ℕ} (hi : i < B) (l : List Lambda)
    (hl : ∀ a ∈ l, Lambda.IsClosed a) (hlen : l.length = K) {W : Lambda}
    (hW : Lambda.IsClosed W) :
    Lambda.reduces (appList (tagTuple B K i) (l ++ [W])) (appList W (l ++ [projSel B i])) := by
  set u : List Lambda := l ++ [W] with hu
  have hucl : ∀ a ∈ u, Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hW
      · exact absurd ha List.not_mem_nil
  have hulen : u.length = K + 1 := by simp [hu, hlen]
  have hred := reduces_appList_lamN hucl
    (appList (Lambda.var 0) (argsFor (fun k => Lambda.var (k + 1)) K ++ [projSel B i]))
  rw [hulen, substDown_appList] at hred
  have hhead : substDown u (Lambda.var 0) = W := by
    rw [substDown_var u hucl 0 (by omega), hulen, hu]
    simp [hlen]
  have hargs : (argsFor (fun k => Lambda.var (k + 1)) K ++ [projSel B i]).map (substDown u)
      = l ++ [projSel B i] := by
    rw [List.map_append, List.map_cons, List.map_nil, substDown_closed (isClosed_projSel hi)]
    congr 1
    refine List.ext_getElem (by simp [hlen]) ?_
    intro p h1 h2
    have hpK : p < K := by simpa using h1
    have helt : (argsFor (fun k => Lambda.var (k + 1)) K)[p]'(by simpa using hpK)
        = Lambda.var (K - 1 - p + 1) := by
      rw [List.getElem_eq_getD (Lambda.var 0),
        getD_argsFor (fun k => Lambda.var (k + 1)) K p hpK]
    rw [List.getElem_map, helt, substDown_var u hucl _ (by omega), hulen,
      List.getElem_eq_getD (Lambda.var 0)]
    have hidx : K + 1 - 1 - (K - 1 - p + 1) = p := by omega
    rw [hidx, hu, List.getD, List.getD, List.getElem?_append_left (by omega)]
  rw [hhead, hargs] at hred
  exact hred

/-! ## Instantiating a Böhm tree by closed terms -/

/-- `instTree ρ x` is the term denoted by the Böhm tree `x` with the closed term `ρ j` substituted
for its `j`-th free variable. -/
def instTree (ρ : ℕ → Lambda) (x : BohmNF) : Lambda := csub ρ 0 x.toTerm

theorem isClosed_instTree {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (x : BohmNF) :
    Lambda.IsClosed (instTree ρ x) := isClosed_csub_zero hρ _

theorem instTree_node {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) (b h : ℕ)
    (args : List BohmNF) :
    instTree ρ (.node b h args)
      = lamN b (csub ρ b (appList (Lambda.var h) (args.map BohmNF.toTerm))) := by
  rw [instTree, BohmNF.toTerm_node, csub_lamN hρ, Nat.zero_add]

/-- **One step of the descent.**  Feeding the `b` closed arguments `argsFor g b` to the
instantiated node exposes the value of its head variable, applied to the instantiated arguments
of the node. -/
theorem reduces_instTree_node {ρ g : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j))
    (hg : ∀ j, Lambda.IsClosed (g j)) (b h : ℕ) (args : List BohmNF) :
    Lambda.reduces (appList (instTree ρ (.node b h args)) (argsFor g b))
      (appList (extendEnv g b ρ h) (args.map (instTree (extendEnv g b ρ)))) := by
  rw [instTree_node hρ]
  refine Lambda.reduces_trans (reduces_appList_csub hg b ρ hρ _) ?_
  rw [csub_appList, csub_var_ge (Nat.zero_le h), Nat.sub_zero, List.map_map]
  exact .refl _

/-! ## Structural bounds on a Böhm tree -/

/-- Every application node of `x` has at most `K` arguments. -/
inductive BohmNF.ArityLe (K : ℕ) : BohmNF → Prop
  | node {b h : ℕ} {args : List BohmNF} : args.length ≤ K → (∀ a ∈ args, BohmNF.ArityLe K a) →
      BohmNF.ArityLe K (.node b h args)

/-- Every free variable of `x` is `< d`. -/
inductive BohmNF.FreeVarsBelow : ℕ → BohmNF → Prop
  | node {d b h : ℕ} {args : List BohmNF} : h < b + d →
      (∀ a ∈ args, BohmNF.FreeVarsBelow (b + d) a) → BohmNF.FreeVarsBelow d (.node b h args)

/-- Along every path of `x` at most `s` binders are met. -/
inductive BohmNF.BinderRoom : ℕ → BohmNF → Prop
  | node {s b h : ℕ} {args : List BohmNF} : b ≤ s → (∀ a ∈ args, BohmNF.BinderRoom (s - b) a) →
      BohmNF.BinderRoom s (.node b h args)

theorem BohmNF.ArityLe.mono {K K' : ℕ} {x : BohmNF} (h : BohmNF.ArityLe K x) (hK : K ≤ K') :
    BohmNF.ArityLe K' x := by
  induction h with
  | node hlen _ ih => exact .node (le_trans hlen hK) ih

theorem BohmNF.FreeVarsBelow.mono {d d' : ℕ} {x : BohmNF} (h : BohmNF.FreeVarsBelow d x)
    (hd : d ≤ d') : BohmNF.FreeVarsBelow d' x := by
  induction h generalizing d' with
  | @node d b h args hh _ ih =>
      exact .node (by omega) (fun a ha => ih a ha (by omega))

theorem BohmNF.BinderRoom.mono {s s' : ℕ} {x : BohmNF} (h : BohmNF.BinderRoom s x) (hs : s ≤ s') :
    BohmNF.BinderRoom s' x := by
  induction h generalizing s' with
  | @node s b h args hb _ ih =>
      exact .node (by omega) (fun a ha => ih a ha (by omega))

/-- The largest number of arguments of an application node of `x`. -/
def BohmNF.maxArity : BohmNF → ℕ
  | .node _ _ args => max args.length ((args.map BohmNF.maxArity).foldr max 0)

/-- The largest number of binders met along a path of `x`. -/
def BohmNF.binderDepth : BohmNF → ℕ
  | .node b _ args => b + ((args.map BohmNF.binderDepth).foldr max 0)

theorem le_foldr_max_of_mem {f : BohmNF → ℕ} :
    ∀ (l : List BohmNF) (a : BohmNF), a ∈ l → f a ≤ (l.map f).foldr max 0 := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons b l ih =>
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact le_max_left _ _
      · exact le_trans (ih a ha) (le_max_right _ _)

theorem BohmNF.arityLe_maxArity (x : BohmNF) : BohmNF.ArityLe x.maxArity x := by
  induction x using BohmNF.ind_mem with
  | _ b h args ih =>
      refine .node (by rw [BohmNF.maxArity]; exact le_max_left _ _) ?_
      intro a ha
      refine (ih a ha).mono ?_
      rw [BohmNF.maxArity]
      exact le_trans (le_foldr_max_of_mem args a ha) (le_max_right _ _)

theorem BohmNF.binderRoom_binderDepth (x : BohmNF) : BohmNF.BinderRoom x.binderDepth x := by
  induction x using BohmNF.ind_mem with
  | _ b h args ih =>
      refine .node (by rw [BohmNF.binderDepth]; omega) ?_
      intro a ha
      refine (ih a ha).mono ?_
      rw [BohmNF.binderDepth, Nat.add_sub_cancel_left]
      exact le_foldr_max_of_mem args a ha

theorem BohmNF.freeBelow_toTerm : ∀ {d : ℕ} {x : BohmNF}, BohmNF.FreeVarsBelow d x →
    freeBelow d x.toTerm := by
  intro d x h
  induction h with
  | @node d b h args hh _ ih =>
      rw [BohmNF.toTerm_node]
      refine freeBelow_lamN b (freeBelow_appList _ (show h < d + b from by omega) ?_)
      intro a ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
      exact freeBelow_mono (by omega) (ih y hy)

theorem BohmNF.isClosed_toTerm {x : BohmNF} (h : BohmNF.FreeVarsBelow 0 x) :
    Lambda.IsClosed x.toTerm :=
  isClosed_of_freeBelow_zero (BohmNF.freeBelow_toTerm h)

theorem BohmNF.freeVarsBelow_of_freeBelow :
    ∀ (x : BohmNF) {d : ℕ}, freeBelow d x.toTerm → BohmNF.FreeVarsBelow d x := by
  intro x
  induction x using BohmNF.ind_mem with
  | _ b h args ih =>
      intro d hfb
      rw [BohmNF.toTerm_node, freeBelow_lamN_iff, freeBelow_appList_iff] at hfb
      refine .node (by have := hfb.1; change h < d + b at this; omega) ?_
      intro a ha
      refine (ih a ha) (freeBelow_mono (by omega) (hfb.2 _ (List.mem_map_of_mem ha)))

/-- A Böhm tree whose denotation is closed has no free variables. -/
theorem BohmNF.freeVarsBelow_zero_of_isClosed {x : BohmNF} (h : Lambda.IsClosed x.toTerm) :
    BohmNF.FreeVarsBelow 0 x :=
  BohmNF.freeVarsBelow_of_freeBelow x (freeBelow_zero_of_isClosed h)

/-! ## Trees that differ -/

/-- `BohmDiffer x y`: the two trees have the same number of binders and the same head all along
some path, at the end of which they differ in the head variable or in the number of arguments.
Since the binder counts agree everywhere along the path, such a difference is a genuine
βη-difference, not one that η-expansion could remove. -/
inductive BohmDiffer : BohmNF → BohmNF → Prop
  | root {b h₁ h₂ : ℕ} {as₁ as₂ : List BohmNF} (hne : h₁ ≠ h₂ ∨ as₁.length ≠ as₂.length) :
      BohmDiffer (.node b h₁ as₁) (.node b h₂ as₂)
  | arg {b h r : ℕ} {as₁ as₂ : List BohmNF} (hr₁ : r < as₁.length) (hr₂ : r < as₂.length)
      (hlen : as₁.length = as₂.length)
      (hd : BohmDiffer (as₁[r]'hr₁) (as₂[r]'hr₂)) :
      BohmDiffer (.node b h as₁) (.node b h as₂)

/-! ## Separating two tagged tuples -/

/-- Separability is inherited along a common list of closed arguments. -/
theorem Separable.of_reduces {M N M' N' : Lambda} (l : List Lambda)
    (hl : ∀ a ∈ l, Lambda.IsClosed a) (hM : Lambda.reduces (appList M l) M')
    (hN : Lambda.reduces (appList N l) N') (h : Separable M' N') : Separable M N := by
  obtain ⟨args, hcl, hM', hN'⟩ := h
  refine ⟨l ++ args, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · exact hcl a ha
  · rw [appList_append]
    exact Lambda.reduces_trans (reduces_appList hM args) hM'
  · rw [appList_append]
    exact Lambda.reduces_trans (reduces_appList hN args) hN'

/-- The list of `B` arguments which is `true` in position `t` and `false` everywhere else; it
turns the tag `projSel B t` into `true` and every other tag into `false`. -/
def boolArgs (B t : ℕ) : List Lambda :=
  (List.range B).map (fun p => if p = t then Lambda.true else Lambda.false)

@[simp] theorem boolArgs_length (B t : ℕ) : (boolArgs B t).length = B := by
  simp [boolArgs]

theorem isClosed_mem_boolArgs {B t : ℕ} {a : Lambda} (ha : a ∈ boolArgs B t) :
    Lambda.IsClosed a := by
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  by_cases hp : p = t <;> simp only [hp, if_true, if_false]
  · exact IsClosed_true
  · exact IsClosed_false

theorem boolArgs_getD {B t i : ℕ} (hi : i < B) :
    (boolArgs B t).getD i (Lambda.var 0) = if i = t then Lambda.true else Lambda.false := by
  rw [← List.getElem_eq_getD (fallback := Lambda.var 0) (h := by simpa using hi)]
  simp [boolArgs]

/-- Applying the tag of the variable `t` to `boolArgs B t'` yields `true` exactly when `t = t'`. -/
theorem reduces_projSel_boolArgs {B t t' : ℕ} (ht : t < B) :
    Lambda.reduces (appList (projSel B t) (boolArgs B t'))
      (if t = t' then Lambda.true else Lambda.false) := by
  have h := reduces_appList_projSel (n := B) (i := t) ht (boolArgs B t')
    (fun a ha => isClosed_mem_boolArgs ha) (boolArgs_length B t')
  rwa [boolArgs_getD ht] at h

theorem isClosed_mem_replicate_I {n : ℕ} {a : Lambda} (ha : a ∈ List.replicate n Lambda.I) :
    Lambda.IsClosed a := by
  rw [List.eq_of_mem_replicate ha]; exact IsClosed_I

theorem getD_append_last (l : List Lambda) (x d : Lambda) : (l ++ [x]).getD l.length d = x := by
  simp

theorem separable_true_false : Separable Lambda.true Lambda.false :=
  ⟨[], fun _ ha => absurd ha List.not_mem_nil, .refl _, .refl _⟩

/-- **Different heads.**  Two tagged tuples carrying different tags and the same number of stored
arguments are separable. -/
theorem separable_tagTuple_of_tag_ne {B K t₁ t₂ : ℕ} (ht₁ : t₁ < B) (ht₂ : t₂ < B)
    (hne : t₁ ≠ t₂) {A₁ A₂ : List Lambda} (hc₁ : ∀ a ∈ A₁, Lambda.IsClosed a)
    (hc₂ : ∀ a ∈ A₂, Lambda.IsClosed a) (hlen : A₁.length = A₂.length) (hK : A₁.length ≤ K) :
    Separable (appList (tagTuple B K t₁) A₁) (appList (tagTuple B K t₂) A₂) := by
  classical
  set k := A₁.length with hk
  set rep : List Lambda := List.replicate (K - k) Lambda.I with hrep
  set W : Lambda := projSel (K + 1) K with hW
  have hWcl : Lambda.IsClosed W := isClosed_projSel (by omega)
  have hrepcl : ∀ a ∈ rep, Lambda.IsClosed a := fun a ha => isClosed_mem_replicate_I ha
  -- the reduction performed on one side
  have key : ∀ (t : ℕ) (A : List Lambda), t < B → (∀ a ∈ A, Lambda.IsClosed a) → A.length = k →
      Lambda.reduces (appList (appList (tagTuple B K t) A) (rep ++ [W])) (projSel B t) := by
    intro t A ht hcA hAlen
    have hcat : ∀ a ∈ A ++ rep, Lambda.IsClosed a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hcA a ha
      · exact hrepcl a ha
    have hcatlen : (A ++ rep).length = K := by
      simp only [List.length_append, List.length_replicate, hAlen, hrep]
      omega
    have hstep := reduces_appList_tagTuple (B := B) (K := K) (i := t) ht (A ++ rep) hcat hcatlen
      (W := W) hWcl
    have hlist : appList (appList (tagTuple B K t) A) (rep ++ [W])
        = appList (tagTuple B K t) ((A ++ rep) ++ [W]) := by
      rw [← appList_append, ← List.append_assoc]
    rw [hlist]
    refine Lambda.reduces_trans hstep ?_
    have hsel := reduces_appList_projSel (n := K + 1) (i := K) (by omega)
      ((A ++ rep) ++ [projSel B t]) ?_ ?_
    · have hgetD : ((A ++ rep) ++ [projSel B t]).getD K (Lambda.var 0) = projSel B t := by
        rw [← hcatlen]
        exact getD_append_last _ _ _
      rwa [hgetD] at hsel
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hcat a ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact isClosed_projSel ht
        · exact absurd ha List.not_mem_nil
    · simp only [List.length_append, List.length_cons, List.length_nil] at hcatlen ⊢
      omega
  refine Separable.of_reduces (rep ++ [W]) ?_ (key t₁ A₁ ht₁ hc₁ rfl)
    (key t₂ A₂ ht₂ hc₂ hlen.symm) ?_
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hrepcl a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hWcl
      · exact absurd ha List.not_mem_nil
  · refine ⟨boolArgs B t₁, fun a ha => isClosed_mem_boolArgs ha, ?_, ?_⟩
    · have h := reduces_projSel_boolArgs (B := B) (t := t₁) (t' := t₁) ht₁
      rwa [if_pos rfl] at h
    · have h := reduces_projSel_boolArgs (B := B) (t := t₂) (t' := t₁) ht₂
      rwa [if_neg (fun hc => hne hc.symm)] at h

/-- **Different arities.**  Two tagged tuples with different numbers of stored arguments are
separable, whatever their tags. -/
theorem separable_tagTuple_of_length_lt {B K t₁ t₂ : ℕ} (ht₁ : t₁ < B) (ht₂ : t₂ < B)
    {A₁ A₂ : List Lambda} (hc₁ : ∀ a ∈ A₁, Lambda.IsClosed a) (hc₂ : ∀ a ∈ A₂, Lambda.IsClosed a)
    (hlt : A₁.length < A₂.length) (hK : A₂.length ≤ K) :
    Separable (appList (tagTuple B K t₁) A₁) (appList (tagTuple B K t₂) A₂) := by
  classical
  set k₁ := A₁.length with hk₁
  set k₂ := A₂.length with hk₂
  set T : Lambda := lamN (K + 1) Lambda.true with hT
  set F : Lambda := lamN (K + 1 + (k₂ - k₁)) Lambda.false with hF
  set R : List Lambda := List.replicate (k₂ - k₁ - 1) Lambda.I ++ [T] with hR
  set E' : List Lambda := List.replicate (K - k₂) Lambda.I ++ (F :: List.replicate
    (k₂ - k₁ - 1) Lambda.I) with hE'
  have hTcl : Lambda.IsClosed T := IsClosed_lamN IsClosed_true _
  have hFcl : Lambda.IsClosed F := IsClosed_lamN IsClosed_false _
  have hE'len : E'.length = K - k₁ := by
    simp only [hE', List.length_append, List.length_cons, List.length_replicate]
    omega
  have hE'cl : ∀ a ∈ E', Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact isClosed_mem_replicate_I ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hFcl
      · exact isClosed_mem_replicate_I ha
  refine Separable.of_reduces (M' := Lambda.true) (N' := Lambda.false) (E' ++ [T]) ?_ ?_ ?_
    separable_true_false
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hE'cl a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hTcl
      · exact absurd ha List.not_mem_nil
  · -- the short side: the tuple absorbs `A₁ ++ E'` and hands everything to `T`
    show Lambda.reduces (appList (appList (tagTuple B K t₁) A₁) (E' ++ [T])) Lambda.true
    have hlist : appList (appList (tagTuple B K t₁) A₁) (E' ++ [T])
        = appList (tagTuple B K t₁) ((A₁ ++ E') ++ [T]) := by
      rw [← appList_append, ← List.append_assoc]
    have hcat : ∀ a ∈ A₁ ++ E', Lambda.IsClosed a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hc₁ a ha
      · exact hE'cl a ha
    have hcatlen : (A₁ ++ E').length = K := by
      simp only [List.length_append, hE'len]
      omega
    rw [hlist]
    refine Lambda.reduces_trans
      (reduces_appList_tagTuple ht₁ (A₁ ++ E') hcat hcatlen hTcl) ?_
    rw [hT]
    refine reduces_appList_const IsClosed_true _ ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    simp only [List.length_append] at hcatlen
    omega
  · -- the long side: the tuple absorbs fewer of the extra arguments, and `F` gets the rest
    show Lambda.reduces (appList (appList (tagTuple B K t₂) A₂) (E' ++ [T])) Lambda.false
    have hsplit : appList (appList (tagTuple B K t₂) A₂) (E' ++ [T])
        = appList (appList (tagTuple B K t₂)
            ((A₂ ++ List.replicate (K - k₂) Lambda.I) ++ [F])) R := by
      rw [← appList_append, ← appList_append, hE', hR]
      congr 1
      simp
    have hcat : ∀ a ∈ A₂ ++ List.replicate (K - k₂) Lambda.I, Lambda.IsClosed a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hc₂ a ha
      · exact isClosed_mem_replicate_I ha
    have hcatlen : (A₂ ++ List.replicate (K - k₂) Lambda.I).length = K := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [hsplit]
    refine Lambda.reduces_trans (reduces_appList
      (reduces_appList_tagTuple ht₂ _ hcat hcatlen hFcl) R) ?_
    rw [← appList_append, hF]
    refine reduces_appList_const IsClosed_false _ ?_
    simp only [List.length_append, List.length_cons, List.length_nil, hcatlen, hR,
      List.length_replicate]
    omega

/-- Extracting the `r`-th stored argument of a tagged tuple. -/
theorem reduces_tagTuple_extract {B K t r : ℕ} (ht : t < B) {A : List Lambda}
    (hcA : ∀ a ∈ A, Lambda.IsClosed a) (hK : A.length ≤ K) (hr : r < A.length) :
    Lambda.reduces (appList (appList (tagTuple B K t) A)
        (List.replicate (K - A.length) Lambda.I ++ [projSel (K + 1) r]))
      (A.getD r (Lambda.var 0)) := by
  set rep : List Lambda := List.replicate (K - A.length) Lambda.I with hrep
  set W : Lambda := projSel (K + 1) r with hW
  have hWcl : Lambda.IsClosed W := isClosed_projSel (by omega)
  have hcat : ∀ a ∈ A ++ rep, Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hcA a ha
    · exact isClosed_mem_replicate_I ha
  have hcatlen : (A ++ rep).length = K := by
    simp only [List.length_append, List.length_replicate, hrep]
    omega
  have hlist : appList (appList (tagTuple B K t) A) (rep ++ [W])
      = appList (tagTuple B K t) ((A ++ rep) ++ [W]) := by
    rw [← appList_append, ← List.append_assoc]
  rw [hlist]
  refine Lambda.reduces_trans (reduces_appList_tagTuple ht (A ++ rep) hcat hcatlen hWcl) ?_
  have hcl' : ∀ a ∈ (A ++ rep) ++ [projSel B t], Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hcat a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact isClosed_projSel ht
      · exact absurd ha List.not_mem_nil
  have hlen' : ((A ++ rep) ++ [projSel B t]).length = K + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hcatlen ⊢
    omega
  have hsel := reduces_appList_projSel (n := K + 1) (i := r) (by omega)
    ((A ++ rep) ++ [projSel B t]) hcl' hlen'
  have hgetD : ((A ++ rep) ++ [projSel B t]).getD r (Lambda.var 0) = A.getD r (Lambda.var 0) := by
    rw [← List.getElem_eq_getD (fallback := Lambda.var 0) (h := by omega),
      ← List.getElem_eq_getD (fallback := Lambda.var 0) (h := hr)]
    have h1 : r < (A ++ rep).length := by simp only [List.length_append]; omega
    rw [List.getElem_append_left h1, List.getElem_append_left hr]
  rwa [hgetD] at hsel

/-! ## The Böhm-out induction -/

/-- The environment substituting the tagged tuple with tag `τ j` for the variable `j`. -/
def tagEnv (B K : ℕ) (τ : ℕ → ℕ) : ℕ → Lambda := fun j => tagTuple B K (τ j)

theorem isClosed_tagEnv {B K : ℕ} {τ : ℕ → ℕ} (hτ : ∀ j, τ j < B) (j : ℕ) :
    Lambda.IsClosed (tagEnv B K τ j) := isClosed_tagTuple (hτ j)

/-- Passing `b` further binders: the new binders get the fresh tags `base, …, base + b - 1`, and
the old variables keep theirs. -/
def tagShift (base b : ℕ) (τ : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if j < b then base + j else τ (j - b)

theorem tagShift_lt {B base b : ℕ} {τ : ℕ → ℕ} (hτ : ∀ j, τ j < B) (hb : base + b ≤ B) :
    ∀ j, tagShift base b τ j < B := by
  intro j
  by_cases hj : j < b <;> simp only [tagShift, hj, if_true, if_false]
  · omega
  · exact hτ _

theorem tagShift_lt_base {d base b : ℕ} {τ : ℕ → ℕ} (hτ : ∀ j, j < d → τ j < base) :
    ∀ j, j < b + d → tagShift base b τ j < base + b := by
  intro j hj
  by_cases hjb : j < b <;> simp only [tagShift, hjb, if_true, if_false]
  · omega
  · have := hτ (j - b) (by omega)
    omega

theorem tagShift_inj {d base b : ℕ} {τ : ℕ → ℕ} (hlt : ∀ j, j < d → τ j < base)
    (hinj : ∀ i j, i < d → j < d → τ i = τ j → i = j) :
    ∀ i j, i < b + d → j < b + d → tagShift base b τ i = tagShift base b τ j → i = j := by
  intro i j hi hj heq
  by_cases hib : i < b <;> by_cases hjb : j < b <;>
    simp only [tagShift, hib, hjb, if_true, if_false] at heq
  · omega
  · have := hlt (j - b) (by omega); omega
  · have := hlt (i - b) (by omega); omega
  · have := hinj (i - b) (j - b) (by omega) (by omega) heq
    omega

theorem extendEnv_tagEnv {B K base b : ℕ} (τ : ℕ → ℕ) :
    extendEnv (tagEnv B K (tagShift base b τ)) b (tagEnv B K τ)
      = tagEnv B K (tagShift base b τ) := by
  funext j
  by_cases hj : j < b
  · simp [extendEnv, hj]
  · simp [extendEnv, tagEnv, tagShift, hj]

/-- The descent step, phrased for the tag environments. -/
theorem reduces_node_tag {B K b h : ℕ} {as : List BohmNF} {base : ℕ} {τ : ℕ → ℕ}
    (hτB : ∀ j, τ j < B) (hb : base + b ≤ B) :
    Lambda.reduces
      (appList (instTree (tagEnv B K τ) (.node b h as))
        (argsFor (tagEnv B K (tagShift base b τ)) b))
      (appList (tagTuple B K (tagShift base b τ h))
        (as.map (instTree (tagEnv B K (tagShift base b τ))))) := by
  have h1 := reduces_instTree_node (ρ := tagEnv B K τ) (g := tagEnv B K (tagShift base b τ))
    (isClosed_tagEnv hτB) (isClosed_tagEnv (tagShift_lt hτB hb)) b h as
  rw [extendEnv_tagEnv] at h1
  exact h1

/-- **Böhm out.**  Two Böhm trees that differ somewhere along a common path are separable, once
their free variables have been replaced by pairwise distinct tagged tuples. -/
theorem separable_instTree {B K : ℕ} :
    ∀ {x y : BohmNF}, BohmDiffer x y → ∀ {d base s : ℕ} {τ : ℕ → ℕ},
      BohmNF.ArityLe K x → BohmNF.ArityLe K y →
      BohmNF.FreeVarsBelow d x → BohmNF.FreeVarsBelow d y →
      BohmNF.BinderRoom s x → BohmNF.BinderRoom s y → base + s ≤ B →
      (∀ j, τ j < B) → (∀ j, j < d → τ j < base) →
      (∀ i j, i < d → j < d → τ i = τ j → i = j) →
      Separable (instTree (tagEnv B K τ) x) (instTree (tagEnv B K τ) y) := by
  intro x y hd
  induction hd with
  | @root b h₁ h₂ as₁ as₂ hne =>
      intro d base s τ ha₁ ha₂ hf₁ hf₂ hb₁ hb₂ hbase hτB hτbase hτinj
      have hbs : b ≤ s := by cases hb₁ with | node hbb _ => exact hbb
      have hbB : base + b ≤ B := by omega
      have hτ'B : ∀ j, tagShift base b τ j < B := tagShift_lt hτB hbB
      have hcl' : ∀ j, Lambda.IsClosed (tagEnv B K (tagShift base b τ) j) := isClosed_tagEnv hτ'B
      have hk₁ : as₁.length ≤ K := by cases ha₁ with | node hl _ => exact hl
      have hk₂ : as₂.length ≤ K := by cases ha₂ with | node hl _ => exact hl
      have hh₁ : h₁ < b + d := by cases hf₁ with | node hh _ => exact hh
      have hh₂ : h₂ < b + d := by cases hf₂ with | node hh _ => exact hh
      have hcA : ∀ (as : List BohmNF) (a : Lambda),
          a ∈ as.map (instTree (tagEnv B K (tagShift base b τ))) → Lambda.IsClosed a := by
        intro as a ha
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
        exact isClosed_instTree hcl' z
      have hlen₁ : (as₁.map (instTree (tagEnv B K (tagShift base b τ)))).length = as₁.length := by
        simp
      have hlen₂ : (as₂.map (instTree (tagEnv B K (tagShift base b τ)))).length = as₂.length := by
        simp
      refine Separable.of_reduces (argsFor (tagEnv B K (tagShift base b τ)) b) ?_
        (reduces_node_tag hτB hbB) (reduces_node_tag hτB hbB) ?_
      · intro a ha
        obtain ⟨k, -, rfl⟩ := mem_argsFor ha
        exact hcl' k
      · rcases Nat.lt_trichotomy as₁.length as₂.length with hl | he | hl
        · exact separable_tagTuple_of_length_lt (hτ'B _) (hτ'B _) (hcA as₁) (hcA as₂)
            (by rw [hlen₁, hlen₂]; exact hl) (by rw [hlen₂]; exact hk₂)
        · have hh : h₁ ≠ h₂ := hne.resolve_right (fun hc => hc he)
          have hne' : tagShift base b τ h₁ ≠ tagShift base b τ h₂ := fun hc =>
            hh (tagShift_inj hτbase hτinj h₁ h₂ hh₁ hh₂ hc)
          exact separable_tagTuple_of_tag_ne (hτ'B _) (hτ'B _) hne' (hcA as₁) (hcA as₂)
            (by rw [hlen₁, hlen₂]; exact he) (by rw [hlen₁]; exact hk₁)
        · exact (separable_tagTuple_of_length_lt (hτ'B _) (hτ'B _) (hcA as₂) (hcA as₁)
            (by rw [hlen₁, hlen₂]; exact hl) (by rw [hlen₁]; exact hk₁)).symm
  | @arg b h r as₁ as₂ hr₁ hr₂ hlen hdiff ih =>
      intro d base s τ ha₁ ha₂ hf₁ hf₂ hb₁ hb₂ hbase hτB hτbase hτinj
      have hbs : b ≤ s := by cases hb₁ with | node hbb _ => exact hbb
      have hbB : base + b ≤ B := by omega
      have hτ'B : ∀ j, tagShift base b τ j < B := tagShift_lt hτB hbB
      have hcl' : ∀ j, Lambda.IsClosed (tagEnv B K (tagShift base b τ) j) := isClosed_tagEnv hτ'B
      have hk₁ : as₁.length ≤ K := by cases ha₁ with | node hl _ => exact hl
      have hcA : ∀ (as : List BohmNF) (a : Lambda),
          a ∈ as.map (instTree (tagEnv B K (tagShift base b τ))) → Lambda.IsClosed a := by
        intro as a ha
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
        exact isClosed_instTree hcl' z
      have hgetD : ∀ (as : List BohmNF) (hr : r < as.length),
          (as.map (instTree (tagEnv B K (tagShift base b τ)))).getD r (Lambda.var 0)
            = instTree (tagEnv B K (tagShift base b τ)) (as[r]'hr) := by
        intro as hr
        rw [← List.getElem_eq_getD (fallback := Lambda.var 0) (h := by simpa using hr)]
        simp
      have hchain : ∀ (as : List BohmNF) (hr : r < as.length), as.length = as₁.length →
          Lambda.reduces
            (appList (instTree (tagEnv B K τ) (.node b h as))
              (argsFor (tagEnv B K (tagShift base b τ)) b ++
                (List.replicate (K - as₁.length) Lambda.I ++ [projSel (K + 1) r])))
            (instTree (tagEnv B K (tagShift base b τ)) (as[r]'hr)) := by
        intro as hr hlen'
        rw [appList_append]
        refine Lambda.reduces_trans (reduces_appList (reduces_node_tag hτB hbB) _) ?_
        have hAlen : (as.map (instTree (tagEnv B K (tagShift base b τ)))).length = as₁.length := by
          simp [hlen']
        have hex := reduces_tagTuple_extract (B := B) (K := K) (t := tagShift base b τ h)
          (r := r) (hτ'B h) (A := as.map (instTree (tagEnv B K (tagShift base b τ)))) (hcA as)
          (by rw [hAlen]; exact hk₁) (by rw [hAlen, ← hlen']; exact hr)
        rw [hgetD as hr, hAlen] at hex
        exact hex
      have ha₁r : BohmNF.ArityLe K (as₁[r]'hr₁) := by
        cases ha₁ with | node _ hargs => exact hargs _ (List.getElem_mem hr₁)
      have ha₂r : BohmNF.ArityLe K (as₂[r]'hr₂) := by
        cases ha₂ with | node _ hargs => exact hargs _ (List.getElem_mem hr₂)
      have hf₁r : BohmNF.FreeVarsBelow (b + d) (as₁[r]'hr₁) := by
        cases hf₁ with | node _ hargs => exact hargs _ (List.getElem_mem hr₁)
      have hf₂r : BohmNF.FreeVarsBelow (b + d) (as₂[r]'hr₂) := by
        cases hf₂ with | node _ hargs => exact hargs _ (List.getElem_mem hr₂)
      have hb₁r : BohmNF.BinderRoom (s - b) (as₁[r]'hr₁) := by
        cases hb₁ with | node _ hargs => exact hargs _ (List.getElem_mem hr₁)
      have hb₂r : BohmNF.BinderRoom (s - b) (as₂[r]'hr₂) := by
        cases hb₂ with | node _ hargs => exact hargs _ (List.getElem_mem hr₂)
      refine Separable.of_reduces
        (argsFor (tagEnv B K (tagShift base b τ)) b ++
          (List.replicate (K - as₁.length) Lambda.I ++ [projSel (K + 1) r])) ?_
        (hchain as₁ hr₁ rfl) (hchain as₂ hr₂ hlen.symm) ?_
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨k, -, rfl⟩ := mem_argsFor ha
          exact hcl' k
        · rcases List.mem_append.1 ha with ha | ha
          · exact isClosed_mem_replicate_I ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact isClosed_projSel (by omega)
            · exact absurd ha List.not_mem_nil
      · exact ih (d := b + d) (base := base + b) (s := s - b) (τ := tagShift base b τ)
          ha₁r ha₂r hf₁r hf₂r hb₁r hb₂r (by omega) hτ'B (tagShift_lt_base hτbase)
          (tagShift_inj hτbase hτinj)

/-! ## Böhm's separation theorem for trees that differ along a path -/

theorem instTree_of_closed {ρ : ℕ → Lambda} {x : BohmNF} (h : BohmNF.FreeVarsBelow 0 x) :
    instTree ρ x = x.toTerm :=
  substEnv_of_isClosed (BohmNF.isClosed_toTerm h) _

/-- **Böhm's theorem, Böhm-out form.**  Two Böhm trees of *closed* normal forms which differ
somewhere along a common path are separable: a single list of closed arguments sends the first to
`true` and the second to `false`. -/
theorem separable_toTerm_of_bohmDiffer {x y : BohmNF} (hd : BohmDiffer x y)
    (hx : BohmNF.FreeVarsBelow 0 x) (hy : BohmNF.FreeVarsBelow 0 y) :
    Separable x.toTerm y.toTerm := by
  classical
  have h := separable_instTree (B := max x.binderDepth y.binderDepth + 1)
    (K := max x.maxArity y.maxArity) hd (d := 0) (base := 0)
    (s := max x.binderDepth y.binderDepth) (τ := fun _ => 0)
    (x.arityLe_maxArity.mono (le_max_left _ _)) (y.arityLe_maxArity.mono (le_max_right _ _))
    hx hy (x.binderRoom_binderDepth.mono (le_max_left _ _))
    (y.binderRoom_binderDepth.mono (le_max_right _ _)) (by omega)
    (fun _ => by simp) (fun j hj => by omega) (fun i j hi _ _ => by omega)
  rwa [instTree_of_closed hx, instTree_of_closed hy] at h

/-! ## Distinct trees with the same binders everywhere -/

/-- The two trees have the same number of binders at every node reachable in both.  For trees with
this property, being distinct is the same as differing along a path: no difference between them
can be attributed to η-expansion. -/
inductive BohmSameBinders : BohmNF → BohmNF → Prop
  | node {b h₁ h₂ : ℕ} {as₁ as₂ : List BohmNF}
      (hargs : ∀ (r : ℕ) (hr₁ : r < as₁.length) (hr₂ : r < as₂.length),
        BohmSameBinders (as₁[r]'hr₁) (as₂[r]'hr₂)) :
      BohmSameBinders (.node b h₁ as₁) (.node b h₂ as₂)

theorem bohmDiffer_of_ne {x y : BohmNF} (hsb : BohmSameBinders x y) (hne : x ≠ y) :
    BohmDiffer x y := by
  induction hsb with
  | @node b h₁ h₂ as₁ as₂ hargs ih =>
      by_cases hh : h₁ = h₂
      · by_cases hl : as₁.length = as₂.length
        · subst hh
          have hex : ∃ (r : ℕ) (hr₁ : r < as₁.length) (hr₂ : r < as₂.length),
              (as₁[r]'hr₁) ≠ (as₂[r]'hr₂) := by
            by_contra hc
            push Not at hc
            exact hne (by rw [List.ext_getElem hl (fun r h₁' h₂' => hc r h₁' h₂')])
          obtain ⟨r, hr₁, hr₂, hrne⟩ := hex
          exact .arg hr₁ hr₂ hl (ih r hr₁ hr₂ hrne)
        · exact .root (Or.inr hl)
      · exact .root (Or.inl hh)

/-- **Böhm's theorem for trees with matching binders.**  Two distinct Böhm trees of closed normal
forms which have the same number of binders at every node are separable. -/
theorem separable_toTerm_of_ne {x y : BohmNF} (hsb : BohmSameBinders x y) (hne : x ≠ y)
    (hx : BohmNF.FreeVarsBelow 0 x) (hy : BohmNF.FreeVarsBelow 0 y) :
    Separable x.toTerm y.toTerm :=
  separable_toTerm_of_bohmDiffer (bohmDiffer_of_ne hsb hne) hx hy

/-- **Böhm's theorem, term form.**  Two *different closed normal forms* whose Böhm trees have the
same number of binders at every node are separable by a list of closed arguments.  The hypothesis
on the binders is what rules out a difference that mere η-expansion would remove. -/
theorem separable_of_toTerm_ne {x y : BohmNF} (hsb : BohmSameBinders x y)
    (hx : Lambda.IsClosed x.toTerm) (hy : Lambda.IsClosed y.toTerm)
    (hne : x.toTerm ≠ y.toTerm) : Separable x.toTerm y.toTerm :=
  separable_toTerm_of_ne hsb (fun hc => hne (by rw [hc]))
    (BohmNF.freeVarsBelow_zero_of_isClosed hx) (BohmNF.freeVarsBelow_zero_of_isClosed hy)

end Lambda

end
