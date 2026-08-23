/-
# Böhm trees of normal forms, and separation at the root

Böhm's theorem says that two distinct βη-normal forms can be told apart by an applicative
context.  This module sets up the machinery for that statement — finite Böhm trees, and the
substitution performed by a list of closed arguments — and proves the two base cases of Böhm's
induction, namely a difference at the *root* of the two trees.

* `Lambda.lamN` — iterated abstraction, and its interaction with substitution;
* `Lambda.substDown`, `Lambda.argsFor` — the substitution performed when `λ…λ t` is applied to a
  list of closed arguments, and the argument lists realising a prescribed substitution;
* `Lambda.BohmNF`, `Lambda.BohmNF.toTerm` — the finite Böhm tree `λ…λ y t₁ … tₖ` of a normal
  form, and the term it denotes.  `Lambda.is_normal_iff_exists_bohmNF` and
  `Lambda.BohmNF.toTerm_injective` say that this is a faithful enumeration of the normal forms:
  the normal terms are exactly the denotations of Böhm trees, and distinct trees denote distinct
  terms;
* `Lambda.Separable` — some closed arguments send the first term to `Lambda.true` and the second
  to `Lambda.false`; `Lambda.Separable.symm` shows this relation is symmetric;
* `Lambda.separable_of_head_ne_gen` — two normal forms whose bound head variables **differ after
  η-expansion to a common arity** are separable (`Lambda.separable_of_head_ne` is the special case
  of equal numbers of leading abstractions);
* `Lambda.separable_of_length_lt_gen` — two normal forms with the same head after η-expansion to a
  common arity but **different numbers of arguments** are separable
  (`Lambda.separable_of_length_lt` is again the special case of equal numbers of abstractions);
* `Lambda.separable_of_root_ne_gen` — the two cases together, phrased for Böhm trees, with
  `Lambda.separable_of_root_ne` the equal-arity special case.

The separation results are therefore already η-general: two trees are separated as soon as their
roots differ once both have been η-expanded to a common number of leading abstractions.  What is
*not* proved here is Böhm's theorem in full: a difference deeper inside the two trees still has to
be brought to the root by a Böhm transformation ("Böhm out").
-/

import Start.Solvability

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Iterated abstraction -/

/-- `lamN n t = λ…λ t`, with `n` leading abstractions. -/
def lamN : ℕ → Lambda → Lambda
  | 0, t => t
  | n + 1, t => Lambda.lam (lamN n t)

@[simp] theorem lamN_zero (t : Lambda) : lamN 0 t = t := rfl

theorem lamN_succ (n : ℕ) (t : Lambda) : lamN (n + 1) t = Lambda.lam (lamN n t) := rfl

/-- Substituting a closed term under `n` abstractions shifts the variable index by `n`. -/
theorem subst_lamN {a : Lambda} (ha : Lambda.IsClosed a) :
    ∀ (m k : ℕ) (t : Lambda), Lambda.subst a k (lamN m t) = lamN m (Lambda.subst a (k + m) t) := by
  intro m
  induction m with
  | zero => intro k t; simp
  | succ m ih =>
      intro k t
      rw [lamN_succ]
      change Lambda.lam (Lambda.subst (Lambda.lift 1 0 a) (k + 1) (lamN m t)) = _
      rw [Lambda.lift_closed ha, ih (k + 1) t, lamN_succ]
      have hk : k + 1 + m = k + (m + 1) := by omega
      rw [hk]

/-- A closed body is untouched by substitution under any number of abstractions. -/
theorem subst_lamN_closed {X : Lambda} (hX : Lambda.IsClosed X) :
    ∀ (m k : ℕ) (a : Lambda), Lambda.subst a k (lamN m X) = lamN m X := by
  intro m
  induction m with
  | zero => intro k a; simpa using hX a k
  | succ m ih =>
      intro k a
      rw [lamN_succ]
      change Lambda.lam (Lambda.subst (Lambda.lift 1 0 a) (k + 1) (lamN m X)) = _
      rw [ih (k + 1) (Lambda.lift 1 0 a)]

theorem IsClosed_lamN {t : Lambda} (ht : Lambda.IsClosed t) (n : ℕ) :
    Lambda.IsClosed (lamN n t) := by
  induction n with
  | zero => simpa using ht
  | succ n ih => exact Lambda.IsClosed_lam ih

/-- Applying `λ…λ t` (with `m + 1` abstractions) to a closed argument. -/
theorem reduces_app_lamN {a : Lambda} (ha : Lambda.IsClosed a) (m : ℕ) (t : Lambda) :
    Lambda.reduces (Lambda.app (lamN (m + 1) t) a) (lamN m (Lambda.subst a m t)) := by
  refine .step _ _ _ (.beta _ _) ?_
  have h : Lambda.subst a 0 (lamN m t) = lamN m (Lambda.subst a m t) := by
    rw [subst_lamN ha m 0 t, Nat.zero_add]
  rw [h]
  exact .refl _

/-- Applying `λ…λ X` with a closed body `X` to any list of arguments of matching length. -/
theorem reduces_appList_lamN_closed {X : Lambda} (hX : Lambda.IsClosed X) :
    ∀ (args : List Lambda), Lambda.reduces (appList (lamN args.length X) args) X := by
  intro args
  induction args with
  | nil => exact .refl _
  | cons a args ih =>
      rw [List.length_cons, appList_cons]
      have hstep : Lambda.reduces (Lambda.app (lamN (args.length + 1) X) a) (lamN args.length X) :=
        .step _ _ _ (.beta _ _) (by rw [subst_lamN_closed hX args.length 0 a]; exact .refl _)
      exact Lambda.reduces_trans (reduces_appList hstep args) ih

/-! ## The substitution performed by a list of arguments -/

/-- `substDown [a₁, …, aₙ] t` substitutes `a₁` for the variable `n - 1`, then `a₂` for `n - 2`,
…, and finally `aₙ` for `0`.  This is the substitution performed when `λ…λ t` with `n` leading
abstractions is applied to `a₁ … aₙ`. -/
def substDown : List Lambda → Lambda → Lambda
  | [], t => t
  | a :: as, t => substDown as (Lambda.subst a as.length t)

@[simp] theorem substDown_nil (t : Lambda) : substDown [] t = t := rfl

theorem substDown_cons (a : Lambda) (as : List Lambda) (t : Lambda) :
    substDown (a :: as) t = substDown as (Lambda.subst a as.length t) := rfl

theorem substDown_closed {t : Lambda} (ht : Lambda.IsClosed t) (as : List Lambda) :
    substDown as t = t := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [substDown_cons, ht a as.length]; exact ih

theorem subst_appList (a : Lambda) (k : ℕ) :
    ∀ (t : Lambda) (Ms : List Lambda),
      Lambda.subst a k (appList t Ms) = appList (Lambda.subst a k t) (Ms.map (Lambda.subst a k)) :=
  fun t Ms => by
    induction Ms generalizing t with
    | nil => rfl
    | cons M Ms ih => rw [appList_cons, ih (Lambda.app t M), List.map_cons, appList_cons]; rfl

theorem substDown_appList :
    ∀ (as : List Lambda) (t : Lambda) (Ms : List Lambda),
      substDown as (appList t Ms) = appList (substDown as t) (Ms.map (substDown as)) := by
  intro as
  induction as with
  | nil =>
      intro t Ms
      have hid : substDown [] = id := funext fun _ => rfl
      simp [hid]
  | cons a as ih =>
      intro t Ms
      rw [substDown_cons, subst_appList, ih, List.map_map]
      rfl

/-- The list of arguments `[f (n-1), f (n-2), …, f 0]`, which substitutes `f k` for the variable
`k` in the body of an `n`-fold abstraction. -/
def argsFor (f : ℕ → Lambda) : ℕ → List Lambda
  | 0 => []
  | n + 1 => f n :: argsFor f n

@[simp] theorem argsFor_length (f : ℕ → Lambda) (n : ℕ) : (argsFor f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [argsFor, List.length_cons, ih]

theorem mem_argsFor {f : ℕ → Lambda} {n : ℕ} {a : Lambda} (h : a ∈ argsFor f n) :
    ∃ k, k < n ∧ a = f k := by
  induction n with
  | zero => cases h
  | succ n ih =>
      rw [argsFor, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨n, by omega, h⟩
      · obtain ⟨k, hk, hak⟩ := ih h
        exact ⟨k, by omega, hak⟩

theorem substDown_argsFor_var {f : ℕ → Lambda} (hf : ∀ k, Lambda.IsClosed (f k)) :
    ∀ {n i : ℕ}, i < n → substDown (argsFor f n) (Lambda.var i) = f i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      rw [argsFor, substDown_cons, argsFor_length]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · have hne : i ≠ n := by omega
        have hgt : ¬ i > n := by omega
        have : Lambda.subst (f n) n (Lambda.var i) = Lambda.var i := by
          simp [Lambda.subst, hne, hgt]
        rw [this]
        exact ih h
      · have : Lambda.subst (f i) i (Lambda.var i) = f i := by simp [Lambda.subst]
        rw [this]
        exact substDown_closed (hf i) _

/-- Applying an `n`-fold abstraction to `n` closed arguments performs `substDown`. -/
theorem reduces_appList_lamN {as : List Lambda} (has : ∀ a ∈ as, Lambda.IsClosed a) (t : Lambda) :
    Lambda.reduces (appList (lamN as.length t) as) (substDown as t) := by
  induction as generalizing t with
  | nil => exact .refl _
  | cons a as ih =>
      rw [List.length_cons, appList_cons, substDown_cons]
      have hstep : Lambda.reduces (Lambda.app (lamN (as.length + 1) t) a)
          (lamN as.length (Lambda.subst a as.length t)) :=
        reduces_app_lamN (has a List.mem_cons_self) _ _
      exact Lambda.reduces_trans (reduces_appList hstep as)
        (ih (fun b hb => has b (List.mem_cons_of_mem a hb)) _)

theorem appList_append :
    ∀ (l₁ l₂ : List Lambda) (t : Lambda), appList t (l₁ ++ l₂) = appList (appList t l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ t; rfl
  | cons a l₁ ih => intro l₂ t; rw [List.cons_append, appList_cons, appList_cons, ih]

theorem argsFor_take (f : ℕ → Lambda) (m : ℕ) :
    ∀ r : ℕ, (argsFor f (m + r)).take r = argsFor (fun k => f (k + m)) r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [show m + (r + 1) = (m + r) + 1 from by omega, argsFor, List.take_succ_cons, ih,
        argsFor]
      congr 2
      omega

theorem argsFor_drop (f : ℕ → Lambda) (m : ℕ) :
    ∀ r : ℕ, (argsFor f (m + r)).drop r = argsFor f m := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [show m + (r + 1) = (m + r) + 1 from by omega, argsFor, List.drop_succ_cons, ih]

/-- Applying `λ…λ xᵢ K₁ … K_p`, with `r` leading abstractions, to `m + r` closed arguments: the
first `r` arguments are consumed by the abstractions, so that the head `xᵢ` is replaced by the
argument of level `i + m`, and the remaining `m` arguments are appended to the arguments of the
head.  Taking `m > 0` is what η-expansion to a larger arity amounts to. -/
theorem reduces_argsFor_head {f : ℕ → Lambda} (hfc : ∀ k, Lambda.IsClosed (f k))
    (m r i : ℕ) (hi : i < r) (Ks : List Lambda) :
    Lambda.reduces (appList (lamN r (appList (Lambda.var i) Ks)) (argsFor f (m + r)))
      (appList (f (i + m))
        (Ks.map (substDown (argsFor (fun k => f (k + m)) r)) ++ argsFor f m)) := by
  have hclg : ∀ k, Lambda.IsClosed ((fun k => f (k + m)) k) := fun k => hfc _
  have hcl : ∀ a ∈ argsFor (fun k => f (k + m)) r, Lambda.IsClosed a := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := mem_argsFor ha
    exact hclg k
  have hred := reduces_appList_lamN (as := argsFor (fun k => f (k + m)) r) hcl
    (appList (Lambda.var i) Ks)
  rw [argsFor_length, substDown_appList, substDown_argsFor_var hclg hi] at hred
  rw [← List.take_append_drop r (argsFor f (m + r)), appList_append, argsFor_take, argsFor_drop]
  refine Lambda.reduces_trans (reduces_appList hred _) ?_
  rw [← appList_append]
  exact .refl _

/-! ## Separation -/

/-- `M` and `N` are *separable*: some closed arguments send `M` to `true` and `N` to `false`.
This is the applicative form of Böhm's separation property; since `Lambda.true` and
`Lambda.false` are the projections, it is equivalent to being separated by an arbitrary
context. -/
def Separable (M N : Lambda) : Prop :=
  ∃ args : List Lambda, (∀ a ∈ args, Lambda.IsClosed a) ∧
    Lambda.reduces (appList M args) Lambda.true ∧ Lambda.reduces (appList N args) Lambda.false

theorem IsClosed_I : Lambda.IsClosed Lambda.I := by
  intro s x
  simp [Lambda.I, Lambda.subst]

theorem IsClosed_true : Lambda.IsClosed Lambda.true := by
  intro s x
  simp [Lambda.true, Lambda.K, Lambda.subst]

theorem IsClosed_false : Lambda.IsClosed Lambda.false := by
  intro s x
  simp [Lambda.false, Lambda.church, Lambda.subst]

/-! ## Normal forms are exactly the finite Böhm trees -/

theorem normal_of_normal_lam {u : Lambda} (h : Lambda.is_normal (Lambda.lam u)) :
    Lambda.is_normal u := fun u' hu => h (Lambda.lam u') (.lam _ _ hu)

theorem normal_of_normal_app_left {f a : Lambda} (h : Lambda.is_normal (Lambda.app f a)) :
    Lambda.is_normal f := fun f' hf => h (Lambda.app f' a) (.app_left _ _ _ hf)

theorem normal_of_normal_app_right {f a : Lambda} (h : Lambda.is_normal (Lambda.app f a)) :
    Lambda.is_normal a := fun a' ha => h (Lambda.app f a') (.app_right _ _ _ ha)

theorem not_lam_of_normal_app {f a : Lambda} (h : Lambda.is_normal (Lambda.app f a)) :
    ∀ u, f ≠ Lambda.lam u := by
  intro u hu
  subst hu
  exact h (Lambda.subst a 0 u) (Lambda.step.beta u a)

theorem is_normal_lamN {t : Lambda} (ht : Lambda.is_normal t) :
    ∀ n, Lambda.is_normal (lamN n t)
  | 0 => ht
  | n + 1 => Lambda.lam_normal (is_normal_lamN ht n)

/-- A normal head that is not an abstraction stays normal, and stays a non-abstraction, when
applied to normal arguments. -/
theorem is_normal_appList :
    ∀ (args : List Lambda) (t : Lambda), Lambda.is_normal t → (∀ u, t ≠ Lambda.lam u) →
      (∀ a ∈ args, Lambda.is_normal a) →
      Lambda.is_normal (appList t args) ∧ ∀ u, appList t args ≠ Lambda.lam u := by
  intro args
  induction args with
  | nil => intro t ht hnl _; exact ⟨ht, hnl⟩
  | cons a args ih =>
      intro t ht hnl hargs
      rw [appList_cons]
      refine ih (Lambda.app t a) (Lambda.app_normal ht (hargs a List.mem_cons_self) hnl)
        (fun u h => Lambda.noConfusion h) (fun b hb => hargs b (List.mem_cons_of_mem a hb))

/-- A **Böhm tree of a normal form**: `node b h args` stands for the term
`λ…λ h t₁ … tₖ` with `b` leading abstractions and the arguments given by `args`.  Since a normal
form has no infinite head reduction, its Böhm tree is this finite tree. -/
inductive BohmNF where
  | node (binders head : ℕ) (args : List BohmNF) : BohmNF

/-- The term denoted by a Böhm tree. -/
def BohmNF.toTerm : BohmNF → Lambda
  | .node b h args => lamN b (appList (Lambda.var h) (args.map BohmNF.toTerm))

theorem BohmNF.toTerm_node (b h : ℕ) (args : List BohmNF) :
    (BohmNF.node b h args).toTerm = lamN b (appList (Lambda.var h) (args.map BohmNF.toTerm)) := by
  rw [BohmNF.toTerm]

/-- Induction over Böhm trees, with the induction hypothesis available for every argument. -/
theorem BohmNF.ind_mem {P : BohmNF → Prop}
    (hnode : ∀ (b h : ℕ) (args : List BohmNF), (∀ a ∈ args, P a) → P (.node b h args)) :
    ∀ x, P x :=
  fun x =>
    BohmNF.rec (motive_1 := P) (motive_2 := fun l => ∀ a ∈ l, P a)
      (fun b h args ih => hnode b h args ih) (fun _ ha => absurd ha List.not_mem_nil)
      (fun _ _ ihh iht a ha => by
        rcases List.mem_cons.1 ha with rfl | hmem
        · exact ihh
        · exact iht a hmem) x

/-- Every Böhm tree denotes a normal form. -/
theorem BohmNF.is_normal_toTerm (x : BohmNF) : Lambda.is_normal x.toTerm := by
  induction x using BohmNF.ind_mem with
  | _ b h args ih =>
      rw [BohmNF.toTerm_node]
      refine is_normal_lamN ?_ b
      refine (is_normal_appList _ (Lambda.var h) (Lambda.var_normal h)
        (fun u hu => Lambda.noConfusion hu) ?_).1
      intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      exact ih a' ha'

/-- Every normal form is denoted by a Böhm tree. -/
theorem exists_bohmNF_of_normal :
    ∀ t : Lambda, Lambda.is_normal t → ∃ x : BohmNF, t = x.toTerm := by
  intro t
  induction t with
  | var h => intro _; exact ⟨.node 0 h [], by rw [BohmNF.toTerm_node]; rfl⟩
  | lam u ih =>
      intro h
      obtain ⟨x, hx⟩ := ih (normal_of_normal_lam h)
      obtain ⟨b, hd, args⟩ := x
      refine ⟨.node (b + 1) hd args, ?_⟩
      rw [BohmNF.toTerm_node, lamN_succ, ← BohmNF.toTerm_node, ← hx]
  | app f a ihf iha =>
      intro h
      obtain ⟨xf, hxf⟩ := ihf (normal_of_normal_app_left h)
      obtain ⟨xa, hxa⟩ := iha (normal_of_normal_app_right h)
      obtain ⟨b, hd, args⟩ := xf
      cases b with
      | succ b =>
          rw [BohmNF.toTerm_node, lamN_succ] at hxf
          exact absurd hxf (not_lam_of_normal_app h _)
      | zero =>
          refine ⟨.node 0 hd (args ++ [xa]), ?_⟩
          rw [BohmNF.toTerm_node, lamN_zero, List.map_append, List.map_cons, List.map_nil,
            appList_concat]
          rw [BohmNF.toTerm_node, lamN_zero] at hxf
          rw [← hxf, ← hxa]

/-- Normal forms **are** the finite Böhm trees. -/
theorem is_normal_iff_exists_bohmNF {t : Lambda} :
    Lambda.is_normal t ↔ ∃ x : BohmNF, t = x.toTerm :=
  ⟨exists_bohmNF_of_normal t, fun ⟨x, hx⟩ => hx ▸ x.is_normal_toTerm⟩

/-! ## Böhm trees are a faithful representation -/

theorem appList_ne_lam :
    ∀ (l : List Lambda) (t : Lambda), (∀ u, t ≠ Lambda.lam u) →
      ∀ u, appList t l ≠ Lambda.lam u := by
  intro l
  induction l with
  | nil => intro t ht u; exact ht u
  | cons a l ih =>
      intro t _ u
      rw [appList_cons]
      exact ih (Lambda.app t a) (fun v h => Lambda.noConfusion h) u

theorem lamN_inj :
    ∀ (b₁ b₂ : ℕ) (X₁ X₂ : Lambda), (∀ u, X₁ ≠ Lambda.lam u) → (∀ u, X₂ ≠ Lambda.lam u) →
      lamN b₁ X₁ = lamN b₂ X₂ → b₁ = b₂ ∧ X₁ = X₂ := by
  intro b₁
  induction b₁ with
  | zero =>
      intro b₂ X₁ X₂ h₁ _ heq
      cases b₂ with
      | zero => exact ⟨rfl, heq⟩
      | succ b₂ =>
          rw [lamN_zero, lamN_succ] at heq
          exact absurd heq (h₁ _)
  | succ b₁ ih =>
      intro b₂ X₁ X₂ h₁ h₂ heq
      cases b₂ with
      | zero =>
          rw [lamN_zero, lamN_succ] at heq
          exact absurd heq.symm (h₂ _)
      | succ b₂ =>
          rw [lamN_succ, lamN_succ] at heq
          obtain ⟨hb, hX⟩ := ih b₂ X₁ X₂ h₁ h₂ (Lambda.lam.inj heq)
          exact ⟨by rw [hb], hX⟩

theorem appList_inj :
    ∀ (l₁ l₂ : List Lambda) (t₁ t₂ : Lambda),
      (∀ p q, t₁ ≠ Lambda.app p q) → (∀ p q, t₂ ≠ Lambda.app p q) →
      appList t₁ l₁ = appList t₂ l₂ → t₁ = t₂ ∧ l₁ = l₂ := by
  intro l₁
  induction l₁ using List.reverseRecOn with
  | nil =>
      intro l₂ t₁ t₂ h₁ _ heq
      cases l₂ using List.reverseRecOn with
      | nil => exact ⟨heq, rfl⟩
      | append_singleton l₂ a _ =>
          rw [appList_nil, appList_concat] at heq
          exact absurd heq (h₁ _ _)
  | append_singleton l₁ a ih =>
      intro l₂ t₁ t₂ h₁ h₂ heq
      cases l₂ using List.reverseRecOn with
      | nil =>
          rw [appList_nil, appList_concat] at heq
          exact absurd heq.symm (h₂ _ _)
      | append_singleton l₂ b _ =>
          rw [appList_concat, appList_concat] at heq
          obtain ⟨hspine, hab⟩ := Lambda.app.inj heq
          obtain ⟨ht, hl⟩ := ih l₂ t₁ t₂ h₁ h₂ hspine
          exact ⟨ht, by rw [hl, hab]⟩

theorem map_toTerm_inj :
    ∀ (l₁ l₂ : List BohmNF), (∀ a ∈ l₁, ∀ y : BohmNF, a.toTerm = y.toTerm → a = y) →
      l₁.map BohmNF.toTerm = l₂.map BohmNF.toTerm → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ heq; cases l₂ with
    | nil => rfl
    | cons b l₂ => exact absurd heq (by simp)
  | cons a l₁ ih =>
      intro l₂ hinj heq
      cases l₂ with
      | nil => exact absurd heq (by simp)
      | cons b l₂ =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at heq
          have hab : a = b := hinj a List.mem_cons_self b heq.1
          have htl : l₁ = l₂ :=
            ih l₂ (fun c hc => hinj c (List.mem_cons_of_mem a hc)) heq.2
          rw [hab, htl]

/-- Distinct Böhm trees denote distinct normal forms: the representation of a normal form by a
Böhm tree is faithful. -/
theorem BohmNF.toTerm_injective : Function.Injective BohmNF.toTerm := by
  have key : ∀ x y : BohmNF, x.toTerm = y.toTerm → x = y := by
    intro x
    induction x using BohmNF.ind_mem with
    | _ b₁ h₁ args₁ ih =>
        intro y hxy
        obtain ⟨b₂, h₂, args₂⟩ := y
        rw [BohmNF.toTerm_node, BohmNF.toTerm_node] at hxy
        obtain ⟨hb, hX⟩ := lamN_inj b₁ b₂ _ _
          (appList_ne_lam _ _ fun u h => Lambda.noConfusion h)
          (appList_ne_lam _ _ fun u h => Lambda.noConfusion h) hxy
        obtain ⟨hhead, hargs⟩ := appList_inj _ _ _ _
          (fun p q h => Lambda.noConfusion h) (fun p q h => Lambda.noConfusion h) hX
        have hh : h₁ = h₂ := Lambda.var.inj hhead
        rw [hb, hh, map_toTerm_inj args₁ args₂ ih hargs]
  exact fun x y h => key x y h

/-- Two normal forms are equal exactly when their Böhm trees are. -/
theorem BohmNF.toTerm_inj_iff {x y : BohmNF} : x.toTerm = y.toTerm ↔ x = y :=
  ⟨fun h => BohmNF.toTerm_injective h, fun h => by rw [h]⟩

/-! ## Separation: same head, different number of arguments -/

/-- The selector `λ…λ x₀` (with `m + 1` abstractions, returning its last argument) is closed. -/
theorem subst_lamN_var0 : ∀ (m k : ℕ) (a : Lambda),
    Lambda.subst a k (lamN (m + 1) (Lambda.var 0)) = lamN (m + 1) (Lambda.var 0) := by
  intro m
  induction m with
  | zero => intro k a; simp [lamN, Lambda.subst]
  | succ m ih =>
      intro k a
      rw [lamN_succ (m + 1)]
      change Lambda.lam (Lambda.subst (Lambda.lift 1 0 a) (k + 1) (lamN (m + 1) (Lambda.var 0))) = _
      rw [ih (k + 1) (Lambda.lift 1 0 a)]

theorem IsClosed_lamN_var0 (m : ℕ) : Lambda.IsClosed (lamN (m + 1) (Lambda.var 0)) :=
  fun s x => subst_lamN_var0 m x s

/-- The selector returns its last argument. -/
theorem reduces_appList_lamN_var0 : ∀ (l : List Lambda) (z : Lambda),
    Lambda.reduces (appList (lamN (l.length + 1) (Lambda.var 0)) (l ++ [z])) z := by
  intro l
  induction l with
  | nil =>
      intro z
      have hz : Lambda.subst z 0 (Lambda.var 0) = z := by simp [Lambda.subst]
      refine .step _ _ _ (.beta _ _) ?_
      rw [lamN_zero, hz]
      exact .refl _
  | cons a l ih =>
      intro z
      rw [List.cons_append, List.length_cons, appList_cons]
      have hstep : Lambda.reduces (Lambda.app (lamN (l.length + 1 + 1) (Lambda.var 0)) a)
          (lamN (l.length + 1) (Lambda.var 0)) :=
        .step _ _ _ (.beta _ _) (by rw [subst_lamN_var0 l.length 0 a]; exact .refl _)
      exact Lambda.reduces_trans (reduces_appList hstep (l ++ [z])) (ih z)

theorem reduces_appList_selector {m : ℕ} (l : List Lambda) (z : Lambda) (h : l.length = m) :
    Lambda.reduces (appList (lamN (m + 1) (Lambda.var 0)) (l ++ [z])) z := by
  subst h
  exact reduces_appList_lamN_var0 l z

theorem reduces_appList_const {X : Lambda} (hX : Lambda.IsClosed X) {m : ℕ} (args : List Lambda)
    (h : args.length = m) : Lambda.reduces (appList (lamN m X) args) X := by
  subst h
  exact reduces_appList_lamN_closed hX args

/-- Separability is symmetric: appending `false, true` swaps the two outcomes. -/
theorem Separable.symm {M N : Lambda} (h : Separable M N) : Separable N M := by
  obtain ⟨args, hcl, hM, hN⟩ := h
  refine ⟨args ++ [Lambda.false, Lambda.true], ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hcl a h
    · rcases List.mem_cons.1 h with rfl | h
      · exact IsClosed_false
      · rcases List.mem_cons.1 h with rfl | h
        · exact IsClosed_true
        · exact absurd h List.not_mem_nil
  · rw [appList_append]
    refine Lambda.reduces_trans (reduces_appList hN [Lambda.false, Lambda.true]) ?_
    exact Lambda.false_works Lambda.false Lambda.true
  · rw [appList_append]
    refine Lambda.reduces_trans (reduces_appList hM [Lambda.false, Lambda.true]) ?_
    exact Lambda.true_works Lambda.false Lambda.true

/-- **The head case of Böhm's theorem.**  Two normal forms whose head variables are bound and,
after η-expansion to the common arity `m₁ + r₁ = m₂ + r₂`, *different* are separated by closed
arguments: substituting a selector for each of the two head variables produces `true` on one side
and `false` on the other, whatever the arguments of the heads are. -/
theorem separable_of_head_ne_gen {m₁ m₂ r₁ r₂ i j : ℕ} (hn : m₁ + r₁ = m₂ + r₂)
    (hi : i < r₁) (hj : j < r₂) (hne : i + m₁ ≠ j + m₂) (Ms Ns : List Lambda) :
    Separable (lamN r₁ (appList (Lambda.var i) Ms)) (lamN r₂ (appList (Lambda.var j) Ns)) := by
  classical
  set f : ℕ → Lambda := fun k =>
    if k = i + m₁ then lamN (Ms.length + m₁) Lambda.true
    else if k = j + m₂ then lamN (Ns.length + m₂) Lambda.false
    else Lambda.I with hf
  have hfc : ∀ k, Lambda.IsClosed (f k) := by
    intro k
    rw [hf]
    dsimp only
    split
    · exact IsClosed_lamN IsClosed_true _
    · split
      · exact IsClosed_lamN IsClosed_false _
      · exact IsClosed_I
  have hfi : f (i + m₁) = lamN (Ms.length + m₁) Lambda.true := by
    rw [hf]; dsimp only; rw [if_pos rfl]
  have hfj : f (j + m₂) = lamN (Ns.length + m₂) Lambda.false := by
    rw [hf]; dsimp only; rw [if_neg fun h => hne h.symm, if_pos rfl]
  have hcl : ∀ a ∈ argsFor f (m₁ + r₁), Lambda.IsClosed a := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := mem_argsFor ha
    exact hfc k
  refine ⟨argsFor f (m₁ + r₁), hcl, ?_, ?_⟩
  · refine Lambda.reduces_trans (reduces_argsFor_head hfc m₁ r₁ i hi Ms) ?_
    rw [hfi]
    exact reduces_appList_const IsClosed_true _ (by simp)
  · rw [hn]
    refine Lambda.reduces_trans (reduces_argsFor_head hfc m₂ r₂ j hj Ns) ?_
    rw [hfj]
    exact reduces_appList_const IsClosed_false _ (by simp)

/-- Two normal forms with the same number of leading abstractions and different bound head
variables are separable. -/
theorem separable_of_head_ne {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (Ms Ns : List Lambda) :
    Separable (lamN n (appList (Lambda.var i) Ms)) (lamN n (appList (Lambda.var j) Ns)) :=
  separable_of_head_ne_gen (m₁ := 0) (m₂ := 0) rfl hi hj (by simpa using hij) Ms Ns

/-- **The arity case of Böhm's theorem.**  Two normal forms whose head variables are bound and,
after η-expansion to the common arity `m₁ + r₁ = m₂ + r₂`, *equal*, but which then have different
numbers of arguments, are separated by closed arguments: the head is replaced by a selector which
reads off an argument supplied after the arguments of the head, and the two sides then read off
different ones. -/
theorem separable_of_length_lt_gen {m₁ m₂ r₁ r₂ i j : ℕ} (hn : m₁ + r₁ = m₂ + r₂)
    (hi : i < r₁) (hj : j < r₂) (hhead : i + m₁ = j + m₂) (Ms Ns : List Lambda)
    (hlt : Ms.length + m₁ < Ns.length + m₂) :
    Separable (lamN r₁ (appList (Lambda.var i) Ms)) (lamN r₂ (appList (Lambda.var j) Ns)) := by
  classical
  set p := Ms.length + m₁ with hp
  obtain ⟨d, hd⟩ : ∃ d, Ns.length + m₂ = p + d + 1 := ⟨Ns.length + m₂ - p - 1, by omega⟩
  set f : ℕ → Lambda := fun k =>
    if k = i + m₁ then lamN (p + d + 2) (Lambda.var 0) else Lambda.I with hf
  set B₁ : Lambda := lamN (d + 1) Lambda.false with hB₁
  set rest : List Lambda := List.replicate d Lambda.I ++ [Lambda.true] with hrest
  have hfc : ∀ k, Lambda.IsClosed (f k) := by
    intro k
    rw [hf]
    dsimp only
    split
    · exact IsClosed_lamN_var0 _
    · exact IsClosed_I
  have hfi : f (i + m₁) = lamN (p + d + 2) (Lambda.var 0) := by
    rw [hf]; dsimp only; rw [if_pos rfl]
  have hfj : f (j + m₂) = lamN (p + d + 2) (Lambda.var 0) := by
    rw [← hhead]; exact hfi
  have hcl : ∀ a ∈ argsFor f (m₁ + r₁), Lambda.IsClosed a := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := mem_argsFor ha
    exact hfc k
  have hclB : ∀ a ∈ B₁ :: rest, Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact IsClosed_lamN (IsClosed_lamN IsClosed_false 0) _
    · rw [hrest] at ha
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha]; exact IsClosed_I
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact IsClosed_true
        · exact absurd ha List.not_mem_nil
  refine ⟨argsFor f (m₁ + r₁) ++ (B₁ :: rest), ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hcl a h
    · exact hclB a h
  · rw [appList_append]
    refine Lambda.reduces_trans
      (reduces_appList (reduces_argsFor_head hfc m₁ r₁ i hi Ms) (B₁ :: rest)) ?_
    rw [← appList_append, hfi]
    have hsplit : (Ms.map (substDown (argsFor (fun k => f (k + m₁)) r₁)) ++ argsFor f m₁) ++
        (B₁ :: rest) =
        ((Ms.map (substDown (argsFor (fun k => f (k + m₁)) r₁)) ++ argsFor f m₁) ++
          (B₁ :: List.replicate d Lambda.I)) ++ [Lambda.true] := by
      rw [hrest]; simp
    rw [hsplit]
    refine reduces_appList_selector _ _ ?_
    simp [argsFor_length, hp]
    omega
  · rw [hn, appList_append]
    refine Lambda.reduces_trans
      (reduces_appList (reduces_argsFor_head hfc m₂ r₂ j hj Ns) (B₁ :: rest)) ?_
    rw [← appList_append, hfj]
    have hsplit : (Ns.map (substDown (argsFor (fun k => f (k + m₂)) r₂)) ++ argsFor f m₂) ++
        (B₁ :: rest) =
        ((Ns.map (substDown (argsFor (fun k => f (k + m₂)) r₂)) ++ argsFor f m₂) ++ [B₁])
          ++ rest := by
      simp
    rw [hsplit, appList_append]
    refine Lambda.reduces_trans (reduces_appList (reduces_appList_selector _ _ ?_) rest) ?_
    · simp [argsFor_length, hp]
      omega
    · rw [hB₁]
      refine reduces_appList_const IsClosed_false _ ?_
      rw [hrest]
      simp

/-- Two normal forms with the same number of leading abstractions and the same bound head
variable, but a different number of arguments, are separable. -/
theorem separable_of_length_lt {n i : ℕ} (hi : i < n) (Ms Ns : List Lambda)
    (hlt : Ms.length < Ns.length) :
    Separable (lamN n (appList (Lambda.var i) Ms)) (lamN n (appList (Lambda.var i) Ns)) :=
  separable_of_length_lt_gen (m₁ := 0) (m₂ := 0) rfl hi hi rfl Ms Ns (by simpa using hlt)

/-! ## Separation of Böhm trees that differ at the root -/

/-- **Böhm's theorem for a difference at the root, up to η.**  Two normal forms whose head
variables are bound are separable as soon as their roots differ after η-expansion to the common
arity `m₁ + b₁ = m₂ + b₂`, either in the head variable or in the number of arguments. -/
theorem separable_of_root_ne_gen {m₁ m₂ b₁ b₂ h₁ h₂ : ℕ} {args₁ args₂ : List BohmNF}
    (hn : m₁ + b₁ = m₂ + b₂) (hb₁ : h₁ < b₁) (hb₂ : h₂ < b₂)
    (hne : h₁ + m₁ ≠ h₂ + m₂ ∨ args₁.length + m₁ ≠ args₂.length + m₂) :
    Separable (BohmNF.node b₁ h₁ args₁).toTerm (BohmNF.node b₂ h₂ args₂).toTerm := by
  rw [BohmNF.toTerm_node, BohmNF.toTerm_node]
  by_cases hh : h₁ + m₁ = h₂ + m₂
  · have hlen : args₁.length + m₁ ≠ args₂.length + m₂ := hne.resolve_left (fun h => h hh)
    rcases Nat.lt_or_ge (args₁.length + m₁) (args₂.length + m₂) with hl | hl
    · exact separable_of_length_lt_gen hn hb₁ hb₂ hh _ _ (by simpa using hl)
    · exact (separable_of_length_lt_gen hn.symm hb₂ hb₁ hh.symm _ _ (by simp; omega)).symm
  · exact separable_of_head_ne_gen hn hb₁ hb₂ hh _ _

/-- **Böhm's theorem for a difference at the root.**  Two normal forms with the same number of
leading abstractions whose head variables are bound are separable as soon as their roots differ,
either in the head variable or in the number of arguments. -/
theorem separable_of_root_ne {b h₁ h₂ : ℕ} {args₁ args₂ : List BohmNF}
    (hb₁ : h₁ < b) (hb₂ : h₂ < b) (hne : h₁ ≠ h₂ ∨ args₁.length ≠ args₂.length) :
    Separable (BohmNF.node b h₁ args₁).toTerm (BohmNF.node b h₂ args₂).toTerm :=
  separable_of_root_ne_gen (m₁ := 0) (m₂ := 0) rfl hb₁ hb₂ (by simpa using hne)

end Lambda

end
