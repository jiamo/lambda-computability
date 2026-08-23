/-
Simple types over the de Bruijn syntax of this development, and **strong normalization**.

The library so far is about the *untyped* calculus, where terms such as `omega` have no normal
form at all.  This file adds the other classical half of the picture: a simply typed lambda
calculus built on the very same `Lambda` syntax, and Tait's reducibility proof that every typable
term is strongly normalizing.

* `Lambda.Ty` — simple types, `base` and `A ⇒ B`.
* `Lambda.Typing Γ t A` — the usual three rules over a context `Γ : List Ty`.
* `Lambda.SN t` — strong normalization, `Acc` of the reverse of `Lambda.step`.
* `Lambda.Red A t` — Tait's reducibility (logical) predicate, defined by recursion on the type.
* `Lambda.cr` — the three "reducibility candidate" conditions CR1, CR2, CR3, proved together by
  induction on the type.
* `Lambda.red_substEnv` — the fundamental lemma: a typed term is reducible under any reducible
  parallel substitution.
* `Lambda.sn_of_typing` — **strong normalization**: `Γ ⊢ t : A` implies `SN t`.

Two corollaries record that the theorem has content: every typable term has a normal form
(`Lambda.hasNormalForm_of_typing`), and the paradigmatic untypable term `omega` is not typable
(`Lambda.not_typing_omega`), so the untyped calculus is strictly larger.
-/

import Start.SelfInterpreter
import Start.NormalizationUndecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

------------------------------------------------------------------------
-- Simple types and typing
------------------------------------------------------------------------

/-- Simple types: one base type and function types. -/
inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

/-- Typing for the de Bruijn syntax; the context lists the types of the free variables, index `0`
first. -/
inductive Typing : List Ty → Lambda → Ty → Prop
  | var {Γ : List Ty} {i : ℕ} {A : Ty} : Γ[i]? = some A → Typing Γ (Lambda.var i) A
  | app {Γ : List Ty} {a b : Lambda} {A B : Ty} :
      Typing Γ a (Ty.arrow A B) → Typing Γ b A → Typing Γ (Lambda.app a b) B
  | lam {Γ : List Ty} {t : Lambda} {A B : Ty} :
      Typing (A :: Γ) t B → Typing Γ (Lambda.lam t) (Ty.arrow A B)

------------------------------------------------------------------------
-- Strong normalization
------------------------------------------------------------------------

/-- A term is strongly normalizing when the reduction relation is well founded above it. -/
def SN (t : Lambda) : Prop := Acc (fun a b => Lambda.step b a) t

theorem SN.step {t t' : Lambda} (h : SN t) (hs : Lambda.step t t') : SN t' := h.inv hs

theorem SN.intro {t : Lambda} (h : ∀ t', Lambda.step t t' → SN t') : SN t := Acc.intro t h

theorem not_step_var {i : ℕ} {t : Lambda} : ¬ Lambda.step (Lambda.var i) t := by
  intro h; cases h

theorem sn_var (i : ℕ) : SN (Lambda.var i) :=
  SN.intro fun _ h => absurd h not_step_var

/-- Single-step reduction is a congruence for substitution. -/
theorem step_subst {t t' : Lambda} (h : Lambda.step t t') :
    ∀ (v : Lambda) (x : ℕ), Lambda.step (Lambda.subst v x t) (Lambda.subst v x t') := by
  induction h with
  | beta a b =>
      intro v x
      have hb := Lambda.step.beta (Lambda.subst (Lambda.lift 1 0 v) (x + 1) a)
        (Lambda.subst v x b)
      simpa [Lambda.subst, Lambda.subst_subst_zero a v b x] using hb
  | app_left t₁ t₁' t₂ _ ih =>
      intro v x
      exact Lambda.step.app_left _ _ _ (ih v x)
  | app_right t₁ t₂ t₂' _ ih =>
      intro v x
      exact Lambda.step.app_right _ _ _ (ih v x)
  | lam t t' _ ih =>
      intro v x
      exact Lambda.step.lam _ _ (ih (Lambda.lift 1 0 v) (x + 1))

/-- If a step-preserving map sends `t` to a strongly normalizing term, then `t` is strongly
normalizing. -/
theorem sn_of_map (f : Lambda → Lambda)
    (hf : ∀ a b, Lambda.step a b → Lambda.step (f a) (f b)) :
    ∀ {s : Lambda}, SN s → ∀ t : Lambda, f t = s → SN t := by
  intro s hs
  induction hs with
  | intro s _ ih =>
      intro t ht
      refine SN.intro fun t' hstep => ?_
      exact ih (f t') (by rw [← ht]; exact hf t t' hstep) t' rfl

theorem sn_of_sn_subst {v : Lambda} {x : ℕ} {t : Lambda}
    (h : SN (Lambda.subst v x t)) : SN t :=
  sn_of_map (Lambda.subst v x) (fun _ _ hs => step_subst hs v x) h t rfl

theorem sn_app_left {t u : Lambda} (h : SN (Lambda.app t u)) : SN t :=
  sn_of_map (fun a => Lambda.app a u)
    (fun _ _ hs => Lambda.step.app_left _ _ _ hs) h t rfl

------------------------------------------------------------------------
-- Neutral terms
------------------------------------------------------------------------

/-- A term is *not an abstraction* when applying it cannot create a redex.  (This is weaker than
`Lambda.Neutral` of `Start/Leftmost.lean`, which additionally constrains the head.) -/
def NotAbs : Lambda → Prop
  | Lambda.lam _ => False
  | _ => True

theorem notAbs_var (i : ℕ) : NotAbs (Lambda.var i) := trivial
theorem notAbs_app (a b : Lambda) : NotAbs (Lambda.app a b) := trivial

------------------------------------------------------------------------
-- Reducibility
------------------------------------------------------------------------

/-- Tait's reducibility predicate. -/
def Red : Ty → Lambda → Prop
  | Ty.base, t => SN t
  | Ty.arrow A B, t => ∀ u : Lambda, Red A u → Red B (Lambda.app t u)

/-- The three reducibility-candidate conditions, proved simultaneously by induction on the
type: reducible terms are strongly normalizing (CR1), reducibility is preserved by reduction
(CR2), and a neutral term all of whose reducts are reducible is reducible (CR3). -/
theorem cr (A : Ty) :
    (∀ t, Red A t → SN t) ∧
    (∀ t t', Red A t → Lambda.step t t' → Red A t') ∧
    (∀ t, NotAbs t → (∀ t', Lambda.step t t' → Red A t') → Red A t) := by
  induction A with
  | base =>
      refine ⟨fun _ h => h, fun _ _ h hs => h.step hs, fun t _ h => SN.intro h⟩
  | arrow A B ihA ihB =>
      obtain ⟨ihA1, ihA2, ihA3⟩ := ihA
      obtain ⟨ihB1, ihB2, ihB3⟩ := ihB
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        have hv : Red A (Lambda.var 0) :=
          ihA3 _ (notAbs_var 0) fun _ h => absurd h not_step_var
        exact sn_app_left (ihB1 _ (ht _ hv))
      · intro t t' ht hs u hu
        exact ihB2 _ _ (ht u hu) (Lambda.step.app_left _ _ _ hs)
      · intro t hn h u hu
        have hsn : SN u := ihA1 u hu
        induction hsn with
        | intro u hacc ihu =>
            refine ihB3 _ (notAbs_app t u) fun w hw => ?_
            cases hw with
            | beta a b => exact hn.elim
            | app_left _ t' _ hstep => exact h t' hstep u hu
            | app_right _ _ u' hstep => exact ihu u' hstep (ihA2 _ _ hu hstep)

theorem cr1 (A : Ty) {t : Lambda} (h : Red A t) : SN t := (cr A).1 t h

theorem cr2 (A : Ty) {t t' : Lambda} (h : Red A t) (hs : Lambda.step t t') : Red A t' :=
  (cr A).2.1 t t' h hs

theorem cr3 (A : Ty) {t : Lambda} (hn : NotAbs t)
    (h : ∀ t', Lambda.step t t' → Red A t') : Red A t := (cr A).2.2 t hn h

theorem red_var (A : Ty) (i : ℕ) : Red A (Lambda.var i) :=
  cr3 A (notAbs_var i) fun _ h => absurd h not_step_var

------------------------------------------------------------------------
-- The abstraction lemma
------------------------------------------------------------------------

theorem red_app_lam_aux (A B : Ty) :
    ∀ s : Lambda, SN s → (∀ v, Red A v → Red B (Lambda.subst v 0 s)) →
      ∀ u : Lambda, SN u → Red A u → Red B (Lambda.app (Lambda.lam s) u) := by
  intro s hs
  induction hs with
  | intro s _ ihs =>
      intro hsub u hu
      induction hu with
      | intro u hacc ihu =>
          intro hru
          refine cr3 B (notAbs_app _ _) fun w hw => ?_
          cases hw with
          | beta a b => exact hsub u hru
          | app_left _ t₁' _ hstep =>
              cases hstep with
              | lam _ s' hs' =>
                  refine ihs s' hs' (fun v hv => cr2 B (hsub v hv) (step_subst hs' v 0)) u
                    (Acc.intro u hacc) hru
          | app_right _ _ u' hstep => exact ihu u' hstep (cr2 A hru hstep)

/-- **Abstraction lemma**: if substituting any reducible term for the bound variable yields a
reducible body, the abstraction is reducible. -/
theorem red_lam {A B : Ty} {s : Lambda}
    (h : ∀ v, Red A v → Red B (Lambda.subst v 0 s)) : Red (Ty.arrow A B) (Lambda.lam s) := by
  intro u hu
  have hsns : SN s := sn_of_sn_subst (cr1 B (h _ (red_var A 0)))
  exact red_app_lam_aux A B s hsns h u (cr1 A hu) hu

------------------------------------------------------------------------
-- Parallel substitution: composition with a single substitution
------------------------------------------------------------------------

/-- Extend an environment with a new term at index `0`, shifting the rest. -/
def envScons (v : Lambda) (u : ℕ → Lambda) : ℕ → Lambda
  | 0 => v
  | k + 1 => u k

/-- Substituting into a parallel substitution amounts to composing the environments. -/
theorem subst_substEnv (v : Lambda) :
    ∀ (t : Lambda) (k : ℕ) (u w : ℕ → Lambda),
      (∀ j, w j = Lambda.subst (Lambda.lift k 0 v) k (u j)) →
      Lambda.subst (Lambda.lift k 0 v) k (substEnv u t) = substEnv w t := by
  intro t
  induction t with
  | var j => intro k u w hw; simp only [substEnv, hw j]
  | app a b iha ihb =>
      intro k u w hw
      simp only [substEnv, Lambda.subst, iha k u w hw, ihb k u w hw]
  | lam t ih =>
      intro k u w hw
      have hlift : Lambda.lift 1 0 (Lambda.lift k 0 v) = Lambda.lift (k + 1) 0 v := by
        rw [Nat.add_comm k 1, Lambda.lift_add]
      have hstep : ∀ j, envCons w j
          = Lambda.subst (Lambda.lift (k + 1) 0 v) (k + 1) (envCons u j) := by
        intro j
        cases j with
        | zero => simp [envCons, Lambda.subst]
        | succ j =>
            simp only [envCons, hw j]
            rw [← hlift, Lambda.lift_subst (u j) (Lambda.lift k 0 v) 1 0 k (Nat.zero_le k)]
      have := ih (k + 1) (envCons u) (envCons w) hstep
      simp only [substEnv, Lambda.subst, hlift]
      exact congrArg Lambda.lam this

theorem subst_zero_substEnv (v : Lambda) (t : Lambda) (u : ℕ → Lambda) :
    Lambda.subst v 0 (substEnv (envCons u) t) = substEnv (envScons v u) t := by
  have key : ∀ j, envScons v u j
      = Lambda.subst (Lambda.lift 0 0 v) 0 (envCons u j) := by
    intro j
    rw [Lambda.lift_zero]
    cases j with
    | zero => simp [envCons, envScons, Lambda.subst]
    | succ j =>
        simp only [envCons, envScons]
        exact (Lambda.subst_lift (u j) v 0).symm
  have h := subst_substEnv v t 0 (envCons u) (envScons v u) key
  rwa [Lambda.lift_zero] at h

------------------------------------------------------------------------
-- The fundamental lemma, and strong normalization
------------------------------------------------------------------------

/-- **Fundamental lemma of the reducibility method.** -/
theorem red_substEnv {Γ : List Ty} {t : Lambda} {A : Ty} (h : Typing Γ t A) :
    ∀ u : ℕ → Lambda, (∀ i A', Γ[i]? = some A' → Red A' (u i)) → Red A (substEnv u t) := by
  induction h with
  | var hi => intro u hu; exact hu _ _ hi
  | app _ _ iha ihb =>
      intro u hu
      exact iha u hu _ (ihb u hu)
  | @lam Γ t A B _ ih =>
      intro u hu
      have hsub : substEnv u (Lambda.lam t) = Lambda.lam (substEnv (envCons u) t) := rfl
      rw [hsub]
      refine red_lam fun v hv => ?_
      rw [subst_zero_substEnv]
      refine ih (envScons v u) fun i A' hi => ?_
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          exact hv
      | succ i => exact hu i A' (by simpa using hi)

/-- **Strong normalization for the simply typed lambda calculus.** -/
theorem sn_of_typing {Γ : List Ty} {t : Lambda} {A : Ty} (h : Typing Γ t A) : SN t := by
  have := red_substEnv h (fun k => Lambda.var k) fun i A' _ => red_var A' i
  rw [substEnv_var_id] at this
  exact cr1 A this

------------------------------------------------------------------------
-- Consequences
------------------------------------------------------------------------

theorem is_normal_of_no_step {t : Lambda} (h : ∀ t', ¬ Lambda.step t t') : Lambda.is_normal t := h

/-- A strongly normalizing term has a normal form. -/
theorem hasNormalForm_of_sn {t : Lambda} (h : SN t) : HasNormalForm t := by
  induction h with
  | intro t _ ih =>
      by_cases hn : ∃ t', Lambda.step t t'
      · obtain ⟨t', ht'⟩ := hn
        obtain ⟨u, hu, hnu⟩ := ih t' ht'
        exact ⟨u, Lambda.reduces.step t t' u ht' hu, hnu⟩
      · exact ⟨t, Lambda.reduces.refl t, fun t' ht' => hn ⟨t', ht'⟩⟩

/-- Every typable term has a normal form. -/
theorem hasNormalForm_of_typing {Γ : List Ty} {t : Lambda} {A : Ty} (h : Typing Γ t A) :
    HasNormalForm t := hasNormalForm_of_sn (sn_of_typing h)

/-- `omega` is not typable: the untyped calculus is strictly larger than the typed one. -/
theorem not_typing_omega {Γ : List Ty} {A : Ty} : ¬ Typing Γ Lambda.omega A := fun h =>
  not_hasNormalForm_omega (hasNormalForm_of_typing h)

/-- Non-vacuity: the identity is typable at every arrow type `A ⇒ A`. -/
theorem typing_I (Γ : List Ty) (A : Ty) : Typing Γ Lambda.I (Ty.arrow A A) :=
  Typing.lam (Typing.var (by simp))

end Lambda
