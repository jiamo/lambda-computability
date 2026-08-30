/-
η-reduction for the untyped λ-calculus: termination and confluence.

`Start/Reduction.lean` gives β-reduction of the untyped calculus and proves it confluent
(`Lambda.confluence_theorem`).  This module adds the other rule for functions,

```
λx. (f x)  ⟶  f      (x not free in f),
```

which in the de Bruijn syntax of `Start/Syntax.lean` reads `lam (app (lift 1 0 t) (var 0)) ⟶ t`.
Unlike the Church-style calculus `λΠ` — where `Start/LambdaPiEta.lean` shows that βη on *raw*
terms is not confluent, because the two rules disagree about the domain annotation — here the
abstraction carries no annotation and βη is perfectly well behaved.  This file proves the facts
about η alone; `Start/LambdaBetaEta.lean` adds the commutation with β and the Church–Rosser
theorem for βη.

* `Lambda.etaStep`, `Lambda.etaReduces` — one step of η-contraction and its reflexive–transitive
  closure, with the congruence rules;
* `Lambda.lift_factor` — the factorisation lemma for liftings, which is what lets an η-step under
  a lifting be reflected back through it (`Lambda.etaStep_lift_inv`);
* `Lambda.nodes`, `Lambda.etaStep.nodes_lt`, `Lambda.exists_etaNf` — an η-step removes two syntax
  nodes, so η-reduction terminates: every term has an η-normal form;
* `Lambda.etaStep.strong_confluence`, `Lambda.etaReduces_church_rosser` — η-reduction is strongly
  confluent, hence confluent.
-/

import Start.TermSize

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-! ### η-reduction -/

/-- One step of η-contraction, `λx. (f x) ⟶ f` when `x` is not free in `f`; in de Bruijn form the
side condition says that the function part is a lifting. -/
inductive etaStep : Lambda → Lambda → Prop
  | eta (t : Lambda) : etaStep (Lambda.lam (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0))) t
  | app_left {f f' : Lambda} (a : Lambda) :
      etaStep f f' → etaStep (Lambda.app f a) (Lambda.app f' a)
  | app_right (f : Lambda) {a a' : Lambda} :
      etaStep a a' → etaStep (Lambda.app f a) (Lambda.app f a')
  | lam {t t' : Lambda} : etaStep t t' → etaStep (Lambda.lam t) (Lambda.lam t')

/-- Many-step η-reduction. -/
inductive etaReduces : Lambda → Lambda → Prop
  | refl (t : Lambda) : etaReduces t t
  | tail {t u v : Lambda} : etaReduces t u → etaStep u v → etaReduces t v

namespace etaReduces

theorem single {t u : Lambda} (h : etaStep t u) : etaReduces t u := (etaReduces.refl t).tail h

theorem trans {t u v : Lambda} (h₁ : etaReduces t u) (h₂ : etaReduces u v) : etaReduces t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem head {t u v : Lambda} (h : etaStep t u) (h' : etaReduces u v) : etaReduces t v :=
  (single h).trans h'

theorem app_left {f f' : Lambda} (a : Lambda) (h : etaReduces f f') :
    etaReduces (Lambda.app f a) (Lambda.app f' a) := by
  induction h with
  | refl => exact etaReduces.refl _
  | tail _ hs ih => exact ih.tail (etaStep.app_left a hs)

theorem app_right (f : Lambda) {a a' : Lambda} (h : etaReduces a a') :
    etaReduces (Lambda.app f a) (Lambda.app f a') := by
  induction h with
  | refl => exact etaReduces.refl _
  | tail _ hs ih => exact ih.tail (etaStep.app_right f hs)

theorem app {f f' a a' : Lambda} (hf : etaReduces f f') (ha : etaReduces a a') :
    etaReduces (Lambda.app f a) (Lambda.app f' a') :=
  (app_left a hf).trans (app_right f' ha)

theorem lam {t t' : Lambda} (h : etaReduces t t') : etaReduces (Lambda.lam t) (Lambda.lam t') := by
  induction h with
  | refl => exact etaReduces.refl _
  | tail _ hs ih => exact ih.tail (etaStep.lam hs)

end etaReduces

/-- No η-step out of a variable. -/
theorem etaStep.var_inv {n : ℕ} {t : Lambda} (h : etaStep (Lambda.var n) t) : False := by cases h

/-! ### Liftings -/

/-- Lifting acts on a variable by a conditional shift. -/
@[simp] theorem lift_var (n k y : ℕ) :
    Lambda.lift n k (Lambda.var y) = Lambda.var (if y < k then y else y + n) := by
  unfold Lambda.lift; split <;> rfl

@[simp] theorem lift_app (n k : ℕ) (f a : Lambda) :
    Lambda.lift n k (Lambda.app f a) = Lambda.app (Lambda.lift n k f) (Lambda.lift n k a) := rfl

@[simp] theorem lift_lam (n k : ℕ) (t : Lambda) :
    Lambda.lift n k (Lambda.lam t) = Lambda.lam (Lambda.lift n (k + 1) t) := rfl

/-- Lifting by one is injective on terms. -/
theorem lift_one_injective (k : ℕ) {t s : Lambda} (h : Lambda.lift 1 k t = Lambda.lift 1 k s) :
    t = s := by
  induction t generalizing k s with
  | var y =>
      cases s with
      | var z =>
          simp only [lift_var, Lambda.var.injEq] at h ⊢
          split_ifs at h <;> omega
      | _ => simp at h
  | app f a ihf iha =>
      cases s with
      | app g b =>
          simp only [lift_app, Lambda.app.injEq] at h
          exact congrArg₂ _ (ihf k h.1) (iha k h.2)
      | _ => simp at h
  | lam b ihb =>
      cases s with
      | lam c =>
          simp only [lift_lam, Lambda.lam.injEq] at h
          exact congrArg _ (ihb (k + 1) h)
      | _ => simp at h

/-- **Factorisation of liftings**: a term lifted at a level above `j` which is also a lifting at
level `j` is itself a lifting at level `j`, and the two liftings can be exchanged. -/
theorem lift_factor : ∀ (t : Lambda) (j k : ℕ) (s : Lambda),
    Lambda.lift 1 (j + k + 1) t = Lambda.lift 1 j s →
      ∃ t₀, t = Lambda.lift 1 j t₀ ∧ Lambda.lift 1 (j + k) t₀ = s := by
  intro t
  induction t with
  | var y =>
      intro j k s hs
      cases s with
      | var z =>
          simp only [lift_var, Lambda.var.injEq] at hs
          refine ⟨Lambda.var (if y < j then y else y - 1), ?_, ?_⟩ <;>
            simp only [lift_var, Lambda.var.injEq] <;> split_ifs at hs ⊢ <;> omega
      | _ => simp at hs
  | app f a ihf iha =>
      intro j k s hs
      cases s with
      | app g b =>
          simp only [lift_app, Lambda.app.injEq] at hs
          obtain ⟨f₀, hf₁, hf₂⟩ := ihf j k g hs.1
          obtain ⟨a₀, ha₁, ha₂⟩ := iha j k b hs.2
          exact ⟨Lambda.app f₀ a₀, by simp [hf₁, ha₁], by simp [hf₂, ha₂]⟩
      | _ => simp at hs
  | lam b ihb =>
      intro j k s hs
      cases s with
      | lam c =>
          simp only [lift_lam, Lambda.lam.injEq] at hs
          have hs' : Lambda.lift 1 ((j + 1) + k + 1) b = Lambda.lift 1 (j + 1) c := by
            simpa [Nat.add_right_comm, Nat.add_assoc] using hs
          obtain ⟨b₀, hb₁, hb₂⟩ := ihb (j + 1) k c hs'
          refine ⟨Lambda.lam b₀, by simp [hb₁], ?_⟩
          simp only [lift_lam, Lambda.lam.injEq]
          simpa [Nat.add_right_comm, Nat.add_assoc] using hb₂
      | _ => simp at hs

/-- Lifting inside a binder pushes past a lifting at level `0`. -/
theorem lift_succ_lift_zero (n k : ℕ) (t : Lambda) :
    Lambda.lift n (k + 1) (Lambda.lift 1 0 t) = Lambda.lift 1 0 (Lambda.lift n k t) :=
  (Lambda.lift_lift t 1 n 0 k (Nat.zero_le k)).symm

/-- η-reduction is stable under lifting. -/
theorem etaStep_lift {t t' : Lambda} (h : etaStep t t') (n k : ℕ) :
    etaStep (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h generalizing k with
  | eta s =>
      have h := etaStep.eta (Lambda.lift n k s)
      simpa [lift_succ_lift_zero] using h
  | app_left a _ ih => exact etaStep.app_left _ (ih k)
  | app_right f _ ih => exact etaStep.app_right _ (ih k)
  | lam _ ih => exact etaStep.lam (ih (k + 1))

/-- η-reduction is stable under lifting. -/
theorem etaReduces_lift {t t' : Lambda} (h : etaReduces t t') (n k : ℕ) :
    etaReduces (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h with
  | refl => exact etaReduces.refl _
  | tail _ hs ih => exact ih.tail (etaStep_lift hs n k)

/-- The general form of the reflection of an η-step through a lifting. -/
theorem etaStep_lift_inv_aux : ∀ {t' w : Lambda}, etaStep t' w → ∀ {k : ℕ} {t : Lambda},
    t' = Lambda.lift 1 k t → ∃ w₀, w = Lambda.lift 1 k w₀ ∧ etaStep t w₀ := by
  intro t' w h
  induction h with
  | eta s =>
      intro k t ht
      cases t with
      | lam b =>
          simp only [lift_lam, Lambda.lam.injEq] at ht
          cases b with
          | app f a =>
              simp only [lift_app, Lambda.app.injEq] at ht
              obtain ⟨hf, ha⟩ := ht
              have ha0 : a = Lambda.var 0 := by
                cases a with
                | var y =>
                    simp only [lift_var, Lambda.var.injEq] at ha
                    congr 1
                    split_ifs at ha
                    all_goals omega
                | _ => simp at ha
              obtain ⟨f₀, hf₁, hf₂⟩ := lift_factor f 0 k s (by simpa using hf.symm)
              subst ha0
              subst hf₁
              exact ⟨f₀, by simpa using hf₂.symm, etaStep.eta f₀⟩
          | _ => simp at ht
      | _ => simp at ht
  | @app_left f f' a _ ih =>
      intro k t ht
      cases t with
      | app f₁ a₁ =>
          simp only [lift_app, Lambda.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.1
          exact ⟨Lambda.app w₀ a₁, by simp [hw₁, ht.2], etaStep.app_left _ hw₂⟩
      | _ => simp at ht
  | @app_right f a a' _ ih =>
      intro k t ht
      cases t with
      | app f₁ a₁ =>
          simp only [lift_app, Lambda.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.2
          exact ⟨Lambda.app f₁ w₀, by simp [hw₁, ht.1], etaStep.app_right _ hw₂⟩
      | _ => simp at ht
  | @lam b b' _ ih =>
      intro k t ht
      cases t with
      | lam b₁ =>
          simp only [lift_lam, Lambda.lam.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht
          exact ⟨Lambda.lam w₀, by simp [hw₁], etaStep.lam hw₂⟩
      | _ => simp at ht

/-- An η-step performed under a lifting comes from an η-step before the lifting. -/
theorem etaStep_lift_inv {k : ℕ} {t w : Lambda} (h : etaStep (Lambda.lift 1 k t) w) :
    ∃ w₀, w = Lambda.lift 1 k w₀ ∧ etaStep t w₀ :=
  etaStep_lift_inv_aux h rfl

/-! ### η-reduction terminates -/

/-- The node measure `Lambda.nodes` of `Start/TermSize.lean` — unlike `Lambda.size` it does not
charge for the size of a de Bruijn index, so it is invariant under lifting. -/
@[simp] theorem nodes_lift (n k : ℕ) (t : Lambda) : nodes (Lambda.lift n k t) = nodes t := by
  induction t generalizing k with
  | var y => by_cases h : y < k <;> simp [h]
  | app f a ihf iha => simp [ihf, iha]
  | lam b ihb => simp [ihb]

/-- An η-step strictly decreases the number of syntax nodes. -/
theorem etaStep.nodes_lt {t u : Lambda} (h : etaStep t u) : nodes u < nodes t := by
  induction h with
  | eta s => simp; omega
  | app_left _ _ ih => simp; omega
  | app_right _ _ ih => simp; omega
  | lam _ ih => simp; omega

/-- A term is η-normal when no η-step applies to it. -/
def EtaNf (t : Lambda) : Prop := ∀ u, ¬ etaStep t u

/-- **η-reduction terminates**: every term has an η-normal form. -/
theorem exists_etaNf (t : Lambda) : ∃ u, etaReduces t u ∧ EtaNf u := by
  suffices h : ∀ n t, nodes t ≤ n → ∃ u, etaReduces t u ∧ EtaNf u from h (nodes t) t le_rfl
  intro n
  induction n with
  | zero => intro t ht; exact absurd ht (by have := nodes_pos t; omega)
  | succ n ih =>
      intro t ht
      by_cases h : EtaNf t
      · exact ⟨t, etaReduces.refl t, h⟩
      · simp only [EtaNf, not_forall, not_not] at h
        obtain ⟨u, hu⟩ := h
        obtain ⟨v, hv₁, hv₂⟩ := ih u (by have := hu.nodes_lt; omega)
        exact ⟨v, etaReduces.head hu hv₁, hv₂⟩

/-! ### η-reduction is confluent -/

/-- The reflexive closure of an η-step. -/
def etaStep0 (t u : Lambda) : Prop := t = u ∨ etaStep t u

namespace etaStep0

theorem red {t u : Lambda} (h : etaStep0 t u) : etaReduces t u := by
  rcases h with rfl | h
  exacts [etaReduces.refl _, etaReduces.single h]

theorem app_left {f f' : Lambda} (a : Lambda) (h : etaStep0 f f') :
    etaStep0 (Lambda.app f a) (Lambda.app f' a) := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (etaStep.app_left a h)]

theorem app_right (f : Lambda) {a a' : Lambda} (h : etaStep0 a a') :
    etaStep0 (Lambda.app f a) (Lambda.app f a') := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (etaStep.app_right f h)]

theorem lam {t t' : Lambda} (h : etaStep0 t t') : etaStep0 (Lambda.lam t) (Lambda.lam t') := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (etaStep.lam h)]

end etaStep0

/-- Inversion for an η-step out of an abstraction. -/
theorem etaStep.lam_inv {b w : Lambda} (h : etaStep (Lambda.lam b) w) :
    (∃ s, b = Lambda.app (Lambda.lift 1 0 s) (Lambda.var 0) ∧ w = s) ∨
      (∃ b', etaStep b b' ∧ w = Lambda.lam b') := by
  cases h with
  | eta _ => exact Or.inl ⟨_, rfl, rfl⟩
  | lam h => exact Or.inr ⟨_, h, rfl⟩

/-- **η-reduction is strongly confluent**: two η-steps out of the same term are joined by at most
one η-step on each side. -/
theorem etaStep.strong_confluence {t u v : Lambda} (h₁ : etaStep t u) (h₂ : etaStep t v) :
    ∃ w, etaStep0 u w ∧ etaStep0 v w := by
  induction h₁ generalizing v with
  | eta s =>
      rcases h₂.lam_inv with ⟨s', hs', rfl⟩ | ⟨b', hb', rfl⟩
      · simp only [Lambda.app.injEq, and_true] at hs'
        exact ⟨s, Or.inl rfl, Or.inl (lift_one_injective 0 hs').symm⟩
      · cases hb' with
        | app_left _ hf =>
            obtain ⟨s₀, rfl, hs⟩ := etaStep_lift_inv hf
            exact ⟨s₀, Or.inr hs, Or.inr (etaStep.eta s₀)⟩
        | app_right _ ha => exact absurd ha etaStep.var_inv
  | @app_left f f' a hf ih =>
      cases h₂ with
      | app_left _ hf₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih hf₂
          exact ⟨Lambda.app w a, hw₁.app_left a, hw₂.app_left a⟩
      | app_right _ ha₂ =>
          exact ⟨Lambda.app f' _, Or.inr (etaStep.app_right _ ha₂), Or.inr (etaStep.app_left _ hf)⟩
  | @app_right f a a' ha ih =>
      cases h₂ with
      | app_left _ hf₂ =>
          exact ⟨Lambda.app _ a', Or.inr (etaStep.app_left _ hf₂), Or.inr (etaStep.app_right _ ha)⟩
      | app_right _ ha₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih ha₂
          exact ⟨Lambda.app f w, hw₁.app_right f, hw₂.app_right f⟩
  | @lam b b' hb ih =>
      rcases h₂.lam_inv with ⟨s, hs, rfl⟩ | ⟨b₂, hb₂, rfl⟩
      · subst hs
        cases hb with
        | app_left _ hf =>
            obtain ⟨s₀, rfl, hs₀⟩ := etaStep_lift_inv hf
            exact ⟨s₀, Or.inr (etaStep.eta s₀), Or.inr hs₀⟩
        | app_right _ ha => exact absurd ha etaStep.var_inv
      · obtain ⟨w, hw₁, hw₂⟩ := ih hb₂
        exact ⟨Lambda.lam w, hw₁.lam, hw₂.lam⟩

/-- Strong confluence tiles along an η-reduction sequence. -/
theorem etaStep.strip {t u v : Lambda} (h₁ : etaStep t u) (h₂ : etaReduces t v) :
    ∃ w, etaReduces u w ∧ etaStep0 v w := by
  induction h₂ with
  | refl => exact ⟨u, etaReduces.refl u, Or.inr h₁⟩
  | @tail v₀ v hv hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      rcases hw₂ with rfl | hw₂
      · exact ⟨v, hw₁.tail hs, Or.inl rfl⟩
      · obtain ⟨z, hz₁, hz₂⟩ := hw₂.strong_confluence hs
        exact ⟨z, hw₁.trans hz₁.red, hz₂⟩

/-- **η-reduction is confluent.** -/
theorem etaReduces_church_rosser {t u v : Lambda} (h₁ : etaReduces t u) (h₂ : etaReduces t v) :
    ∃ w, etaReduces u w ∧ etaReduces v w := by
  induction h₁ with
  | refl => exact ⟨v, h₂, etaReduces.refl v⟩
  | @tail u₀ u hu hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      obtain ⟨z, hz₁, hz₂⟩ := hs.strip hw₁
      exact ⟨z, hz₁, hw₂.trans hz₂.red⟩

end Lambda
