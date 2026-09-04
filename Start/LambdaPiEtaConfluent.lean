/-
**Confluence of `βη` for `λΠ`, modulo the domain annotations.**

`Start/LambdaPiEta.lean` shows that βη-reduction of *raw* `λΠ` terms is not confluent: in
Nederpelt's counterexample `λ(x : ∗). ((λ(y : □). y) x)` the β-reduct and the η-reduct differ
exactly in the domain annotation of an abstraction, and both are βη-normal.  The annotation is
the only obstruction, and this module proves it.

Write `eraseAnn` for the operation that replaces every domain annotation of an abstraction by the
fixed dummy `∗`; a term is `Erased` when it is its own erasure.  Then:

* `LambdaPi.eraseAnn`, `LambdaPi.Erased`, with the substitution lemmas `eraseAnn_rename`,
  `eraseAnn_subst`, `eraseAnn_inst`, and the closure of `Erased` under β- and η-reduction;
* `LambdaPi.erased_step_eta_comm` — **strong commutation** on erased terms: a β-step and an η-step
  out of the same erased term close up, with η-steps on one side and at most one β-step on the
  other.  This is precisely the diagram that Nederpelt's term refutes for arbitrary annotations:
  the critical case is a β-redex hidden under an η-redex, `λ(x : A). ((λ(y : A'). b) x)`, which
  closes up only when `A` and `A'` agree;
* `LambdaPi.erased_comm` — hence `β*` and `η*` commute on erased terms (Hindley's lemma);
* `LambdaPi.erased_betaEta_church_rosser` — hence, with η-postponement
  (`Start/LambdaPiEtaPostpone.lean`), βη-reduction *is* confluent on erased terms;
* `LambdaPi.betaEtaConv_eraseAnn` — every term is βη-convertible to its erasure, so
* `LambdaPi.betaEtaConv_iff_join` — **two raw terms are βη-convertible exactly when their
  annotation erasures have a common βη-reduct**: the Church–Rosser property holds for `λΠ` modulo
  annotations.

The consequences are the ones the conversion rule of a type theory needs, and they now hold for
the η-extended conversion just as `Start/LambdaPi.lean` proves them for β:
`LambdaPi.betaEtaConv_sort_inj` (a sort is convertible only to itself),
`LambdaPi.not_betaEtaConv_sort_pi` (a sort is never convertible to a product) and
`LambdaPi.betaEtaConv_pi_inv` (products are injective, up to erasure, in both arguments).
-/

import Start.LambdaPiEtaPostpone

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Inversion lemmas for single steps -/

theorem Step.app_inv {f a w : Tm} (h : Step (Tm.app f a) w) :
    (∃ A b, f = Tm.lam A b ∧ w = b[a]) ∨ (∃ f', Step f f' ∧ w = Tm.app f' a) ∨
      (∃ a', Step a a' ∧ w = Tm.app f a') := by
  cases h with
  | beta A b a => exact Or.inl ⟨A, b, rfl, rfl⟩
  | appL _ hs => exact Or.inr (Or.inl ⟨_, hs, rfl⟩)
  | appR _ hs => exact Or.inr (Or.inr ⟨_, hs, rfl⟩)

theorem Step.lam_inv {A b w : Tm} (h : Step (Tm.lam A b) w) :
    (∃ A', Step A A' ∧ w = Tm.lam A' b) ∨ (∃ b', Step b b' ∧ w = Tm.lam A b') := by
  cases h with
  | lamL _ hs => exact Or.inl ⟨_, hs, rfl⟩
  | lamR _ hs => exact Or.inr ⟨_, hs, rfl⟩

theorem Step.pi_inv {A B w : Tm} (h : Step (Tm.pi A B) w) :
    (∃ A', Step A A' ∧ w = Tm.pi A' B) ∨ (∃ B', Step B B' ∧ w = Tm.pi A B') := by
  cases h with
  | piL _ hs => exact Or.inl ⟨_, hs, rfl⟩
  | piR _ hs => exact Or.inr ⟨_, hs, rfl⟩

theorem EtaStep.app_inv {f a w : Tm} (h : EtaStep (Tm.app f a) w) :
    (∃ f', EtaStep f f' ∧ w = Tm.app f' a) ∨ (∃ a', EtaStep a a' ∧ w = Tm.app f a') := by
  cases h with
  | appL _ hs => exact Or.inl ⟨_, hs, rfl⟩
  | appR _ hs => exact Or.inr ⟨_, hs, rfl⟩

theorem EtaStep.pi_inv {A B w : Tm} (h : EtaStep (Tm.pi A B) w) :
    (∃ A', EtaStep A A' ∧ w = Tm.pi A' B) ∨ (∃ B', EtaStep B B' ∧ w = Tm.pi A B') := by
  cases h with
  | piL _ hs => exact Or.inl ⟨_, hs, rfl⟩
  | piR _ hs => exact Or.inr ⟨_, hs, rfl⟩

/-- A β-step out of an application of a `shift`ed abstraction: the standard identity that makes an
η-redex whose body is a β-redex collapse. -/
theorem inst_app_shift (f a : Tm) : (Tm.app (shift f) (Tm.var 0))[a] = Tm.app f a := by
  change Tm.app ((shift f)[a]) a = Tm.app f a
  rw [inst_shift]

/-! ### Erasing the domain annotations -/

/-- Replace every domain annotation of an abstraction by the dummy sort `∗`. -/
def eraseAnn : Tm → Tm
  | Tm.var n => Tm.var n
  | Tm.sort s => Tm.sort s
  | Tm.app f a => Tm.app (eraseAnn f) (eraseAnn a)
  | Tm.lam _ b => Tm.lam (Tm.sort Srt.star) (eraseAnn b)
  | Tm.pi A B => Tm.pi (eraseAnn A) (eraseAnn B)

/-- A term is **erased** when it carries no information in its domain annotations. -/
def Erased (t : Tm) : Prop := eraseAnn t = t

@[simp] theorem eraseAnn_var (n : ℕ) : eraseAnn (Tm.var n) = Tm.var n := rfl

@[simp] theorem eraseAnn_sort (s : Srt) : eraseAnn (Tm.sort s) = Tm.sort s := rfl

@[simp] theorem eraseAnn_app (f a : Tm) :
    eraseAnn (Tm.app f a) = Tm.app (eraseAnn f) (eraseAnn a) := rfl

@[simp] theorem eraseAnn_lam (A b : Tm) :
    eraseAnn (Tm.lam A b) = Tm.lam (Tm.sort Srt.star) (eraseAnn b) := rfl

@[simp] theorem eraseAnn_pi (A B : Tm) :
    eraseAnn (Tm.pi A B) = Tm.pi (eraseAnn A) (eraseAnn B) := rfl

theorem eraseAnn_rename (ρ : ℕ → ℕ) (t : Tm) :
    eraseAnn (LambdaPi.rename ρ t) = LambdaPi.rename ρ (eraseAnn t) := by
  induction t generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [eraseAnn, ihf, iha]
  | lam A b _ ihb => simp [eraseAnn, ihb]
  | pi A B ihA ihB => simp [eraseAnn, ihA, ihB]

theorem eraseAnn_shift (t : Tm) : eraseAnn (shift t) = shift (eraseAnn t) :=
  eraseAnn_rename Nat.succ t

theorem eraseAnn_subst (σ : ℕ → Tm) (t : Tm) :
    eraseAnn (subst σ t) = subst (fun n => eraseAnn (σ n)) (eraseAnn t) := by
  induction t generalizing σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [eraseAnn, ihf, iha]
  | lam A b _ ihb =>
      have hup : ∀ n, eraseAnn (LambdaPi.up σ n) = LambdaPi.up (fun n => eraseAnn (σ n)) n := by
        intro n
        cases n with
        | zero => rfl
        | succ n => exact eraseAnn_shift (σ n)
      simp only [subst, eraseAnn, ihb, Tm.lam.injEq, true_and]
      exact subst_congr hup (eraseAnn b)
  | pi A B ihA ihB =>
      have hup : ∀ n, eraseAnn (LambdaPi.up σ n) = LambdaPi.up (fun n => eraseAnn (σ n)) n := by
        intro n
        cases n with
        | zero => rfl
        | succ n => exact eraseAnn_shift (σ n)
      simp only [subst, eraseAnn, ihA, ihB, Tm.pi.injEq, true_and]
      exact subst_congr hup (eraseAnn B)

theorem eraseAnn_inst (a t : Tm) : eraseAnn (t[a]) = (eraseAnn t)[eraseAnn a] := by
  have h : ∀ n, eraseAnn (LambdaPi.scons a LambdaPi.ids n)
      = LambdaPi.scons (eraseAnn a) LambdaPi.ids n := by
    intro n
    cases n with
    | zero => rfl
    | succ n => rfl
  simp only [inst, eraseAnn_subst]
  exact subst_congr h (eraseAnn t)

theorem eraseAnn_idem (t : Tm) : eraseAnn (eraseAnn t) = eraseAnn t := by
  induction t with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [eraseAnn, ihf, iha]
  | lam A b _ ihb => simp [eraseAnn, ihb]
  | pi A B ihA ihB => simp [eraseAnn, ihA, ihB]

theorem erased_eraseAnn (t : Tm) : Erased (eraseAnn t) := eraseAnn_idem t

theorem erased_var (n : ℕ) : Erased (Tm.var n) := rfl

theorem erased_sort (s : Srt) : Erased (Tm.sort s) := rfl

theorem Erased.app_left {f a : Tm} (h : Erased (Tm.app f a)) : Erased f :=
  (Tm.app.inj (h : Tm.app (eraseAnn f) (eraseAnn a) = Tm.app f a)).1

theorem Erased.app_right {f a : Tm} (h : Erased (Tm.app f a)) : Erased a :=
  (Tm.app.inj (h : Tm.app (eraseAnn f) (eraseAnn a) = Tm.app f a)).2

theorem Erased.app {f a : Tm} (hf : Erased f) (ha : Erased a) : Erased (Tm.app f a) := by
  change Tm.app (eraseAnn f) (eraseAnn a) = Tm.app f a
  rw [hf, ha]

theorem Erased.lam_annot {A b : Tm} (h : Erased (Tm.lam A b)) : A = Tm.sort Srt.star :=
  (Tm.lam.inj (h : Tm.lam (Tm.sort Srt.star) (eraseAnn b) = Tm.lam A b)).1.symm

theorem Erased.lam_body {A b : Tm} (h : Erased (Tm.lam A b)) : Erased b :=
  (Tm.lam.inj (h : Tm.lam (Tm.sort Srt.star) (eraseAnn b) = Tm.lam A b)).2

theorem Erased.lam {b : Tm} (hb : Erased b) : Erased (Tm.lam (Tm.sort Srt.star) b) := by
  change Tm.lam (Tm.sort Srt.star) (eraseAnn b) = Tm.lam (Tm.sort Srt.star) b
  rw [hb]

theorem Erased.pi_left {A B : Tm} (h : Erased (Tm.pi A B)) : Erased A :=
  (Tm.pi.inj (h : Tm.pi (eraseAnn A) (eraseAnn B) = Tm.pi A B)).1

theorem Erased.pi_right {A B : Tm} (h : Erased (Tm.pi A B)) : Erased B :=
  (Tm.pi.inj (h : Tm.pi (eraseAnn A) (eraseAnn B) = Tm.pi A B)).2

theorem Erased.pi {A B : Tm} (hA : Erased A) (hB : Erased B) : Erased (Tm.pi A B) := by
  change Tm.pi (eraseAnn A) (eraseAnn B) = Tm.pi A B
  rw [hA, hB]

theorem Erased.shift {t : Tm} (h : Erased (LambdaPi.shift t)) : Erased t := by
  have h' : LambdaPi.shift (eraseAnn t) = LambdaPi.shift t := by
    rw [← eraseAnn_shift]; exact h
  exact shift_injective h'

theorem Erased.inst {b a : Tm} (hb : Erased b) (ha : Erased a) : Erased (b[a]) := by
  change eraseAnn (b[a]) = b[a]
  rw [eraseAnn_inst, hb, ha]

/-- Erasedness is preserved by β-reduction. -/
theorem Erased.step : ∀ {t u : Tm}, Step t u → Erased t → Erased u := by
  intro t u h
  induction h with
  | beta A b a => intro ht; exact Erased.inst ht.app_left.lam_body ht.app_right
  | appL a _ ih => intro ht; exact Erased.app (ih ht.app_left) ht.app_right
  | appR f _ ih => intro ht; exact Erased.app ht.app_left (ih ht.app_right)
  | lamL b hs _ =>
      intro ht
      rw [ht.lam_annot] at hs
      exact absurd hs not_step_sort
  | lamR A _ ih =>
      intro ht
      have hA : A = Tm.sort Srt.star := ht.lam_annot
      subst hA
      exact Erased.lam (ih ht.lam_body)
  | piL B _ ih => intro ht; exact Erased.pi (ih ht.pi_left) ht.pi_right
  | piR A _ ih => intro ht; exact Erased.pi ht.pi_left (ih ht.pi_right)

/-- Erasedness is preserved by η-reduction. -/
theorem Erased.etaStep : ∀ {t u : Tm}, EtaStep t u → Erased t → Erased u := by
  intro t u h
  induction h with
  | eta A t => intro ht; exact ht.lam_body.app_left.shift
  | appL a _ ih => intro ht; exact Erased.app (ih ht.app_left) ht.app_right
  | appR f _ ih => intro ht; exact Erased.app ht.app_left (ih ht.app_right)
  | lamL b hs _ =>
      intro ht
      rw [ht.lam_annot] at hs
      exact absurd hs EtaStep.sort_inv
  | lamR A _ ih =>
      intro ht
      have hA : A = Tm.sort Srt.star := ht.lam_annot
      subst hA
      exact Erased.lam (ih ht.lam_body)
  | piL B _ ih => intro ht; exact Erased.pi (ih ht.pi_left) ht.pi_right
  | piR A _ ih => intro ht; exact Erased.pi ht.pi_left (ih ht.pi_right)

theorem Erased.red {t u : Tm} (h : Red t u) (ht : Erased t) : Erased u := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact ih.step hs

theorem Erased.etaRed {t u : Tm} (h : EtaRed t u) (ht : Erased t) : Erased u := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact ih.etaStep hs

/-! ### Strong commutation of β and η on erased terms -/

/-- At most one β-step. -/
def Step01 (t u : Tm) : Prop := t = u ∨ Step t u

theorem Step01.refl (t : Tm) : Step01 t t := Or.inl rfl

theorem Step01.red {t u : Tm} (h : Step01 t u) : Red t u := by
  rcases h with rfl | hs
  · exact Red.refl t
  · exact Red.single hs

theorem Step01.appL {f f' : Tm} (a : Tm) (h : Step01 f f') : Step01 (Tm.app f a) (Tm.app f' a) := by
  rcases h with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Step.appL a hs)

theorem Step01.appR (f : Tm) {a a' : Tm} (h : Step01 a a') : Step01 (Tm.app f a) (Tm.app f a') := by
  rcases h with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Step.appR f hs)

theorem Step01.lamR (A : Tm) {b b' : Tm} (h : Step01 b b') : Step01 (Tm.lam A b) (Tm.lam A b') := by
  rcases h with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Step.lamR A hs)

theorem Step01.piL {A A' : Tm} (B : Tm) (h : Step01 A A') : Step01 (Tm.pi A B) (Tm.pi A' B) := by
  rcases h with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Step.piL B hs)

theorem Step01.piR (A : Tm) {B B' : Tm} (h : Step01 B B') : Step01 (Tm.pi A B) (Tm.pi A B') := by
  rcases h with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Step.piR A hs)

/-- **Strong commutation of β and η on erased terms**: a β-step and an η-step out of the same
erased term close up by η-steps on the β-side and at most one β-step on the η-side.

For arbitrary annotations this is false — it is exactly what Nederpelt's counterexample refutes —
and the case where erasedness is used is the one where the β-redex sits directly under the
η-redex. -/
theorem erased_step_eta_comm : ∀ {t u : Tm}, Step t u → ∀ {v : Tm}, EtaStep t v → Erased t →
    ∃ w, EtaRed u w ∧ Step01 v w := by
  intro t u h
  induction h with
  | beta A b a =>
      intro v hv ht
      rcases EtaStep.app_inv hv with ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · rcases EtaStep.lam_inv hf with ⟨s, hb, hf'⟩ | ⟨A', hA', hf'⟩ | ⟨b', hb', hf'⟩
        · subst hb
          subst hf'
          refine ⟨Tm.app f' a, ?_, Or.inl rfl⟩
          rw [inst_app_shift]
          exact EtaRed.refl _
        · rw [ht.app_left.lam_annot] at hA'
          exact absurd hA' EtaStep.sort_inv
        · subst hf'
          refine ⟨b'[a], ?_, Or.inr (Step.beta A b' a)⟩
          exact (EtaPar.inst hb'.toEtaPar (EtaPar.refl a)).toEtaRed
      · refine ⟨b[a'], ?_, Or.inr (Step.beta A b a')⟩
        exact (EtaPar.inst (EtaPar.refl b) ha.toEtaPar).toEtaRed
  | @appL f f' a hs ih =>
      intro v hv ht
      rcases EtaStep.app_inv hv with ⟨f₂, hf₂, rfl⟩ | ⟨a₂, ha₂, rfl⟩
      · obtain ⟨w, hw, hs'⟩ := ih hf₂ ht.app_left
        exact ⟨Tm.app w a, EtaRed.appL a hw, hs'.appL a⟩
      · exact ⟨Tm.app f' a₂, EtaRed.appR f' (EtaRed.single ha₂), Or.inr (Step.appL a₂ hs)⟩
  | @appR f a a' hs ih =>
      intro v hv ht
      rcases EtaStep.app_inv hv with ⟨f₂, hf₂, rfl⟩ | ⟨a₂, ha₂, rfl⟩
      · exact ⟨Tm.app f₂ a', EtaRed.appL a' (EtaRed.single hf₂), Or.inr (Step.appR f₂ hs)⟩
      · obtain ⟨w, hw, hs'⟩ := ih ha₂ ht.app_right
        exact ⟨Tm.app f w, EtaRed.appR f hw, hs'.appR f⟩
  | @lamL A A' b hs _ =>
      intro v hv ht
      rw [ht.lam_annot] at hs
      exact absurd hs not_step_sort
  | @lamR A b b' hs ih =>
      intro v hv ht
      have hA : A = Tm.sort Srt.star := ht.lam_annot
      rcases EtaStep.lam_inv hv with ⟨s, hb, hv'⟩ | ⟨A₂, hA₂, hv'⟩ | ⟨b₂, hb₂, hv'⟩
      · subst hb
        subst hv'
        rcases Step.app_inv hs with ⟨A₀, b₀, hshift, hb'⟩ | ⟨g, hg, hb'⟩ | ⟨a₂, ha₂, -⟩
        · -- the β-redex sits directly under the η-redex: both reducts are the same erased term
          cases v with
          | var n => simp [shift] at hshift
          | sort s' => simp [shift] at hshift
          | app f₁ a₁ => simp [shift] at hshift
          | pi A₁ B₁ => simp [shift] at hshift
          | lam A₁ b₁ =>
              simp only [shift, rename_lam, Tm.lam.injEq] at hshift
              obtain ⟨hA₀, hb₀⟩ := hshift
              have hAstar : A₁ = Tm.sort Srt.star :=
                (((ht.lam_body).app_left).shift).lam_annot
              subst hb'
              subst hb₀
              refine ⟨Tm.lam A ((LambdaPi.rename (LambdaPi.upr Nat.succ) b₁)[Tm.var 0]), ?_, ?_⟩
              · exact EtaRed.refl _
              · rw [inst_zero_rename_upr_succ, hA, hAstar]
                exact Or.inl rfl
        · obtain ⟨s', hg', hss'⟩ := step_rename_inv hg Nat.succ v rfl
          subst hb'
          subst hg'
          exact ⟨s', EtaRed.single (EtaStep.eta A s'), Or.inr hss'⟩
        · exact absurd ha₂ not_step_var
      · rw [hA] at hA₂
        exact absurd hA₂ EtaStep.sort_inv
      · subst hv'
        obtain ⟨w, hw, hs'⟩ := ih hb₂ ht.lam_body
        exact ⟨Tm.lam A w, EtaRed.lamR A hw, hs'.lamR A⟩
  | @piL A A' B hs ih =>
      intro v hv ht
      rcases EtaStep.pi_inv hv with ⟨A₂, hA₂, rfl⟩ | ⟨B₂, hB₂, rfl⟩
      · obtain ⟨w, hw, hs'⟩ := ih hA₂ ht.pi_left
        exact ⟨Tm.pi w B, EtaRed.piL B hw, hs'.piL B⟩
      · exact ⟨Tm.pi A' B₂, EtaRed.piR A' (EtaRed.single hB₂), Or.inr (Step.piL B₂ hs)⟩
  | @piR A B B' hs ih =>
      intro v hv ht
      rcases EtaStep.pi_inv hv with ⟨A₂, hA₂, rfl⟩ | ⟨B₂, hB₂, rfl⟩
      · exact ⟨Tm.pi A₂ B', EtaRed.piL B' (EtaRed.single hA₂), Or.inr (Step.piR A₂ hs)⟩
      · obtain ⟨w, hw, hs'⟩ := ih hB₂ ht.pi_right
        exact ⟨Tm.pi A w, EtaRed.piR A hw, hs'.piR A⟩

/-- One β-step commutes with an η-reduction. -/
theorem erased_step_etaRed_comm : ∀ {t v : Tm}, EtaRed t v → ∀ {u : Tm}, Step t u → Erased t →
    ∃ w, EtaRed u w ∧ Step01 v w := by
  intro t v h
  induction h with
  | refl => intro u hu _; exact ⟨u, EtaRed.refl u, Or.inr hu⟩
  | tail h₀ hs ih =>
      intro u hu ht
      obtain ⟨w₀, hw₀, hs₀⟩ := ih hu ht
      rcases hs₀ with rfl | hstep
      · exact ⟨_, hw₀.tail hs, Step01.refl _⟩
      · obtain ⟨w, hw, hs'⟩ := erased_step_eta_comm hstep hs (Erased.etaRed h₀ ht)
        exact ⟨w, hw₀.trans hw, hs'⟩

/-! ### The erased calculus in the vocabulary of `Start/Rewriting.lean`

The commutation above holds only above an erased term, so the relations handed to the abstract
interface are the steps *out of* erased terms; erasedness is preserved by both, so their closures
are the ordinary reductions started at an erased term. -/

/-- A β-step out of an erased term. -/
def StepE (t u : Tm) : Prop := Erased t ∧ Step t u

/-- An η-step out of an erased term. -/
def EtaStepE (t u : Tm) : Prop := Erased t ∧ EtaStep t u

theorem StepE.red {t u : Tm} (h : Rewriting.Star StepE t u) : Red t u := by
  induction h with
  | refl => exact Red.refl t
  | tail _ hs ih => exact ih.tail hs.2

theorem StepE.of_red {t u : Tm} (ht : Erased t) (h : Red t u) : Rewriting.Star StepE t u := by
  induction h with
  | refl => exact Rewriting.Star.refl t
  | @tail u v hu hs ih => exact ih.tail ⟨Erased.red hu ht, hs⟩

theorem EtaStepE.etaRed {t u : Tm} (h : Rewriting.Star EtaStepE t u) : EtaRed t u := by
  induction h with
  | refl => exact EtaRed.refl t
  | tail _ hs ih => exact ih.tail hs.2

theorem EtaStepE.of_etaRed {t u : Tm} (ht : Erased t) (h : EtaRed t u) :
    Rewriting.Star EtaStepE t u := by
  induction h with
  | refl => exact Rewriting.Star.refl t
  | @tail u v hu hs ih => exact ih.tail ⟨Erased.etaRed hu ht, hs⟩

/-- `erased_step_eta_comm` in the vocabulary of the interface: on erased terms β and η **strongly
commute** — the β-side of the diagram is at most one step. -/
theorem stronglyCommute_erased : Rewriting.StronglyCommute StepE EtaStepE := by
  rintro t u v ⟨ht, hstep⟩ ⟨-, heta⟩
  obtain ⟨w, hw, hs⟩ := erased_step_eta_comm hstep heta ht
  refine ⟨w, EtaStepE.of_etaRed (Erased.step hstep ht) hw, ?_⟩
  rcases hs with rfl | hs
  · exact Relation.ReflGen.refl
  · exact Relation.ReflGen.single ⟨Erased.etaStep heta ht, hs⟩

/-- **β and η commute on erased terms**, an instance of Hindley's
`Rewriting.commute_of_stronglyCommute`. -/
theorem erased_comm : ∀ {t u : Tm}, Red t u → ∀ {v : Tm}, EtaRed t v → Erased t →
    ∃ w, EtaRed u w ∧ Red v w := by
  intro t u h v hv ht
  obtain ⟨w, hw₁, hw₂⟩ :=
    Rewriting.commute_of_stronglyCommute stronglyCommute_erased
      (StepE.of_red ht h) (EtaStepE.of_etaRed ht hv)
  exact ⟨w, EtaStepE.etaRed hw₁, StepE.red hw₂⟩

/-! ### Confluence -/

/-- β out of an erased term is confluent. -/
theorem confluent_stepE : Rewriting.Confluent StepE := by
  intro t u v h₁ h₂
  rcases h₁.cases_head with rfl | ⟨t₁, ht₁, -⟩
  · exact ⟨v, h₂, Rewriting.Star.refl v⟩
  · have ht : Erased t := ht₁.1
    obtain ⟨w, hw₁, hw₂⟩ := church_rosser (StepE.red h₁) (StepE.red h₂)
    exact ⟨w, StepE.of_red (Erased.red (StepE.red h₁) ht) hw₁,
      StepE.of_red (Erased.red (StepE.red h₂) ht) hw₂⟩

/-- η out of an erased term is confluent. -/
theorem confluent_etaStepE : Rewriting.Confluent EtaStepE := by
  intro t u v h₁ h₂
  rcases h₁.cases_head with rfl | ⟨t₁, ht₁, -⟩
  · exact ⟨v, h₂, Rewriting.Star.refl v⟩
  · have ht : Erased t := ht₁.1
    obtain ⟨w, hw₁, hw₂⟩ :=
      EtaRed.church_rosser (EtaStepE.etaRed h₁) (EtaStepE.etaRed h₂)
    exact ⟨w, EtaStepE.of_etaRed (Erased.etaRed (EtaStepE.etaRed h₁) ht) hw₁,
      EtaStepE.of_etaRed (Erased.etaRed (EtaStepE.etaRed h₂) ht) hw₂⟩

theorem betaEtaRed_of_star_alt {t u : Tm}
    (h : Rewriting.Star (Rewriting.Alt StepE EtaStepE) t u) : BetaEtaRed t u := by
  induction h with
  | refl => exact BetaEtaRed.refl t
  | tail _ hs ih =>
      rcases hs with hs | hs
      · exact ih.tail (Or.inl hs.2)
      · exact ih.tail (Or.inr hs.2)

theorem star_alt_of_betaEtaRed {t u : Tm} (ht : Erased t) (h : BetaEtaRed t u) :
    Rewriting.Star (Rewriting.Alt StepE EtaStepE) t u := by
  induction h with
  | refl => exact Rewriting.Star.refl t
  | @tail u v hu hs ih =>
      refine ih.tail ?_
      have hue : Erased u := by
        obtain ⟨m, hm, he⟩ := betaEtaRed_iff.mp hu
        exact Erased.etaRed he (Erased.red hm ht)
      rcases hs with hs | hs
      · exact Or.inl ⟨hue, hs⟩
      · exact Or.inr ⟨hue, hs⟩

/-- **βη-reduction is confluent on erased terms**, an instance of **Hindley–Rosen**
(`Rewriting.confluent_alt_of_commute`): β is confluent, η is confluent, and they commute by
`stronglyCommute_erased`. -/
theorem erased_betaEta_church_rosser {t u v : Tm} (ht : Erased t) (h₁ : BetaEtaRed t u)
    (h₂ : BetaEtaRed t v) : ∃ w, BetaEtaRed u w ∧ BetaEtaRed v w := by
  obtain ⟨w, hw₁, hw₂⟩ :=
    Rewriting.confluent_alt_of_commute confluent_stepE confluent_etaStepE
      (Rewriting.commute_of_stronglyCommute stronglyCommute_erased)
      (star_alt_of_betaEtaRed ht h₁) (star_alt_of_betaEtaRed ht h₂)
  exact ⟨w, betaEtaRed_of_star_alt hw₁, betaEtaRed_of_star_alt hw₂⟩

/-! ### Transporting reductions along the erasure -/

theorem Step.eraseAnn : ∀ {t u : Tm}, Step t u →
    Red (LambdaPi.eraseAnn t) (LambdaPi.eraseAnn u) := by
  intro t u h
  induction h with
  | beta A b a =>
      have h1 : LambdaPi.eraseAnn (Tm.app (Tm.lam A b) a)
          = Tm.app (Tm.lam (Tm.sort Srt.star) (LambdaPi.eraseAnn b)) (LambdaPi.eraseAnn a) := rfl
      rw [h1, eraseAnn_inst]
      exact Red.single (Step.beta _ _ _)
  | appL a _ ih => exact Red.appL _ ih
  | appR f _ ih => exact Red.appR _ ih
  | lamL b _ => exact Red.refl _
  | lamR A _ ih => exact Red.lamR _ ih
  | piL B _ ih => exact Red.piL _ ih
  | piR A _ ih => exact Red.piR _ ih

theorem EtaStep.eraseAnn : ∀ {t u : Tm}, EtaStep t u →
    EtaRed (LambdaPi.eraseAnn t) (LambdaPi.eraseAnn u) := by
  intro t u h
  induction h with
  | eta A t =>
      have h1 : LambdaPi.eraseAnn (Tm.lam A (Tm.app (LambdaPi.shift t) (Tm.var 0)))
          = Tm.lam (Tm.sort Srt.star)
              (Tm.app (LambdaPi.shift (LambdaPi.eraseAnn t)) (Tm.var 0)) := by
        change Tm.lam (Tm.sort Srt.star)
          (Tm.app (LambdaPi.eraseAnn (LambdaPi.shift t)) (Tm.var 0)) = _
        rw [eraseAnn_shift]
      rw [h1]
      exact EtaRed.single (EtaStep.eta _ _)
  | appL a _ ih => exact EtaRed.appL _ ih
  | appR f _ ih => exact EtaRed.appR _ ih
  | lamL b _ => exact EtaRed.refl _
  | lamR A _ ih => exact EtaRed.lamR _ ih
  | piL B _ ih => exact EtaRed.piL _ ih
  | piR A _ ih => exact EtaRed.piR _ ih

theorem BetaEtaStep.eraseAnn {t u : Tm} (h : BetaEtaStep t u) :
    BetaEtaRed (LambdaPi.eraseAnn t) (LambdaPi.eraseAnn u) := by
  rcases h with hs | hs
  · exact BetaEtaRed.of_red hs.eraseAnn
  · exact BetaEtaRed.of_etaRed hs.eraseAnn

theorem BetaEtaRed.eraseAnn {t u : Tm} (h : BetaEtaRed t u) :
    BetaEtaRed (LambdaPi.eraseAnn t) (LambdaPi.eraseAnn u) := by
  induction h with
  | refl => exact BetaEtaRed.refl _
  | tail _ hs ih => exact ih.trans hs.eraseAnn

/-! ### Congruence for βη-conversion, and conversion with the erasure -/

namespace BetaEtaConv

theorem appL {f f' : Tm} (a : Tm) (h : BetaEtaConv f f') :
    BetaEtaConv (Tm.app f a) (Tm.app f' a) := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih =>
      rcases hs with hb | he
      · exact ih.step (Or.inl (Step.appL a hb))
      · exact ih.step (Or.inr (EtaStep.appL a he))
  | stepInv _ hs ih =>
      rcases hs with hb | he
      · exact ih.stepInv (Or.inl (Step.appL a hb))
      · exact ih.stepInv (Or.inr (EtaStep.appL a he))

theorem appR (f : Tm) {a a' : Tm} (h : BetaEtaConv a a') :
    BetaEtaConv (Tm.app f a) (Tm.app f a') := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih =>
      rcases hs with hb | he
      · exact ih.step (Or.inl (Step.appR f hb))
      · exact ih.step (Or.inr (EtaStep.appR f he))
  | stepInv _ hs ih =>
      rcases hs with hb | he
      · exact ih.stepInv (Or.inl (Step.appR f hb))
      · exact ih.stepInv (Or.inr (EtaStep.appR f he))

theorem lamR (A : Tm) {b b' : Tm} (h : BetaEtaConv b b') :
    BetaEtaConv (Tm.lam A b) (Tm.lam A b') := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih =>
      rcases hs with hb | he
      · exact ih.step (Or.inl (Step.lamR A hb))
      · exact ih.step (Or.inr (EtaStep.lamR A he))
  | stepInv _ hs ih =>
      rcases hs with hb | he
      · exact ih.stepInv (Or.inl (Step.lamR A hb))
      · exact ih.stepInv (Or.inr (EtaStep.lamR A he))

theorem piL {A A' : Tm} (B : Tm) (h : BetaEtaConv A A') :
    BetaEtaConv (Tm.pi A B) (Tm.pi A' B) := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih =>
      rcases hs with hb | he
      · exact ih.step (Or.inl (Step.piL B hb))
      · exact ih.step (Or.inr (EtaStep.piL B he))
  | stepInv _ hs ih =>
      rcases hs with hb | he
      · exact ih.stepInv (Or.inl (Step.piL B hb))
      · exact ih.stepInv (Or.inr (EtaStep.piL B he))

theorem piR (A : Tm) {B B' : Tm} (h : BetaEtaConv B B') :
    BetaEtaConv (Tm.pi A B) (Tm.pi A B') := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih =>
      rcases hs with hb | he
      · exact ih.step (Or.inl (Step.piR A hb))
      · exact ih.step (Or.inr (EtaStep.piR A he))
  | stepInv _ hs ih =>
      rcases hs with hb | he
      · exact ih.stepInv (Or.inl (Step.piR A hb))
      · exact ih.stepInv (Or.inr (EtaStep.piR A he))

end BetaEtaConv

/-- **Every term is βη-convertible to its annotation erasure**: βη-conversion cannot see the
domain annotations. -/
theorem betaEtaConv_eraseAnn (t : Tm) : BetaEtaConv t (eraseAnn t) := by
  induction t with
  | var n => exact BetaEtaConv.refl _
  | sort s => exact BetaEtaConv.refl _
  | app f a ihf iha =>
      exact (BetaEtaConv.appL a ihf).trans (BetaEtaConv.appR _ iha)
  | lam A b _ ihb =>
      exact (BetaEtaConv.lamR A ihb).trans (betaEtaConv_lam_annot A (Tm.sort Srt.star) _)
  | pi A B ihA ihB =>
      exact (BetaEtaConv.piL B ihA).trans (BetaEtaConv.piR _ ihB)

/-- **Church–Rosser for `λΠ` modulo annotations**: two raw terms are βη-convertible exactly when
their annotation erasures have a common βη-reduct. -/
theorem betaEtaConv_iff_join {t u : Tm} :
    BetaEtaConv t u ↔ ∃ w, BetaEtaRed (eraseAnn t) w ∧ BetaEtaRed (eraseAnn u) w := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨eraseAnn t, BetaEtaRed.refl _, BetaEtaRed.refl _⟩
    | step _ hs ih =>
        obtain ⟨w, hw₁, hw₂⟩ := ih
        obtain ⟨w', hw'₁, hw'₂⟩ :=
          erased_betaEta_church_rosser (erased_eraseAnn _) hw₂ hs.eraseAnn
        exact ⟨w', hw₁.trans hw'₁, hw'₂⟩
    | stepInv _ hs ih =>
        obtain ⟨w, hw₁, hw₂⟩ := ih
        exact ⟨w, hw₁, hs.eraseAnn.trans hw₂⟩
  · rintro ⟨w, hw₁, hw₂⟩
    exact ((betaEtaConv_eraseAnn t).trans (BetaEtaConv.ofRed hw₁)).trans
      ((betaEtaConv_eraseAnn u).trans (BetaEtaConv.ofRed hw₂)).symm

/-! ### Consequences for the conversion rule -/

theorem betaEtaRed_sort_inv {s : Srt} {u : Tm} (h : BetaEtaRed (Tm.sort s) u) :
    u = Tm.sort s := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      subst ih
      rcases hs with hb | he
      · exact absurd hb not_step_sort
      · exact absurd he EtaStep.sort_inv

theorem betaEtaRed_pi_inv : ∀ {A B u : Tm}, BetaEtaRed (Tm.pi A B) u →
    ∃ A' B', u = Tm.pi A' B' ∧ BetaEtaRed A A' ∧ BetaEtaRed B B' := by
  intro A B u h
  induction h with
  | refl => exact ⟨A, B, rfl, BetaEtaRed.refl A, BetaEtaRed.refl B⟩
  | tail _ hs ih =>
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := ih
      rcases hs with hb | he
      · rcases Step.pi_inv hb with ⟨A₂, hA₂, rfl⟩ | ⟨B₂, hB₂, rfl⟩
        · exact ⟨A₂, B₁, rfl, hA₁.tail (Or.inl hA₂), hB₁⟩
        · exact ⟨A₁, B₂, rfl, hA₁, hB₁.tail (Or.inl hB₂)⟩
      · rcases EtaStep.pi_inv he with ⟨A₂, hA₂, rfl⟩ | ⟨B₂, hB₂, rfl⟩
        · exact ⟨A₂, B₁, rfl, hA₁.tail (Or.inr hA₂), hB₁⟩
        · exact ⟨A₁, B₂, rfl, hA₁, hB₁.tail (Or.inr hB₂)⟩

/-- A sort is βη-convertible only to its own sort. -/
theorem betaEtaConv_sort_inj {s s' : Srt} (h : BetaEtaConv (Tm.sort s) (Tm.sort s')) : s = s' := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaConv_iff_join.mp h
  rw [eraseAnn_sort] at hw₁ hw₂
  have h₁ : w = Tm.sort s := betaEtaRed_sort_inv hw₁
  have h₂ : w = Tm.sort s' := betaEtaRed_sort_inv hw₂
  rw [h₁] at h₂
  exact Tm.sort.inj h₂

/-- A sort is never βη-convertible to a product. -/
theorem not_betaEtaConv_sort_pi {s : Srt} {A B : Tm} :
    ¬ BetaEtaConv (Tm.sort s) (Tm.pi A B) := by
  intro h
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaConv_iff_join.mp h
  rw [eraseAnn_sort] at hw₁
  rw [eraseAnn_pi] at hw₂
  have h₁ : w = Tm.sort s := betaEtaRed_sort_inv hw₁
  obtain ⟨A₁, B₁, h₂, -, -⟩ := betaEtaRed_pi_inv hw₂
  rw [h₁] at h₂
  exact Tm.noConfusion h₂

/-- Products are injective for βη-conversion, up to the annotations they contain. -/
theorem betaEtaConv_pi_inv {A B A' B' : Tm} (h : BetaEtaConv (Tm.pi A B) (Tm.pi A' B')) :
    BetaEtaConv A A' ∧ BetaEtaConv B B' := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaConv_iff_join.mp h
  rw [eraseAnn_pi] at hw₁ hw₂
  obtain ⟨A₁, B₁, hw, hA₁, hB₁⟩ := betaEtaRed_pi_inv hw₁
  obtain ⟨A₂, B₂, hw', hA₂, hB₂⟩ := betaEtaRed_pi_inv hw₂
  rw [hw] at hw'
  simp only [Tm.pi.injEq] at hw'
  obtain ⟨hA, hB⟩ := hw'
  subst hA
  subst hB
  exact ⟨betaEtaConv_iff_join.mpr ⟨A₁, hA₁, hA₂⟩, betaEtaConv_iff_join.mpr ⟨B₁, hB₁, hB₂⟩⟩

end LambdaPi
