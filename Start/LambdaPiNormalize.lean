/-
**Normal forms of `λΠ`, and decidability of conversion.**

Strong normalization (`Start/LambdaPiSN.lean`) says that reduction terminates; Church–Rosser
(`Start/LambdaPi.lean`) says that it is confluent.  Together they say that a typable term has
*one* normal form, and that two typable terms are convertible exactly when their normal forms are
equal.  This module makes that effective: it gives a computable one-step reduction function,
iterates it to a computable normal form of a strongly normalizing term, and derives that
conversion of typable terms is decidable.

* `LambdaPi.nf_unique` — a term has at most one normal form;
* `LambdaPi.conv_iff_normalForm_eq` — two terms with normal forms are convertible iff those normal
  forms are equal;
* `LambdaPi.stepFn` — a computable reduction strategy, with `LambdaPi.stepFn_sound` and
  `LambdaPi.normal_of_stepFn_none`: it makes a step whenever it returns one, and returns nothing
  only at a normal form;
* `LambdaPi.nf` — the normal form of a strongly normalizing term, obtained by iterating `stepFn`
  the number of times `Nat.find` extracts from strong normalization; `LambdaPi.nf_spec`;
* `LambdaPi.decidableConv` — **conversion of strongly normalizing terms is decidable**, and
  `LambdaPi.Typing.decidableConv` — hence conversion of terms typable in a well-formed context.
-/

import Start.LambdaPiSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Uniqueness of normal forms -/

/-- A normal term reduces only to itself. -/
theorem Normal.red_eq {t u : Tm} (h : Normal t) (hr : Red t u) : u = t := by
  induction hr with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (h _)

/-- **A term has at most one normal form.** -/
theorem nf_unique {t u v : Tm} (hu : Red t u) (hnu : Normal u) (hv : Red t v) (hnv : Normal v) :
    u = v := by
  obtain ⟨w, hw₁, hw₂⟩ := church_rosser hu hv
  rw [hnu.red_eq hw₁] at hw₂
  exact hnv.red_eq hw₂

/-- **Two terms with normal forms are convertible exactly when the normal forms agree.** -/
theorem conv_iff_normalForm_eq {t u v w : Tm} (hv : Red t v) (hnv : Normal v) (hw : Red u w)
    (hnw : Normal w) : Conv t u ↔ v = w := by
  constructor
  · intro hc
    obtain ⟨z, hz₁, hz₂⟩ := hc.church_rosser
    obtain ⟨z₁, hv₁, hz₁'⟩ := church_rosser hv hz₁
    obtain ⟨z₂, hw₁, hz₂'⟩ := church_rosser hw hz₂
    rw [hnv.red_eq hv₁] at hz₁'
    rw [hnw.red_eq hw₁] at hz₂'
    exact nf_unique hz₁' hnv hz₂' hnw
  · intro h
    subst h
    exact (Conv.ofRed hv).trans (Conv.ofRed hw).symm

/-! ### A computable reduction strategy -/

/-- One step of reduction, computed: the leftmost redex of the term, if there is one. -/
def stepFn : Tm → Option Tm
  | Tm.var _ => none
  | Tm.sort _ => none
  | Tm.lam A b =>
      match stepFn A with
      | some A' => some (Tm.lam A' b)
      | none => (stepFn b).map (Tm.lam A)
  | Tm.pi A B =>
      match stepFn A with
      | some A' => some (Tm.pi A' B)
      | none => (stepFn B).map (Tm.pi A)
  | Tm.app (Tm.lam _ b) a => some (b[a])
  | Tm.app (Tm.var n) a => (stepFn a).map (Tm.app (Tm.var n))
  | Tm.app (Tm.sort s) a => (stepFn a).map (Tm.app (Tm.sort s))
  | Tm.app (Tm.pi A B) a =>
      match stepFn (Tm.pi A B) with
      | some f' => some (Tm.app f' a)
      | none => (stepFn a).map (Tm.app (Tm.pi A B))
  | Tm.app (Tm.app f0 a0) a =>
      match stepFn (Tm.app f0 a0) with
      | some f' => some (Tm.app f' a)
      | none => (stepFn a).map (Tm.app (Tm.app f0 a0))

/-- The computed step is a step. -/
theorem stepFn_sound : ∀ {t u : Tm}, stepFn t = some u → Step t u := by
  intro t
  induction t with
  | var n => intro u h; simp [stepFn] at h
  | sort s => intro u h; simp [stepFn] at h
  | lam A b ihA ihb =>
      intro u h
      rw [stepFn] at h
      split at h
      · rename_i A' hA
        cases h
        exact Step.lamL b (ihA hA)
      · rename_i hA
        rcases hb : stepFn b with _ | b'
        · rw [hb] at h; simp at h
        · rw [hb] at h; cases h; exact Step.lamR A (ihb hb)
  | pi A B ihA ihB =>
      intro u h
      rw [stepFn] at h
      split at h
      · rename_i A' hA
        cases h
        exact Step.piL B (ihA hA)
      · rename_i hA
        rcases hB : stepFn B with _ | B'
        · rw [hB] at h; simp at h
        · rw [hB] at h; cases h; exact Step.piR A (ihB hB)
  | app f a ihf iha =>
      intro u h
      cases f with
      | lam A b => rw [stepFn] at h; cases h; exact Step.beta A b a
      | var n =>
          rw [stepFn] at h
          rcases ha : stepFn a with _ | a'
          · rw [ha] at h; simp at h
          · rw [ha] at h; cases h; exact Step.appR _ (iha ha)
      | sort s =>
          rw [stepFn] at h
          rcases ha : stepFn a with _ | a'
          · rw [ha] at h; simp at h
          · rw [ha] at h; cases h; exact Step.appR _ (iha ha)
      | pi A B =>
          rw [stepFn] at h
          split at h
          · rename_i f' hf
            cases h
            exact Step.appL a (ihf hf)
          · rename_i hf
            rcases ha : stepFn a with _ | a'
            · rw [ha] at h; simp at h
            · rw [ha] at h; cases h; exact Step.appR _ (iha ha)
      | app f0 a0 =>
          rw [stepFn] at h
          split at h
          · rename_i f' hf
            cases h
            exact Step.appL a (ihf hf)
          · rename_i hf
            rcases ha : stepFn a with _ | a'
            · rw [ha] at h; simp at h
            · rw [ha] at h; cases h; exact Step.appR _ (iha ha)

/-- When the strategy finds nothing, the term is normal. -/
theorem normal_of_stepFn_none : ∀ {t : Tm}, stepFn t = none → Normal t := by
  intro t
  induction t with
  | var n => intro _ u hst; cases hst
  | sort s => intro _ u hst; cases hst
  | lam A b ihA ihb =>
      intro h u hst
      rw [stepFn] at h
      rcases hA : stepFn A with _ | A' <;> rw [hA] at h
      · rcases hb : stepFn b with _ | b' <;> rw [hb] at h
        · cases hst with
          | lamL _ hs => exact ihA hA _ hs
          | lamR _ hs => exact ihb hb _ hs
        · simp at h
      · simp at h
  | pi A B ihA ihB =>
      intro h u hst
      rw [stepFn] at h
      rcases hA : stepFn A with _ | A' <;> rw [hA] at h
      · rcases hB : stepFn B with _ | B' <;> rw [hB] at h
        · cases hst with
          | piL _ hs => exact ihA hA _ hs
          | piR _ hs => exact ihB hB _ hs
        · simp at h
      · simp at h
  | app f a ihf iha =>
      intro h u hst
      cases f with
      | lam A b => rw [stepFn] at h; simp at h
      | var n =>
          rw [stepFn] at h
          rcases ha : stepFn a with _ | a' <;> rw [ha] at h
          · cases hst with
            | appL _ hs => exact (ihf rfl) _ hs
            | appR _ hs => exact iha ha _ hs
          · simp at h
      | sort s =>
          rw [stepFn] at h
          rcases ha : stepFn a with _ | a' <;> rw [ha] at h
          · cases hst with
            | appL _ hs => exact (ihf rfl) _ hs
            | appR _ hs => exact iha ha _ hs
          · simp at h
      | pi A B =>
          rw [stepFn] at h
          rcases hf : stepFn (Tm.pi A B) with _ | f' <;> rw [hf] at h
          · rcases ha : stepFn a with _ | a' <;> rw [ha] at h
            · cases hst with
              | appL _ hs => exact ihf hf _ hs
              | appR _ hs => exact iha ha _ hs
            · simp at h
          · simp at h
      | app f0 a0 =>
          rw [stepFn] at h
          rcases hf : stepFn (Tm.app f0 a0) with _ | f' <;> rw [hf] at h
          · rcases ha : stepFn a with _ | a' <;> rw [ha] at h
            · cases hst with
              | appL _ hs => exact ihf hf _ hs
              | appR _ hs => exact iha ha _ hs
            · simp at h
          · simp at h

/-! ### Iterating the strategy -/

/-- Iterate the reduction strategy, stopping at a normal term. -/
def stepIter : ℕ → Tm → Tm
  | 0, t => t
  | n + 1, t =>
      match stepFn t with
      | none => t
      | some u => stepIter n u

theorem stepIter_red (n : ℕ) (t : Tm) : Red t (stepIter n t) := by
  induction n generalizing t with
  | zero => exact Red.refl t
  | succ n ih =>
      rw [stepIter]
      rcases h : stepFn t with _ | u
      · exact Red.refl t
      · exact Red.head (stepFn_sound h) (ih u)

/-- A strongly normalizing term is normal after enough iterations. -/
theorem exists_stepIter_normal {t : Tm} (h : SN t) : ∃ n, stepFn (stepIter n t) = none := by
  induction h with
  | intro t _ ih =>
      rcases hst : stepFn t with _ | u
      · exact ⟨0, hst⟩
      · obtain ⟨n, hn⟩ := ih u (stepFn_sound hst)
        exact ⟨n + 1, by rw [stepIter, hst]; exact hn⟩

/-- **The normal form of a strongly normalizing term**, computed by iterating the reduction
strategy. -/
def nf (t : Tm) (h : SN t) : Tm := stepIter (Nat.find (exists_stepIter_normal h)) t

/-- The computed normal form is a normal form: the term reduces to it, and it is normal. -/
theorem nf_spec (t : Tm) (h : SN t) : Red t (nf t h) ∧ Normal (nf t h) :=
  ⟨stepIter_red _ t, normal_of_stepFn_none (Nat.find_spec (exists_stepIter_normal h))⟩

theorem nf_red (t : Tm) (h : SN t) : Red t (nf t h) := (nf_spec t h).1

theorem nf_normal (t : Tm) (h : SN t) : Normal (nf t h) := (nf_spec t h).2

/-! ### Decidability of conversion -/

/-- **Conversion of strongly normalizing terms is decidable**: compute the two normal forms and
compare them. -/
def decidableConv {t u : Tm} (ht : SN t) (hu : SN u) : Decidable (Conv t u) :=
  decidable_of_iff (nf t ht = nf u hu)
    (conv_iff_normalForm_eq (nf_red t ht) (nf_normal t ht) (nf_red u hu) (nf_normal u hu)).symm

/-- Conversion of terms typable in a well-formed context is decidable. -/
def Typing.decidableConv {Γ : Ctx} {t u A B : Tm} (ht : Typing Γ t A) (hu : Typing Γ u B)
    (hΓ : Wf Γ) : Decidable (Conv t u) :=
  _root_.LambdaPi.decidableConv (ht.sn hΓ) (hu.sn hΓ)

end LambdaPi
