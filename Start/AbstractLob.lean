/-
**Löb's theorem and the second incompleteness theorem from the derivability conditions.**

This is the abstract form of the argument, in the style of Hilbert–Bernays–Löb: nothing about
arithmetic is used.  A *provability system* (`Lambda.Lob.ProvabilitySystem`) consists of

* a type of sentences with an implication and a falsum;
* a set of theorems (`Thm`), containing the axioms `K : A → (B → A)` and
  `S : (A → (B → C)) → ((A → B) → (A → C))` and closed under modus ponens;
* a provability operator `box` on sentences satisfying the derivability conditions
  * `D1` : if `⊢ A` then `⊢ □A`,
  * `D2` : `⊢ □(A → B) → (□A → □B)`,
  * `D3` : `⊢ □A → □□A`;
* the diagonal lemma for the formulas `□X → B`: for every `B` a sentence `L` with
  `⊢ L → (□L → B)` and `⊢ (□L → B) → L`.

Main results:

* `Lambda.Lob.ProvabilitySystem.lob` — **Löb's theorem**: if `⊢ □B → B` then `⊢ B`;
* `Lambda.Lob.ProvabilitySystem.lob_internal` — the formalized version `⊢ □(□B → B) → □B`;
* `Lambda.Lob.ProvabilitySystem.not_thm_con` — **the second incompleteness theorem**: a
  consistent system does not prove its own consistency `□⊥ → ⊥`;
* `Lambda.Lob.ProvabilitySystem.not_thm_reflection` — the system proves the reflection principle
  `□A → A` only for its theorems `A`.

`Lambda.Lob.ProvabilitySystem.trueBox` is a consistent instance, so the hypotheses are not
contradictory.  A theory of arithmetic satisfying them is the subject of a separate task.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda.Lob

/-- A theory with a provability operator satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma for the formulas `□X → B`. -/
structure ProvabilitySystem where
  /-- The sentences. -/
  Sen : Type
  /-- Implication. -/
  imp : Sen → Sen → Sen
  /-- Falsum. -/
  bot : Sen
  /-- The provability operator, a sentence `□A` for each sentence `A`. -/
  box : Sen → Sen
  /-- The theorems. -/
  Thm : Sen → Prop
  /-- The axiom `A → (B → A)`. -/
  ax_k : ∀ A B, Thm (imp A (imp B A))
  /-- The axiom `(A → (B → C)) → ((A → B) → (A → C))`. -/
  ax_s : ∀ A B C, Thm (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))
  /-- Modus ponens. -/
  mp : ∀ {A B}, Thm (imp A B) → Thm A → Thm B
  /-- `D1`: provable sentences are provably provable. -/
  d1 : ∀ {A}, Thm A → Thm (box A)
  /-- `D2`: provability is closed under modus ponens, provably. -/
  d2 : ∀ A B, Thm (imp (box (imp A B)) (imp (box A) (box B)))
  /-- `D3`: provability is provably provable. -/
  d3 : ∀ A, Thm (imp (box A) (box (box A)))
  /-- The diagonal lemma for the formulas `□X → B`. -/
  diag : ∀ B, ∃ L, Thm (imp L (imp (box L) B)) ∧ Thm (imp (imp (box L) B) L)

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- Consistency: falsum is not a theorem. -/
def Consistent : Prop := ¬ T.Thm T.bot

/-- The sentence expressing consistency, `□⊥ → ⊥`. -/
def con : T.Sen := T.imp (T.box T.bot) T.bot

variable {T}

/-! ### A little propositional logic -/

theorem imp_self' (A : T.Sen) : T.Thm (T.imp A A) :=
  T.mp (T.mp (T.ax_s A (T.imp A A) A) (T.ax_k A (T.imp A A))) (T.ax_k A A)

/-- Weakening a theorem by a hypothesis. -/
theorem weaken {A B : T.Sen} (h : T.Thm B) : T.Thm (T.imp A B) := T.mp (T.ax_k B A) h

/-- Modus ponens under a hypothesis. -/
theorem mp_under {A B C : T.Sen} (h₁ : T.Thm (T.imp A (T.imp B C))) (h₂ : T.Thm (T.imp A B)) :
    T.Thm (T.imp A C) :=
  T.mp (T.mp (T.ax_s A B C) h₁) h₂

/-- Composition of implications. -/
theorem trans {A B C : T.Sen} (h₁ : T.Thm (T.imp A B)) (h₂ : T.Thm (T.imp B C)) :
    T.Thm (T.imp A C) :=
  mp_under (weaken h₂) h₁

/-- `D2` as a rule. -/
theorem box_mp {A B : T.Sen} (h : T.Thm (T.box (T.imp A B))) : T.Thm (T.imp (T.box A) (T.box B)) :=
  T.mp (T.d2 A B) h

/-- Provable implications give provable implications between the boxes. -/
theorem box_mono {A B : T.Sen} (h : T.Thm (T.imp A B)) : T.Thm (T.imp (T.box A) (T.box B)) :=
  box_mp (T.d1 h)

/-! ### Löb's theorem -/

/-- The core of the argument: for the diagonal sentence `L` of `B`, `⊢ □L → □B`. -/
theorem box_diag_imp_box {B L : T.Sen} (hL : T.Thm (T.imp L (T.imp (T.box L) B))) :
    T.Thm (T.imp (T.box L) (T.box B)) := by
  -- `⊢ □L → □(□L → B)`
  have h1 : T.Thm (T.imp (T.box L) (T.box (T.imp (T.box L) B))) := box_mono hL
  -- `⊢ □L → (□□L → □B)`
  have h2 : T.Thm (T.imp (T.box L) (T.imp (T.box (T.box L)) (T.box B))) :=
    trans h1 (T.d2 (T.box L) B)
  exact mp_under h2 (T.d3 L)

/-- **Löb's theorem.**  If `⊢ □B → B` then `⊢ B`. -/
theorem lob {B : T.Sen} (h : T.Thm (T.imp (T.box B) B)) : T.Thm B := by
  obtain ⟨L, hL₁, hL₂⟩ := T.diag B
  have h3 : T.Thm (T.imp (T.box L) B) := trans (box_diag_imp_box hL₁) h
  have hL : T.Thm L := T.mp hL₂ h3
  exact T.mp h3 (T.d1 hL)

/-- **Löb's theorem, formalized**: `⊢ □(□B → B) → □B`. -/
theorem lob_internal (B : T.Sen) : T.Thm (T.imp (T.box (T.imp (T.box B) B)) (T.box B)) := by
  obtain ⟨L, hL₁, hL₂⟩ := T.diag B
  set H := T.box (T.imp (T.box B) B) with hH
  -- `⊢ □L → □B`
  have h3 : T.Thm (T.imp (T.box L) (T.box B)) := box_diag_imp_box hL₁
  -- `⊢ (□B → B) → ((□L → □B) → (□L → B))`
  have hcomp : T.Thm (T.imp (T.imp (T.box B) B)
      (T.imp (T.imp (T.box L) (T.box B)) (T.imp (T.box L) B))) := by
    have hs : ∀ X Y Z : T.Sen,
        T.Thm (T.imp (T.imp Y Z) (T.imp (T.imp X Y) (T.imp X Z))) := by
      intro X Y Z
      exact trans (T.ax_k (T.imp Y Z) X) (T.ax_s X Y Z)
    exact hs (T.box L) (T.box B) B
  -- `⊢ □(□B → B) → □((□L → □B) → (□L → B))`
  have h4 : T.Thm (T.imp H (T.box (T.imp (T.imp (T.box L) (T.box B)) (T.imp (T.box L) B)))) :=
    box_mono hcomp
  -- `⊢ □(□B → B) → (□(□L → □B) → □(□L → B))`
  have h5 : T.Thm (T.imp H (T.imp (T.box (T.imp (T.box L) (T.box B)))
      (T.box (T.imp (T.box L) B)))) :=
    trans h4 (T.d2 _ _)
  -- `⊢ □(□L → □B)` by `D1`
  have h6 : T.Thm (T.imp H (T.box (T.imp (T.box L) B))) := mp_under h5 (weaken (T.d1 h3))
  -- `⊢ □(□L → B) → □L`
  have h7 : T.Thm (T.imp (T.box (T.imp (T.box L) B)) (T.box L)) := box_mono hL₂
  -- `⊢ H → □L → □B`
  exact trans (trans h6 h7) h3

/-! ### The second incompleteness theorem -/

/-- **The second incompleteness theorem.**  A consistent system does not prove its own
consistency `□⊥ → ⊥`. -/
theorem not_thm_con (hT : T.Consistent) : ¬ T.Thm T.con := fun h => hT (lob h)

/-- The reflection principle `□A → A` is provable only for theorems `A`. -/
theorem not_thm_reflection {A : T.Sen} (hA : ¬ T.Thm A) : ¬ T.Thm (T.imp (T.box A) A) :=
  fun h => hA (lob h)

/-! ### The hypotheses are consistent -/

/-- A consistent provability system: sentences are propositions, theorems are true propositions,
and `□A` is the true proposition.  It shows that the hypotheses do not force inconsistency (so the
theorems above are not vacuous); the operator `□` here is of course not a provability predicate. -/
def trueBox : ProvabilitySystem where
  Sen := Prop
  imp A B := A → B
  bot := False
  box _ := True
  Thm A := A
  ax_k _ _ a _ := a
  ax_s _ _ _ f g a := f a (g a)
  mp h a := h a
  d1 _ := trivial
  d2 _ _ _ _ := trivial
  d3 _ _ := trivial
  diag B := ⟨B, fun b _ => b, fun f => f trivial⟩

theorem trueBox_consistent : trueBox.Consistent := fun h => h

end ProvabilitySystem

end Lambda.Lob
