/-
**Cobham terms are countable.**

Cobham's class of polynomial-time functions is presented by a syntax, `Complexity.Cob`, so there
are only countably many of them.  This module makes that precise by a Gödel numbering
`Complexity.Cob.encNat`, built from `Nat.pair`, and proves it injective; the nesting of the
constructor `Cob.comp` inside `List` is handled by the auxiliary code `Complexity.natListEnc` of a
list of numbers.

The consequence recorded here — that a single sequence `ℕ → Cob` runs through every Cobham term
(`Complexity.exists_surjective_cob`) — is what makes diagonalization against *all* polynomial-time
functions possible; `Start/CookLevinExists.lean` uses it.

Main definitions:

* `Complexity.natListEnc` — an injective code of a list of numbers;
* `Complexity.Cob.encNat` — a Gödel number for a Cobham term.

Main results:

* `Complexity.Cob.encNat_injective` — the Gödel numbering is injective;
* `Complexity.instCountableCob` — **there are only countably many Cobham terms**;
* `Complexity.exists_surjective_cob` — a sequence running through every Cobham term.
-/

import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Coding lists of numbers -/

/-- An injective code of a list of numbers. -/
def natListEnc : List ℕ → ℕ
  | [] => 0
  | n :: ns => Nat.pair n (natListEnc ns) + 1

theorem natListEnc_injective : Function.Injective natListEnc := by
  intro l
  induction l with
  | nil =>
      intro m hm
      cases m with
      | nil => rfl
      | cons b bs => simp [natListEnc] at hm
  | cons a as ih =>
      intro m hm
      cases m with
      | nil => simp [natListEnc] at hm
      | cons b bs =>
          simp only [natListEnc, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at hm
          rw [hm.1, ih hm.2]

/-! ### A Gödel numbering of Cobham terms -/

/-- A Gödel number for a Cobham term: the constructor is named by the first component of a pair,
its arguments by the second. -/
def Cob.encNat : Cob → ℕ
  | .proj i => Nat.pair 0 i
  | .empty => Nat.pair 1 0
  | .app b => Nat.pair 2 (cond b 1 0)
  | .smash => Nat.pair 3 0
  | .comp f gs => Nat.pair 4 (Nat.pair f.encNat (natListEnc (gs.attach.map fun g => g.1.encNat)))
  | .bRec g h₀ h₁ bd =>
      Nat.pair 5 (Nat.pair g.encNat (Nat.pair h₀.encNat (Nat.pair h₁.encNat bd.encNat)))
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · omega
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

@[simp] theorem Cob.encNat_proj (i : ℕ) : (Cob.proj i).encNat = Nat.pair 0 i := by rw [Cob.encNat]

@[simp] theorem Cob.encNat_empty : Cob.empty.encNat = Nat.pair 1 0 := by rw [Cob.encNat]

@[simp] theorem Cob.encNat_app (b : Bool) : (Cob.app b).encNat = Nat.pair 2 (cond b 1 0) := by
  rw [Cob.encNat]

@[simp] theorem Cob.encNat_smash : Cob.smash.encNat = Nat.pair 3 0 := by rw [Cob.encNat]

@[simp] theorem Cob.encNat_comp (f : Cob) (gs : List Cob) :
    (Cob.comp f gs).encNat = Nat.pair 4 (Nat.pair f.encNat (natListEnc (gs.map Cob.encNat))) := by
  rw [Cob.encNat, List.attach_map_val]

@[simp] theorem Cob.encNat_bRec (g h₀ h₁ bd : Cob) :
    (Cob.bRec g h₀ h₁ bd).encNat =
      Nat.pair 5 (Nat.pair g.encNat (Nat.pair h₀.encNat (Nat.pair h₁.encNat bd.encNat))) := by
  rw [Cob.encNat]

theorem cond_nat_inj {b b' : Bool} (h : (cond b 1 0 : ℕ) = cond b' 1 0) : b = b' := by
  cases b <;> cases b' <;> simp_all

theorem Cob.encNat_injective_aux :
    ∀ (s : ℕ) (c₁ : Cob), sizeOf c₁ ≤ s → ∀ c₂ : Cob, c₁.encNat = c₂.encNat → c₁ = c₂ := by
  intro s
  induction s with
  | zero => intro c₁ hc; exact absurd hc (by cases c₁ <;> simp)
  | succ s ih =>
      intro c₁ hc c₂ heq
      have hlist : ∀ l₁ : List Cob, sizeOf l₁ ≤ s → ∀ l₂ : List Cob,
          List.map Cob.encNat l₁ = List.map Cob.encNat l₂ → l₁ = l₂ := by
        intro l₁
        induction l₁ with
        | nil =>
            intro _ l₂ h
            cases l₂ with
            | nil => rfl
            | cons b bs => simp at h
        | cons a as ihl =>
            intro hsz l₂ h
            cases l₂ with
            | nil => simp at h
            | cons b bs =>
                simp only [List.map_cons, List.cons.injEq] at h
                have hsa : sizeOf a ≤ s := by simp only [List.cons.sizeOf_spec] at hsz; omega
                have hsas : sizeOf as ≤ s := by simp only [List.cons.sizeOf_spec] at hsz; omega
                exact congrArg₂ _ (ih a hsa b h.1) (ihl hsas bs h.2)
      cases c₁ with
      | proj i =>
          cases c₂ <;> first
            | exact congrArg Cob.proj (by simpa using heq)
            | exact absurd heq (by simp [Nat.pair_eq_pair])
      | empty =>
          cases c₂ <;> first
            | rfl
            | exact absurd heq (by simp [Nat.pair_eq_pair])
      | app b =>
          cases c₂ <;> first
            | exact congrArg Cob.app (cond_nat_inj (by simpa using heq))
            | exact absurd heq (by simp [Nat.pair_eq_pair])
      | smash =>
          cases c₂ <;> first
            | rfl
            | exact absurd heq (by simp [Nat.pair_eq_pair])
      | comp f gs =>
          cases c₂ <;> first
            | (rename_i f' gs'
               have h : f.encNat = f'.encNat ∧
                   natListEnc (List.map Cob.encNat gs)
                     = natListEnc (List.map Cob.encNat gs') := by simpa using heq
               have hsz : sizeOf f + sizeOf gs ≤ s := by
                 simp only [Cob.comp.sizeOf_spec] at hc; omega
               rw [ih f (by omega) f' h.1, hlist gs (by omega) gs' (natListEnc_injective h.2)])
            | exact absurd heq (by simp [Nat.pair_eq_pair])
      | bRec g h₀ h₁ bd =>
          cases c₂ <;> first
            | (rename_i g' h₀' h₁' bd'
               have h : g.encNat = g'.encNat ∧ h₀.encNat = h₀'.encNat ∧
                   h₁.encNat = h₁'.encNat ∧ bd.encNat = bd'.encNat := by simpa using heq
               have hsz : sizeOf g + sizeOf h₀ + sizeOf h₁ + sizeOf bd ≤ s := by
                 simp only [Cob.bRec.sizeOf_spec] at hc; omega
               rw [ih g (by omega) g' h.1, ih h₀ (by omega) h₀' h.2.1,
                 ih h₁ (by omega) h₁' h.2.2.1, ih bd (by omega) bd' h.2.2.2])
            | exact absurd heq (by simp [Nat.pair_eq_pair])

theorem Cob.encNat_injective : Function.Injective Cob.encNat :=
  fun c₁ c₂ h => Cob.encNat_injective_aux (sizeOf c₁) c₁ le_rfl c₂ h

/-- **There are only countably many Cobham terms.** -/
instance instCountableCob : Countable Cob := Cob.encNat_injective.countable

/-- A single sequence runs through every Cobham term. -/
theorem exists_surjective_cob : ∃ φ : ℕ → Cob, Function.Surjective φ :=
  exists_surjective_nat Cob

end Complexity
