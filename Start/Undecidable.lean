/-
Undecidability of convergence for lambda terms.

The capstone `lambdaComputable_iff_partrec` says that the lambda calculus computes exactly the
partial recursive functions.  That equivalence has a classical consequence which is worth
recording separately: the *halting problem for the lambda calculus* is undecidable.  Concretely,
no computable predicate on codes of lambda terms decides whether the coded term reduces to a
Church numeral.

The proof is a reduction.  The universal partial function `k ↦ eval (ofNat Code k) 0` is partial
recursive, hence (by `lambdaComputable_of_partrec`) it has a lambda realizer `F`; and
`F (church k)` reduces to a Church numeral exactly when the `k`-th machine halts on input `0`.
Since `k ↦ encode (F (church k))` is primitive recursive, decidability of convergence would
decide the halting problem, contradicting `ComputablePred.halting_problem`.
-/

import Start.PartialCapstone
import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Convergence
------------------------------------------------------------------------

/-- A lambda term *converges* if it reduces to some Church numeral.  This is the lambda-calculus
analogue of a machine halting with an output. -/
def ConvergesToNumeral (t : Lambda) : Prop := ∃ k : ℕ, Lambda.reduces t (Lambda.church k)

/-- The code-level convergence predicate: `c` is the code of a term that converges. -/
def CodeConverges (c : ℕ) : Prop := ∃ t : Lambda, Lambda.decode c = some t ∧ ConvergesToNumeral t

theorem decode_encode (t : Lambda) : Lambda.decode (Lambda.encode t) = some t :=
  Encodable.encodek (α := Lambda) t

@[simp] theorem codeConverges_encode (t : Lambda) :
    CodeConverges (Lambda.encode t) ↔ ConvergesToNumeral t := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [decode_encode] at hu
    exact (Option.some_inj.mp hu) ▸ h
  · intro h
    exact ⟨t, decode_encode t, h⟩

/-- Sanity check: Church numerals themselves converge, so the predicate is not empty. -/
theorem codeConverges_church (k : ℕ) : CodeConverges (Lambda.encode (Lambda.church k)) :=
  (codeConverges_encode _).2 ⟨k, Lambda.reduces.refl _⟩

theorem encode_app (a b : Lambda) :
    Lambda.encode (Lambda.app a b) = Lambda.app_code (Lambda.encode a) (Lambda.encode b) := rfl

------------------------------------------------------------------------
-- The universal partial function and its lambda realizer
------------------------------------------------------------------------

/-- The universal partial function: run the `k`-th partial recursive code on input `0`. -/
def univHalt (k : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code k) 0

theorem univHalt_partrec : Partrec univHalt :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)

/-- A closed term whose value at `church k` mirrors the `k`-th machine's run on `0`. -/
def haltTerm : Lambda := Classical.choose (lambdaComputable_of_partrec univHalt_partrec)

theorem haltTerm_spec (k m : ℕ) : univHalt k = Part.some m ↔
    Lambda.reduces (Lambda.app haltTerm (Lambda.church k)) (Lambda.church m) :=
  Classical.choose_spec (lambdaComputable_of_partrec univHalt_partrec) k m

/-- The reduction: the `k`-th machine halts on `0` exactly when the corresponding lambda term
converges. -/
theorem univHalt_dom_iff (k : ℕ) :
    (univHalt k).Dom ↔ ConvergesToNumeral (Lambda.app haltTerm (Lambda.church k)) := by
  constructor
  · intro h
    exact ⟨univHalt k |>.get h, (haltTerm_spec k _).1 (Part.get_eq_iff_eq_some.mp rfl)⟩
  · rintro ⟨m, hm⟩
    rw [((haltTerm_spec k m).2 hm)]
    trivial

/-- The code of the reducing term, as a function of `k`. -/
def haltCode (k : ℕ) : ℕ := Lambda.app_code (Lambda.encode haltTerm) (Lambda.church_code k)

theorem haltCode_primrec : Primrec haltCode :=
  Primrec₂.comp Lambda.app_code_primrec (Primrec.const _) Lambda.church_code_primrec

theorem haltCode_eq (k : ℕ) :
    haltCode k = Lambda.encode (Lambda.app haltTerm (Lambda.church k)) := by
  rw [encode_app, haltCode, Lambda.encode_church_eq_church_code]

theorem codeConverges_haltCode (k : ℕ) : CodeConverges (haltCode k) ↔ (univHalt k).Dom := by
  rw [haltCode_eq, codeConverges_encode, univHalt_dom_iff]

------------------------------------------------------------------------
-- Undecidability
------------------------------------------------------------------------

/-- **The halting problem for the lambda calculus.**  No computable predicate on codes of lambda
terms decides whether the coded term reduces to a Church numeral. -/
theorem not_computablePred_codeConverges : ¬ ComputablePred CodeConverges := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c : Nat.Partrec.Code => f (haltCode (Encodable.encode c)), ?_, ?_⟩)
  · exact hf.comp (haltCode_primrec.to_comp.comp (Primrec.encode.to_comp.comp Computable.id))
  · funext c
    have hk : univHalt (Encodable.encode c) = Nat.Partrec.Code.eval c 0 := by
      simp only [univHalt, Denumerable.ofNat_encode]
    have := codeConverges_haltCode (Encodable.encode c)
    rw [hfe] at this
    rw [eq_iff_iff, ← hk]
    exact this.symm

------------------------------------------------------------------------
-- The predicate is non-trivial: `omega` does not converge
------------------------------------------------------------------------

theorem reduces_omega_eq : ∀ {s t : Lambda}, Lambda.reduces s t → s = Lambda.omega →
    t = Lambda.omega := by
  intro s t h
  induction h with
  | refl u => exact id
  | step a b c hab _ ih => exact fun ha => ih (Lambda.step_omega_eq b (ha ▸ hab))

/-- `omega` diverges: it reduces to no Church numeral. -/
theorem not_convergesToNumeral_omega : ¬ ConvergesToNumeral Lambda.omega := by
  rintro ⟨k, h⟩
  have h2 := reduces_omega_eq h rfl
  rw [Lambda.omega] at h2
  simp [Lambda.church] at h2

theorem not_codeConverges_omega : ¬ CodeConverges (Lambda.encode Lambda.omega) :=
  fun h => not_convergesToNumeral_omega ((codeConverges_encode _).1 h)

/-- Restated for terms: convergence of lambda terms is undecidable. -/
theorem not_computablePred_convergesToNumeral :
    ¬ ComputablePred (fun c : ℕ => ∃ t : Lambda, Lambda.decode c = some t ∧
      ∃ k : ℕ, Lambda.reduces t (Lambda.church k)) :=
  not_computablePred_codeConverges

end Lambda
