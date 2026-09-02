/-
**Completeness at a level of the arithmetical hierarchy.**

`Start/ArithHierarchy.lean` defines the classes `Σ⁰ₙ`, `Π⁰ₙ` and `Δ⁰ₙ`, and
`Start/ArithHierarchyProper.lean` builds a *universal* predicate for each level and diagonalises
against it.  This module turns the universal predicates into **complete** ones for many-one
reducibility, and reads off the consequences.

* `Lambda.Arith.SigmaComplete`, `Lambda.Arith.PiComplete` — being at a level and being hard for
  it: every predicate of the class many-one reduces to it.
* `Lambda.Arith.SigmaAt.of_manyOne`, `Lambda.Arith.PiAt.of_manyOne`,
  `Lambda.Arith.DeltaAt.of_manyOne` — every level is closed downwards under many-one
  reducibility, the fact that makes completeness meaningful.
* `Lambda.Arith.UnivSigma.oneOne_hard`, `Lambda.Arith.UnivSigma.sigmaComplete` — a universal
  `Σ⁰ₙ` predicate is `Σ⁰ₙ`-complete, and in fact hard already for *one-one* reducibility, the
  reduction being `x ↦ ⟨e, x⟩` for the index `e` of the reduced predicate.
* `Lambda.Arith.exists_sigmaComplete`, `Lambda.Arith.exists_piComplete`,
  `Lambda.Arith.exists_sigmaOneOneComplete` — every level `n + 1` has complete predicates.
* `Lambda.Arith.SigmaComplete.compl`, `Lambda.Arith.PiComplete.compl` — complementation exchanges
  `Σ⁰ₙ`-completeness and `Π⁰ₙ`-completeness.
* `Lambda.Arith.SigmaComplete.of_manyOne`, `Lambda.Arith.PiComplete.of_manyOne` — completeness
  travels upwards along reductions.
* The negative half, at every level `n + 1`: a `Σ⁰ₙ₊₁`-complete predicate is not `Π⁰ₙ₊₁`
  (`Lambda.Arith.SigmaComplete.not_piAt`), not `Δ⁰ₙ₊₁` (`.not_deltaAt`) and not `Σ⁰ₙ`
  (`.not_sigmaAt_lower`), with the `Π` duals; in particular a complete predicate for a level is
  never computable (`Lambda.Arith.SigmaComplete.not_computablePred`).
* `Lambda.Arith.sigmaComplete_one_codeHasNormalForm`,
  `Lambda.Arith.sigmaComplete_one_codeConverges` — the halting set of the lambda calculus is
  `Σ⁰₁`-complete in this sense, which places the earlier `Σ₁`-completeness theorem of
  `Start/HaltingComplete.lean` inside the hierarchy.
* `Lambda.Arith.not_exists_arithmetical_complete` — the arithmetical predicates as a whole have
  no many-one complete member, although each single level does.
-/

import Start.ArithHierarchyProper
import Start.ArithBounded

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ## Levels are closed downwards under many-one reducibility -/

/-- If `Q` many-one reduces to a `Σ⁰ₙ` predicate then `Q` is itself `Σ⁰ₙ`. -/
theorem SigmaAt.of_manyOne {n : ℕ} {P Q : ℕ → Prop} (hP : SigmaAt n P) (h : Q ≤₀ P) :
    SigmaAt n Q := by
  obtain ⟨f, hf, hQ⟩ := h
  exact (hP.subst hf).of_iff hQ

/-- If `Q` many-one reduces to a `Π⁰ₙ` predicate then `Q` is itself `Π⁰ₙ`. -/
theorem PiAt.of_manyOne {n : ℕ} {P Q : ℕ → Prop} (hP : PiAt n P) (h : Q ≤₀ P) : PiAt n Q := by
  obtain ⟨f, hf, hQ⟩ := h
  exact (hP.subst hf).of_iff hQ

/-- If `Q` many-one reduces to a `Δ⁰ₙ` predicate then `Q` is itself `Δ⁰ₙ`. -/
theorem DeltaAt.of_manyOne {n : ℕ} {P Q : ℕ → Prop} (hP : DeltaAt n P) (h : Q ≤₀ P) :
    DeltaAt n Q :=
  ⟨hP.1.of_manyOne h, hP.2.of_manyOne h⟩

/-! ## Complete predicates -/

/-- `P` is **`Σ⁰ₙ`-complete**: it is `Σ⁰ₙ`, and every `Σ⁰ₙ` predicate many-one reduces to it. -/
def SigmaComplete (n : ℕ) (P : ℕ → Prop) : Prop :=
  SigmaAt n P ∧ ∀ Q : ℕ → Prop, SigmaAt n Q → Q ≤₀ P

/-- `P` is **`Π⁰ₙ`-complete**: it is `Π⁰ₙ`, and every `Π⁰ₙ` predicate many-one reduces to it. -/
def PiComplete (n : ℕ) (P : ℕ → Prop) : Prop :=
  PiAt n P ∧ ∀ Q : ℕ → Prop, PiAt n Q → Q ≤₀ P

/-- Fixing the first component of a pair is a computable, injective operation. -/
theorem computable_injective_pairLeft (e : ℕ) :
    Computable (fun x : ℕ => Nat.pair e x) ∧ Function.Injective fun x : ℕ => Nat.pair e x := by
  refine ⟨(Primrec₂.natPair.comp (Primrec.const e) Primrec.id).to_comp, fun a b hab => ?_⟩
  have := congrArg Nat.unpair hab
  simpa using this

/-- **A universal `Σ⁰ₙ` predicate is hard for the level under one-one reducibility**: the
reduction is `x ↦ ⟨e, x⟩`, which is injective. -/
theorem UnivSigma.oneOne_hard {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) (Q : ℕ → Prop)
    (hQ : SigmaAt n Q) : Q ≤₁ U := by
  obtain ⟨e, he⟩ := h.2 Q hQ
  obtain ⟨hcomp, hinj⟩ := computable_injective_pairLeft e
  exact ⟨_, hcomp, hinj, he⟩

/-- **A universal `Σ⁰ₙ` predicate is `Σ⁰ₙ`-complete.** -/
theorem UnivSigma.sigmaComplete {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) :
    SigmaComplete n U :=
  ⟨h.1, fun Q hQ => (h.oneOne_hard Q hQ).to_many_one⟩

/-- **A universal `Π⁰ₙ` predicate is hard for the level under one-one reducibility.** -/
theorem UnivPi.oneOne_hard {n : ℕ} {V : ℕ → Prop} (h : UnivPi n V) (Q : ℕ → Prop)
    (hQ : PiAt n Q) : Q ≤₁ V := by
  obtain ⟨e, he⟩ := h.2 Q hQ
  obtain ⟨hcomp, hinj⟩ := computable_injective_pairLeft e
  exact ⟨_, hcomp, hinj, he⟩

/-- **A universal `Π⁰ₙ` predicate is `Π⁰ₙ`-complete.** -/
theorem UnivPi.piComplete {n : ℕ} {V : ℕ → Prop} (h : UnivPi n V) : PiComplete n V :=
  ⟨h.1, fun Q hQ => (h.oneOne_hard Q hQ).to_many_one⟩

/-- **Every level `n + 1` has a `Σ⁰ₙ₊₁`-complete predicate.** -/
theorem exists_sigmaComplete (n : ℕ) : ∃ P : ℕ → Prop, SigmaComplete (n + 1) P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨U, hU.sigmaComplete⟩

/-- **Every level `n + 1` has a `Π⁰ₙ₊₁`-complete predicate.** -/
theorem exists_piComplete (n : ℕ) : ∃ P : ℕ → Prop, PiComplete (n + 1) P := by
  obtain ⟨V, hV⟩ := exists_univPi n
  exact ⟨V, hV.piComplete⟩

/-- The completeness of the previous theorem holds already for one-one reducibility. -/
theorem exists_sigmaOneOneComplete (n : ℕ) :
    ∃ P : ℕ → Prop, SigmaAt (n + 1) P ∧ ∀ Q : ℕ → Prop, SigmaAt (n + 1) Q → Q ≤₁ P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨U, hU.1, hU.oneOne_hard⟩

/-- The `Π` form: completeness for one-one reducibility. -/
theorem exists_piOneOneComplete (n : ℕ) :
    ∃ P : ℕ → Prop, PiAt (n + 1) P ∧ ∀ Q : ℕ → Prop, PiAt (n + 1) Q → Q ≤₁ P := by
  obtain ⟨V, hV⟩ := exists_univPi n
  exact ⟨V, hV.1, hV.oneOne_hard⟩

/-! ## Complementation and transport -/

/-- **The complement of a `Σ⁰ₙ`-complete predicate is `Π⁰ₙ`-complete.** -/
theorem SigmaComplete.compl {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete n P) :
    PiComplete n fun x => ¬ P x := by
  classical
  refine ⟨piAt_iff_sigmaAt_not.2 (h.1.of_iff fun _ => not_not), fun Q hQ => ?_⟩
  obtain ⟨f, hf, hred⟩ := h.2 _ (piAt_iff_sigmaAt_not.1 hQ)
  exact ⟨f, hf, fun x => ⟨fun hx hP => (hred x).2 hP hx,
    fun hx => not_not.1 fun hnq => hx ((hred x).1 hnq)⟩⟩

/-- **The complement of a `Π⁰ₙ`-complete predicate is `Σ⁰ₙ`-complete.** -/
theorem PiComplete.compl {n : ℕ} {P : ℕ → Prop} (h : PiComplete n P) :
    SigmaComplete n fun x => ¬ P x := by
  classical
  refine ⟨sigmaAt_iff_piAt_not.2 (h.1.of_iff fun _ => not_not), fun Q hQ => ?_⟩
  obtain ⟨f, hf, hred⟩ := h.2 _ (sigmaAt_iff_piAt_not.1 hQ)
  exact ⟨f, hf, fun x => ⟨fun hx hP => (hred x).2 hP hx,
    fun hx => not_not.1 fun hnq => hx ((hred x).1 hnq)⟩⟩

/-- **Completeness travels upwards along reductions**: anything at the level to which a complete
predicate reduces is complete as well. -/
theorem SigmaComplete.of_manyOne {n : ℕ} {P R : ℕ → Prop} (h : SigmaComplete n P)
    (hR : SigmaAt n R) (hPR : P ≤₀ R) : SigmaComplete n R :=
  ⟨hR, fun Q hQ => (h.2 Q hQ).trans hPR⟩

/-- The `Π` form of the previous theorem. -/
theorem PiComplete.of_manyOne {n : ℕ} {P R : ℕ → Prop} (h : PiComplete n P) (hR : PiAt n R)
    (hPR : P ≤₀ R) : PiComplete n R :=
  ⟨hR, fun Q hQ => (h.2 Q hQ).trans hPR⟩

/-- Two `Σ⁰ₙ`-complete predicates are many-one equivalent. -/
theorem SigmaComplete.manyOneEquiv {n : ℕ} {P R : ℕ → Prop} (hP : SigmaComplete n P)
    (hR : SigmaComplete n R) : P ≤₀ R ∧ R ≤₀ P :=
  ⟨hR.2 P hP.1, hP.2 R hR.1⟩

/-! ## What completeness rules out -/

/-- **A `Σ⁰ₙ₊₁`-complete predicate is not `Π⁰ₙ₊₁`.**  Otherwise every `Σ⁰ₙ₊₁` predicate would be
`Π⁰ₙ₊₁`, and the two sides of the level would coincide. -/
theorem SigmaComplete.not_piAt {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete (n + 1) P) :
    ¬ PiAt (n + 1) P := by
  intro hPi
  obtain ⟨Q, hQ, hnQ⟩ := exists_sigmaAt_not_piAt n
  exact hnQ (hPi.of_manyOne (h.2 Q hQ))

/-- **A `Π⁰ₙ₊₁`-complete predicate is not `Σ⁰ₙ₊₁`.** -/
theorem PiComplete.not_sigmaAt {n : ℕ} {P : ℕ → Prop} (h : PiComplete (n + 1) P) :
    ¬ SigmaAt (n + 1) P := by
  intro hSig
  obtain ⟨Q, hQ, hnQ⟩ := exists_piAt_not_sigmaAt n
  exact hnQ (hSig.of_manyOne (h.2 Q hQ))

/-- A `Σ⁰ₙ₊₁`-complete predicate is not `Δ⁰ₙ₊₁`. -/
theorem SigmaComplete.not_deltaAt {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete (n + 1) P) :
    ¬ DeltaAt (n + 1) P := fun hD => h.not_piAt hD.2

/-- A `Π⁰ₙ₊₁`-complete predicate is not `Δ⁰ₙ₊₁`. -/
theorem PiComplete.not_deltaAt {n : ℕ} {P : ℕ → Prop} (h : PiComplete (n + 1) P) :
    ¬ DeltaAt (n + 1) P := fun hD => h.not_sigmaAt hD.1

/-- **A `Σ⁰ₙ₊₁`-complete predicate does not sit at the previous level**: it is not `Σ⁰ₙ`, so the
hierarchy really climbs at a complete predicate. -/
theorem SigmaComplete.not_sigmaAt_lower {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete (n + 1) P) :
    ¬ SigmaAt n P := fun hlow => h.not_piAt (PiAt.of_sigmaAt hlow)

/-- A `Σ⁰ₙ₊₁`-complete predicate is not `Π⁰ₙ` either. -/
theorem SigmaComplete.not_piAt_lower {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete (n + 1) P) :
    ¬ PiAt n P := fun hlow => h.not_piAt hlow.succ

/-- A `Π⁰ₙ₊₁`-complete predicate is not `Π⁰ₙ`. -/
theorem PiComplete.not_piAt_lower {n : ℕ} {P : ℕ → Prop} (h : PiComplete (n + 1) P) :
    ¬ PiAt n P := fun hlow => h.not_sigmaAt (SigmaAt.of_piAt hlow)

/-- **A complete predicate for a level is never computable.** -/
theorem SigmaComplete.not_computablePred {n : ℕ} {P : ℕ → Prop} (h : SigmaComplete (n + 1) P) :
    ¬ ComputablePred P := fun hc => h.not_sigmaAt_lower (sigmaAt_of_computablePred hc n)

/-- A `Π⁰ₙ₊₁`-complete predicate is never computable either. -/
theorem PiComplete.not_computablePred {n : ℕ} {P : ℕ → Prop} (h : PiComplete (n + 1) P) :
    ¬ ComputablePred P := fun hc => h.not_piAt_lower (piAt_of_computablePred hc n)

/-! ## Level one: the halting set of the lambda calculus -/

/-- **The halting set of the lambda calculus is `Σ⁰₁`-complete.**  This is the `Σ₁`-completeness
theorem of `Start/HaltingComplete.lean`, read inside the arithmetical hierarchy. -/
theorem sigmaComplete_one_codeHasNormalForm : SigmaComplete 1 CodeHasNormalForm :=
  ⟨sigmaAt_one_iff.2 rePred_codeHasNormalForm,
    fun _ hQ => rePred_le_codeHasNormalForm (sigmaAt_one_iff.1 hQ)⟩

/-- **"Reduces to a Church numeral" is `Σ⁰₁`-complete** as well. -/
theorem sigmaComplete_one_codeConverges : SigmaComplete 1 CodeConverges :=
  ⟨sigmaAt_one_iff.2 rePred_codeConverges,
    fun _ hQ => rePred_le_codeConverges (sigmaAt_one_iff.1 hQ)⟩

/-- Completeness at level one recovers undecidability: the halting set is not computable. -/
theorem not_computablePred_codeHasNormalForm' : ¬ ComputablePred CodeHasNormalForm :=
  sigmaComplete_one_codeHasNormalForm.not_computablePred

/-- The complement of the halting set is `Π⁰₁`-complete. -/
theorem piComplete_one_not_codeHasNormalForm :
    PiComplete 1 fun c => ¬ CodeHasNormalForm c :=
  sigmaComplete_one_codeHasNormalForm.compl

/-! ## The arithmetical predicates have no complete member -/

/-- **No arithmetical predicate is complete for all of them.**  Each single level has a complete
predicate, but their union does not: a complete `P` would be `Σ⁰ₙ` for some `n`, and then every
arithmetical predicate would be `Σ⁰ₙ`. -/
theorem not_exists_arithmetical_complete :
    ¬ ∃ P : ℕ → Prop, Arithmetical P ∧ ∀ Q : ℕ → Prop, Arithmetical Q → Q ≤₀ P := by
  rintro ⟨P, ⟨n, hn⟩, hall⟩
  obtain ⟨Q, hQ, hnQ⟩ := exists_arithmetical_not_sigmaAt n
  exact hnQ (hn.of_manyOne (hall Q hQ))

end Arith
end Lambda
