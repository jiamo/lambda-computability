/-
**The arithmetical hierarchy is proper.**

`Start/ArithHierarchy.lean` defines the classes `Σ⁰ₙ`, `Π⁰ₙ` and `Δ⁰ₙ` and proves their
structural theory.  Nothing there rules out the possibility that the classes collapse: that
every `Σ⁰₂` predicate is already `Σ⁰₁`, say.  This module shows that they do not, by the
classical route through *universal* predicates and diagonalisation.

* `Lambda.Arith.UnivSigma`, `Lambda.Arith.UnivPi` — being universal for a level: a predicate of
  one number that is itself at the level, and into which every predicate at that level is
  substituted by fixing an index.
* `Lambda.Arith.univOne` — the universal `Σ⁰₁` predicate `⟨e, x⟩ ↦ x ∈ Wₑ`, universal by the
  standard numbering of the r.e. sets (`Lambda.Post.Wset`, `Lambda.Post.exists_index`).
* `Lambda.Arith.UnivSigma.not` — negating a universal `Σ⁰ₙ` predicate gives a universal `Π⁰ₙ`
  one; `Lambda.Arith.UnivPi.sigmaSucc` — prefixing a universal `Π⁰ₙ` predicate with one
  existential quantifier gives a universal `Σ⁰ₙ₊₁` one.  Hence
  `Lambda.Arith.exists_univSigma` : **every level `n + 1` has a universal predicate**.
* `Lambda.Arith.UnivSigma.not_sigmaAt_diag` — the diagonal complement `x ↦ ¬ U ⟨x, x⟩` of a
  universal `Σ⁰ₙ` predicate is not `Σ⁰ₙ`, while `Lambda.Arith.UnivSigma.piAt_diag` says it is
  `Π⁰ₙ`.
* The consequences, for every level `n + 1`:
  `Lambda.Arith.exists_piAt_not_sigmaAt`, `Lambda.Arith.exists_sigmaAt_not_piAt` (the two sides
  of a level differ), `Lambda.Arith.sigmaAt_ne_piAt`,
  `Lambda.Arith.exists_sigmaAt_not_deltaAt` (`Δ⁰ₙ₊₁ ⊊ Σ⁰ₙ₊₁`), and the properness of the
  hierarchy itself: `Lambda.Arith.sigmaAt_proper`, `Lambda.Arith.piAt_proper`,
  `Lambda.Arith.deltaAt_proper`.
* `Lambda.Arith.Arithmetical` — sitting at some level; `Lambda.Arith.exists_arithmetical_not_sigmaAt`
  — no level exhausts the arithmetical predicates, and
  `Lambda.Arith.not_exists_univ_arithmetical` — the union of the levels, unlike each single level,
  has no universal predicate.

At level one this recovers familiar facts: the halting problem is `Σ⁰₁` but not `Π⁰₁`, and the
`Σ⁰₁` predicates are not closed under complement.
-/

import Start.ArithHierarchy

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ## Universal predicates -/

/-- `U` is **universal for `Σ⁰ₙ`**: it is itself `Σ⁰ₙ`, and every `Σ⁰ₙ` predicate is obtained
from it by fixing the first component of the argument pair. -/
def UnivSigma (n : ℕ) (U : ℕ → Prop) : Prop :=
  SigmaAt n U ∧ ∀ P : ℕ → Prop, SigmaAt n P → ∃ e, ∀ x, P x ↔ U (Nat.pair e x)

/-- `V` is **universal for `Π⁰ₙ`**. -/
def UnivPi (n : ℕ) (V : ℕ → Prop) : Prop :=
  PiAt n V ∧ ∀ P : ℕ → Prop, PiAt n P → ∃ e, ∀ x, P x ↔ V (Nat.pair e x)

/-- **Negating a universal `Σ⁰ₙ` predicate gives a universal `Π⁰ₙ` predicate.** -/
theorem UnivSigma.not {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) :
    UnivPi n fun z => ¬ U z := by
  classical
  refine ⟨piAt_iff_sigmaAt_not.2 (h.1.of_iff fun x => not_not), ?_⟩
  intro P hP
  obtain ⟨e, he⟩ := h.2 _ (piAt_iff_sigmaAt_not.1 hP)
  refine ⟨e, fun x => ?_⟩
  change P x ↔ ¬ U (Nat.pair e x)
  rw [← he x, not_not]

/-- One existential quantifier in front of a universal `Π⁰ₙ` predicate, with the index carried
along: the intended reading of `sigmaSucc V ⟨e, x⟩` is `∃ y, V ⟨e, ⟨x, y⟩⟩`. -/
def sigmaSucc (V : ℕ → Prop) (z : ℕ) : Prop :=
  ∃ y, V (Nat.pair z.unpair.1 (Nat.pair z.unpair.2 y))

/-- The rearrangement of the argument that `sigmaSucc` performs is computable. -/
theorem computable_sigmaSuccArg :
    Computable fun w : ℕ =>
      Nat.pair w.unpair.1.unpair.1 (Nat.pair w.unpair.1.unpair.2 w.unpair.2) := by
  have h1 : Primrec fun w : ℕ => w.unpair.1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun w : ℕ => w.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp h1))
    (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp h1)) h2)).to_comp

/-- **A universal `Π⁰ₙ` predicate yields a universal `Σ⁰ₙ₊₁` predicate.** -/
theorem UnivPi.sigmaSucc {n : ℕ} {V : ℕ → Prop} (h : UnivPi n V) :
    UnivSigma (n + 1) (sigmaSucc V) := by
  constructor
  · refine sigmaAt_succ_iff.2 ⟨fun w =>
      V (Nat.pair w.unpair.1.unpair.1 (Nat.pair w.unpair.1.unpair.2 w.unpair.2)),
      h.1.subst computable_sigmaSuccArg, fun x => ?_⟩
    simp only [Arith.sigmaSucc, Nat.unpair_pair]
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := sigmaAt_succ_iff.1 hP
    obtain ⟨e, he⟩ := h.2 Q hQ
    refine ⟨e, fun x => ?_⟩
    rw [hPQ x]
    simp only [Arith.sigmaSucc, Nat.unpair_pair]
    exact exists_congr fun y => he (Nat.pair x y)

/-! ## The universal `Σ⁰₁` predicate -/

/-- The universal `Σ⁰₁` predicate: `univOne ⟨e, x⟩` says that `x` belongs to the `e`-th
recursively enumerable set. -/
def univOne (z : ℕ) : Prop := Post.Wset z.unpair.1 z.unpair.2

/-- The universal `Σ⁰₁` predicate is recursively enumerable. -/
theorem rePred_univOne : REPred univOne := by
  have hcode : Computable fun z : ℕ => (ofNat Code z.unpair.1) :=
    (Computable.ofNat Code).comp (Primrec.fst.comp Primrec.unpair).to_comp
  have hsnd : Computable fun z : ℕ => z.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  exact (Code.eval_part.comp hcode hsnd).dom_re

/-- **Level one has a universal predicate**: the numbering of the r.e. sets. -/
theorem univSigma_one : UnivSigma 1 univOne := by
  refine ⟨sigmaAt_one_iff.2 rePred_univOne, fun P hP => ?_⟩
  obtain ⟨e, he⟩ := Post.exists_index (sigmaAt_one_iff.1 hP)
  refine ⟨e, fun x => ?_⟩
  simpa [univOne] using he x

/-- **Every level `n + 1` of the hierarchy has a universal predicate.** -/
theorem exists_univSigma : ∀ n : ℕ, ∃ U : ℕ → Prop, UnivSigma (n + 1) U
  | 0 => ⟨univOne, univSigma_one⟩
  | (n + 1) => by
      obtain ⟨U, hU⟩ := exists_univSigma n
      exact ⟨sigmaSucc fun z => ¬ U z, hU.not.sigmaSucc⟩

/-- Every level `n + 1` has a universal `Π` predicate as well. -/
theorem exists_univPi (n : ℕ) : ∃ V : ℕ → Prop, UnivPi (n + 1) V := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨_, hU.not⟩

/-! ## Diagonalisation -/

/-- **The diagonal complement of a universal `Σ⁰ₙ` predicate is not `Σ⁰ₙ`.** -/
theorem UnivSigma.not_sigmaAt_diag {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) :
    ¬ SigmaAt n fun x => ¬ U (Nat.pair x x) := by
  intro hD
  obtain ⟨e, he⟩ := h.2 _ hD
  by_cases hUe : U (Nat.pair e e)
  · exact (he e).2 hUe hUe
  · exact hUe ((he e).1 hUe)

/-- The diagonal complement of a universal `Σ⁰ₙ` predicate is `Π⁰ₙ`. -/
theorem UnivSigma.piAt_diag {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) :
    PiAt n fun x => ¬ U (Nat.pair x x) := by
  classical
  have hdiag : Computable fun x : ℕ => Nat.pair x x :=
    (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp
  exact piAt_iff_sigmaAt_not.2 ((h.1.subst hdiag).of_iff fun x => not_not)

/-- A universal `Σ⁰ₙ` predicate is not `Π⁰ₙ`. -/
theorem UnivSigma.not_piAt {n : ℕ} {U : ℕ → Prop} (h : UnivSigma n U) : ¬ PiAt n U := by
  classical
  intro hU
  have hdiag : Computable fun x : ℕ => Nat.pair x x :=
    (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp
  exact h.not_sigmaAt_diag (sigmaAt_iff_piAt_not.2 ((hU.subst hdiag).of_iff fun x => not_not))

/-! ## The hierarchy is proper -/

/-- **The two sides of a level differ**: at every level `n + 1` there is a `Π⁰ₙ₊₁` predicate
that is not `Σ⁰ₙ₊₁`. -/
theorem exists_piAt_not_sigmaAt (n : ℕ) :
    ∃ P : ℕ → Prop, PiAt (n + 1) P ∧ ¬ SigmaAt (n + 1) P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨_, hU.piAt_diag, hU.not_sigmaAt_diag⟩

/-- At every level `n + 1` there is a `Σ⁰ₙ₊₁` predicate that is not `Π⁰ₙ₊₁`: the universal one. -/
theorem exists_sigmaAt_not_piAt (n : ℕ) :
    ∃ P : ℕ → Prop, SigmaAt (n + 1) P ∧ ¬ PiAt (n + 1) P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨U, hU.1, hU.not_piAt⟩

/-- **`Σ⁰ₙ₊₁ ≠ Π⁰ₙ₊₁`.** -/
theorem sigmaAt_ne_piAt (n : ℕ) : ¬ ∀ P : ℕ → Prop, SigmaAt (n + 1) P ↔ PiAt (n + 1) P := by
  intro h
  obtain ⟨P, hP, hnP⟩ := exists_sigmaAt_not_piAt n
  exact hnP ((h P).1 hP)

/-- **`Δ⁰ₙ₊₁ ⊊ Σ⁰ₙ₊₁`**: the universal `Σ⁰ₙ₊₁` predicate is not `Δ⁰ₙ₊₁`. -/
theorem exists_sigmaAt_not_deltaAt (n : ℕ) :
    ∃ P : ℕ → Prop, SigmaAt (n + 1) P ∧ ¬ DeltaAt (n + 1) P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨U, hU.1, fun hD => hU.not_piAt hD.2⟩

/-- **`Δ⁰ₙ₊₁ ⊊ Π⁰ₙ₊₁`.** -/
theorem exists_piAt_not_deltaAt (n : ℕ) :
    ∃ P : ℕ → Prop, PiAt (n + 1) P ∧ ¬ DeltaAt (n + 1) P := by
  obtain ⟨U, hU⟩ := exists_univSigma n
  exact ⟨_, hU.piAt_diag, fun hD => hU.not_sigmaAt_diag hD.1⟩

/-- **The `Σ` hierarchy is proper**: `Σ⁰ₙ₊₁ ⊊ Σ⁰ₙ₊₂`. -/
theorem sigmaAt_proper (n : ℕ) :
    ∃ P : ℕ → Prop, SigmaAt (n + 2) P ∧ ¬ SigmaAt (n + 1) P := by
  obtain ⟨P, hP, hnP⟩ := exists_piAt_not_sigmaAt n
  exact ⟨P, SigmaAt.of_piAt hP, hnP⟩

/-- **The `Π` hierarchy is proper**: `Π⁰ₙ₊₁ ⊊ Π⁰ₙ₊₂`. -/
theorem piAt_proper (n : ℕ) :
    ∃ P : ℕ → Prop, PiAt (n + 2) P ∧ ¬ PiAt (n + 1) P := by
  obtain ⟨P, hP, hnP⟩ := exists_sigmaAt_not_piAt n
  exact ⟨P, PiAt.of_sigmaAt hP, hnP⟩

/-- **The `Δ` hierarchy is proper**: `Δ⁰ₙ₊₁ ⊊ Δ⁰ₙ₊₂`. -/
theorem deltaAt_proper (n : ℕ) :
    ∃ P : ℕ → Prop, DeltaAt (n + 2) P ∧ ¬ DeltaAt (n + 1) P := by
  obtain ⟨P, hP, hnP⟩ := exists_piAt_not_sigmaAt n
  exact ⟨P, DeltaAt.of_piAt hP, fun hD => hnP hD.1⟩

/-- **No level of the hierarchy is closed under complement.** -/
theorem not_sigmaAt_closed_under_not (n : ℕ) :
    ¬ ∀ P : ℕ → Prop, SigmaAt (n + 1) P → SigmaAt (n + 1) fun x => ¬ P x := by
  classical
  intro h
  obtain ⟨P, hP, hnP⟩ := exists_sigmaAt_not_piAt n
  exact hnP (piAt_iff_sigmaAt_not.2 (h P hP))

/-! ## No universal arithmetical predicate -/

/-- A predicate is **arithmetical** when it sits at some level of the hierarchy. -/
def Arithmetical (P : ℕ → Prop) : Prop := ∃ n, SigmaAt n P

/-- The arithmetical predicates are closed under complement. -/
theorem Arithmetical.not {P : ℕ → Prop} (h : Arithmetical P) : Arithmetical fun x => ¬ P x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, piAt_iff_sigmaAt_not.1 (PiAt.of_sigmaAt hn)⟩

/-- The arithmetical predicates are closed under substituting a computable function. -/
theorem Arithmetical.subst {P : ℕ → Prop} (h : Arithmetical P) {f : ℕ → ℕ}
    (hf : Computable f) : Arithmetical fun x => P (f x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.subst hf⟩

/-- **There is no universal arithmetical predicate**: no single arithmetical predicate has every
arithmetical predicate among its sections.  (Levels do have universal predicates; their union
does not.) -/
theorem not_exists_univ_arithmetical :
    ¬ ∃ T : ℕ → Prop, Arithmetical T ∧
      ∀ P : ℕ → Prop, Arithmetical P → ∃ e, ∀ x, P x ↔ T (Nat.pair e x) := by
  rintro ⟨T, hT, huniv⟩
  have hdiag : Computable fun x : ℕ => Nat.pair x x :=
    (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp
  obtain ⟨e, he⟩ := huniv _ ((hT.subst hdiag).not)
  by_cases hTe : T (Nat.pair e e)
  · exact (he e).2 hTe hTe
  · exact hTe ((he e).1 hTe)

/-- No level exhausts the arithmetical predicates. -/
theorem exists_arithmetical_not_sigmaAt (n : ℕ) :
    ∃ P : ℕ → Prop, Arithmetical P ∧ ¬ SigmaAt n P := by
  obtain ⟨P, hP, hnP⟩ := exists_piAt_not_sigmaAt n
  exact ⟨P, ⟨n + 2, SigmaAt.of_piAt hP⟩, fun h => hnP h.succ⟩

/-! ## Level one, in familiar terms -/

/-- At level one, properness says that the r.e. predicates are not closed under complement. -/
theorem exists_rePred_not_rePred_compl :
    ∃ P : ℕ → Prop, REPred P ∧ ¬ REPred fun x => ¬ P x := by
  obtain ⟨P, hP, hnP⟩ := exists_sigmaAt_not_piAt 0
  exact ⟨P, sigmaAt_one_iff.1 hP, fun h => hnP (piAt_one_iff.2 h)⟩

/-- At level one, `Δ⁰₁ ⊊ Σ⁰₁` is the existence of an r.e. predicate that is not computable. -/
theorem exists_rePred_not_computablePred :
    ∃ P : ℕ → Prop, REPred P ∧ ¬ ComputablePred P := by
  obtain ⟨P, hP, hnP⟩ := exists_sigmaAt_not_deltaAt 0
  exact ⟨P, sigmaAt_one_iff.1 hP, fun h => hnP (deltaAt_one_iff.2 h)⟩

end Arith
end Lambda
