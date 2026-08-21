/-
Boundary / interface records inspired by LACI's obligation-based architecture.

These records package the key properties of the lambda calculus development
into clean interfaces that can be consumed by downstream modules without
depending on internal proof details.
-/

import Start.Syntax
import Start.Reduction
import Start.Church
import Start.EvalSound
import Start.Arithmetic
import Start.Combinators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section


------------------------------------------------------------------------
-- A14: ReductionBoundary — packages the reduction pipeline
------------------------------------------------------------------------

/-- Interface record for the reduction theory.
    A consumer only needs these fields to use confluence results. -/
structure ReductionBoundary where
  /-- Single-step reduction is embedded in the multi-step closure. -/
  step_to_reduces : ∀ {t t' : Lambda}, Lambda.step t t' → Lambda.reduces t t'
  /-- Transitivity of multi-step reduction. -/
  reduces_trans : ∀ {t₁ t₂ t₃ : Lambda}, Lambda.reduces t₁ t₂ → Lambda.reduces t₂ t₃ →
      Lambda.reduces t₁ t₃
  /-- Confluence: if t reduces to both t₁ and t₂, there is a common reduct. -/
  confluence : ∀ {t t₁ t₂ : Lambda}, Lambda.reduces t t₁ → Lambda.reduces t t₂ →
    ∃ t₃, Lambda.reduces t₁ t₃ ∧ Lambda.reduces t₂ t₃

------------------------------------------------------------------------
-- A15: EncodingBoundary — packages the Church numeral interface
------------------------------------------------------------------------

/-- Interface record for the Church numeral encoding of the naturals.

    The fields state that Church numerals are closed normal forms, that the
    encoding is injective, and that the successor combinator computes. -/
structure EncodingBoundary where
  /-- Church numerals are closed terms. -/
  church_closed : ∀ n : ℕ, Lambda.IsClosed (Lambda.church n)
  /-- Church numerals are normal forms. -/
  church_normal : ∀ n : ℕ, Lambda.is_normal (Lambda.church n)
  /-- Distinct naturals have distinct Church numerals. -/
  church_injective : ∀ {n m : ℕ}, Lambda.church n = Lambda.church m → n = m
  /-- Successor combinator computes correctly on church numerals. -/
  succ_correct : ∀ n : ℕ,
    Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n)) (Lambda.church (n + 1))

------------------------------------------------------------------------
-- A16: ComputabilityInternalizer — minimal computability interface
------------------------------------------------------------------------

/-- Minimal interface for consuming lambda computability results.
    Inspired by LACI's TM2LamInternalizer record: a witness term together with
    the obligation that it computes `f` on Church-encoded inputs. -/
structure ComputabilityInternalizer (f : ℕ →. ℕ) where
  /-- A witness term that computes the function. -/
  witnessF : Lambda
  /-- The witness correctly maps church-encoded inputs to outputs. -/
  witness_correct : ∀ n m : ℕ,
    f n = Part.some m ↔
      Lambda.reduces (Lambda.app witnessF (Lambda.church n)) (Lambda.church m)

------------------------------------------------------------------------
-- A17: Adapter — concrete theorems → ReductionBoundary
------------------------------------------------------------------------

/-- Build a ReductionBoundary from the concrete theorems in Start.Reduction. -/
theorem ReductionBoundary.fromConcrete : ReductionBoundary where
  step_to_reduces := fun hs =>
    Lambda.reduces.step _ _ _ hs (Lambda.reduces.refl _)
  reduces_trans := fun h1 h2 => Lambda.reduces_trans h1 h2
  confluence := fun h1 h2 => Lambda.confluence_theorem h1 h2

------------------------------------------------------------------------
-- A18: Adapter — concrete theorems → EncodingBoundary
------------------------------------------------------------------------

/-- Build an EncodingBoundary from the concrete theorems. -/
theorem EncodingBoundary.fromConcrete : EncodingBoundary where
  church_closed := Lambda.church_closed
  church_normal := Lambda.church_normal
  church_injective := Lambda.church_injective
  succ_correct := Lambda.succ_correct

------------------------------------------------------------------------
-- A19: Adapter — concrete theorems → ComputabilityInternalizer
------------------------------------------------------------------------

/-- Build a ComputabilityInternalizer from a LambdaComputable witness. -/
def ComputabilityInternalizer.fromLambdaComputable
    (f : ℕ →. ℕ) (hf : LambdaComputable f) : ComputabilityInternalizer f where
  witnessF := hf.choose
  witness_correct := hf.choose_spec

------------------------------------------------------------------------
-- A20: Roundtrip — internalizer recovers boundary obligations
------------------------------------------------------------------------

/-- The reduction boundary can be recovered from any setting that has
    step, transitivity, and confluence. This is the "roundtrip" property. -/
theorem ReductionBoundary.roundtrip (rb : ReductionBoundary) :
    ∀ {t t₁ t₂ : Lambda},
    Lambda.reduces t t₁ → Lambda.reduces t t₂ →
    ∃ t₃, Lambda.reduces t₁ t₃ ∧ Lambda.reduces t₂ t₃ :=
  rb.confluence

/-- Roundtrip for the computability interface: an internalizer for `f`
    witnesses that `f` is lambda computable. -/
theorem ComputabilityInternalizer.toLambdaComputable {f : ℕ →. ℕ}
    (ci : ComputabilityInternalizer f) : LambdaComputable f :=
  ⟨ci.witnessF, ci.witness_correct⟩

end
